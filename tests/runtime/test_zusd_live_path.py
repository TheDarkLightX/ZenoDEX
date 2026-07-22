"""Live-path wiring tests for zUSD single-vault Rust authority."""

from __future__ import annotations

import os
import sys
from dataclasses import asdict
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
_TOOLS_RUNTIME = _REPO / "tools" / "runtime"
for _p in (str(_REPO), str(_TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402

from src.core import zusd  # noqa: E402
from src.runtime.authority import (  # noqa: E402
    AuthorityError,
    AuthorityMode,
    AuthorityPolicy,
    reset_active_authority_policy,
    set_active_authority_policy,
)


def _policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"zusd": mode},
        promoted_surfaces=frozenset({"zusd"}),
    )


@pytest.fixture(autouse=True)
def _reset_policy_after():
    yield
    reset_active_authority_policy()


@pytest.fixture(scope="module")
def rust_env():
    try:
        bin_path = locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"rust runtime unavailable: {exc}")
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(bin_path)
    yield bin_path
    if old is None:
        os.environ.pop("ZENODEX_RUNTIME_BIN", None)
    else:
        os.environ["ZENODEX_RUNTIME_BIN"] = old


def _cmd(tag: str, **args) -> zusd.ZUSDCommand:
    return zusd.ZUSDCommand(tag, args)


def test_default_python_authority_is_byte_identical():
    s = zusd.init_state()
    cmd = _cmd("bootstrap_oracle", auth_ok=True, price_e8=zusd.E8)
    assert zusd.step(s, cmd) == zusd._step_python(s, cmd)


def test_rust_authority_with_python_shadow_agrees_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    rust_state = zusd.init_state()
    py_state = zusd.init_state()
    for cmd in (
        _cmd("bootstrap_oracle", auth_ok=True, price_e8=zusd.E8),
        _cmd("deposit_collateral", amount_e8=1_000_000_000_000),
        _cmd("mint_zusd", amount_e8=500 * zusd.E8),
        _cmd("repay_zusd", amount_e8=100 * zusd.E8),
        _cmd("deposit_sp", amount_e8=50 * zusd.E8),
        _cmd("withdraw_sp", amount_e8=25 * zusd.E8),
        _cmd("redeem_zusd", amount_e8=50 * zusd.E8),
    ):
        got = zusd.step(rust_state, cmd)
        ref = zusd._step_python(py_state, cmd)
        assert got.ok == ref.ok
        assert got.effects == ref.effects
        assert asdict(got.state) == asdict(ref.state)
        rust_state = got.state
        py_state = ref.state


def test_rust_authority_finalized_oracle_liquidation_sequence(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    state = zusd.init_state()

    for cmd in (
        _cmd("bootstrap_oracle", auth_ok=True, price_e8=100 * zusd.E8),
        _cmd("deposit_collateral", amount_e8=2 * zusd.E8),
        _cmd("mint_zusd", amount_e8=150 * zusd.E8),
        _cmd("deposit_sp", amount_e8=150 * zusd.E8),
        _cmd("oracle_report", auth_ok=True, price_e8=70 * zusd.E8),
    ):
        result = zusd.step(state, cmd)
        assert result.ok, result.error
        assert result.state is not None
        state = result.state

    before_reject = state
    pending_liquidation = zusd.step(state, _cmd("liquidate"))
    assert pending_liquidation.ok is False
    assert pending_liquidation.state is None
    assert pending_liquidation.effects is None
    assert pending_liquidation.error == "liquidation blocked by oracle pending mismatch"
    assert state == before_reject

    committed = zusd.step(state, _cmd("oracle_commit", auth_ok=True))
    assert committed.ok, committed.error
    assert committed.state is not None
    assert "health_vault_below_mcr" in zusd.check_health_conditions(committed.state)

    liquidated = zusd.step(committed.state, _cmd("liquidate"))
    assert liquidated.ok, liquidated.error
    assert liquidated.state is not None
    assert liquidated.effects is not None
    assert liquidated.state.debt_e8 == 0
    assert liquidated.effects["liquidated_debt_e8"] == 150 * zusd.E8


def test_rust_shadow_mode_keeps_python_authoritative_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    s = zusd.init_state()
    cmd = _cmd("bootstrap_oracle", auth_ok=True, price_e8=zusd.E8)
    assert zusd.step(s, cmd) == zusd._step_python(s, cmd)


def test_fails_closed_on_injected_disagreement(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    real = zusd._step_python

    def fake_step(state, cmd):
        result = real(state, cmd)
        if result.ok and result.state is not None:
            bad = zusd.ZUSDState(**{**result.state.__dict__, "now_epoch": result.state.now_epoch + 1})
            return zusd.ZUSDStepResult(ok=True, state=bad, effects=result.effects)
        return result

    monkeypatch.setattr(zusd, "_step_python", fake_step)
    with pytest.raises(AuthorityError):
        zusd.step(zusd.init_state(), _cmd("bootstrap_oracle", auth_ok=True, price_e8=zusd.E8))


def test_fails_closed_when_rust_unavailable_under_authority():
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
        with pytest.raises(AuthorityError):
            zusd.step(zusd.init_state(), _cmd("bootstrap_oracle", auth_ok=True, price_e8=zusd.E8))
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old


def test_rust_shadow_unavailable_keeps_python():
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
        s = zusd.init_state()
        cmd = _cmd("bootstrap_oracle", auth_ok=True, price_e8=zusd.E8)
        assert zusd.step(s, cmd) == zusd._step_python(s, cmd)
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old
