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


def test_authority_doc_parity_rejects_non_exact_shapes():
    state = zusd.init_state()
    accept_cmd = _cmd("bootstrap_oracle", auth_ok=True, price_e8=zusd.E8)
    accept_doc = zusd._result_to_authority_doc(state, accept_cmd, zusd._step_python(state, accept_cmd))
    assert zusd._authority_docs_agree(accept_doc, dict(accept_doc))
    assert not zusd._authority_docs_agree(accept_doc, {**accept_doc, "extra": "metadata"})

    missing_receipt = dict(accept_doc)
    missing_receipt.pop("receipt")
    assert not zusd._authority_docs_agree(accept_doc, missing_receipt)

    reject_cmd = _cmd("deposit_collateral", amount_e8=-1)
    reject_doc = zusd._result_to_authority_doc(state, reject_cmd, zusd._step_python(state, reject_cmd))
    assert zusd._authority_docs_agree(reject_doc, dict(reject_doc))
    assert not zusd._authority_docs_agree(reject_doc, {**reject_doc, "receipt": {"tag": "reject"}})
    assert not zusd._authority_docs_agree(reject_doc, {**reject_doc, "extra": "metadata"})


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
