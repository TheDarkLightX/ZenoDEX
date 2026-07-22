"""Rust/Python parity for the audit-critical zUSD authority repairs."""

from __future__ import annotations

import os
import sys
from dataclasses import asdict
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
for candidate in (str(REPO), str(TOOLS_RUNTIME)):
    if candidate not in sys.path:
        sys.path.insert(0, candidate)

from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402

from src.core import zusd  # noqa: E402
from src.runtime.authority import (  # noqa: E402
    AuthorityMode,
    AuthorityPolicy,
    reset_active_authority_policy,
    set_active_authority_policy,
)

E8 = zusd.E8


def _policy() -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"zusd": AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW},
        promoted_surfaces=frozenset({"zusd"}),
    )


@pytest.fixture(autouse=True)
def _reset_policy() -> None:
    yield
    reset_active_authority_policy()


@pytest.fixture(scope="module")
def rust_env() -> Path:
    try:
        binary = locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"Rust runtime unavailable: {exc}")
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(binary)
    yield binary
    if old is None:
        os.environ.pop("ZENODEX_RUNTIME_BIN", None)
    else:
        os.environ["ZENODEX_RUNTIME_BIN"] = old


def _cmd(tag: str, **args: int | bool) -> zusd.ZUSDCommand:
    return zusd.ZUSDCommand(tag, args)


def _step_both(state: zusd.ZUSDState, command: zusd.ZUSDCommand) -> zusd.ZUSDStepResult:
    reference = zusd._step_python(state, command)
    result = zusd.step(state, command)
    assert result.ok == reference.ok
    assert result.error == reference.error
    assert result.effects == reference.effects
    if result.state is None or reference.state is None:
        assert result.state is reference.state
    else:
        assert asdict(result.state) == asdict(reference.state)
    return result


def _accepted(state: zusd.ZUSDState, tag: str, **args: int | bool) -> zusd.ZUSDState:
    result = _step_both(state, _cmd(tag, **args))
    assert result.ok, result.error
    assert result.state is not None
    return result.state


def _cap_state() -> zusd.ZUSDState:
    return zusd.ZUSDState(
        now_epoch=0,
        oracle_seen=True,
        oracle_last_update_epoch=0,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        collateral_e8=100 * E8,
        debt_e8=1_400 * E8,
        free_debt_e8=100 * E8,
        sp_debt_e8=1_300 * E8,
        max_debt_e8=1_500 * E8,
        max_debt_supply_e8=1_500 * E8,
    )


def test_rust_mint_above_shared_vault_and_supply_cap_rejects(
    rust_env: Path,
) -> None:
    set_active_authority_policy(_policy())
    state = _cap_state()

    # The promoted Rust surface is single-vault. Valid parameters require the
    # per-vault cap to be no greater than the global cap, so this rejection is
    # selected by the per-vault check before the equivalent total-debt check.
    rejected = _step_both(state, _cmd("mint_zusd", amount_e8=101 * E8))

    assert rejected.ok is False
    assert rejected.state is None
    assert rejected.effects is None
    assert rejected.error == "mint exceeds per-vault max_debt_e8"
    assert state.debt_e8 == 1_400 * E8


def test_rust_mint_accepts_exact_total_debt_cap(rust_env: Path) -> None:
    set_active_authority_policy(_policy())

    accepted = _step_both(_cap_state(), _cmd("mint_zusd", amount_e8=100 * E8))

    assert accepted.ok, accepted.error
    assert accepted.state is not None
    assert accepted.state.debt_e8 == 1_500 * E8
    assert accepted.state.free_debt_e8 == 200 * E8
    assert accepted.state.sp_debt_e8 == 1_300 * E8
    assert zusd.check_invariants(accepted.state) == []


def _pending_distress() -> zusd.ZUSDState:
    state = zusd.init_state()
    state = _accepted(state, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    state = _accepted(state, "deposit_collateral", amount_e8=2 * E8)
    state = _accepted(state, "mint_zusd", amount_e8=150 * E8)
    state = _accepted(state, "deposit_sp", amount_e8=150 * E8)
    return _accepted(state, "oracle_report", price_e8=70 * E8, auth_ok=True)


def test_pending_observation_has_no_rust_liquidation_authority(rust_env: Path) -> None:
    set_active_authority_policy(_policy())
    pending = _pending_distress()

    rejected = _step_both(pending, _cmd("liquidate"))

    assert rejected.ok is False
    assert rejected.state is None
    assert rejected.effects is None
    assert rejected.error == "liquidation blocked by oracle pending mismatch"


def test_adverse_price_can_finalize_before_rust_liquidation(rust_env: Path) -> None:
    set_active_authority_policy(_policy())
    pending = _pending_distress()

    committed = _step_both(pending, _cmd("oracle_commit", auth_ok=True))
    assert committed.ok, committed.error
    assert committed.state is not None
    finalized = committed.state
    assert finalized.price_e8 == 70 * E8
    assert finalized.price_pending_e8 == 70 * E8
    assert zusd.check_invariants(finalized) == []
    health = zusd.check_health_conditions(finalized)
    assert "health_vault_below_mcr" in health
    assert "health_system_bad_debt" in health

    liquidated = _step_both(finalized, _cmd("liquidate"))
    assert liquidated.ok, liquidated.error
    assert liquidated.state is not None
    assert liquidated.effects is not None
    assert liquidated.state.debt_e8 == 0
    assert liquidated.state.collateral_e8 == 0
    assert liquidated.effects["liquidated_debt_e8"] == 150 * E8


def test_stale_finalized_price_has_no_rust_liquidation_authority(rust_env: Path) -> None:
    set_active_authority_policy(_policy())
    pending = _pending_distress()
    finalized = _accepted(pending, "oracle_commit", auth_ok=True)
    stale = _accepted(
        finalized,
        "advance_epoch",
        delta=finalized.max_oracle_staleness_epochs + 1,
    )

    rejected = _step_both(stale, _cmd("liquidate"))

    assert rejected.ok is False
    assert rejected.state is None
    assert rejected.effects is None
    assert rejected.error == "liquidation blocked by stale finalized oracle"
