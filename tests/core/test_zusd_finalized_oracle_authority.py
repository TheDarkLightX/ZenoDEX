from __future__ import annotations

from src.core.zusd import (
    E8,
    ZUSDCommand,
    ZUSDMultiCommand,
    ZUSDMultiState,
    ZUSDState,
    check_health_conditions,
    check_invariants,
    check_multi_health_conditions,
    check_multi_invariants,
    init_multi_state,
    init_state,
    step,
    step_multi,
)


def _single_ok(state: ZUSDState, tag: str, **args: int | bool) -> ZUSDState:
    result = step(state, ZUSDCommand(tag=tag, args=args))
    assert result.ok, result.error
    assert result.state is not None
    return result.state


def _multi_ok(
    state: ZUSDMultiState,
    tag: str,
    **args: int | bool | str,
) -> ZUSDMultiState:
    result = step_multi(state, ZUSDMultiCommand(tag=tag, args=args))
    assert result.ok, result.error
    assert result.state is not None
    return result.state


def _single_pending_distress() -> ZUSDState:
    state = init_state()
    state = _single_ok(state, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    state = _single_ok(state, "deposit_collateral", amount_e8=2 * E8)
    state = _single_ok(state, "mint_zusd", amount_e8=150 * E8)
    state = _single_ok(state, "deposit_sp", amount_e8=150 * E8)
    return _single_ok(state, "oracle_report", price_e8=70 * E8, auth_ok=True)


def _multi_pending_distress() -> ZUSDMultiState:
    state = init_multi_state()
    state = _multi_ok(state, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    state = _multi_ok(state, "deposit_collateral", vault="a", amount_e8=3 * E8)
    state = _multi_ok(state, "deposit_collateral", vault="b", amount_e8=2 * E8)
    state = _multi_ok(state, "mint_zusd", vault="a", amount_e8=150 * E8)
    state = _multi_ok(state, "mint_zusd", vault="b", amount_e8=100 * E8)
    state = _multi_ok(state, "deposit_sp", amount_e8=180 * E8)
    return _multi_ok(state, "oracle_report", price_e8=50 * E8, auth_ok=True)


def test_pending_single_price_cannot_authorize_liquidation() -> None:
    state = _single_pending_distress()

    result = step(state, ZUSDCommand(tag="liquidate", args={}))

    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == "liquidation blocked by oracle pending mismatch"
    assert state.price_e8 == 100 * E8
    assert state.price_pending_e8 == 70 * E8


def test_single_price_finalization_precedes_liquidation() -> None:
    pending = _single_pending_distress()

    committed_result = step(
        pending,
        ZUSDCommand(tag="oracle_commit", args={"auth_ok": True}),
    )
    assert committed_result.ok, committed_result.error
    assert committed_result.state is not None
    committed = committed_result.state
    assert committed.price_e8 == 70 * E8
    assert committed.price_pending_e8 == 70 * E8
    assert check_invariants(committed) == []
    assert "health_vault_below_mcr" in check_health_conditions(committed)
    assert "health_system_bad_debt" in check_health_conditions(committed)

    liquidated = step(committed, ZUSDCommand(tag="liquidate", args={}))
    assert liquidated.ok, liquidated.error
    assert liquidated.state is not None
    assert liquidated.effects is not None
    assert liquidated.state.debt_e8 == 0
    assert liquidated.state.collateral_e8 == 0
    assert liquidated.effects["liquidated_debt_e8"] == 150 * E8


def test_stale_finalized_single_price_cannot_authorize_liquidation() -> None:
    state = _single_pending_distress()
    state = _single_ok(state, "oracle_commit", auth_ok=True)
    state = _single_ok(
        state,
        "advance_epoch",
        delta=state.max_oracle_staleness_epochs + 1,
    )

    result = step(state, ZUSDCommand(tag="liquidate", args={}))

    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == "liquidation blocked by stale finalized oracle"


def test_fresh_single_report_restores_finalization_after_oracle_outage() -> None:
    state = _single_pending_distress()
    state = _single_ok(state, "oracle_commit", auth_ok=True)
    state = _single_ok(
        state,
        "advance_epoch",
        delta=state.max_oracle_staleness_epochs + 1,
    )
    stale_finalized_epoch = state.oracle_last_update_epoch

    state = _single_ok(state, "oracle_report", price_e8=60 * E8, auth_ok=True)
    assert state.oracle_last_update_epoch == stale_finalized_epoch
    assert state.oracle_pending_report_epoch == state.now_epoch

    state = _single_ok(state, "oracle_commit", auth_ok=True)
    assert state.oracle_last_update_epoch == state.now_epoch
    assert state.price_e8 == state.price_pending_e8 == 60 * E8

    liquidated = step(state, ZUSDCommand(tag="liquidate", args={}))
    assert liquidated.ok, liquidated.error
    assert liquidated.state is not None
    assert liquidated.effects is not None


def test_pending_multi_price_cannot_authorize_liquidation() -> None:
    state = _multi_pending_distress()

    result = step_multi(
        state,
        ZUSDMultiCommand(tag="liquidate", args={"vault": "a"}),
    )

    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == "liquidation blocked by oracle pending mismatch"
    assert state.price_e8 == 100 * E8
    assert state.price_pending_e8 == 50 * E8


def test_multi_price_finalization_precedes_liquidation() -> None:
    pending = _multi_pending_distress()

    committed_result = step_multi(
        pending,
        ZUSDMultiCommand(tag="oracle_commit", args={"auth_ok": True}),
    )
    assert committed_result.ok, committed_result.error
    assert committed_result.state is not None
    committed = committed_result.state
    assert committed.price_e8 == 50 * E8
    assert committed.price_pending_e8 == 50 * E8
    assert check_multi_invariants(committed) == []
    health = check_multi_health_conditions(committed)
    assert "health_vault_a_below_mcr" in health
    assert "health_vault_b_below_mcr" in health

    liquidated = step_multi(
        committed,
        ZUSDMultiCommand(tag="liquidate", args={"vault": "a"}),
    )
    assert liquidated.ok, liquidated.error
    assert liquidated.state is not None
    assert liquidated.effects is not None
    assert liquidated.state.vault_a.debt_e8 == 0
    assert liquidated.state.vault_a.collateral_e8 == 0
    assert liquidated.state.vault_b.debt_e8 == 100 * E8
    assert liquidated.effects["vault"] == "a"


def test_stale_finalized_multi_price_cannot_authorize_liquidation() -> None:
    state = _multi_pending_distress()
    state = _multi_ok(state, "oracle_commit", auth_ok=True)
    state = _multi_ok(
        state,
        "advance_epoch",
        delta=state.max_oracle_staleness_epochs + 1,
    )

    result = step_multi(
        state,
        ZUSDMultiCommand(tag="liquidate", args={"vault": "a"}),
    )

    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == "liquidation blocked by stale finalized oracle"


def test_fresh_multi_report_restores_finalization_after_oracle_outage() -> None:
    state = _multi_pending_distress()
    state = _multi_ok(state, "oracle_commit", auth_ok=True)
    state = _multi_ok(
        state,
        "advance_epoch",
        delta=state.max_oracle_staleness_epochs + 1,
    )
    stale_finalized_epoch = state.oracle_last_update_epoch

    state = _multi_ok(state, "oracle_report", price_e8=40 * E8, auth_ok=True)
    assert state.oracle_last_update_epoch == stale_finalized_epoch
    assert state.oracle_pending_report_epoch == state.now_epoch

    state = _multi_ok(state, "oracle_commit", auth_ok=True)
    assert state.oracle_last_update_epoch == state.now_epoch
    assert state.price_e8 == state.price_pending_e8 == 40 * E8

    liquidated = step_multi(
        state,
        ZUSDMultiCommand(tag="liquidate", args={"vault": "a"}),
    )
    assert liquidated.ok, liquidated.error
    assert liquidated.state is not None
    assert liquidated.effects is not None
