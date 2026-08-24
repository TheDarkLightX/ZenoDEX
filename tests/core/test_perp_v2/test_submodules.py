from __future__ import annotations

from dataclasses import replace

import src.core.perp_v2.effects as effects
import src.core.perp_v2.guards as guards
import src.core.perp_v2.updates as updates
from src.core.perp_v2.errors import PerpInvariantError
from src.core.perp_v2.math import (
    MAX_COLLATERAL,
    liq_penalty_capped,
    maint_margin_req,
    partial_liq_penalty_capped,
    remaining_position_signed,
)
from src.core.perp_v2.state import initial_state
from src.core.perp_v2.types import Action, ActionParams, EpochPhase, Event, PerpState


def _open_state(**kwargs) -> PerpState:
    defaults = dict(
        now_epoch=2,
        epoch_phase=EpochPhase.OPEN,
        oracle_seen=True,
        oracle_last_update_epoch=2,
        index_price_e8=100_000_000,
        collateral_quote=100_000,
        position_base=100,
        entry_price_e8=100_000_000,
    )
    defaults.update(kwargs)
    return replace(initial_state(), **defaults)


def _ready_to_settle(**kwargs) -> PerpState:
    defaults = dict(
        now_epoch=2,
        epoch_phase=EpochPhase.PRICE_PUBLISHED,
        clearing_price_seen=True,
        clearing_price_epoch=2,
        clearing_price_e8=100_000_000,
        oracle_seen=True,
        oracle_last_update_epoch=1,
        index_price_e8=100_000_000,
        collateral_quote=100_000,
        position_base=100,
        entry_price_e8=100_000_000,
    )
    defaults.update(kwargs)
    return replace(initial_state(), **defaults)


def test_guard_set_position_breaker_is_reduce_only() -> None:
    state = _open_state(breaker_active=True)

    assert guards.guard_set_position(
        state,
        ActionParams(action=Action.SET_POSITION, new_position_base=50, auth_ok=True),
    )
    assert not guards.guard_set_position(
        state,
        ActionParams(action=Action.SET_POSITION, new_position_base=101, auth_ok=True),
    )
    assert not guards.guard_set_position(
        state,
        ActionParams(action=Action.SET_POSITION, new_position_base=-50, auth_ok=True),
    )


def test_guard_settle_epoch_rejects_liquidation_overflow_path() -> None:
    state = _ready_to_settle(
        collateral_quote=1_000,
        position_base=100_000,
        entry_price_e8=100_000_000,
        fee_pool_quote=MAX_COLLATERAL - 100,
        min_notional_for_bounty=0,
    )

    assert not guards.guard_settle_epoch(state, ActionParams(action=Action.SETTLE_EPOCH))


def test_guard_settle_epoch_rejects_missing_oracle_snapshot() -> None:
    # Arrange: the clearing price is current while no authenticated Oracle value exists.
    state = _ready_to_settle(
        oracle_seen=False,
        oracle_last_update_epoch=0,
        index_price_e8=0,
        position_base=0,
        entry_price_e8=0,
    )

    # Act.
    allowed = guards.guard_settle_epoch(state, ActionParams(action=Action.SETTLE_EPOCH))

    # Assert.
    assert allowed is False


def test_guard_settle_epoch_oracle_freshness_boundary() -> None:
    # Arrange: one state is exactly fresh; the other exceeds the window by one epoch.
    exact = _ready_to_settle(
        now_epoch=101,
        clearing_price_epoch=101,
        oracle_last_update_epoch=1,
        max_oracle_staleness_epochs=100,
    )
    stale = replace(
        exact,
        now_epoch=102,
        clearing_price_epoch=102,
    )

    # Act.
    exact_allowed = guards.guard_settle_epoch(exact, ActionParams(action=Action.SETTLE_EPOCH))
    stale_allowed = guards.guard_settle_epoch(stale, ActionParams(action=Action.SETTLE_EPOCH))

    # Assert.
    assert exact_allowed is True
    assert stale_allowed is False


def test_apply_settle_epoch_liquidation_branch_recomputes_accounting() -> None:
    state = _ready_to_settle(
        collateral_quote=1_000,
        position_base=100_000,
        entry_price_e8=100_000_000,
        fee_pool_quote=25,
        fee_income=25,
        initial_insurance=50,
        insurance_balance=75,
        min_notional_for_bounty=0,
    )

    next_state = updates.apply_settle_epoch(state, ActionParams(action=Action.SETTLE_EPOCH))
    expected_penalty = liq_penalty_capped(
        state.collateral_quote,
        state.position_base,
        state.clearing_price_e8,
        state.liquidation_penalty_bps,
        state.min_notional_for_bounty,
    )

    assert next_state.liquidated_this_step is True
    assert next_state.position_base == 0
    assert next_state.entry_price_e8 == 0
    assert next_state.fee_pool_quote == state.fee_pool_quote + expected_penalty
    assert next_state.fee_income == state.fee_income + expected_penalty
    assert next_state.insurance_balance == (
        next_state.initial_insurance + next_state.fee_income - next_state.claims_paid
    )


def test_apply_partial_liquidate_preserves_fee_and_insurance_identity() -> None:
    state = _open_state(
        collateral_quote=5_000,
        position_base=100_000,
        entry_price_e8=100_000_000,
        fee_pool_quote=100,
        fee_income=100,
        initial_insurance=500,
        insurance_balance=600,
        min_notional_for_bounty=0,
    )
    params = ActionParams(action=Action.PARTIAL_LIQUIDATE, fraction_bps=2_500, auth_ok=True)

    next_state = updates.apply_partial_liquidate(state, params)
    expected_remaining = remaining_position_signed(state.position_base, params.fraction_bps)
    expected_penalty = partial_liq_penalty_capped(
        state.collateral_quote,
        state.position_base,
        params.fraction_bps,
        state.index_price_e8,
        state.liquidation_penalty_bps,
        state.min_notional_for_bounty,
    )

    assert next_state.position_base == expected_remaining
    assert next_state.collateral_quote == state.collateral_quote - expected_penalty
    assert next_state.fee_pool_quote == state.fee_pool_quote + expected_penalty
    assert next_state.fee_income == state.fee_income + expected_penalty
    assert next_state.insurance_balance == (
        next_state.initial_insurance + next_state.fee_income - next_state.claims_paid
    )
    assert next_state.liquidated_this_step is True


def test_effect_settle_epoch_forces_oracle_fresh_and_uses_post_state() -> None:
    state = _open_state(
        now_epoch=10,
        oracle_last_update_epoch=0,
        position_base=100,
        collateral_quote=100_000,
    )

    effect = effects.effect_settle_epoch(state, ActionParams(action=Action.SETTLE_EPOCH))

    assert effect.event == Event.EPOCH_SETTLED
    assert effect.oracle_fresh is True
    assert effect.collateral_after == state.collateral_quote
    assert effect.maint_req_quote == maint_margin_req(
        state.position_base,
        state.index_price_e8,
        state.maintenance_margin_bps,
        state.depeg_buffer_bps,
    )


def test_effect_withdraw_collateral_reports_margin_failure_for_bad_post_state() -> None:
    state = _open_state(collateral_quote=0, position_base=100)

    effect = effects.effect_withdraw_collateral(
        state,
        ActionParams(action=Action.WITHDRAW_COLLATERAL, amount=1, auth_ok=True),
    )

    assert effect.event == Event.COLLATERAL_WITHDRAWN
    assert effect.margin_ok is False
    assert effect.maint_req_quote > effect.collateral_after


def test_perp_invariant_error_preserves_violations_and_message() -> None:
    err = PerpInvariantError(["inv_a", "inv_b"])

    assert err.violations == ["inv_a", "inv_b"]
    assert str(err) == "invariant violations: inv_a, inv_b"
