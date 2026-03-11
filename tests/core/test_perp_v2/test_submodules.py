from __future__ import annotations

from dataclasses import replace

import src.core.perp_v2.effects as effects
import src.core.perp_v2.guards as guards
import src.core.perp_v2.updates as updates
from src.core.perp_v2.errors import PerpInvariantError
from src.core.perp_v2.math import (
    MAX_COLLATERAL,
    MAX_FUNDING_CUMULATIVE,
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


def test_guard_settle_epoch_rejects_missing_or_wrong_epoch_price() -> None:
    missing_seen = _ready_to_settle(clearing_price_seen=False)
    wrong_epoch = _ready_to_settle(clearing_price_epoch=1)

    assert not guards.guard_settle_epoch(missing_seen, ActionParams(action=Action.SETTLE_EPOCH))
    assert not guards.guard_settle_epoch(wrong_epoch, ActionParams(action=Action.SETTLE_EPOCH))


def test_guard_settle_epoch_rejects_collateral_out_of_bounds_after_pnl() -> None:
    state = _ready_to_settle(
        collateral_quote=0,
        position_base=100,
        entry_price_e8=100_000_000,
        clearing_price_e8=95_000_000,
    )

    assert not guards.guard_settle_epoch(state, ActionParams(action=Action.SETTLE_EPOCH))


def test_settle_liquidation_overflow_checks_cover_fee_income_and_insurance() -> None:
    fee_income_overflow = _ready_to_settle(
        collateral_quote=1_000,
        position_base=100_000,
        entry_price_e8=100_000_000,
        fee_income=MAX_COLLATERAL,
        min_notional_for_bounty=0,
    )
    insurance_overflow = _ready_to_settle(
        collateral_quote=1_000,
        position_base=100_000,
        entry_price_e8=100_000_000,
        initial_insurance=MAX_COLLATERAL,
        min_notional_for_bounty=0,
    )

    assert not guards._settle_liq_overflow_ok(fee_income_overflow, 1_000, 100_000_000)
    assert not guards._settle_liq_overflow_ok(insurance_overflow, 1_000, 100_000_000)


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


def test_guard_withdraw_collateral_rejects_stale_oracle_for_open_position() -> None:
    state = _open_state(
        now_epoch=10,
        oracle_last_update_epoch=7,
        max_oracle_staleness_epochs=1,
    )

    assert not guards.guard_withdraw_collateral(
        state,
        ActionParams(action=Action.WITHDRAW_COLLATERAL, amount=1, auth_ok=True),
    )


def test_guard_set_position_rejects_stale_or_over_max_paths() -> None:
    too_large = _open_state(max_position_abs=100)
    stale = _open_state(
        now_epoch=10,
        oracle_last_update_epoch=7,
        max_oracle_staleness_epochs=1,
    )

    assert not guards.guard_set_position(
        too_large,
        ActionParams(action=Action.SET_POSITION, new_position_base=101, auth_ok=True),
    )
    assert not guards.guard_set_position(
        stale,
        ActionParams(action=Action.SET_POSITION, new_position_base=50, auth_ok=True),
    )


def test_guard_set_position_breaker_rejects_opening_from_flat() -> None:
    state = _open_state(position_base=0, entry_price_e8=0, breaker_active=True)

    assert not guards.guard_set_position(
        state,
        ActionParams(action=Action.SET_POSITION, new_position_base=1, auth_ok=True),
    )


def test_guard_apply_funding_rejects_stale_oracle_and_collateral_bounds() -> None:
    stale = _open_state(
        now_epoch=10,
        oracle_last_update_epoch=7,
        max_oracle_staleness_epochs=1,
    )
    underflow = _open_state(collateral_quote=0, position_base=1_000)
    overflow = _open_state(collateral_quote=MAX_COLLATERAL, position_base=-1_000)

    assert not guards.guard_apply_funding(
        stale,
        ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=10, auth_ok=True),
    )
    assert not guards.guard_apply_funding(
        underflow,
        ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=100, auth_ok=True),
    )
    assert not guards.guard_apply_funding(
        overflow,
        ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=100, auth_ok=True),
    )


def test_guard_apply_funding_rejects_margin_and_cumulative_overflow() -> None:
    maint_fail = _open_state(collateral_quote=6, position_base=100)
    cumulative_overflow = _open_state(
        collateral_quote=1_000,
        position_base=1_000,
        funding_paid_cumulative=MAX_FUNDING_CUMULATIVE,
    )

    assert not guards.guard_apply_funding(
        maint_fail,
        ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=100, auth_ok=True),
    )
    assert not guards.guard_apply_funding(
        cumulative_overflow,
        ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=100, auth_ok=True),
    )


def test_guard_deposit_insurance_and_claim_reject_overflow_paths() -> None:
    deposit_initial_overflow = _open_state(initial_insurance=MAX_COLLATERAL, insurance_balance=0)
    claim_paid_overflow = _open_state(
        insurance_balance=1,
        claims_paid=MAX_COLLATERAL,
        initial_insurance=MAX_COLLATERAL,
    )
    negative_resulting = _open_state(
        insurance_balance=1,
        initial_insurance=0,
        fee_income=0,
        claims_paid=0,
    )

    assert not guards.guard_deposit_insurance(
        deposit_initial_overflow,
        ActionParams(action=Action.DEPOSIT_INSURANCE, amount=1),
    )
    assert not guards.guard_apply_insurance_claim(
        claim_paid_overflow,
        ActionParams(action=Action.APPLY_INSURANCE_CLAIM, claim_amount=1, auth_ok=True),
    )
    assert not guards.guard_apply_insurance_claim(
        negative_resulting,
        ActionParams(action=Action.APPLY_INSURANCE_CLAIM, claim_amount=1, auth_ok=True),
    )


def test_guard_partial_liquidate_rejects_nonpositive_index_and_too_small_fraction() -> None:
    bad_index = _open_state(collateral_quote=5, position_base=100, index_price_e8=0)
    too_small = _open_state(collateral_quote=5, position_base=100, min_notional_for_bounty=0)

    assert not guards.guard_partial_liquidate(
        bad_index,
        ActionParams(action=Action.PARTIAL_LIQUIDATE, fraction_bps=10_000, auth_ok=True),
    )
    assert not guards.guard_partial_liquidate(
        too_small,
        ActionParams(action=Action.PARTIAL_LIQUIDATE, fraction_bps=1, auth_ok=True),
    )


def test_guard_partial_liquidate_rejects_fee_and_insurance_overflow_paths() -> None:
    fee_pool_overflow = _open_state(
        collateral_quote=500,
        position_base=100_000,
        fee_pool_quote=MAX_COLLATERAL,
        min_notional_for_bounty=0,
    )
    fee_income_overflow = _open_state(
        collateral_quote=500,
        position_base=100_000,
        fee_income=MAX_COLLATERAL,
        min_notional_for_bounty=0,
    )
    insurance_overflow = _open_state(
        collateral_quote=500,
        position_base=100_000,
        initial_insurance=MAX_COLLATERAL,
        min_notional_for_bounty=0,
    )

    assert not guards.guard_partial_liquidate(
        fee_pool_overflow,
        ActionParams(action=Action.PARTIAL_LIQUIDATE, fraction_bps=10_000, auth_ok=True),
    )
    assert not guards.guard_partial_liquidate(
        fee_income_overflow,
        ActionParams(action=Action.PARTIAL_LIQUIDATE, fraction_bps=10_000, auth_ok=True),
    )
    assert not guards.guard_partial_liquidate(
        insurance_overflow,
        ActionParams(action=Action.PARTIAL_LIQUIDATE, fraction_bps=10_000, auth_ok=True),
    )


def test_guard_partial_liquidate_rejects_defensive_auto_fraction_zero(monkeypatch) -> None:
    state = _open_state(collateral_quote=5, position_base=100, min_notional_for_bounty=0)
    monkeypatch.setattr(guards, "compute_partial_close_fraction", lambda *args: 0)

    assert not guards.guard_partial_liquidate(
        state,
        ActionParams(action=Action.PARTIAL_LIQUIDATE, fraction_bps=0, auth_ok=True),
    )


def test_guard_partial_liquidate_rejects_defensive_out_of_bounds_post_penalty(monkeypatch) -> None:
    state = _open_state(collateral_quote=5, position_base=100, min_notional_for_bounty=0)
    monkeypatch.setattr(guards, "partial_liq_penalty_capped", lambda *args: -MAX_COLLATERAL)

    assert not guards.guard_partial_liquidate(
        state,
        ActionParams(action=Action.PARTIAL_LIQUIDATE, fraction_bps=10_000, auth_ok=True),
    )


def test_perp_invariant_error_preserves_violations_and_message() -> None:
    err = PerpInvariantError(["inv_a", "inv_b"])

    assert err.violations == ["inv_a", "inv_b"]
    assert str(err) == "invariant violations: inv_a, inv_b"
