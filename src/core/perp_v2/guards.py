"""Guard functions for `perp_v2`.

One pure function per ESSO action. Each returns True iff the action is allowed
in the given PRE-state with the given parameters.

These are direct translations of the guard blocks in
`src/kernels/dex/perp_epoch_isolated_v2.yaml`.
"""

from __future__ import annotations

from .math import (
    MAX_COLLATERAL,
    MAX_EPOCH,
    MAX_FUNDING_CUMULATIVE,
    abs_val,
    funding_payment,
    init_margin_req,
    is_liquidatable,
    is_oracle_fresh,
    liq_penalty_capped,
    maint_margin_req,
    pnl_quote,
    settle_price,
)
from .types import ActionParams, PerpState


def guard_advance_epoch(state: PerpState, params: ActionParams) -> bool:
    return state.now_epoch + params.delta <= MAX_EPOCH


def guard_publish_clearing_price(state: PerpState, params: ActionParams) -> bool:
    return state.clearing_price_epoch < state.now_epoch


def guard_settle_epoch(state: PerpState, params: ActionParams) -> bool:
    if not state.clearing_price_seen:
        return False
    if state.clearing_price_epoch != state.now_epoch:
        return False
    if state.oracle_last_update_epoch >= state.now_epoch:
        return False

    sp = settle_price(
        state.clearing_price_e8, state.index_price_e8,
        state.max_oracle_move_bps, state.oracle_seen,
    )
    pnl = pnl_quote(state.position_base, sp, state.index_price_e8)
    coll_after_pnl = state.collateral_quote + pnl

    if coll_after_pnl < 0 or coll_after_pnl > MAX_COLLATERAL:
        return False

    if state.position_base != 0 and is_liquidatable(
        state.position_base, coll_after_pnl, sp,
        state.maintenance_margin_bps, state.depeg_buffer_bps,
    ):
        if not _settle_liq_overflow_ok(state, coll_after_pnl, sp):
            return False

    return True


def _settle_liq_overflow_ok(
    state: PerpState, coll_after_pnl: int, sp: int,
) -> bool:
    """Check fee-pool / fee-income / insurance overflow during liquidation."""
    penalty = liq_penalty_capped(
        coll_after_pnl, state.position_base, sp,
        state.liquidation_penalty_bps, state.min_notional_for_bounty,
    )
    if state.fee_pool_quote + penalty > MAX_COLLATERAL:
        return False
    new_fee_income = state.fee_income + penalty
    if new_fee_income > MAX_COLLATERAL:
        return False
    new_insurance = state.initial_insurance + new_fee_income - state.claims_paid
    return new_insurance <= MAX_COLLATERAL


def guard_deposit_collateral(state: PerpState, params: ActionParams) -> bool:
    if not params.auth_ok:
        return False
    return state.collateral_quote + params.amount <= MAX_COLLATERAL


def guard_withdraw_collateral(state: PerpState, params: ActionParams) -> bool:
    if not params.auth_ok:
        return False
    if params.amount > state.collateral_quote:
        return False
    if state.position_base == 0:
        return True

    if not is_oracle_fresh(
        state.now_epoch, state.oracle_last_update_epoch,
        state.max_oracle_staleness_epochs, state.oracle_seen,
    ):
        return False

    remaining = state.collateral_quote - params.amount
    return remaining >= maint_margin_req(
        state.position_base, state.index_price_e8,
        state.maintenance_margin_bps, state.depeg_buffer_bps,
    )


def guard_set_position(state: PerpState, params: ActionParams) -> bool:
    if not params.auth_ok:
        return False
    if not state.oracle_seen:
        return False
    if abs_val(params.new_position_base) > state.max_position_abs:
        return False

    if state.breaker_active:
        return _guard_set_position_breaker(state, params)
    return _guard_set_position_normal(state, params)


def _guard_set_position_breaker(state: PerpState, params: ActionParams) -> bool:
    """Reduce-only when breaker active: no opening, no increase, no sign flip."""
    if state.position_base == 0 and params.new_position_base != 0:
        return False
    if abs_val(params.new_position_base) > abs_val(state.position_base):
        return False
    if params.new_position_base != 0:
        if (state.position_base >= 0) != (params.new_position_base >= 0):
            return False
    return True


def _guard_set_position_normal(state: PerpState, params: ActionParams) -> bool:
    """Normal trading: oracle freshness + initial margin check."""
    if not is_oracle_fresh(
        state.now_epoch, state.oracle_last_update_epoch,
        state.max_oracle_staleness_epochs, state.oracle_seen,
    ):
        return False
    if params.new_position_base == 0:
        return True
    return state.collateral_quote >= init_margin_req(
        params.new_position_base, state.index_price_e8,
        state.initial_margin_bps,
    )


def guard_clear_breaker(state: PerpState, params: ActionParams) -> bool:
    return params.auth_ok and state.breaker_active and state.position_base == 0


def guard_apply_funding(state: PerpState, params: ActionParams) -> bool:
    if not params.auth_ok:
        return False
    if not is_oracle_fresh(
        state.now_epoch, state.oracle_last_update_epoch,
        state.max_oracle_staleness_epochs, state.oracle_seen,
    ):
        return False
    if state.funding_last_applied_epoch >= state.now_epoch:
        return False
    if not (-state.funding_cap_bps <= params.new_rate_bps <= state.funding_cap_bps):
        return False
    if state.position_base == 0:
        return False

    fp = funding_payment(state.position_base, state.index_price_e8, params.new_rate_bps)
    coll_after = state.collateral_quote - fp
    if coll_after < 0 or coll_after > MAX_COLLATERAL:
        return False
    if coll_after < maint_margin_req(
        state.position_base, state.index_price_e8,
        state.maintenance_margin_bps, state.depeg_buffer_bps,
    ):
        return False

    new_cumulative = state.funding_paid_cumulative + fp
    return -MAX_FUNDING_CUMULATIVE <= new_cumulative <= MAX_FUNDING_CUMULATIVE


def guard_deposit_insurance(state: PerpState, params: ActionParams) -> bool:
    if state.initial_insurance + params.amount > MAX_COLLATERAL:
        return False
    return state.insurance_balance + params.amount <= MAX_COLLATERAL


def guard_apply_insurance_claim(state: PerpState, params: ActionParams) -> bool:
    if not params.auth_ok:
        return False
    if params.claim_amount > state.insurance_balance:
        return False
    if state.claims_paid + params.claim_amount > MAX_COLLATERAL:
        return False
    resulting = state.initial_insurance + state.fee_income - (state.claims_paid + params.claim_amount)
    return resulting >= 0
