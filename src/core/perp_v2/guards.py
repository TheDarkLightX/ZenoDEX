"""Guard functions for `perp_v2`.

One pure function per kernel action id. Each returns True iff the action is allowed
in the given PRE-state with the given parameters.

These are direct translations of the guard blocks in
`src/kernels/dex/perp_epoch_isolated_v3.yaml`.
"""

from __future__ import annotations

from .math import (
    BPS_SCALE,
    MAX_COLLATERAL,
    MAX_EPOCH,
    MAX_FUNDING_CUMULATIVE,
    abs_val,
    compute_partial_close_fraction,
    funding_payment,
    init_margin_req,
    is_liquidatable,
    is_oracle_fresh,
    is_settle_oracle_usable,
    liq_penalty_capped,
    maint_margin_req,
    partial_liq_penalty_capped,
    pnl_quote,
    remaining_position_signed,
    settle_price,
)
from .types import ActionParams, EpochPhase, PerpState


def guard_advance_epoch(state: PerpState, params: ActionParams) -> bool:
    return state.now_epoch + params.delta <= MAX_EPOCH


def guard_publish_clearing_price(state: PerpState, params: ActionParams) -> bool:
    if state.epoch_phase != EpochPhase.OPEN:
        return False
    return state.clearing_price_epoch < state.now_epoch


def guard_settle_epoch(state: PerpState, params: ActionParams) -> bool:
    """Settle the current epoch (PnL realization + optional liquidation).

    Preconditions (high-level):
    - A clearing price has been published for the current `now_epoch`.
    - This epoch has not already been settled.
    - Post-PnL collateral stays within integer bounds.
    - If the position becomes liquidatable at settlement, liquidation accounting
      must not overflow fee/insurance tracking variables.
    """
    if state.epoch_phase != EpochPhase.PRICE_PUBLISHED:
        return False
    if not state.clearing_price_seen:
        return False
    if state.clearing_price_epoch != state.now_epoch:
        return False
    if state.oracle_last_update_epoch >= state.now_epoch:
        return False
    # Scientist-driven anti-manipulation hardening:
    # settlement requires a usable oracle snapshot (seen + positive index + not stale),
    # except for the deterministic bootstrap settle (no oracle yet, flat position).
    bootstrap_oracle = (
        (not state.oracle_seen)
        and state.index_price_e8 == 0
        and state.position_base == 0
    )
    if (not bootstrap_oracle) and (not is_settle_oracle_usable(
        state.now_epoch,
        state.oracle_last_update_epoch,
        state.max_oracle_staleness_epochs,
        state.oracle_seen,
        state.index_price_e8,
    )):
        return False

    sp = settle_price(
        state.clearing_price_e8,
        state.index_price_e8,
        state.max_oracle_move_bps,
        state.oracle_seen,
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


def _settle_liq_overflow_ok(state: PerpState, coll_after_pnl: int, sp: int) -> bool:
    """Overflow checks for the liquidation path during settlement.

    Liquidation may add a penalty into the fee pool and fee income; the derived
    insurance reserve is `initial_insurance + fee_income - claims_paid`.
    """
    penalty = liq_penalty_capped(
        coll_after_pnl,
        state.position_base,
        sp,
        state.liquidation_penalty_bps,
        state.min_notional_for_bounty,
    )
    if state.fee_pool_quote + penalty > MAX_COLLATERAL:
        return False
    new_fee_income = state.fee_income + penalty
    if new_fee_income > MAX_COLLATERAL:
        return False
    new_insurance = state.initial_insurance + new_fee_income - state.claims_paid
    return new_insurance <= MAX_COLLATERAL


def guard_deposit_collateral(state: PerpState, params: ActionParams) -> bool:
    if state.epoch_phase != EpochPhase.OPEN:
        return False
    if not params.auth_ok:
        return False
    return state.collateral_quote + params.amount <= MAX_COLLATERAL


def guard_withdraw_collateral(state: PerpState, params: ActionParams) -> bool:
    if state.epoch_phase != EpochPhase.OPEN:
        return False
    if not params.auth_ok:
        return False
    if params.amount > state.collateral_quote:
        return False
    if state.position_base == 0:
        return True

    # Fail-closed on malformed oracle snapshots.
    if state.index_price_e8 <= 0:
        return False
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
    if state.epoch_phase != EpochPhase.OPEN:
        return False
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
    # Fail-closed on malformed oracle snapshots.
    if state.index_price_e8 <= 0:
        return False
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
    """Apply a funding-rate update (once per epoch, authorized).

    Funding is only applied when:
    - the epoch is in OPEN or PRICE_PUBLISHED phase (after clearing price is known),
    - the oracle is fresh,
    - the epoch has not already had funding applied,
    - the funding rate is within the configured cap,
    - and the resulting collateral still satisfies maintenance margin.
    """
    if state.epoch_phase not in (EpochPhase.OPEN, EpochPhase.PRICE_PUBLISHED):
        return False
    if not params.auth_ok:
        return False
    # Fail-closed on malformed oracle snapshots.
    if state.index_price_e8 <= 0:
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


def guard_partial_liquidate(state: PerpState, params: ActionParams) -> bool:
    """Partially liquidate an underwater position.

    The position must be below maintenance margin (liquidatable) at the
    current index price. The fraction_bps parameter selects how much of
    the position to close:
    - fraction_bps == 0: auto-compute minimum fraction via binary search
    - fraction_bps > 0: use the specified fraction

    Preconditions:
    - Epoch in OPEN phase (position accounting happens during OPEN).
    - Authorization required.
    - Oracle must be fresh and index price positive.
    - Position must be non-zero and below maintenance margin.
    - The resulting collateral after penalty must stay non-negative
      and within bounds.
    """
    if state.epoch_phase != EpochPhase.OPEN:
        return False
    if not params.auth_ok:
        return False
    if state.position_base == 0:
        return False
    if state.index_price_e8 <= 0:
        return False
    if not is_oracle_fresh(
        state.now_epoch, state.oracle_last_update_epoch,
        state.max_oracle_staleness_epochs, state.oracle_seen,
    ):
        return False

    # Position must actually be liquidatable at current index price.
    if not is_liquidatable(
        state.position_base, state.collateral_quote, state.index_price_e8,
        state.maintenance_margin_bps, state.depeg_buffer_bps,
    ):
        return False

    # Resolve fraction_bps: 0 means auto-compute.
    fraction = params.fraction_bps
    if fraction == 0:
        fraction = compute_partial_close_fraction(
            state.position_base, state.collateral_quote, state.index_price_e8,
            state.maintenance_margin_bps, state.depeg_buffer_bps,
            state.liquidation_penalty_bps, state.min_notional_for_bounty,
        )
    if fraction < 1 or fraction > BPS_SCALE:
        return False

    # Check collateral bounds after penalty.
    penalty = partial_liq_penalty_capped(
        state.collateral_quote, state.position_base, fraction,
        state.index_price_e8, state.liquidation_penalty_bps,
        state.min_notional_for_bounty,
    )
    new_collateral = state.collateral_quote - penalty
    if new_collateral < 0 or new_collateral > MAX_COLLATERAL:
        return False

    # Fee/insurance overflow checks.
    new_fee_pool = state.fee_pool_quote + penalty
    if new_fee_pool > MAX_COLLATERAL:
        return False
    new_fee_income = state.fee_income + penalty
    if new_fee_income > MAX_COLLATERAL:
        return False
    new_insurance = state.initial_insurance + new_fee_income - state.claims_paid
    if new_insurance > MAX_COLLATERAL:
        return False

    # After partial close, remaining position must satisfy maint margin
    # (unless fully closed).
    remaining = remaining_position_signed(state.position_base, fraction)
    if remaining != 0:
        mreq = maint_margin_req(
            remaining, state.index_price_e8,
            state.maintenance_margin_bps, state.depeg_buffer_bps,
        )
        if new_collateral < mreq:
            return False

    return True
