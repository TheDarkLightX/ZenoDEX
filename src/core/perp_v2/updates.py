"""State transition functions for `perp_v2`.

One pure function per ESSO action. Each returns a new `PerpState` with the
action's updates applied.

Semantics:
- updates evaluate against the PRE-state,
- updates are simultaneous (ESSO style),
- we implement updates via `dataclasses.replace()` on frozen dataclasses.
"""

from __future__ import annotations

from dataclasses import replace

from .math import (
    funding_payment,
    is_liquidatable,
    liq_penalty_capped,
    oracle_move_violated,
    pnl_quote,
    settle_price,
)
from .types import ActionParams, PerpState


def apply_advance_epoch(state: PerpState, params: ActionParams) -> PerpState:
    return replace(
        state,
        now_epoch=state.now_epoch + params.delta,
        liquidated_this_step=False,
    )


def apply_publish_clearing_price(state: PerpState, params: ActionParams) -> PerpState:
    return replace(
        state,
        clearing_price_seen=True,
        clearing_price_epoch=state.now_epoch,
        clearing_price_e8=params.price_e8,
        liquidated_this_step=False,
    )


def apply_settle_epoch(state: PerpState, params: ActionParams) -> PerpState:
    sp = settle_price(
        state.clearing_price_e8, state.index_price_e8,
        state.max_oracle_move_bps, state.oracle_seen,
    )
    pnl = pnl_quote(state.position_base, sp, state.index_price_e8)
    coll_after_pnl = state.collateral_quote + pnl

    liq = is_liquidatable(
        state.position_base, coll_after_pnl, sp,
        state.maintenance_margin_bps, state.depeg_buffer_bps,
    )
    move_violated = oracle_move_violated(
        state.clearing_price_e8, state.index_price_e8,
        state.max_oracle_move_bps, state.oracle_seen,
    )

    if liq:
        penalty = liq_penalty_capped(
            coll_after_pnl, state.position_base, sp,
            state.liquidation_penalty_bps, state.min_notional_for_bounty,
        )
        new_collateral = coll_after_pnl - penalty
        new_fee_pool = state.fee_pool_quote + penalty
        new_fee_income = state.fee_income + penalty
        new_position = 0
        new_entry = 0
    else:
        new_collateral = coll_after_pnl
        new_fee_pool = state.fee_pool_quote
        new_fee_income = state.fee_income
        new_position = state.position_base
        # Spec: entry_price_e8 is 0 when flat, else equals the settled price.
        new_entry = 0 if state.position_base == 0 else sp

    # Insurance balance recomputed from accounting identity in both branches.
    new_insurance = state.initial_insurance + new_fee_income - state.claims_paid

    return replace(
        state,
        oracle_last_update_epoch=state.now_epoch,
        oracle_seen=True,
        liquidated_this_step=liq,
        index_price_e8=sp,
        breaker_active=state.breaker_active or move_violated,
        breaker_last_trigger_epoch=(
            state.now_epoch if move_violated else state.breaker_last_trigger_epoch
        ),
        collateral_quote=new_collateral,
        fee_pool_quote=new_fee_pool,
        fee_income=new_fee_income,
        insurance_balance=new_insurance,
        position_base=new_position,
        entry_price_e8=new_entry,
    )


def apply_deposit_collateral(state: PerpState, params: ActionParams) -> PerpState:
    return replace(
        state,
        collateral_quote=state.collateral_quote + params.amount,
        liquidated_this_step=False,
    )


def apply_withdraw_collateral(state: PerpState, params: ActionParams) -> PerpState:
    return replace(
        state,
        collateral_quote=state.collateral_quote - params.amount,
        liquidated_this_step=False,
    )


def apply_set_position(state: PerpState, params: ActionParams) -> PerpState:
    return replace(
        state,
        position_base=params.new_position_base,
        entry_price_e8=0 if params.new_position_base == 0 else state.index_price_e8,
        liquidated_this_step=False,
    )


def apply_clear_breaker(state: PerpState, params: ActionParams) -> PerpState:
    return replace(
        state,
        breaker_active=False,
        breaker_last_trigger_epoch=0,
        liquidated_this_step=False,
    )


def apply_funding(state: PerpState, params: ActionParams) -> PerpState:
    fp = funding_payment(state.position_base, state.index_price_e8, params.new_rate_bps)
    return replace(
        state,
        funding_rate_bps=params.new_rate_bps,
        funding_last_applied_epoch=state.now_epoch,
        collateral_quote=state.collateral_quote - fp,
        funding_paid_cumulative=state.funding_paid_cumulative + fp,
        liquidated_this_step=False,
    )


def apply_deposit_insurance(state: PerpState, params: ActionParams) -> PerpState:
    return replace(
        state,
        initial_insurance=state.initial_insurance + params.amount,
        insurance_balance=state.insurance_balance + params.amount,
        liquidated_this_step=False,
    )


def apply_insurance_claim(state: PerpState, params: ActionParams) -> PerpState:
    new_claims = state.claims_paid + params.claim_amount
    return replace(
        state,
        claims_paid=new_claims,
        insurance_balance=state.initial_insurance + state.fee_income - new_claims,
        liquidated_this_step=False,
    )
