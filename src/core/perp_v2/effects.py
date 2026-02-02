"""Effect functions for the perp_v2 risk engine.

One pure function per ESSO action. Each computes the ``Effect`` from the
POST-state (ESSO semantics: effects evaluate on the state *after* updates).
"""

from __future__ import annotations

from .math import (
    init_margin_req,
    is_oracle_fresh,
    maint_margin_req,
    notional_quote,
)
from .types import ActionParams, Effect, Event, PerpState


def _common_effects(state: PerpState, *, oracle_fresh_override: bool | None = None) -> dict[str, bool | int]:
    """Shared effect fields computed from post-state.

    `oracle_fresh_override` lets `settle_epoch` force `oracle_fresh=True`
    (because it sets `oracle_last_update_epoch := now_epoch` in the same step).
    """
    fresh = (
        oracle_fresh_override
        if oracle_fresh_override is not None
        else is_oracle_fresh(
            state.now_epoch, state.oracle_last_update_epoch,
            state.max_oracle_staleness_epochs, state.oracle_seen,
        )
    )
    notional = notional_quote(state.position_base, state.index_price_e8)
    maint_req = maint_margin_req(
        state.position_base, state.index_price_e8,
        state.maintenance_margin_bps, state.depeg_buffer_bps,
    )
    margin_ok = True if state.position_base == 0 else state.collateral_quote >= maint_req

    return dict(
        oracle_fresh=fresh,
        notional_quote=notional,
        effective_maint_bps=state.maintenance_margin_bps + state.depeg_buffer_bps,
        maint_req_quote=maint_req,
        init_req_quote=init_margin_req(
            state.position_base, state.index_price_e8, state.initial_margin_bps,
        ),
        margin_ok=margin_ok,
        liquidated=state.liquidated_this_step,
        collateral_after=state.collateral_quote,
        fee_pool_after=state.fee_pool_quote,
        insurance_after=state.insurance_balance,
    )


def effect_advance_epoch(state: PerpState, params: ActionParams) -> Effect:
    return Effect(event=Event.EPOCH_ADVANCED, **_common_effects(state))


def effect_publish_clearing_price(state: PerpState, params: ActionParams) -> Effect:
    return Effect(event=Event.CLEARING_PRICE_PUBLISHED, **_common_effects(state))


def effect_settle_epoch(state: PerpState, params: ActionParams) -> Effect:
    return Effect(event=Event.EPOCH_SETTLED, **_common_effects(state, oracle_fresh_override=True))


def effect_deposit_collateral(state: PerpState, params: ActionParams) -> Effect:
    return Effect(event=Event.COLLATERAL_DEPOSITED, **_common_effects(state))


def effect_withdraw_collateral(state: PerpState, params: ActionParams) -> Effect:
    return Effect(event=Event.COLLATERAL_WITHDRAWN, **_common_effects(state))


def effect_set_position(state: PerpState, params: ActionParams) -> Effect:
    return Effect(event=Event.POSITION_SET, **_common_effects(state))


def effect_clear_breaker(state: PerpState, params: ActionParams) -> Effect:
    return Effect(event=Event.BREAKER_CLEARED, **_common_effects(state))


def effect_apply_funding(state: PerpState, params: ActionParams) -> Effect:
    return Effect(event=Event.FUNDING_APPLIED, **_common_effects(state))


def effect_deposit_insurance(state: PerpState, params: ActionParams) -> Effect:
    return Effect(event=Event.INSURANCE_DEPOSITED, **_common_effects(state))


def effect_apply_insurance_claim(state: PerpState, params: ActionParams) -> Effect:
    return Effect(event=Event.INSURANCE_CLAIM_PAID, **_common_effects(state))
