"""Invariant checkers for `perp_v2`.

This file mirrors the invariants in `src/kernels/dex/perp_epoch_isolated_v3.yaml`.
Each function returns True when the invariant holds, and `check_all()` returns
the list of violated invariant IDs (empty = all pass).

Note: these are per-kernel invariants (single-account abstraction), not global
multi-account conservation laws.
"""

from __future__ import annotations

from typing import Callable

from .math import BPS_SCALE, maint_margin_req
from .types import EpochPhase, PerpState


def inv_clearing_not_from_future(s: PerpState) -> bool:
    return s.clearing_price_epoch <= s.now_epoch


def inv_clearing_seen_zeroed(s: PerpState) -> bool:
    if s.clearing_price_seen:
        return True
    return s.clearing_price_epoch == 0 and s.clearing_price_e8 == 0


def inv_oracle_not_from_future(s: PerpState) -> bool:
    return s.oracle_last_update_epoch <= s.now_epoch


def inv_oracle_seen_zeroed(s: PerpState) -> bool:
    if s.oracle_seen:
        return True
    return s.oracle_last_update_epoch == 0 and s.index_price_e8 == 0


def inv_oracle_seen_positive_index(s: PerpState) -> bool:
    if not s.oracle_seen:
        return True
    return s.index_price_e8 > 0


def inv_breaker_not_from_future(s: PerpState) -> bool:
    return s.breaker_last_trigger_epoch <= s.now_epoch


def inv_breaker_inactive_zeroed(s: PerpState) -> bool:
    if s.breaker_active:
        return True
    return s.breaker_last_trigger_epoch == 0


def inv_margin_params_ordered(s: PerpState) -> bool:
    eff_maint = s.maintenance_margin_bps + s.depeg_buffer_bps
    return s.max_oracle_move_bps <= eff_maint <= s.initial_margin_bps


def inv_entry_zero_when_flat(s: PerpState) -> bool:
    if s.position_base != 0:
        return True
    return s.entry_price_e8 == 0


def inv_entry_matches_price_when_open(s: PerpState) -> bool:
    if s.position_base == 0:
        return True
    return s.entry_price_e8 == s.index_price_e8


def inv_maint_margin_ok(s: PerpState) -> bool:
    if s.position_base == 0:
        return True
    mreq = maint_margin_req(
        s.position_base, s.index_price_e8,
        s.maintenance_margin_bps, s.depeg_buffer_bps,
    )
    return s.collateral_quote >= mreq


def inv_funding_bounded(s: PerpState) -> bool:
    return -s.funding_cap_bps <= s.funding_rate_bps <= s.funding_cap_bps


def inv_insurance_nonneg(s: PerpState) -> bool:
    return s.insurance_balance >= 0


def inv_insurance_conservation(s: PerpState) -> bool:
    return s.insurance_balance == s.initial_insurance + s.fee_income - s.claims_paid


def inv_liquidation_ic_guard(s: PerpState) -> bool:
    eff_maint = s.maintenance_margin_bps + s.depeg_buffer_bps
    return s.liquidation_penalty_bps < eff_maint


def inv_funded_liquidation(s: PerpState) -> bool:
    """Funded-liquidation parameter inequality.

    ``penalty * (BPS + m) <= BPS * (eff_maint - m)`` guarantees that after any
    single clamped oracle move the liquidation penalty priced at the post-move
    price is covered by the account's own post-move equity, so the
    ``liq_penalty_capped`` cap never binds and the keeper reward never draws
    on the insurance fund.  Lean proof:
    ``Proofs.PerpEpochSafety.liquidation_penalty_funded_after_bounded_move``.

    Strictly stronger than ``inv_liquidation_ic_guard`` (which ignores the
    oracle clamp ``m``): with ``m = eff_maint`` the IC guard still passes
    while the penalty is unfunded at the clamp edge.
    """
    eff_maint = s.maintenance_margin_bps + s.depeg_buffer_bps
    return (
        s.liquidation_penalty_bps * (BPS_SCALE + s.max_oracle_move_bps)
        <= BPS_SCALE * (eff_maint - s.max_oracle_move_bps)
    )


def inv_funding_epoch_gated(s: PerpState) -> bool:
    return s.funding_last_applied_epoch <= s.now_epoch


def inv_fee_pool_eq_fee_income(s: PerpState) -> bool:
    return s.fee_pool_quote == s.fee_income


def inv_phase_consistent(s: PerpState) -> bool:
    """Phase matches observable state."""
    if s.epoch_phase == EpochPhase.PRICE_PUBLISHED:
        return s.clearing_price_epoch == s.now_epoch and s.clearing_price_seen
    if s.epoch_phase == EpochPhase.SETTLED:
        return s.oracle_last_update_epoch >= s.now_epoch
    return True  # OPEN has no additional constraint


# ---------------------------------------------------------------------------
# Registry + check_all
# ---------------------------------------------------------------------------

INVARIANT_REGISTRY: dict[str, Callable[[PerpState], bool]] = {
    "inv_clearing_not_from_future": inv_clearing_not_from_future,
    "inv_clearing_seen_zeroed": inv_clearing_seen_zeroed,
    "inv_oracle_not_from_future": inv_oracle_not_from_future,
    "inv_oracle_seen_zeroed": inv_oracle_seen_zeroed,
    "inv_oracle_seen_positive_index": inv_oracle_seen_positive_index,
    "inv_breaker_not_from_future": inv_breaker_not_from_future,
    "inv_breaker_inactive_zeroed": inv_breaker_inactive_zeroed,
    "inv_margin_params_ordered": inv_margin_params_ordered,
    "inv_entry_zero_when_flat": inv_entry_zero_when_flat,
    "inv_entry_matches_price_when_open": inv_entry_matches_price_when_open,
    "inv_maint_margin_ok": inv_maint_margin_ok,
    "inv_funding_bounded": inv_funding_bounded,
    "inv_insurance_nonneg": inv_insurance_nonneg,
    "inv_insurance_conservation": inv_insurance_conservation,
    "inv_liquidation_ic_guard": inv_liquidation_ic_guard,
    "inv_funded_liquidation": inv_funded_liquidation,
    "inv_funding_epoch_gated": inv_funding_epoch_gated,
    "inv_fee_pool_eq_fee_income": inv_fee_pool_eq_fee_income,
    "inv_phase_consistent": inv_phase_consistent,
}


def check_all(state: PerpState) -> list[str]:
    """Return list of violated invariant IDs (empty = all pass)."""
    return [
        inv_id
        for inv_id, check_fn in INVARIANT_REGISTRY.items()
        if not check_fn(state)
    ]
