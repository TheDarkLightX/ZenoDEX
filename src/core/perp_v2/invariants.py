"""Invariant checkers for `perp_v2`.

This file mirrors the invariants in `src/kernels/dex/perp_epoch_isolated_v3.yaml`.
Each function returns True when the invariant holds, and `check_all()` returns
the list of violated invariant IDs (empty = all pass).

Note: these are per-kernel invariants (single-account abstraction), not global
multi-account conservation laws.
"""

from __future__ import annotations

from typing import Callable

from ..perp_state_domain import state_domain_violations
from .math import BPS_SCALE, maint_margin_req
from .types import Action, ActionParams, EpochPhase, PerpState


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
        s.position_base,
        s.index_price_e8,
        s.maintenance_margin_bps,
        s.depeg_buffer_bps,
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


def funded_liquidation_params_ok_bps(
    *,
    max_oracle_move_bps: int,
    maintenance_margin_bps: int,
    depeg_buffer_bps: int,
    liquidation_penalty_bps: int,
) -> bool:
    """True when post-move margin headroom can fund the liquidation penalty."""
    if (
        min(max_oracle_move_bps, maintenance_margin_bps, depeg_buffer_bps, liquidation_penalty_bps)
        < 0
    ):
        return False
    eff_maint_bps = maintenance_margin_bps + depeg_buffer_bps
    if max_oracle_move_bps >= eff_maint_bps:
        return False
    return liquidation_penalty_bps * (BPS_SCALE + max_oracle_move_bps) <= (
        BPS_SCALE * (eff_maint_bps - max_oracle_move_bps)
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


def inv_phase_published_has_settlement_path(s: PerpState) -> bool:
    """Every published state has an enabled ordinary settlement transition."""
    if s.epoch_phase is not EpochPhase.PRICE_PUBLISHED:
        return True

    from .guards import guard_settle_epoch

    return guard_settle_epoch(
        s,
        ActionParams(action=Action.SETTLE_EPOCH),
    )


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
    "inv_funding_epoch_gated": inv_funding_epoch_gated,
    "inv_fee_pool_eq_fee_income": inv_fee_pool_eq_fee_income,
    "inv_phase_consistent": inv_phase_consistent,
    "inv_phase_published_has_settlement_path": (inv_phase_published_has_settlement_path),
}


def check_all(state: PerpState) -> list[str]:
    """Return exact domain or semantic invariant violations.

    Domain validation runs first so semantic predicates never execute on a
    malformed or behavior-changing state object.
    """

    domain_violations = state_domain_violations(state)
    if domain_violations:
        return domain_violations
    return [inv_id for inv_id, check_fn in INVARIANT_REGISTRY.items() if not check_fn(state)]


def check_prestate(state: PerpState, action: Action | None) -> list[str]:
    """Return action-aware pre-state violations.

    Partial liquidation is the sole transition whose purpose is to repair an
    under-maintenance account. Every domain, ownership-shape, accounting, and
    lifecycle invariant still applies, and the accepted post-state must satisfy
    the complete invariant registry.
    """
    violations = check_all(state)
    if action is not Action.PARTIAL_LIQUIDATE:
        return violations
    return [violation for violation in violations if violation != "inv_maint_margin_ok"]
