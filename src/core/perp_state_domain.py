"""Exact state-domain validation shared by isolated perps cores.

Python annotations do not enforce runtime domains.  This module mirrors the
state-variable type/range declarations in the versioned isolated-perps specs
and fails closed if ``PerpState`` gains a field without an explicit domain.
"""

from __future__ import annotations

from .perp_v2.types import EpochPhase, PerpState

_MAX_EPOCH = 1_000_000
_MAX_PRICE_E8 = 1_000_000_000_000
_MAX_QUOTE = 1_000_000_000_000_000
_MAX_POSITION = 1_000_000
_MAX_BPS = 10_000
_MAX_DEPEG_BPS = 5_000
_MAX_NOTIONAL_FOR_BOUNTY = 1_000_000_000_000

_BOOL_FIELDS = frozenset(
    {
        "breaker_active",
        "clearing_price_seen",
        "oracle_seen",
        "liquidated_this_step",
    }
)

_INT_BOUNDS: dict[str, tuple[int, int]] = {
    "breaker_last_trigger_epoch": (0, _MAX_EPOCH),
    "claims_paid": (0, _MAX_QUOTE),
    "clearing_price_e8": (0, _MAX_PRICE_E8),
    "clearing_price_epoch": (0, _MAX_EPOCH),
    "collateral_quote": (0, _MAX_QUOTE),
    "depeg_buffer_bps": (0, _MAX_DEPEG_BPS),
    "entry_price_e8": (0, _MAX_PRICE_E8),
    "fee_income": (0, _MAX_QUOTE),
    "fee_pool_quote": (0, _MAX_QUOTE),
    "funding_cap_bps": (1, _MAX_BPS),
    "funding_last_applied_epoch": (0, _MAX_EPOCH),
    "funding_paid_cumulative": (-_MAX_QUOTE, _MAX_QUOTE),
    "funding_rate_bps": (-_MAX_BPS, _MAX_BPS),
    "index_price_e8": (0, _MAX_PRICE_E8),
    "initial_insurance": (0, _MAX_QUOTE),
    "initial_margin_bps": (0, _MAX_BPS),
    "insurance_balance": (0, _MAX_QUOTE),
    "liquidation_penalty_bps": (0, _MAX_BPS),
    "maintenance_margin_bps": (0, _MAX_BPS),
    "max_oracle_move_bps": (0, _MAX_BPS),
    "max_oracle_staleness_epochs": (1, _MAX_EPOCH),
    "max_position_abs": (1, _MAX_POSITION),
    "min_notional_for_bounty": (0, _MAX_NOTIONAL_FOR_BOUNTY),
    "now_epoch": (0, _MAX_EPOCH),
    "oracle_last_update_epoch": (0, _MAX_EPOCH),
    "position_base": (-_MAX_POSITION, _MAX_POSITION),
}

_EXPECTED_FIELDS = _BOOL_FIELDS | frozenset(_INT_BOUNDS) | {"epoch_phase"}
_ACTUAL_FIELDS = frozenset(PerpState.__dataclass_fields__)
if _ACTUAL_FIELDS != _EXPECTED_FIELDS:
    missing = sorted(_ACTUAL_FIELDS - _EXPECTED_FIELDS)
    stale = sorted(_EXPECTED_FIELDS - _ACTUAL_FIELDS)
    raise RuntimeError(
        "PerpState domain registry drift "
        f"(unregistered={missing}, stale={stale})"
    )


def state_domain_violations(state: object) -> list[str]:
    """Return every exact type/range violation in canonical field order.

    Exact base-type checks reject behavior-changing subclasses and reject
    Python's ``bool``-as-``int`` coercion at the authoritative core boundary.
    """

    if type(state) is not PerpState:
        return ["domain_state_type"]

    violations: list[str] = []
    for field_name in sorted(_BOOL_FIELDS):
        if type(getattr(state, field_name)) is not bool:
            violations.append(f"domain_{field_name}")

    if type(state.epoch_phase) is not EpochPhase:
        violations.append("domain_epoch_phase")

    for field_name in sorted(_INT_BOUNDS):
        value = getattr(state, field_name)
        lower, upper = _INT_BOUNDS[field_name]
        if type(value) is not int or value < lower or value > upper:
            violations.append(f"domain_{field_name}")

    return violations


__all__ = ["state_domain_violations"]
