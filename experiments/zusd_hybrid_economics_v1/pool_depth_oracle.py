"""Design-stage zUSD buyback pool-depth oracle.

This module makes the Stage-C depth gate from the zUSD hybrid-economics
notes executable without wiring it into live zUSD admission. It is an
integer-only micro-spec for review and simulation:

    min_pool_depth = multiplier * ceil(B_cap * 10_000 / fee_bps)

The default multiplier is 2, matching the experimental recommendation in
``16_min_depth_sandwich_gate.md``. A zero-fee pool has no finite fee-funded
depth gate in this model, so it is never eligible through this rule.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Any

BPS_SCALE = 10_000
DEFAULT_DEPTH_SAFETY_MULTIPLIER = 2


def _require_int(value: Any, *, name: str, minimum: int, maximum: int | None = None) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < minimum:
        raise ValueError(f"{name} must be at least {minimum}")
    if maximum is not None and value > maximum:
        raise ValueError(f"{name} must be at most {maximum}")
    return int(value)


def _ceil_div(numerator: int, denominator: int) -> int:
    if numerator < 0:
        raise ValueError("numerator must be non-negative")
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    return (numerator + denominator - 1) // denominator


@dataclass(frozen=True)
class ZUSDBuybackDepthGate:
    """Integer parameters for the design-stage zUSD pool-depth gate."""

    buyback_budget_cap_quote: int
    fee_bps: int
    sigma_bps: int
    observed_pool_depth_quote: int
    safety_multiplier: int = DEFAULT_DEPTH_SAFETY_MULTIPLIER


@dataclass(frozen=True)
class ZUSDBuybackDepthGateResult:
    """Evaluation of the Stage-C zUSD depth and sigma-fee gates."""

    required_min_pool_depth_quote: int | None
    sigma_fee_rule_ok: bool
    depth_gate_ok: bool
    eligible: bool


def sigma_fee_rule_ok(*, sigma_bps: int, fee_bps: int) -> bool:
    """Return the exact fee-padded sigma rule from the Stage-C derivation."""
    sigma = _require_int(sigma_bps, name="sigma_bps", minimum=0, maximum=BPS_SCALE)
    fee = _require_int(fee_bps, name="fee_bps", minimum=0, maximum=BPS_SCALE)
    return sigma * BPS_SCALE <= 2 * fee * (BPS_SCALE - fee)


def recommended_min_pool_depth_quote(
    *,
    buyback_budget_cap_quote: int,
    fee_bps: int,
    safety_multiplier: int = DEFAULT_DEPTH_SAFETY_MULTIPLIER,
) -> int | None:
    """Return the recommended minimum quote depth, or ``None`` for zero-fee pools."""
    budget = _require_int(
        buyback_budget_cap_quote,
        name="buyback_budget_cap_quote",
        minimum=0,
    )
    fee = _require_int(fee_bps, name="fee_bps", minimum=0, maximum=BPS_SCALE)
    multiplier = _require_int(safety_multiplier, name="safety_multiplier", minimum=1)
    if budget == 0:
        return 0
    if fee == 0:
        return None
    return multiplier * _ceil_div(budget * BPS_SCALE, fee)


def evaluate_zusd_buyback_depth_gate(gate: ZUSDBuybackDepthGate) -> ZUSDBuybackDepthGateResult:
    """Evaluate the design-stage zUSD buyback eligibility gate.

    The experimental recommendation enforces both C2 and E3:
    the sigma-fee rule must hold and committed quote depth must meet the
    configured minimum. This is stricter than using either condition alone.
    """
    depth = _require_int(
        gate.observed_pool_depth_quote,
        name="observed_pool_depth_quote",
        minimum=0,
    )
    required_depth = recommended_min_pool_depth_quote(
        buyback_budget_cap_quote=gate.buyback_budget_cap_quote,
        fee_bps=gate.fee_bps,
        safety_multiplier=gate.safety_multiplier,
    )
    sigma_ok = sigma_fee_rule_ok(sigma_bps=gate.sigma_bps, fee_bps=gate.fee_bps)
    depth_ok = required_depth is not None and depth >= required_depth
    return ZUSDBuybackDepthGateResult(
        required_min_pool_depth_quote=required_depth,
        sigma_fee_rule_ok=sigma_ok,
        depth_gate_ok=depth_ok,
        eligible=sigma_ok and depth_ok,
    )


def twap_consecutive_control_gain_cost_ratio(
    *,
    buyback_budget_per_epoch_quote: int,
    pool_depth_quote: int,
    bias_bps: int,
    window_epochs: int,
) -> Fraction:
    """Return the exact distributed TWAP manipulation gain/cost ratio.

    ``window_epochs`` is validated but cancels from the ratio under consecutive
    control: both extraction and round-trip manipulation cost scale linearly in
    the number of controlled epochs.
    """
    budget = _require_int(
        buyback_budget_per_epoch_quote,
        name="buyback_budget_per_epoch_quote",
        minimum=0,
    )
    depth = _require_int(pool_depth_quote, name="pool_depth_quote", minimum=1)
    bias = _require_int(bias_bps, name="bias_bps", minimum=1, maximum=BPS_SCALE)
    _require_int(window_epochs, name="window_epochs", minimum=1)
    return Fraction(budget * 2 * BPS_SCALE, depth * bias)

