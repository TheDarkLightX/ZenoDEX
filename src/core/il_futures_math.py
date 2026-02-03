"""Impermanent loss computation from reserve snapshots.

IL is defined as a non-negative loss:
  IL = 1 - 2 * sqrt(price_ratio) / (1 + price_ratio)

Where:
  price_ratio = (reserve_x_after * reserve_y_before) / (reserve_x_before * reserve_y_after)

Returns 0 when price_ratio = 1 (no change), positive otherwise.
This is the standard IL formula from Uniswap v2 analysis.

All operations use integer arithmetic with explicit floor division.
"""

from __future__ import annotations

from math import isqrt


BPS_DENOM = 10_000
PRECISION = 10**18  # High-precision intermediate scaling


def compute_il_bps(
    reserve_x_before: int,
    reserve_y_before: int,
    reserve_x_after: int,
    reserve_y_after: int,
) -> int:
    """Compute impermanent loss in basis points from reserve snapshots.

    Uses IL = 1 - 2*sqrt(p)/(1+p) where p = price_ratio_after / price_ratio_before.

    Returns non-negative IL in bps (0 = no IL, 10000 = 100% loss).
    Returns 0 for zero reserves (undefined, fail-safe).

    All arithmetic is integer-only with floor division.
    """
    if reserve_x_before <= 0 or reserve_y_before <= 0:
        return 0
    if reserve_x_after <= 0 or reserve_y_after <= 0:
        return 0

    # price_ratio = (x_after / y_after) / (x_before / y_before)
    #             = (x_after * y_before) / (x_before * y_after)
    # We compute this as a rational with PRECISION scaling.
    numerator = reserve_x_after * reserve_y_before * PRECISION
    denominator = reserve_x_before * reserve_y_after
    if denominator == 0:
        return 0

    p_scaled = numerator // denominator  # price_ratio * PRECISION

    # IL = 1 - 2*sqrt(p) / (1 + p)
    # With scaling: sqrt_p = isqrt(p_scaled * PRECISION) for sqrt(p) * PRECISION
    sqrt_p_scaled = isqrt(p_scaled * PRECISION)

    # 2 * sqrt(p) / (1 + p) in bps:
    # = 2 * sqrt_p_scaled * BPS_DENOM * PRECISION / (PRECISION + p_scaled) / PRECISION
    denom = PRECISION + p_scaled
    if denom == 0:
        return 0

    value_ratio_bps = (2 * sqrt_p_scaled * BPS_DENOM) // denom

    # IL = 10000 - value_ratio_bps (clamped to [0, 10000])
    il_bps = BPS_DENOM - value_ratio_bps
    return max(0, min(il_bps, BPS_DENOM))


def compute_payout(
    il_bps: int,
    position_value: int,
    coverage_ratio_bps: int,
) -> int:
    """Compute IL futures payout from measured IL.

    payout = position_value * il_bps * coverage_ratio_bps / (10000 * 10000)

    Integer floor division. Non-negative.
    """
    if il_bps <= 0 or position_value <= 0 or coverage_ratio_bps <= 0:
        return 0
    return (position_value * il_bps * coverage_ratio_bps) // (BPS_DENOM * BPS_DENOM)
