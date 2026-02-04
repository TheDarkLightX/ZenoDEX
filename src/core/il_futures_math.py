"""Impermanent loss (IL) computation from reserve snapshots.

We use the standard Uniswap v2 IL formula (as a non-negative loss):

  IL = 1 - 2 * sqrt(p) / (1 + p)

where:

  p = (reserve_x_after / reserve_y_after) / (reserve_x_before / reserve_y_before)
    = (reserve_x_after * reserve_y_before) / (reserve_x_before * reserve_y_after)

For integer-only, bounded kernels, it's useful to avoid large fixed-point
scalings. We instead compute the same value ratio via the exact algebraic
rearrangement:

  2*sqrt(p)/(1+p) = 2*sqrt(p_num*p_den) / (p_num + p_den)

where:
  p_num = reserve_x_after * reserve_y_before
  p_den = reserve_x_before * reserve_y_after

All operations use integer arithmetic with explicit floor division.
"""

from __future__ import annotations

from math import isqrt


BPS_DENOM = 10_000


def compute_il_bps(
    reserve_x_before: int,
    reserve_y_before: int,
    reserve_x_after: int,
    reserve_y_after: int,
) -> int:
    """Compute impermanent loss in basis points (bps) from reserve snapshots.

    Returns:
    - IL in [0, 10000], where 0 = no IL and 10000 = 100% loss.
    - 0 for any zero/invalid reserves (fail-safe).
    """
    if reserve_x_before <= 0 or reserve_y_before <= 0:
        return 0
    if reserve_x_after <= 0 or reserve_y_after <= 0:
        return 0

    p_num = reserve_x_after * reserve_y_before
    p_den = reserve_x_before * reserve_y_after
    denom = p_num + p_den
    if p_den == 0 or denom == 0:
        return 0

    # value_ratio_bps := floor(2*sqrt(p_num*p_den)/(p_num+p_den) * 10000)
    sqrt_term = isqrt(p_num * p_den)
    value_ratio_bps = (2 * sqrt_term * BPS_DENOM) // denom
    il_bps = BPS_DENOM - value_ratio_bps
    return max(0, min(int(il_bps), BPS_DENOM))


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
