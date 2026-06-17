"""
Adaptive profile selection for two-pool CPMM split routing.

This module is intentionally policy-only: it computes deterministic
`(window, profile)` choices from pool reserves, fees, and amount scale. The swap
math and quote evaluation stay in `split_routing.py`.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from .domain_limits import is_strict_int

ADAPTIVE_SEARCH_PROFILES = frozenset({
    "adaptive_v1",
    "adaptive_v2",
    "adaptive_v3",
    "adaptive_v4",
    "adaptive_v5",
    "adaptive_v6",
    "adaptive_v7",
})


class _PoolLike(Protocol):
    x: int
    y: int
    fee_bps: int


@dataclass(frozen=True)
class _SplitRoutingFeatures:
    min_x: int
    min_y: int
    fee_gap: int
    fee_max: int
    x_ratio_hi: bool
    y_ratio_hi: bool
    near_sym: bool
    prefer_canon: bool
    amt_med: bool
    amt_hi: bool
    amt_very_hi: bool
    imbalance_hi: bool
    high: bool
    med: bool


def _require_int_control(value: object, *, name: str) -> int:
    if not is_strict_int(value):
        raise ValueError(f"{name} must be an int")
    return int(value)


def _require_nonnegative_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def _ratio_ge_num_denom(*, a: int, b: int, num: int, denom: int) -> bool:
    """
    Return True iff a/b >= num/denom for positive integers.
    """
    if b <= 0:
        return False
    if denom <= 0:
        return False
    return int(a) * int(denom) >= int(b) * int(num)


def _near_equal_bps(*, a: int, b: int, tol_bps: int) -> bool:
    """
    Return True iff |a-b| <= tol_bps/10_000 * min(a,b) for positive integers.
    """
    if a <= 0 or b <= 0:
        return False
    if tol_bps < 0:
        return False
    mn = a if a <= b else b
    return abs(int(a) - int(b)) * 10_000 <= int(tol_bps) * int(mn)


def _split_routing_features(pool0: _PoolLike, pool1: _PoolLike, amount_in: int) -> _SplitRoutingFeatures:
    x0, y0, f0 = int(pool0.x), int(pool0.y), int(pool0.fee_bps)
    x1, y1, f1 = int(pool1.x), int(pool1.y), int(pool1.fee_bps)
    min_x = min(x0, x1)
    min_y = min(y0, y1)
    fee_gap = abs(int(f0) - int(f1))
    fee_max = max(int(f0), int(f1))
    x_ratio_hi = _ratio_ge_num_denom(a=max(x0, x1), b=max(1, min_x), num=3, denom=1)
    y_ratio_hi = _ratio_ge_num_denom(a=max(y0, y1), b=max(1, min_y), num=5, denom=1)
    near_sym_raw = _near_equal_bps(a=x0, b=y0, tol_bps=1500) or _near_equal_bps(a=x1, b=y1, tol_bps=1500)
    near_sym = bool(near_sym_raw and min_x <= 200)
    amount = int(amount_in)
    amt_med = bool(min_x > 0 and amount >= 40 * int(min_x))
    amt_hi = bool(min_x > 0 and amount >= 80 * int(min_x))
    amt_very_hi = bool(min_x > 0 and amount >= 120 * int(min_x))
    imbalance_hi = bool(x_ratio_hi and y_ratio_hi)
    high = bool(amt_med or fee_gap >= 60 or x_ratio_hi or y_ratio_hi or near_sym)
    return _SplitRoutingFeatures(
        min_x=min_x,
        min_y=min_y,
        fee_gap=fee_gap,
        fee_max=fee_max,
        x_ratio_hi=x_ratio_hi,
        y_ratio_hi=y_ratio_hi,
        near_sym=near_sym,
        prefer_canon=bool(min_x <= 400),
        amt_med=amt_med,
        amt_hi=amt_hi,
        amt_very_hi=amt_very_hi,
        imbalance_hi=imbalance_hi,
        high=high,
        med=bool(high or fee_gap >= 30),
    )


def _resolve_adaptive_v1(features: _SplitRoutingFeatures) -> tuple[int, str]:
    if features.high:
        return 96, "dense24"
    if features.med:
        return 64, "dense24"
    return 64, "baseline"


def _resolve_adaptive_v2(features: _SplitRoutingFeatures) -> tuple[int, str]:
    if features.high:
        return 96, "dense24"
    if features.med:
        return 64, "dense24"
    return 64, "baseline_canon16"


def _resolve_adaptive_v3(features: _SplitRoutingFeatures) -> tuple[int, str]:
    if features.high:
        return 96, "dense24"
    if features.med:
        return 64, "dense24"
    return (64, "baseline_canon16") if features.prefer_canon else (64, "baseline")


def _adaptive_v4_high(features: _SplitRoutingFeatures) -> bool:
    return bool(
        features.amt_hi
        or features.fee_gap >= 90
        or features.imbalance_hi
        or (features.near_sym and features.fee_gap >= 40)
    )


def _resolve_adaptive_v4(features: _SplitRoutingFeatures) -> tuple[int, str]:
    if _adaptive_v4_high(features):
        return 96, "dense24"
    return 64, "baseline_canon16"


def _resolve_adaptive_v5(features: _SplitRoutingFeatures) -> tuple[int, str]:
    thin_out = bool(features.min_y <= 80)
    hard5 = bool(
        (features.amt_hi and features.fee_max >= 120)
        or (features.amt_very_hi and features.fee_gap >= 50)
        or (thin_out and features.amt_med and features.fee_max >= 120)
        or (features.amt_hi and features.min_y <= 64)
        or (features.imbalance_hi and features.fee_max >= 90)
    )
    extreme5 = bool(
        (features.amt_very_hi and features.fee_max >= 180)
        or (thin_out and features.amt_hi and features.fee_max >= 180)
        or (features.amt_very_hi and features.min_y <= 48)
    )
    if extreme5:
        return 128, "dense32"
    if hard5:
        return 96, "dense32"
    if _adaptive_v4_high(features):
        return 96, "dense24"
    return 64, "baseline_canon16"


def _resolve_adaptive_v6_or_v7(profile: str, features: _SplitRoutingFeatures) -> tuple[int, str]:
    thin_out = bool(features.min_y <= 80)
    hard6 = bool(
        (features.amt_hi and features.fee_max >= 145)
        or (features.amt_very_hi and features.fee_gap >= 80)
        or (thin_out and features.amt_med and features.fee_max >= 145)
        or (features.amt_hi and features.min_y <= 44)
        or (features.imbalance_hi and features.fee_max >= 100)
    )
    extreme6 = bool(
        (features.amt_very_hi and features.fee_max >= 195)
        or (thin_out and features.amt_hi and features.fee_max >= 195)
        or (features.amt_very_hi and features.min_y <= 32)
    )
    high6 = bool(
        features.amt_hi
        or features.fee_gap >= 110
        or features.imbalance_hi
        or (features.near_sym and features.fee_gap >= 40)
    )
    if extreme6:
        return 128, "dense32"
    if hard6:
        return 96, "dense32"
    if high6:
        return 96, "dense24"
    if profile == "adaptive_v7":
        return 64, "dgstr_v1"
    return 64, "baseline_canon16"


def resolve_two_pool_split_search_params(
    pool0: _PoolLike,
    pool1: _PoolLike,
    amount_in: int,
    *,
    search_profile: str,
    window: int,
) -> tuple[int, str]:
    """
    Resolve adaptive split policies into concrete `(window, profile)` pairs.
    """
    amount_in_i = _require_int_control(amount_in, name="amount_in")
    window_i = _require_nonnegative_control(window, name="window")
    prof = str(search_profile).strip().lower()
    if prof not in ADAPTIVE_SEARCH_PROFILES:
        return window_i, str(search_profile)
    if amount_in_i <= 0:
        return window_i, "baseline"

    features = _split_routing_features(pool0, pool1, amount_in_i)
    if prof == "adaptive_v1":
        return _resolve_adaptive_v1(features)
    if prof == "adaptive_v2":
        return _resolve_adaptive_v2(features)
    if prof == "adaptive_v3":
        return _resolve_adaptive_v3(features)
    if prof == "adaptive_v4":
        return _resolve_adaptive_v4(features)
    if prof == "adaptive_v5":
        return _resolve_adaptive_v5(features)
    return _resolve_adaptive_v6_or_v7(prof, features)
