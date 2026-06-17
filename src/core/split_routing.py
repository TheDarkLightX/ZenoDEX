"""
Split routing for CPMM exact-in (state-of-the-art execution).

Problem:
Given two parallel CPMM pools for the same asset pair (x,y) with fees, and a total
input amount D (exact-in), choose a split D = a + (D-a) maximizing total output.

This is a key "DEX v2 -> v3+" capability:
- It reduces price impact by distributing flow across liquidity sources.
- It is deterministic and can be certificate-verified (brute-force in bounded regimes).

We implement:
- exact_out_for_pool_exact_in(): integer CPMM v8 semantics (fee ceil, output floor)
- best_split_two_pools_exact_in(): fast heuristic + local search, deterministic tie-break
- brute_force_best_split_two_pools_exact_in(): reference solver for testing/certification

Determinism:
- Ties broken by smaller split `a` (send less to pool0).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Tuple

from ..kernels.python.cpmm_swap_v8 import compute_fee_total as _fee_total_v8
from .domain_limits import is_strict_int
from .split_routing_profiles import ADAPTIVE_SEARCH_PROFILES, resolve_two_pool_split_search_params
from .split_routing_staircase import (
    staircase_jump_best_split_two_pools_exact_in as _staircase_jump_best_split_two_pools_exact_in,
)
from .split_routing_windowed import WindowSearchPlan, search_windowed_both_valid

BPS_DENOM = 10_000
EXACT_STAIRCASE_PROFILE = "staircase_exact"


@dataclass(frozen=True)
class PoolXY:
    x: int  # reserve_in
    y: int  # reserve_out
    fee_bps: int


@dataclass
class _SplitQuoteCache:
    pool0: PoolXY
    pool1: PoolXY
    amount_in: int
    totals: dict[int, int | None]

    def total_out(self, a: int) -> int | None:
        if not (0 <= a <= self.amount_in):
            return None
        if a in self.totals:
            return self.totals[a]

        b = int(self.amount_in) - int(a)
        try:
            out0 = exact_out_for_pool_exact_in(self.pool0, a) if a > 0 else 0
            out1 = exact_out_for_pool_exact_in(self.pool1, b) if b > 0 else 0
        except ValueError:
            self.totals[a] = None
            return None

        total = int(out0 + out1)
        self.totals[a] = total
        return total


def _require_int_control(value: object, *, name: str) -> int:
    if not is_strict_int(value):
        raise ValueError(f"{name} must be an int")
    return int(value)


def _require_positive_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) <= 0:
        raise ValueError(f"{name} must be positive")
    return int(value)


def _require_nonnegative_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def exact_out_for_pool_exact_in(pool: PoolXY, amount_in: int) -> int:
    """
    Exact-in quote under v8 semantics:
      fee = ceil(gross * fee_bps / 10_000)
      net = gross - fee
      out = floor(y * net / (x + net))
    Raises ValueError on invalid/degenerate trades (matching kernel behavior).
    """
    x = _require_int_control(pool.x, name="reserve_in")
    y = _require_int_control(pool.y, name="reserve_out")
    fee_bps = _require_int_control(pool.fee_bps, name="fee_bps")
    amount_in_i = _require_positive_control(amount_in, name="amount_in")
    if x <= 0 or y <= 0:
        raise ValueError("cannot swap against empty reserve")
    if not (0 <= fee_bps <= 10_000):
        raise ValueError("fee_bps out of range")
    fee = _fee_total_v8(gross_in=amount_in_i, fee_bps=fee_bps)
    net = amount_in_i - fee
    if net <= 0:
        raise ValueError("net_in must be positive")
    out = (y * net) // (x + net)
    if out <= 0:
        raise ValueError("amount_out is zero")
    if out > y:
        raise ValueError("amount_out exceeds reserve_out")
    return int(out)


def brute_force_best_split_two_pools_exact_in(pool0: PoolXY, pool1: PoolXY, amount_in: int) -> Tuple[int, int]:
    """
    Reference: brute force all splits a in [0..amount_in], return (best_out, best_a).
    Deterministic tie-break: smallest a.
    """
    amount_in_i = _require_positive_control(amount_in, name="amount_in")
    best_out: int | None = None
    best_a = 0
    for a in range(0, amount_in_i + 1):
        b = amount_in_i - a
        try:
            out0 = exact_out_for_pool_exact_in(pool0, a) if a > 0 else 0
            out1 = exact_out_for_pool_exact_in(pool1, b) if b > 0 else 0
        except ValueError:
            continue
        total = out0 + out1
        if best_out is None or total > best_out or (total == best_out and a < best_a):
            best_out = total
            best_a = a
    if best_out is None:
        raise ValueError("no feasible split")
    return best_out, best_a


def _search_profile_params(search_profile: str) -> tuple[str, int, bool, int]:
    profile = str(search_profile).strip().lower()
    if profile == "baseline":
        return profile, 8, False, 0
    if profile == "baseline_canon16":
        # Baseline schedule, but with extra left-sweep centers to reduce canonical tie-break mismatches
        # without paying the full dense-profile global scan cost.
        return profile, 8, False, 16
    if profile == "dense24":
        return profile, 24, True, 0
    if profile == "dense32":
        return profile, 32, True, 0
    if profile == "dgstr_v1":
        # Experimental: discrete golden-section / ternary refinement plus bounded rescue scans.
        # This profile is intentionally not the default; it targets easy regimes where the
        # objective is close to unimodal and call-count reduction matters more than full-span coverage.
        return profile, 8, False, 0
    raise ValueError(f"unsupported search_profile: {search_profile}")


def _is_better_candidate(
    cand: tuple[int, int] | None,
    best: tuple[int, int] | None,
) -> bool:
    if cand is None:
        return False
    if best is None:
        return True
    return bool(cand[0] > best[0] or (cand[0] == best[0] and cand[1] < best[1]))


def staircase_jump_best_split_two_pools_exact_in(pool0: PoolXY, pool1: PoolXY, amount_in: int) -> tuple[int, int]:
    amount_in_i = _require_positive_control(amount_in, name="amount_in")
    return _staircase_jump_best_split_two_pools_exact_in(
        pool0,
        pool1,
        amount_in_i,
        quote_exact_in=exact_out_for_pool_exact_in,
    )


def _min_valid_amount_for_pool(
    *,
    pool: PoolXY,
    amount_in_total: int,
) -> int | None:
    def is_valid(a: int) -> bool:
        if a <= 0:
            return False
        try:
            exact_out_for_pool_exact_in(pool, int(a))
        except ValueError:
            return False
        return True

    if not is_valid(int(amount_in_total)):
        return None
    lo = 1
    hi = int(amount_in_total)
    while lo < hi:
        mid = (lo + hi) // 2
        if is_valid(int(mid)):
            hi = mid
        else:
            lo = mid + 1
    return int(lo)


def _resolve_entrypoint_profile(
    pool0: PoolXY,
    pool1: PoolXY,
    amount_in: int,
    *,
    window: int,
    search_profile: str,
) -> tuple[int, str]:
    profile = str(search_profile).strip().lower()
    if profile == EXACT_STAIRCASE_PROFILE:
        return int(window), profile
    if profile not in ADAPTIVE_SEARCH_PROFILES:
        return int(window), profile
    return resolve_two_pool_split_search_params(
        pool0,
        pool1,
        int(amount_in),
        search_profile=profile,
        window=int(window),
    )


def _best_endpoint_split(amount_in: int, total_out: Callable[[int], int | None]) -> tuple[int, int] | None:
    best: tuple[int, int] | None = None
    for a in (0, int(amount_in)):
        total = total_out(a)
        if total is None:
            continue
        candidate = (int(total), int(a))
        if _is_better_candidate(candidate, best):
            best = candidate
    return best


def _both_valid_bounds(pool0: PoolXY, pool1: PoolXY, amount_in: int) -> tuple[int, int] | None:
    min0 = _min_valid_amount_for_pool(pool=pool0, amount_in_total=int(amount_in))
    min1 = _min_valid_amount_for_pool(pool=pool1, amount_in_total=int(amount_in))
    if min0 is None or min1 is None:
        return None

    lo_both = int(min0)
    hi_both = int(amount_in) - int(min1)
    return (lo_both, hi_both) if lo_both <= hi_both else None


def best_split_two_pools_exact_in(
    pool0: PoolXY,
    pool1: PoolXY,
    amount_in: int,
    *,
    window: int = 64,
    search_profile: str = "adaptive_v6",
) -> Tuple[int, int]:
    """
    Fast deterministic split optimizer with smallest-`a` tie-breaks.

    Small trades use the brute-force oracle. Larger trades use endpoints plus a
    multi-center window search seeded by a continuous marginal-output estimate.
    """
    amount_in_i = _require_positive_control(amount_in, name="amount_in")
    window_i = _require_nonnegative_control(window, name="window")

    window, profile = _resolve_entrypoint_profile(
        pool0,
        pool1,
        amount_in_i,
        window=window_i,
        search_profile=search_profile,
    )
    if profile == EXACT_STAIRCASE_PROFILE:
        return staircase_jump_best_split_two_pools_exact_in(pool0, pool1, amount_in_i)

    _profile, grid_n, force_dense_grid, left_sweep_k = _search_profile_params(profile)

    brute_force_max = 4096
    if amount_in_i <= brute_force_max:
        return brute_force_best_split_two_pools_exact_in(pool0, pool1, amount_in_i)

    quote_cache = _SplitQuoteCache(pool0=pool0, pool1=pool1, amount_in=amount_in_i, totals={})
    best = _best_endpoint_split(amount_in_i, quote_cache.total_out)

    bounds = _both_valid_bounds(pool0, pool1, amount_in_i)
    if bounds is not None:
        best_both = search_windowed_both_valid(WindowSearchPlan(
            pool0=pool0,
            pool1=pool1,
            amount_in=amount_in_i,
            bounds=bounds,
            profile=profile,
            grid_n=int(grid_n),
            force_dense_grid=force_dense_grid,
            left_sweep_k=int(left_sweep_k),
            window=int(window),
            total_out=quote_cache.total_out,
        ))
        if _is_better_candidate(best_both, best):
            best = best_both

    if best is None:
        raise ValueError("no feasible split")
    return int(best[0]), int(best[1])
