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

BPS_DENOM = 10_000
ADAPTIVE_SEARCH_PROFILES = frozenset({
    "adaptive_v1",
    "adaptive_v2",
    "adaptive_v3",
    "adaptive_v4",
    "adaptive_v5",
    "adaptive_v6",
    "adaptive_v7",
})
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


@dataclass(frozen=True)
class _WindowSearchPlan:
    pool0: PoolXY
    pool1: PoolXY
    amount_in: int
    bounds: tuple[int, int]
    profile: str
    grid_n: int
    force_dense_grid: bool
    left_sweep_k: int
    window: int
    total_out: Callable[[int], int | None]


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


def exact_out_for_pool_exact_in(pool: PoolXY, amount_in: int) -> int:
    """
    Exact-in quote under v8 semantics:
      fee = ceil(gross * fee_bps / 10_000)
      net = gross - fee
      out = floor(y * net / (x + net))
    Raises ValueError on invalid/degenerate trades (matching kernel behavior).
    """
    if pool.x <= 0 or pool.y <= 0:
        raise ValueError("cannot swap against empty reserve")
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if not (0 <= pool.fee_bps <= 10_000):
        raise ValueError("fee_bps out of range")
    fee = _fee_total_v8(gross_in=amount_in, fee_bps=pool.fee_bps)
    net = amount_in - fee
    if net <= 0:
        raise ValueError("net_in must be positive")
    out = (pool.y * net) // (pool.x + net)
    if out <= 0:
        raise ValueError("amount_out is zero")
    if out > pool.y:
        raise ValueError("amount_out exceeds reserve_out")
    return int(out)


def brute_force_best_split_two_pools_exact_in(pool0: PoolXY, pool1: PoolXY, amount_in: int) -> Tuple[int, int]:
    """
    Reference: brute force all splits a in [0..amount_in], return (best_out, best_a).
    Deterministic tie-break: smallest a.
    """
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    best_out: int | None = None
    best_a = 0
    for a in range(0, amount_in + 1):
        b = amount_in - a
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


def _derivative_gt(pool0: PoolXY, a0: int, pool1: PoolXY, a1: int) -> bool:
    """
    Compare continuous marginal outputs without floats.

    For the continuous approximation (ignore ceil/floor effects):
      out(a) = y * (α*a) / (x + α*a), where α = (BPS - fee_bps)/BPS.
    The derivative simplifies to:
      out'(a) ∝ (y * α_num * x) / (BPS*x + α_num*a)^2
    where α_num = BPS - fee_bps.

    Returns True iff out0'(a0) > out1'(a1).
    """
    a0 = int(a0)
    a1 = int(a1)
    alpha0 = int(BPS_DENOM) - int(pool0.fee_bps)
    alpha1 = int(BPS_DENOM) - int(pool1.fee_bps)
    if alpha0 <= 0 or alpha1 <= 0:
        return False
    if pool0.x <= 0 or pool0.y <= 0 or pool1.x <= 0 or pool1.y <= 0:
        return False
    # Compare: w0/den0^2 > w1/den1^2  <=>  w0*den1^2 > w1*den0^2
    w0 = int(pool0.y) * int(alpha0) * int(pool0.x)
    w1 = int(pool1.y) * int(alpha1) * int(pool1.x)
    den0 = int(BPS_DENOM) * int(pool0.x) + int(alpha0) * int(a0)
    den1 = int(BPS_DENOM) * int(pool1.x) + int(alpha1) * int(a1)
    if den0 <= 0 or den1 <= 0:
        return False
    return int(w0) * int(den1) * int(den1) > int(w1) * int(den0) * int(den0)


def _seed_opt_split_by_derivative(
    pool0: PoolXY,
    pool1: PoolXY,
    *,
    amount_in_total: int,
    lo_both: int,
    hi_both: int,
) -> int:
    """
    Deterministic integer seed for the best split (continuous approximation).

    We binary-search for the first `a` where:
      out0'(a) <= out1'(D-a)
    within the both-valid interval [lo_both, hi_both].
    """
    D = int(amount_in_total)
    lo = int(lo_both)
    hi = int(hi_both)
    if lo > hi:
        return lo
    # If even at hi, pool0 has higher marginal output, the optimum is at the boundary.
    if _derivative_gt(pool0, hi, pool1, int(D - hi)):
        return hi
    # If already <= at lo, the root is at/before lo.
    if not _derivative_gt(pool0, lo, pool1, int(D - lo)):
        return lo

    # Monotone: g(a)=out0'(a)-out1'(D-a) decreases with a.
    while lo < hi:
        mid = (lo + hi) // 2
        if _derivative_gt(pool0, mid, pool1, int(D - mid)):
            lo = mid + 1
        else:
            hi = mid
    return int(lo)


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


def _ceil_div_positive(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    return (int(numerator) + int(denominator) - 1) // int(denominator)


def _min_gross_in_for_output_level(pool: PoolXY, output_level: int) -> int | None:
    alpha = int(BPS_DENOM) - int(pool.fee_bps)
    target = int(output_level)
    if alpha <= 0 or target <= 0 or target >= int(pool.y):
        return None

    # Invert floor(y*n/(x+n)) >= target to n >= ceil(target*x/(y-target)),
    # then invert net=floor(gross*alpha/BPS_DENOM).
    min_net = _ceil_div_positive(target * int(pool.x), int(pool.y) - target)
    return _ceil_div_positive(min_net * int(BPS_DENOM), alpha)


def _pool_output_jump_candidates(pool: PoolXY, amount_in_total: int) -> set[int]:
    candidates: set[int] = set()
    try:
        max_output = exact_out_for_pool_exact_in(pool, int(amount_in_total))
    except ValueError:
        return candidates

    for output_level in range(1, int(max_output) + 1):
        gross_in = _min_gross_in_for_output_level(pool, output_level)
        if gross_in is not None and gross_in <= int(amount_in_total):
            candidates.add(int(gross_in))
    return candidates


def staircase_jump_best_split_two_pools_exact_in(pool0: PoolXY, pool1: PoolXY, amount_in: int) -> tuple[int, int]:
    """
    Exact two-pool CPMM split by enumerating pool0 output jump points.

    Complexity is O(J) quotes where J is the number of distinct positive pool0
    outputs reachable with `amount_in`, plus two endpoint checks. This is exact
    because pool0 is constant between jumps and pool1 cannot improve as input is
    shifted away from it.
    """
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")

    quote_cache = _SplitQuoteCache(pool0=pool0, pool1=pool1, amount_in=int(amount_in), totals={})
    best: tuple[int, int] | None = None
    for a in sorted({0, int(amount_in)} | _pool_output_jump_candidates(pool0, int(amount_in))):
        total = quote_cache.total_out(int(a))
        if total is None:
            continue
        candidate = (int(total), int(a))
        if _is_better_candidate(candidate, best):
            best = candidate

    if best is None:
        raise ValueError("no feasible split")
    return int(best[0]), int(best[1])


def _scan_range_best(
    *,
    lo: int,
    hi: int,
    total_out: Callable[[int], int | None],
) -> tuple[int, int] | None:
    if lo > hi:
        return None
    best_out = -1
    best_a = 0
    for a in range(int(lo), int(hi) + 1):
        tot = total_out(int(a))
        if tot is None:
            continue
        if tot > best_out or (tot == best_out and int(a) < best_a):
            best_out = int(tot)
            best_a = int(a)
    return None if best_out < 0 else (int(best_out), int(best_a))


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


def _canonicalize_leftmost(
    *,
    lo_both: int,
    candidate: tuple[int, int],
    total_out: Callable[[int], int | None],
) -> tuple[int, int]:
    best_out, best_a = int(candidate[0]), int(candidate[1])
    while best_a > int(lo_both):
        prev = total_out(int(best_a) - 1)
        if prev is None or int(prev) != int(best_out):
            break
        best_a -= 1
    return int(best_out), int(best_a)


def _search_dgstr_v1(
    *,
    lo_both: int,
    hi_both: int,
    a_star: int,
    window: int,
    total_out: Callable[[int], int | None],
) -> tuple[int, int] | None:
    """
    Experimental search profile:
    - sparse deterministic probes across the feasible interval,
    - repeated discrete ternary refinement,
    - bounded rescue scans around the strongest probe centers.

    This is intentionally scoped to easy regimes and is not used as the default profile.
    """
    lo = int(lo_both)
    hi = int(hi_both)
    if lo > hi:
        return None

    point_vals: dict[int, int | None] = {}

    def probe(a: int) -> int | None:
        if not (lo <= int(a) <= hi):
            return None
        key = int(a)
        if key not in point_vals:
            point_vals[key] = total_out(key)
        return point_vals[key]

    best: tuple[int, int] | None = None
    span = int(hi - lo)
    centers = {int(lo), int(hi), int((lo + hi) // 2), int(a_star)}
    if span > 0:
        for i in range(1, 8):
            centers.add(int(lo + (span * i) // 8))

    for c in sorted(centers):
        val = probe(int(c))
        if val is None:
            continue
        cand = (int(val), int(c))
        if _is_better_candidate(cand, best):
            best = cand

    cur_lo = int(lo)
    cur_hi = int(hi)
    while cur_hi - cur_lo > max(4 * int(window), 160):
        span = int(cur_hi - cur_lo)
        step = max(1, span // 3)
        m1 = int(cur_lo + step)
        m2 = int(cur_hi - step)
        v1 = probe(int(m1))
        v2 = probe(int(m2))
        if v2 is None or (v1 is not None and int(v1) > int(v2)):
            cur_hi = int(m2)
        elif v1 is None or int(v2) > int(v1):
            cur_lo = int(m1)
        else:
            cur_lo = int(m1)
            cur_hi = int(m2)

    ranked = [(int(v), int(a)) for a, v in point_vals.items() if v is not None]
    ranked.sort(key=lambda t: (int(t[0]), -int(t[1])), reverse=True)

    rescue_centers = [int(a) for _v, a in ranked[:6]]
    rescue_centers.extend([int(cur_lo), int(cur_hi), int((cur_lo + cur_hi) // 2), int(a_star)])

    seen: set[int] = set()
    for c in rescue_centers:
        if int(c) in seen:
            continue
        seen.add(int(c))
        scan_cand = _scan_range_best(
            lo=max(int(lo), int(c) - int(window)),
            hi=min(int(hi), int(c) + int(window)),
            total_out=total_out,
        )
        if _is_better_candidate(scan_cand, best):
            best = scan_cand

    if best is None:
        return None
    return _canonicalize_leftmost(lo_both=int(lo), candidate=best, total_out=total_out)


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


def _split_routing_features(pool0: PoolXY, pool1: PoolXY, amount_in: int) -> _SplitRoutingFeatures:
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
    pool0: PoolXY,
    pool1: PoolXY,
    amount_in: int,
    *,
    search_profile: str,
    window: int,
) -> tuple[int, str]:
    """
    Resolve adaptive split policies into concrete `(window, profile)` pairs.
    """
    prof = str(search_profile).strip().lower()
    if prof not in ADAPTIVE_SEARCH_PROFILES:
        return int(window), str(search_profile)
    if amount_in <= 0:
        return int(window), "baseline"

    features = _split_routing_features(pool0, pool1, int(amount_in))
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


def _split_search_centers(
    *,
    lo_both: int,
    hi_both: int,
    a_star: int,
    grid_n: int,
    window: int,
    force_dense_grid: bool,
    left_sweep_k: int,
) -> set[int]:
    span = int(hi_both) - int(lo_both)
    centers = {int(lo_both), int(hi_both), int((lo_both + hi_both) // 2), int(a_star)}
    if span > 0 and (force_dense_grid or span > int(grid_n) * int(window)):
        for i in range(1, int(grid_n)):
            centers.add(int(lo_both) + (span * i) // int(grid_n))

    if int(left_sweep_k) <= 0 or int(window) <= 0:
        return centers
    for k in range(1, int(left_sweep_k) + 1):
        c = int(a_star) - int(k) * int(window)
        if c <= int(lo_both):
            centers.add(int(lo_both))
            break
        centers.add(c)
    return centers


def _scan_centers_best(
    *,
    centers: set[int],
    lo_both: int,
    hi_both: int,
    window: int,
    total_out: Callable[[int], int | None],
) -> tuple[int, int] | None:
    best: tuple[int, int] | None = None
    for c in sorted(centers):
        candidate = _scan_range_best(
            lo=max(int(lo_both), int(c) - int(window)),
            hi=min(int(hi_both), int(c) + int(window)),
            total_out=total_out,
        )
        if _is_better_candidate(candidate, best):
            best = candidate
    return best


def _refine_window_best(
    *,
    candidate: tuple[int, int],
    lo_both: int,
    hi_both: int,
    span: int,
    window: int,
    total_out: Callable[[int], int | None],
) -> tuple[int, int]:
    refine_out, refine_a = int(candidate[0]), int(candidate[1])
    half = max(1, int(window))
    while True:
        scan_cand = _scan_range_best(
            lo=max(int(lo_both), refine_a - half),
            hi=min(int(hi_both), refine_a + half),
            total_out=total_out,
        )
        if _is_better_candidate(scan_cand, (refine_out, refine_a)):
            if scan_cand is None:
                raise RuntimeError("internal split-routing candidate ordering invariant violated")
            refine_out, refine_a = int(scan_cand[0]), int(scan_cand[1])

        r_lo = max(int(lo_both), refine_a - half)
        r_hi = min(int(hi_both), refine_a + half)
        if r_lo == int(lo_both) and r_hi == int(hi_both):
            break
        if refine_a in (r_lo, r_hi) and refine_a not in (int(lo_both), int(hi_both)):
            half = min(int(span), half * 2)
            continue
        break
    return refine_out, refine_a


def _dense_profile_leftmost(
    *,
    candidate: tuple[int, int],
    lo_both: int,
    total_out: Callable[[int], int | None],
    force_dense_grid: bool,
) -> tuple[int, int]:
    best_out, best_a = _canonicalize_leftmost(lo_both=int(lo_both), candidate=candidate, total_out=total_out)
    if not force_dense_grid:
        return best_out, best_a

    for a_scan in range(int(lo_both), int(best_a)):
        total = total_out(int(a_scan))
        if total is not None and int(total) == int(best_out):
            return int(best_out), int(a_scan)
    return int(best_out), int(best_a)


def _search_windowed_both_valid(plan: _WindowSearchPlan) -> tuple[int, int] | None:
    lo_both, hi_both = int(plan.bounds[0]), int(plan.bounds[1])
    a_star = _seed_opt_split_by_derivative(
        plan.pool0,
        plan.pool1,
        amount_in_total=int(plan.amount_in),
        lo_both=lo_both,
        hi_both=hi_both,
    )
    a_star = max(lo_both, min(hi_both, int(a_star)))
    if plan.profile == "dgstr_v1":
        return _search_dgstr_v1(
            lo_both=lo_both,
            hi_both=hi_both,
            a_star=a_star,
            window=int(plan.window),
            total_out=plan.total_out,
        )

    span = hi_both - lo_both
    centers = _split_search_centers(
        lo_both=lo_both,
        hi_both=hi_both,
        a_star=a_star,
        grid_n=int(plan.grid_n),
        window=int(plan.window),
        force_dense_grid=plan.force_dense_grid,
        left_sweep_k=int(plan.left_sweep_k),
    )
    local_best = _scan_centers_best(
        centers=centers,
        lo_both=lo_both,
        hi_both=hi_both,
        window=int(plan.window),
        total_out=plan.total_out,
    )
    if local_best is None:
        return None
    refined = _refine_window_best(
        candidate=local_best,
        lo_both=lo_both,
        hi_both=hi_both,
        span=span,
        window=int(plan.window),
        total_out=plan.total_out,
    )
    return _dense_profile_leftmost(
        candidate=refined,
        lo_both=lo_both,
        total_out=plan.total_out,
        force_dense_grid=plan.force_dense_grid,
    )


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
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if window < 0:
        raise ValueError("window must be non-negative")

    window, profile = _resolve_entrypoint_profile(
        pool0,
        pool1,
        int(amount_in),
        window=int(window),
        search_profile=search_profile,
    )
    if profile == EXACT_STAIRCASE_PROFILE:
        return staircase_jump_best_split_two_pools_exact_in(pool0, pool1, int(amount_in))

    _profile, grid_n, force_dense_grid, left_sweep_k = _search_profile_params(profile)

    brute_force_max = 4096
    if amount_in <= brute_force_max:
        return brute_force_best_split_two_pools_exact_in(pool0, pool1, amount_in)

    quote_cache = _SplitQuoteCache(pool0=pool0, pool1=pool1, amount_in=int(amount_in), totals={})
    best = _best_endpoint_split(int(amount_in), quote_cache.total_out)

    bounds = _both_valid_bounds(pool0, pool1, int(amount_in))
    if bounds is not None:
        best_both = _search_windowed_both_valid(_WindowSearchPlan(
            pool0=pool0,
            pool1=pool1,
            amount_in=int(amount_in),
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
