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
_ADAPTIVE_V6_STAIRCASE_MAX_OUTPUT_LEVELS = 4096


@dataclass(frozen=True)
class PoolXY:
    x: int  # reserve_in
    y: int  # reserve_out
    fee_bps: int


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


def _min_gross_for_output_level(pool: PoolXY, t: int) -> int | None:
    """
    Closed-form minimal gross input `a` with out(a) >= t under v8 semantics.

    Proven exact (Lean: Proofs/SplitRoutingStaircase.lean, le_feeOut_iff):
        t <= out(a)  <=>  a >= ceil( ceil(t*x/(y-t)) * B / (B - fee) )
    for 0 < x, 0 < t < y, fee < B. Returns None when level t is unreachable.
    """
    t = int(t)
    if t <= 0:
        return None
    x, y, fee = int(pool.x), int(pool.y), int(pool.fee_bps)
    if x <= 0 or t >= y:
        return None
    alpha = BPS_DENOM - fee
    if alpha <= 0:
        return None
    n_t = -((-t * x) // (y - t))  # ceil(t*x / (y-t))
    a_t = -((-n_t * BPS_DENOM) // alpha)  # ceil(n_t * B / alpha)
    return int(max(a_t, 1))


def _staircase_v1_output_level_budget(pool0: PoolXY, pool1: PoolXY, amount_in: int) -> int | None:
    """
    Upper-bound the number of pool-0 output levels visited by staircase_v1.

    A return value of 0 means the both-valid interval is empty, so the exact
    solver only checks single-pool endpoints. None means the bound could not be
    established from valid pool-0/pool-1 inputs.
    """
    D = int(amount_in)
    if D <= 0:
        return None
    min0 = _min_gross_for_output_level(pool0, 1)
    min1 = _min_gross_for_output_level(pool1, 1)
    if min0 is None or min1 is None:
        return 0
    hi = D - int(min1)
    if int(min0) > int(hi):
        return 0
    try:
        return int(exact_out_for_pool_exact_in(pool0, int(hi)))
    except ValueError:
        return None


def staircase_jump_best_split_two_pools_exact_in(
    pool0: PoolXY,
    pool1: PoolXY,
    amount_in: int,
) -> Tuple[int, int]:
    """
    EXACT optimal split via staircase jump enumeration (deterministic,
    leftmost tie-break), bit-identical to brute force.

    Mathematical basis (Lean: Proofs/SplitRoutingStaircase.lean):
    - `two_pool_split_candidate_complete`: out0(a) is a monotone staircase
      and out1(D-a) an antitone one, so the leftmost maximizer of their sum
      over the both-valid interval [lo, hi] is `lo` or a jump point of out0.
    - `le_feeOut_iff` / `jump_point_closed_form`: the jump point for output
      level t is a_t = ceil(ceil(t*x0/(y0-t)) * B / (B - fee0)) - two
      ceiling divisions, no search.

    Cost: one cached pool-0 quote to identify each next jump, plus one pool-1
    quote to score that candidate (= O(min(span, out0(hi)))) versus O(span)
    quote pairs for brute force.
    """
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    D = int(amount_in)

    out0_cache: dict[int, int | None] = {}
    out1_cache: dict[int, int | None] = {}

    def quote0(a: int) -> int | None:
        a = int(a)
        if a <= 0:
            return 0
        if a not in out0_cache:
            try:
                out0_cache[a] = int(exact_out_for_pool_exact_in(pool0, a))
            except ValueError:
                out0_cache[a] = None
        return out0_cache[a]

    def quote1(b: int) -> int | None:
        b = int(b)
        if b <= 0:
            return 0
        if b not in out1_cache:
            try:
                out1_cache[b] = int(exact_out_for_pool_exact_in(pool1, b))
            except ValueError:
                out1_cache[b] = None
        return out1_cache[b]

    def total_out(a: int) -> int | None:
        b = D - a
        out0 = quote0(int(a))
        out1 = quote1(int(b))
        if out0 is None or out1 is None:
            return None
        return int(out0 + out1)

    best: tuple[int, int] | None = None

    def consider(a: int) -> None:
        nonlocal best
        tot = total_out(int(a))
        if tot is None:
            return
        cand = (int(tot), int(a))
        if _is_better_candidate(cand, best):
            best = cand

    # Single-pool endpoints, as in the existing search.
    consider(0)
    consider(D)

    # Both-valid interval [lo, hi]: closed-form minimal valid gross per pool
    # (out >= 1 is exactly level t = 1; validity is monotone in the gross).
    min0 = _min_gross_for_output_level(pool0, 1)
    min1 = _min_gross_for_output_level(pool1, 1)
    if min0 is not None and min1 is not None:
        lo = int(min0)
        hi = D - int(min1)
        a = lo
        # Walk jump points in ascending order: ascending visit order plus
        # strict-improvement updates yields the global leftmost maximizer
        # (every split is dominated by a candidate at or left of it).
        while a <= hi:
            out0 = quote0(int(a))
            if out0 is None:
                break  # only possible if level 1 itself is infeasible
            consider(a)
            a_next = _min_gross_for_output_level(pool0, int(out0) + 1)
            if a_next is None or int(a_next) <= a or int(a_next) > hi:
                break
            a = int(a_next)

    if best is None:
        raise ValueError("no feasible split")
    return int(best[0]), int(best[1])


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


def resolve_two_pool_split_search_params(
    pool0: PoolXY,
    pool1: PoolXY,
    amount_in: int,
    *,
    search_profile: str,
    window: int,
) -> tuple[int, str]:
    """
    Resolve higher-level split search policies into concrete `(window, profile)` pairs.

    This is an algorithm-invention hook: it lets the router request an adaptive policy
    without hardcoding it into the routing hot path.

    Currently supported policies:
    - baseline/dense24/dense32: identity
    - adaptive_v1: choose between (baseline,w64), (dense24,w64), (dense24,w96)
    - adaptive_v2: choose between (baseline_canon16,w64), (dense24,w64), (dense24,w96)
    - adaptive_v3: choose between (baseline,w64)/(baseline_canon16,w64), (dense24,w64), (dense24,w96)
    - adaptive_v4: choose between (baseline_canon16,w64) and (dense24,w96) with stricter escalation
    - adaptive_v5: adaptive_v4 + high-fee/high-pressure escalation to dense32 tiers
    - adaptive_v6: use exact staircase_v1 when its output-level budget is bounded,
      otherwise use tighter adaptive_v5 thresholds
    - adaptive_v7: adaptive_v6 hard-regime tiers, but route easy manifolds to experimental dgstr_v1
    """
    prof = str(search_profile).strip().lower()
    if prof not in {"adaptive_v1", "adaptive_v2", "adaptive_v3", "adaptive_v4", "adaptive_v5", "adaptive_v6", "adaptive_v7"}:
        return int(window), str(search_profile)

    if amount_in <= 0:
        return int(window), "baseline"

    x0, y0, f0 = int(pool0.x), int(pool0.y), int(pool0.fee_bps)
    x1, y1, f1 = int(pool1.x), int(pool1.y), int(pool1.fee_bps)
    D = int(amount_in)

    min_x = min(x0, x1)
    min_y = min(y0, y1)

    fee_gap = abs(int(f0) - int(f1))
    fee_max = max(int(f0), int(f1))
    x_ratio_hi = _ratio_ge_num_denom(a=max(x0, x1), b=max(1, min_x), num=3, denom=1)  # max/min >= 3
    y_ratio_hi = _ratio_ge_num_denom(a=max(y0, y1), b=max(1, min_y), num=5, denom=1)  # max/min >= 5

    # Symmetric-reserve manifold heuristic: near-equal reserves can induce wide plateaus,
    # but treat it as a hardness signal only in small-reserve regimes.
    near_sym_raw = _near_equal_bps(a=x0, b=y0, tol_bps=1500) or _near_equal_bps(a=x1, b=y1, tol_bps=1500)
    near_sym = bool(near_sym_raw and min_x <= 200)

    # Small-reserve regimes are where integer plateaus/disconnected maximizers are most common; prefer
    # canonicalizing profiles here even when not otherwise "hard".
    prefer_canon = bool(min_x <= 400)

    # Amount scale relative to smallest reserve_in (input-side liquidity proxy).
    amt_med = bool(min_x > 0 and D >= 40 * int(min_x))
    amt_hi = bool(min_x > 0 and D >= 80 * int(min_x))
    amt_very_hi = bool(min_x > 0 and D >= 120 * int(min_x))
    imbalance_hi = bool(x_ratio_hi and y_ratio_hi)

    # Tiered selection:
    # - Default to cheap baseline (w64).
    # - Escalate to dense24 for medium hardness.
    # - Escalate to dense24+w96 for high hardness.
    high = bool(amt_med or fee_gap >= 60 or x_ratio_hi or y_ratio_hi or near_sym)
    med = bool(high or fee_gap >= 30)

    if prof == "adaptive_v2":
        if high:
            return 96, "dense24"
        if med:
            return 64, "dense24"
        return 64, "baseline_canon16"

    if prof == "adaptive_v3":
        if high:
            return 96, "dense24"
        if med:
            return 64, "dense24"
        return (64, "baseline_canon16") if prefer_canon else (64, "baseline")

    if prof == "adaptive_v4":
        # Stricter escalation than v3:
        # - Default to baseline_canon16_w64 (strong quality/call-cost tradeoff).
        # - Escalate only for clearly hard regimes to dense24_w96.
        high4 = bool(amt_hi or fee_gap >= 90 or imbalance_hi or (near_sym and fee_gap >= 40))
        if high4:
            return 96, "dense24"
        return 64, "baseline_canon16"

    if prof == "adaptive_v5":
        # v5 keeps v4's cheap default posture but escalates in a stricter
        # high-fee/high-pressure manifold where dense24 can miss oracle optima.
        high4 = bool(amt_hi or fee_gap >= 90 or imbalance_hi or (near_sym and fee_gap >= 40))
        thin_out = bool(min_y <= 80)
        hard5 = bool(
            (amt_hi and fee_max >= 120)
            or (amt_very_hi and fee_gap >= 50)
            or (thin_out and amt_med and fee_max >= 120)
            or (amt_hi and min_y <= 64)
            or (imbalance_hi and fee_max >= 90)
        )
        extreme5 = bool(
            (amt_very_hi and fee_max >= 180)
            or (thin_out and amt_hi and fee_max >= 180)
            or (amt_very_hi and min_y <= 48)
        )
        if extreme5:
            return 128, "dense32"
        if hard5:
            return 96, "dense32"
        if high4:
            return 96, "dense24"
        return 64, "baseline_canon16"

    if prof in {"adaptive_v6", "adaptive_v7"}:
        # v6 retunes v5 thresholds using supervised stress-holdout evidence:
        # - keep dense32 escalation for the stress miss manifold,
        # - reduce unnecessary dense32 activation on default regimes.
        if prof == "adaptive_v6":
            staircase_budget = _staircase_v1_output_level_budget(pool0, pool1, D)
            if (
                staircase_budget is not None
                and int(staircase_budget) <= _ADAPTIVE_V6_STAIRCASE_MAX_OUTPUT_LEVELS
            ):
                return 0, "staircase_v1"
        high6 = bool(amt_hi or fee_gap >= 110 or imbalance_hi or (near_sym and fee_gap >= 40))
        thin_out = bool(min_y <= 80)
        hard6 = bool(
            (amt_hi and fee_max >= 145)
            or (amt_very_hi and fee_gap >= 80)
            or (thin_out and amt_med and fee_max >= 145)
            or (amt_hi and min_y <= 44)
            or (imbalance_hi and fee_max >= 100)
        )
        extreme6 = bool(
            (amt_very_hi and fee_max >= 195)
            or (thin_out and amt_hi and fee_max >= 195)
            or (amt_very_hi and min_y <= 32)
        )
        if extreme6:
            return 128, "dense32"
        if hard6:
            return 96, "dense32"
        if high6:
            return 96, "dense24"
        if prof == "adaptive_v7":
            return 64, "dgstr_v1"
        return 64, "baseline_canon16"

    # adaptive_v1 (legacy)
    if high:
        return 96, "dense24"
    if med:
        return 64, "dense24"
    return 64, "baseline"


def best_split_two_pools_exact_in(
    pool0: PoolXY,
    pool1: PoolXY,
    amount_in: int,
    *,
    window: int = 64,
    search_profile: str = "adaptive_v6",
) -> Tuple[int, int]:
    """
    Fast deterministic split optimizer:
    - For small trades, use brute-force (exact + canonical).
    - For larger trades, use a multi-center window search seeded by a continuous approximation,
      plus endpoints and a refinement pass.
    - Choose best total output; tie-break by smallest a.

    `search_profile` (guarded mode):
    - "baseline": legacy search schedule.
    - "dense24": denser deterministic coarse probes (24 bins) + local refinement.
    - "dense32": very dense deterministic coarse probes (32 bins) + local refinement.
    - "dgstr_v1": experimental discrete golden-section / ternary refinement with bounded rescue scans.
    - "staircase_v1": EXACT jump enumeration (Lean: Proofs/SplitRoutingStaircase.lean);
      bit-identical to brute force including the leftmost tie-break, with O(1)
      quote work per distinct pool-0 output level instead of per split point.

    This is intended to be iteratively improved with counterexample mining.
    """
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if window < 0:
        raise ValueError("window must be non-negative")
    # Allow adaptive profile names directly at the algorithm entrypoint.
    # This keeps call sites simple while retaining explicit deterministic resolution.
    profile = str(search_profile).strip().lower()
    if profile in {"adaptive_v1", "adaptive_v2", "adaptive_v3", "adaptive_v4", "adaptive_v5", "adaptive_v6", "adaptive_v7"}:
        window, profile = resolve_two_pool_split_search_params(
            pool0,
            pool1,
            int(amount_in),
            search_profile=profile,
            window=int(window),
        )

    if profile == "staircase_v1":
        # Proven-exact optimizer: candidate completeness and closed-form jump
        # points are certified in Lean (two_pool_split_candidate_complete,
        # le_feeOut_iff). No window/grid parameters apply.
        return staircase_jump_best_split_two_pools_exact_in(pool0, pool1, amount_in)

    _profile, grid_n, force_dense_grid, left_sweep_k = _search_profile_params(profile)

    brute_force_max = 4096
    if amount_in <= brute_force_max:
        return brute_force_best_split_two_pools_exact_in(pool0, pool1, amount_in)

    tot_cache: dict[int, int | None] = {}

    def total_out(a: int) -> int | None:
        if not (0 <= a <= amount_in):
            return None
        if a in tot_cache:
            return tot_cache[a]
        b = amount_in - a
        try:
            out0 = exact_out_for_pool_exact_in(pool0, a) if a > 0 else 0
            out1 = exact_out_for_pool_exact_in(pool1, b) if b > 0 else 0
        except ValueError:
            tot_cache[a] = None
            return None
        tot = int(out0 + out1)
        tot_cache[a] = tot
        return tot

    best: tuple[int, int] | None = None
    for a in (0, amount_in):
        tot = total_out(a)
        if tot is None:
            continue
        cand = (int(tot), int(a))
        if _is_better_candidate(cand, best):
            best = cand

    min0 = _min_valid_amount_for_pool(pool=pool0, amount_in_total=int(amount_in))
    min1 = _min_valid_amount_for_pool(pool=pool1, amount_in_total=int(amount_in))
    if min0 is not None and min1 is not None:
        lo_both = min0
        hi_both = amount_in - min1
        if lo_both <= hi_both:
            a_star = _seed_opt_split_by_derivative(
                pool0,
                pool1,
                amount_in_total=int(amount_in),
                lo_both=int(lo_both),
                hi_both=int(hi_both),
            )
            a_star = max(lo_both, min(hi_both, a_star))

            best_both: tuple[int, int] | None
            if profile == "dgstr_v1":
                best_both = _search_dgstr_v1(
                    lo_both=int(lo_both),
                    hi_both=int(hi_both),
                    a_star=int(a_star),
                    window=int(window),
                    total_out=total_out,
                )
            else:
                span = hi_both - lo_both
                centers = {lo_both, hi_both, (lo_both + hi_both) // 2, a_star}
                if span > 0 and (force_dense_grid or span > int(grid_n) * int(window)):
                    # Deterministic coarse coverage grid; density controlled by search_profile.
                    for i in range(1, int(grid_n)):
                        centers.add(lo_both + (span * i) // int(grid_n))

                if int(left_sweep_k) > 0 and int(window) > 0:
                    # Deterministic extra coverage to the left of the continuous optimum.
                    #
                    # Motivation: under integer rounding, the set of maximizers can be disconnected; a local plateau
                    # walk-left only canonicalizes within the discovered segment. Adding a bounded left sweep reduces
                    # tie-break mismatches (min-a among maximizers) without forcing a full global scan.
                    for k in range(1, int(left_sweep_k) + 1):
                        c = int(a_star) - int(k) * int(window)
                        if c <= lo_both:
                            centers.add(lo_both)
                            break
                        centers.add(c)

                best_both = None
                for c in sorted(centers):
                    scan_cand = _scan_range_best(
                        lo=max(lo_both, c - window),
                        hi=min(hi_both, c + window),
                        total_out=total_out,
                    )
                    if _is_better_candidate(scan_cand, best_both):
                        best_both = scan_cand

                if best_both is not None:
                    # Refine by expanding around the current best within the both-valid interval.
                    refine_out, refine_a = best_both
                    half = max(1, int(window))
                    while True:
                        scan_cand = _scan_range_best(
                            lo=max(lo_both, refine_a - half),
                            hi=min(hi_both, refine_a + half),
                            total_out=total_out,
                        )
                        if _is_better_candidate(scan_cand, (int(refine_out), int(refine_a))):
                            # Invariant: _is_better_candidate(None, _) is False, so scan_cand is
                            # non-None inside this branch. Explicit guard (not `assert`) so
                            # it survives `python -O`.
                            if scan_cand is None:
                                raise AssertionError(
                                    "internal: _is_better_candidate accepted a None candidate")
                            refine_out, refine_a = scan_cand
                        r_lo = max(lo_both, refine_a - half)
                        r_hi = min(hi_both, refine_a + half)
                        if r_lo == lo_both and r_hi == hi_both:
                            break
                        # If the best is at the edge of our scanned window, keep expanding.
                        #
                        # Important: if the best is at the *global* boundary (lo_both/hi_both), naive expansion
                        # degenerates into scanning the full span even when we already probed other centers.
                        # This can create an O(D) call cliff in deep-liquidity regimes where the optimum is at a boundary.
                        if refine_a in (r_lo, r_hi) and refine_a not in (lo_both, hi_both):
                            half *= 2
                            if half >= span:
                                half = span
                            continue
                        break

                    best_both = _canonicalize_leftmost(
                        lo_both=int(lo_both),
                        candidate=(int(refine_out), int(refine_a)),
                        total_out=total_out,
                    )

                    if force_dense_grid:
                        # Dense profiles pay a small extra pass to enforce global canonical tie-break:
                        # choose the smallest feasible `a` that attains `refine_out`.
                        refine_out2, refine_a2 = best_both
                        for a_scan in range(int(lo_both), int(refine_a2)):
                            tot_scan = total_out(int(a_scan))
                            if tot_scan is not None and int(tot_scan) == int(refine_out2):
                                best_both = (int(refine_out2), int(a_scan))
                                break

            if _is_better_candidate(best_both, best):
                best = best_both

    if best is None:
        raise ValueError("no feasible split")
    return int(best[0]), int(best[1])
