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
from typing import Tuple

from ..kernels.python.cpmm_swap_v8 import compute_fee_total as _fee_total_v8

BPS_DENOM = 10_000


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
        except Exception:
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
    raise ValueError(f"unsupported search_profile: {search_profile}")


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
    - adaptive_v6: tighter adaptive_v5 thresholds tuned to cut default-call cost while preserving stress quality
    """
    prof = str(search_profile).strip().lower()
    if prof not in {"adaptive_v1", "adaptive_v2", "adaptive_v3", "adaptive_v4", "adaptive_v5", "adaptive_v6"}:
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

    if prof == "adaptive_v6":
        # v6 retunes v5 thresholds using supervised stress-holdout evidence:
        # - keep dense32 escalation for the stress miss manifold,
        # - reduce unnecessary dense32 activation on default regimes.
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

    This is intended to be iteratively improved with counterexample mining.
    """
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if window < 0:
        raise ValueError("window must be non-negative")
    # Allow adaptive profile names directly at the algorithm entrypoint.
    # This keeps call sites simple while retaining explicit deterministic resolution.
    profile = str(search_profile).strip().lower()
    if profile in {"adaptive_v1", "adaptive_v2", "adaptive_v3", "adaptive_v4", "adaptive_v5", "adaptive_v6"}:
        window, profile = resolve_two_pool_split_search_params(
            pool0,
            pool1,
            int(amount_in),
            search_profile=profile,
            window=int(window),
        )

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
        except Exception:
            tot_cache[a] = None
            return None
        tot = int(out0 + out1)
        tot_cache[a] = tot
        return tot

    def scan_range(lo: int, hi: int) -> tuple[int, int] | None:
        if lo > hi:
            return None
        best_out = -1
        best_a = 0
        for a in range(lo, hi + 1):
            tot = total_out(a)
            if tot is None:
                continue
            if tot > best_out or (tot == best_out and a < best_a):
                best_out = tot
                best_a = a
        return None if best_out < 0 else (best_out, best_a)

    def is_valid(pool: PoolXY, a: int) -> bool:
        if a <= 0:
            return False
        try:
            exact_out_for_pool_exact_in(pool, a)
        except Exception:
            return False
        return True

    def min_valid_amount(pool: PoolXY) -> int | None:
        if not is_valid(pool, amount_in):
            return None
        lo = 1
        hi = amount_in
        while lo < hi:
            mid = (lo + hi) // 2
            if is_valid(pool, mid):
                hi = mid
            else:
                lo = mid + 1
        return int(lo)

    best_out = -1
    best_a = 0
    for a in (0, amount_in):
        tot = total_out(a)
        if tot is None:
            continue
        if tot > best_out or (tot == best_out and a < best_a):
            best_out = tot
            best_a = a

    min0 = min_valid_amount(pool0)
    min1 = min_valid_amount(pool1)
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

            best_both: tuple[int, int] | None = None
            for c in sorted(centers):
                r_lo = max(lo_both, c - window)
                r_hi = min(hi_both, c + window)
                cand = scan_range(r_lo, r_hi)
                if cand is None:
                    continue
                if best_both is None or cand[0] > best_both[0] or (cand[0] == best_both[0] and cand[1] < best_both[1]):
                    best_both = cand

            if best_both is not None:
                # Refine by expanding around the current best within the both-valid interval.
                refine_out, refine_a = best_both
                half = max(1, int(window))
                while True:
                    r_lo = max(lo_both, refine_a - half)
                    r_hi = min(hi_both, refine_a + half)
                    cand = scan_range(r_lo, r_hi)
                    if cand is not None:
                        refine_out2, refine_a2 = cand
                        if refine_out2 > refine_out or (refine_out2 == refine_out and refine_a2 < refine_a):
                            refine_out, refine_a = refine_out2, refine_a2
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

                # Canonicalize within a local plateau: walk left while output stays maximal.
                a0 = refine_a
                while a0 > lo_both:
                    prev = total_out(a0 - 1)
                    if prev is None or prev != refine_out:
                        break
                    a0 -= 1

                if force_dense_grid:
                    # Dense profiles pay a small extra pass to enforce global canonical tie-break:
                    # choose the smallest feasible `a` that attains `refine_out`.
                    for a_scan in range(lo_both, a0):
                        tot_scan = total_out(a_scan)
                        if tot_scan is not None and tot_scan == refine_out:
                            a0 = a_scan
                            break
                best_both = (refine_out, a0)

                if best_both[0] > best_out or (best_both[0] == best_out and best_both[1] < best_a):
                    best_out, best_a = best_both

    if best_out < 0:
        raise ValueError("no feasible split")
    return best_out, best_a
