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

import math
from dataclasses import dataclass
from typing import Tuple

from ..kernels.python.cpmm_swap_v8 import compute_fee_total as _fee_total_v8


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


def _alpha_approx(pool: PoolXY) -> float:
    # Ignore ceil effects; approximate net = gross * (1 - fee_bps/10_000).
    return max(0.0, 1.0 - float(pool.fee_bps) / 10_000.0)


def _continuous_opt_split(pool0: PoolXY, pool1: PoolXY, amount_in: int) -> float:
    """
    Continuous optimal split for fee-as-multiplicative (approx), derived by equalizing marginal output:
      f'(a) = y*alpha*x/(x+alpha*a)^2
    Solve f0'(a) = f1'(D-a).
    """
    D = float(amount_in)
    a0 = _alpha_approx(pool0)
    a1 = _alpha_approx(pool1)
    if a0 <= 0 or a1 <= 0:
        return 0.0
    s0 = math.sqrt(max(0.0, float(pool0.y) * a0 * float(pool0.x)))
    s1 = math.sqrt(max(0.0, float(pool1.y) * a1 * float(pool1.x)))
    if s0 == 0 or s1 == 0:
        return 0.0
    k = s0 / s1
    denom = a0 + k * a1
    if denom == 0:
        return 0.0
    num = k * (float(pool1.x) + a1 * D) - float(pool0.x)
    a = num / denom
    if a < 0:
        return 0.0
    if a > D:
        return D
    return a


def best_split_two_pools_exact_in(pool0: PoolXY, pool1: PoolXY, amount_in: int, *, window: int = 64) -> Tuple[int, int]:
    """
    Fast deterministic split optimizer:
    - For small trades, use brute-force (exact + canonical).
    - For larger trades, use a multi-center window search seeded by a continuous approximation,
      plus endpoints and a refinement pass.
    - Choose best total output; tie-break by smallest a.

    This is intended to be iteratively improved with counterexample mining.
    """
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if window < 0:
        raise ValueError("window must be non-negative")

    brute_force_max = 4096
    if amount_in <= brute_force_max:
        return brute_force_best_split_two_pools_exact_in(pool0, pool1, amount_in)

    def total_out(a: int) -> int | None:
        if not (0 <= a <= amount_in):
            return None
        b = amount_in - a
        try:
            out0 = exact_out_for_pool_exact_in(pool0, a) if a > 0 else 0
            out1 = exact_out_for_pool_exact_in(pool1, b) if b > 0 else 0
        except Exception:
            return None
        return int(out0 + out1)

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
            a_star = int(_continuous_opt_split(pool0, pool1, amount_in))
            a_star = max(lo_both, min(hi_both, a_star))

            span = hi_both - lo_both
            centers = {lo_both, hi_both, (lo_both + hi_both) // 2, a_star}
            if span > 8 * window:
                # Add a small deterministic grid for coverage on wide intervals.
                for i in range(1, 8):
                    centers.add(lo_both + (span * i) // 8)

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
                    if refine_a in (r_lo, r_hi):
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
                best_both = (refine_out, a0)

                if best_both[0] > best_out or (best_both[0] == best_out and best_both[1] < best_a):
                    best_out, best_a = best_both

    if best_out < 0:
        raise ValueError("no feasible split")
    return best_out, best_a
