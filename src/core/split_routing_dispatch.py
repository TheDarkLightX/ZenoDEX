"""
Split routing across *pool objects* (multi-curve via AMM dispatch).

This module extends `src/core/split_routing.py` (CPMM-specific) to support splitting across
arbitrary pool curve types by treating each pool as an exact-in oracle:

  out_i(a) = quote_exact_in(pool_i, a)

We then maximize `out_0(a) + out_1(D-a)` for total input `D`.

Notes:
- For CPMM pools we reuse the specialized, faster solver from `split_routing.py`.
- For non-CPMM pools we use a deterministic windowed search with bounded brute-force on small trades.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

from ..kernels.python.exact_out_many_pool_canonical_domain_v1 import (
    DEFAULT_EXACT_OUT_MANY_POOL_MAX_ENUMERATED_CANDIDATES,
)
from ..kernels.python.exact_out_many_pool_canonical_domain_v1 import (
    build_exact_out_many_pool_selected_domain as _kernel_build_exact_out_many_pool_selected_domain,
)
from ..kernels.python.exact_out_many_pool_repaired_prefilter_v1 import (
    select_many_pool_repaired_prefilter_candidates as _kernel_select_many_pool_repaired_prefilter_candidates,
)
from ..state.balances import Amount, AssetId
from ..state.pools import CURVE_TAG_CPMM, PoolState
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .split_routing import (
    PoolXY,
    best_split_two_pools_exact_in,
    exact_out_for_pool_exact_in,
    resolve_two_pool_split_search_params,
)
from .split_routing_types import (
    ExactOutCapacityGuard,
    ExactOutRouteCanonicalKey,
    SplitLegExactOutQuote,
    SplitLegQuote,
    SplitManyPoolsExactOutQuote,
    SplitManyPoolsQuote,
    SplitTwoPoolsQuote,
    exact_out_route_canonical_key_for_legs,
)
from .split_routing_types import (
    exact_out_route_canonical_key as exact_out_route_canonical_key,
)


def _reserves_for(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId) -> Optional[Tuple[int, int]]:
    if pool.status.value != "ACTIVE":
        return None
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    return None


def _quote_exact_in(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_in: Amount) -> int:
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    reserves = _reserves_for(pool, asset_in=asset_in, asset_out=asset_out)
    if reserves is None:
        raise ValueError("pool does not support this direction (or is inactive)")
    rin, rout = reserves
    out, _ = swap_exact_in_for_pool(pool, reserve_in=rin, reserve_out=rout, amount_in=int(amount_in))
    return int(out)


def _quote_exact_out(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_out: Amount) -> int:
    if amount_out <= 0:
        raise ValueError("amount_out must be positive")
    reserves = _reserves_for(pool, asset_in=asset_in, asset_out=asset_out)
    if reserves is None:
        raise ValueError("pool does not support this direction (or is inactive)")
    rin, rout = reserves
    amount_in, _ = swap_exact_out_for_pool(pool, reserve_in=rin, reserve_out=rout, amount_out=int(amount_out))
    return int(amount_in)


def _is_valid_exact_out(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_out: Amount) -> bool:
    if amount_out <= 0:
        return False
    try:
        _quote_exact_out(pool, asset_in=asset_in, asset_out=asset_out, amount_out=amount_out)
    except ValueError:
        return False
    return True


def _is_valid(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_in: Amount) -> bool:
    if amount_in <= 0:
        return False
    try:
        _quote_exact_in(pool, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in)
    except ValueError:
        return False
    return True


def _build_exact_out_capacity_guard(
    caps_by_pool: Sequence[Tuple[str, int]],
    *,
    amount_out_total: Amount,
    max_legs: int,
) -> ExactOutCapacityGuard:
    ranked_caps = sorted(
        ((str(pool_id), int(cap)) for pool_id, cap in caps_by_pool if int(cap) > 0),
        key=lambda item: (-int(item[1]), item[0]),
    )
    top_caps = tuple(ranked_caps[: min(int(max_legs), len(ranked_caps))])
    capacity_upper_bound = sum(int(cap) for _pool_id, cap in top_caps)
    return ExactOutCapacityGuard(
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        top_caps=top_caps,
        capacity_upper_bound=int(capacity_upper_bound),
    )


def exact_out_capacity_guard_for_pools(
    pools: Sequence[PoolState],
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out_total: Amount,
    max_legs: int,
) -> ExactOutCapacityGuard:
    if amount_out_total <= 0:
        raise ValueError("amount_out_total must be positive")
    if max_legs <= 0:
        raise ValueError("max_legs must be positive")
    caps_by_pool: list[tuple[str, int]] = []
    target_out = int(amount_out_total)
    for pool in pools:
        if pool.status.value != "ACTIVE":
            continue
        reserves = _reserves_for(pool, asset_in=asset_in, asset_out=asset_out)
        if reserves is None:
            continue
        _rin, rout = reserves
        cap = int(rout) - 1
        if cap <= 0:
            continue
        try:
            _quote_exact_out(
                pool,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_out=min(int(target_out), int(cap)),
            )
        except ValueError:
            continue
        caps_by_pool.append((pool.pool_id, int(cap)))
    return _build_exact_out_capacity_guard(
        caps_by_pool,
        amount_out_total=int(target_out),
        max_legs=int(max_legs),
    )


def _min_valid_amount(
    pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_in_total: Amount
) -> Optional[int]:
    if not _is_valid(pool, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in_total):
        return None
    lo = 1
    hi = int(amount_in_total)
    while lo < hi:
        mid = (lo + hi) // 2
        if _is_valid(pool, asset_in=asset_in, asset_out=asset_out, amount_in=int(mid)):
            hi = mid
        else:
            lo = mid + 1
    return int(lo)


def _brute_force_best_split(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
) -> Tuple[int, int]:
    if amount_in_total <= 0:
        raise ValueError("amount_in_total must be positive")
    best_out: int | None = None
    best_a = 0
    for a in range(0, int(amount_in_total) + 1):
        b = int(amount_in_total) - a
        try:
            out0 = _quote_exact_in(pool0, asset_in=asset_in, asset_out=asset_out, amount_in=a) if a > 0 else 0
            out1 = _quote_exact_in(pool1, asset_in=asset_in, asset_out=asset_out, amount_in=b) if b > 0 else 0
        except ValueError:
            continue
        total = int(out0 + out1)
        if best_out is None or total > best_out or (total == best_out and a < best_a):
            best_out = total
            best_a = a
    if best_out is None:
        raise ValueError("no feasible split")
    return int(best_out), int(best_a)


def _generic_best_split_two_pools_exact_in(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
    window: int,
    brute_force_max: int,
) -> Tuple[int, int]:
    if amount_in_total <= 0:
        raise ValueError("amount_in_total must be positive")
    if window < 0:
        raise ValueError("window must be non-negative")

    if int(amount_in_total) <= int(brute_force_max):
        return _brute_force_best_split(
            pool0,
            pool1,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in_total=amount_in_total,
        )

    def total_out(a: int) -> int | None:
        if not (0 <= a <= int(amount_in_total)):
            return None
        b = int(amount_in_total) - a
        try:
            out0 = _quote_exact_in(pool0, asset_in=asset_in, asset_out=asset_out, amount_in=a) if a > 0 else 0
            out1 = _quote_exact_in(pool1, asset_in=asset_in, asset_out=asset_out, amount_in=b) if b > 0 else 0
        except ValueError:
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

    best_out = -1
    best_a = 0
    for a in (0, int(amount_in_total)):
        tot = total_out(a)
        if tot is None:
            continue
        if tot > best_out or (tot == best_out and a < best_a):
            best_out = int(tot)
            best_a = int(a)

    min0 = _min_valid_amount(pool0, asset_in=asset_in, asset_out=asset_out, amount_in_total=amount_in_total)
    min1 = _min_valid_amount(pool1, asset_in=asset_in, asset_out=asset_out, amount_in_total=amount_in_total)
    if min0 is not None and min1 is not None:
        lo_both = int(min0)
        hi_both = int(amount_in_total) - int(min1)
        if lo_both <= hi_both:
            span = int(hi_both - lo_both)
            centers = {lo_both, hi_both, (lo_both + hi_both) // 2}
            if span > 8 * int(window):
                for i in range(1, 8):
                    centers.add(lo_both + (span * i) // 8)

            best_both: tuple[int, int] | None = None
            for c in sorted(centers):
                r_lo = max(lo_both, int(c) - int(window))
                r_hi = min(hi_both, int(c) + int(window))
                cand = scan_range(r_lo, r_hi)
                if cand is None:
                    continue
                if best_both is None or cand[0] > best_both[0] or (cand[0] == best_both[0] and cand[1] < best_both[1]):
                    best_both = cand

            if best_both is not None:
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
                    if refine_a in (r_lo, r_hi):
                        half *= 2
                        if half >= span:
                            half = span
                        continue
                    break

                # Canonicalize within a local plateau.
                a0 = int(refine_a)
                while a0 > lo_both:
                    prev = total_out(a0 - 1)
                    if prev is None or int(prev) != int(refine_out):
                        break
                    a0 -= 1

                if int(refine_out) > best_out or (int(refine_out) == best_out and int(a0) < best_a):
                    best_out, best_a = int(refine_out), int(a0)

    if best_out < 0:
        raise ValueError("no feasible split")
    return int(best_out), int(best_a)


def best_split_two_pools_exact_in_for_pools(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
    window: int = 96,
    search_profile: str = "adaptive_v6",
) -> SplitTwoPoolsQuote:
    """
    Compute the best exact-in split across two pools for the same asset pair direction.

    Determinism:
    - Pools are ordered by `pool_id` before split optimization.
    - Ties are broken by smaller `amount_in_0` (send less to the first pool).
    """
    if amount_in_total <= 0:
        raise ValueError("amount_in_total must be positive")

    # Canonicalize pool order.
    p0, p1 = (pool0, pool1) if pool0.pool_id <= pool1.pool_id else (pool1, pool0)

    # Fast path: CPMM uses the dedicated solver.
    if p0.curve_tag == CURVE_TAG_CPMM and p1.curve_tag == CURVE_TAG_CPMM:
        r0 = _reserves_for(p0, asset_in=asset_in, asset_out=asset_out)
        r1 = _reserves_for(p1, asset_in=asset_in, asset_out=asset_out)
        if r0 is None or r1 is None:
            raise ValueError("pools do not support this direction (or are inactive)")
        rin0, rout0 = r0
        rin1, rout1 = r1
        xy0 = PoolXY(x=int(rin0), y=int(rout0), fee_bps=int(p0.fee_bps))
        xy1 = PoolXY(x=int(rin1), y=int(rout1), fee_bps=int(p1.fee_bps))
        win2, prof2 = resolve_two_pool_split_search_params(
            xy0,
            xy1,
            int(amount_in_total),
            search_profile=str(search_profile),
            window=int(window),
        )
        best_out, best_a = best_split_two_pools_exact_in(
            xy0,
            xy1,
            int(amount_in_total),
            window=int(win2),
            search_profile=str(prof2),
        )
        out0 = exact_out_for_pool_exact_in(xy0, best_a) if best_a > 0 else 0
        out1 = exact_out_for_pool_exact_in(xy1, int(amount_in_total) - best_a) if best_a < int(amount_in_total) else 0
        return SplitTwoPoolsQuote(
            pool0_id=p0.pool_id,
            pool1_id=p1.pool_id,
            amount_in_total=int(amount_in_total),
            amount_out_total=int(best_out),
            amount_in_0=int(best_a),
            amount_out_0=int(out0),
            amount_in_1=int(amount_in_total) - int(best_a),
            amount_out_1=int(out1),
        )

    best_out, best_a = _generic_best_split_two_pools_exact_in(
        p0,
        p1,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in_total=amount_in_total,
        window=int(window),
        brute_force_max=2048,
    )
    b = int(amount_in_total) - int(best_a)
    out0 = _quote_exact_in(p0, asset_in=asset_in, asset_out=asset_out, amount_in=int(best_a)) if best_a > 0 else 0
    out1 = _quote_exact_in(p1, asset_in=asset_in, asset_out=asset_out, amount_in=int(b)) if b > 0 else 0
    if int(out0 + out1) != int(best_out):
        # Defensive: recompute total from per-leg quotes.
        best_out = int(out0 + out1)
    return SplitTwoPoolsQuote(
        pool0_id=p0.pool_id,
        pool1_id=p1.pool_id,
        amount_in_total=int(amount_in_total),
        amount_out_total=int(best_out),
        amount_in_0=int(best_a),
        amount_out_0=int(out0),
        amount_in_1=int(b),
        amount_out_1=int(out1),
    )


def best_split_two_pools_exact_out_for_pools(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out_total: Amount,
    window: int = 64,
    brute_force_max: int = 512,
) -> SplitTwoPoolsQuote:
    """
    Compute the best exact-out split across two pools for the same asset pair direction:
      minimize `amount_in_0 + amount_in_1` subject to `amount_out_0 + amount_out_1 = amount_out_total`.

    Determinism:
    - Pools are ordered by `pool_id` before split optimization.
    - Ties are broken by the full exact-out canonical key
      `route_key_out = (amount_in_total, leg_count, legs_lex)`.

    Performance:
    - Uses brute-force for `amount_out_total <= brute_force_max`.
    - Otherwise uses a deterministic windowed search around a continuous approximation.
    """
    if amount_out_total <= 0:
        raise ValueError("amount_out_total must be positive")
    if window < 0:
        raise ValueError("window must be non-negative")
    if brute_force_max < 0:
        raise ValueError("brute_force_max must be non-negative")

    # Canonicalize pool order.
    p0, p1 = (pool0, pool1) if pool0.pool_id <= pool1.pool_id else (pool1, pool0)

    r0 = _reserves_for(p0, asset_in=asset_in, asset_out=asset_out)
    r1 = _reserves_for(p1, asset_in=asset_in, asset_out=asset_out)
    if r0 is None or r1 is None:
        raise ValueError("pools do not support this direction (or are inactive)")
    rin0, rout0 = r0
    rin1, rout1 = r1

    Q = int(amount_out_total)
    # Upper bounds (conservative) for per-leg exact-out under CPMM-like semantics: amount_out < reserve_out.
    max0 = max(0, int(rout0) - 1)
    max1 = max(0, int(rout1) - 1)
    lo = max(0, int(Q) - int(max1))
    hi = min(int(Q), int(max0))
    if lo > hi:
        raise ValueError("no feasible split for desired amount_out_total")
    span = int(hi - lo)

    def total_in(q0: int) -> int | None:
        if q0 < lo or q0 > hi:
            return None
        q1 = int(Q) - int(q0)
        try:
            in0 = _quote_exact_out(p0, asset_in=asset_in, asset_out=asset_out, amount_out=int(q0)) if q0 > 0 else 0
            in1 = _quote_exact_out(p1, asset_in=asset_in, asset_out=asset_out, amount_out=int(q1)) if q1 > 0 else 0
        except ValueError:
            return None
        return int(in0 + in1)

    def route_key_for_split(q0: int, total_input: int) -> ExactOutRouteCanonicalKey:
        q1 = int(Q) - int(q0)
        legs: list[tuple[str, int]] = []
        if int(q0) > 0:
            legs.append((p0.pool_id, int(q0)))
        if int(q1) > 0:
            legs.append((p1.pool_id, int(q1)))
        return exact_out_route_canonical_key_for_legs(
            amount_in_total=int(total_input),
            legs=tuple(legs),
        )

    def scan_range(a: int, b: int) -> tuple[int, int] | None:
        if a > b:
            return None
        best_in: int | None = None
        best_key: ExactOutRouteCanonicalKey | None = None
        best_q0 = int(a)
        for q0 in range(int(a), int(b) + 1):
            tot = total_in(int(q0))
            if tot is None:
                continue
            cand_key = route_key_for_split(int(q0), int(tot))
            if best_in is None or best_key is None:
                best_in = int(tot)
                best_key = cand_key
                best_q0 = int(q0)
                continue
            if int(tot) < int(best_in) or (int(tot) == int(best_in) and cand_key < best_key):
                best_in = int(tot)
                best_key = cand_key
                best_q0 = int(q0)
        return None if best_in is None else (int(best_in), int(best_q0))

    def _windowed_search() -> tuple[int, int]:
        # Deterministic integer seed using continuous marginal input approximation (no floats).
        #
        # Approximate exact-out input:
        #   in(q) ~ (x*q/(y-q)) / α,  α = (BPS-fee)/BPS
        # Then:
        #   in'(q) ∝ (x*y) / (α_num*(y-q)^2), α_num = BPS - fee_bps
        # A continuous minimizer satisfies:
        #   in0'(q0) == in1'(Q-q0).
        BPS = 10_000
        alpha0 = int(BPS) - int(p0.fee_bps)
        alpha1 = int(BPS) - int(p1.fee_bps)

        def deriv_ge(q0: int) -> bool:
            q0 = int(q0)
            q1 = int(Q) - int(q0)
            y0_minus = int(rout0) - int(q0)
            y1_minus = int(rout1) - int(q1)
            if y0_minus <= 0 or y1_minus <= 0:
                # Outside feasible region; force it away from the boundary.
                return True
            if alpha0 <= 0 or alpha1 <= 0:
                # Degenerate fee regime; fall back to midpoint seed behavior.
                return True
            # Compare:
            #   rin0*rout0/(alpha0*(y0-q0)^2) >= rin1*rout1/(alpha1*(y1-q1)^2)
            # <=> rin0*rout0*alpha1*(y1-q1)^2 >= rin1*rout1*alpha0*(y0-q0)^2
            left = int(rin0) * int(rout0) * int(alpha1) * int(y1_minus) * int(y1_minus)
            right = int(rin1) * int(rout1) * int(alpha0) * int(y0_minus) * int(y0_minus)
            return left >= right

        def seed_q0() -> int:
            a = int(lo)
            b = int(hi)
            if a > b:
                return a
            # If already derivative>=0 at the left edge, keep left bias.
            if deriv_ge(a):
                return a
            # If still derivative<0 at the right edge, optimum is at the boundary.
            if not deriv_ge(b):
                return b
            while a < b:
                mid = (a + b) // 2
                if deriv_ge(mid):
                    b = mid
                else:
                    a = mid + 1
            return int(a)

        q0_star = seed_q0()

        centers = {int(lo), int(hi), int(q0_star), int((int(lo) + int(hi)) // 2)}
        if int(span) > 8 * int(window):
            # Reduce the number of additional grid centers to keep quote costs bounded, while still
            # covering near-endpoint pockets where rounding can create small global improvements.
            for i in (1, 3, 5, 7):
                centers.add(int(lo) + (int(span) * int(i)) // 8)

        best_in = 0
        best_key: ExactOutRouteCanonicalKey | None = None
        best_q0 = int(lo)
        best_found = False
        for c in sorted(centers):
            r_lo = max(int(lo), int(c) - int(window))
            r_hi = min(int(hi), int(c) + int(window))
            cand = scan_range(int(r_lo), int(r_hi))
            if cand is None:
                continue
            cand_in, cand_q0 = cand
            cand_key = route_key_for_split(int(cand_q0), int(cand_in))
            if (not best_found) or best_key is None or cand_in < best_in or (cand_in == best_in and cand_key < best_key):
                best_in, best_q0 = int(cand_in), int(cand_q0)
                best_key = cand_key
                best_found = True

        if not best_found:
            raise ValueError("no feasible split")

        # Canonicalization sweep (bounded): when minimizers are disconnected, local plateau walking is insufficient.
        # Scan a left-biased band near the current best and pick the leftmost minimizer found.
        canon_left = max(128, 4 * int(window))
        sweep_lo = max(int(lo), int(best_q0) - int(canon_left))
        sweep = scan_range(int(sweep_lo), int(best_q0))
        if sweep is not None:
            sweep_in, sweep_q0 = sweep
            sweep_key = route_key_for_split(int(sweep_q0), int(sweep_in))
            if best_key is None or sweep_in < best_in or (sweep_in == best_in and sweep_key < best_key):
                best_in, best_q0 = int(sweep_in), int(sweep_q0)
                best_key = sweep_key
        return int(best_in), int(best_q0)

    # Small exact-out amounts: brute force for exact optimality + canonical tie-break.
    if int(Q) <= int(brute_force_max) or span <= int(brute_force_max):
        brute = scan_range(int(lo), int(hi))
        if brute is None:
            raise ValueError("no feasible split")
        best_in, best_q0 = brute
    else:
        best_in, best_q0 = _windowed_search()

    q1 = int(Q) - int(best_q0)
    in0 = _quote_exact_out(p0, asset_in=asset_in, asset_out=asset_out, amount_out=int(best_q0)) if best_q0 > 0 else 0
    in1 = _quote_exact_out(p1, asset_in=asset_in, asset_out=asset_out, amount_out=int(q1)) if q1 > 0 else 0
    return SplitTwoPoolsQuote(
        pool0_id=p0.pool_id,
        pool1_id=p1.pool_id,
        amount_in_total=int(in0 + in1),
        amount_out_total=int(Q),
        amount_in_0=int(in0),
        amount_out_0=int(best_q0),
        amount_in_1=int(in1),
        amount_out_1=int(q1),
    )


_ExactInStepCandidate = Tuple[str, int, int, int]  # pool_id, delta, increment, current_amount


@dataclass
class _ExactInManyPoolContext:
    asset_in: AssetId
    asset_out: AssetId
    pools_by_id: Dict[str, PoolState]
    min_valid: Dict[str, int]
    quote_cache: Dict[Tuple[str, int], int]

    def quote(self, pool_id: str, amount_in: int) -> Optional[int]:
        if amount_in < 0:
            return None
        if amount_in == 0:
            return 0
        min_amount = self.min_valid.get(pool_id)
        if min_amount is None or int(amount_in) < int(min_amount):
            return None
        key = (pool_id, int(amount_in))
        if key in self.quote_cache:
            return self.quote_cache[key]
        out = _quote_exact_in(
            self.pools_by_id[pool_id],
            asset_in=self.asset_in,
            asset_out=self.asset_out,
            amount_in=int(amount_in),
        )
        self.quote_cache[key] = int(out)
        return int(out)


def _validate_many_pool_exact_in_args(
    *,
    amount_in_total: Amount,
    max_legs: int,
    max_candidates: int,
    max_iters: int,
) -> None:
    if amount_in_total <= 0:
        raise ValueError("amount_in_total must be positive")
    if max_legs <= 0:
        raise ValueError("max_legs must be positive")
    if max_candidates <= 0:
        raise ValueError("max_candidates must be positive")
    if max_iters <= 0:
        raise ValueError("max_iters must be positive")


def _feasible_exact_in_pools(
    pools: Sequence[PoolState],
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
) -> List[PoolState]:
    feasible: List[PoolState] = []
    for pool in pools:
        if pool.status.value != "ACTIVE":
            continue
        if _reserves_for(pool, asset_in=asset_in, asset_out=asset_out) is None:
            continue
        if not _is_valid(pool, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in_total):
            continue
        feasible.append(pool)
    return feasible


def _rank_exact_in_candidate_pools(
    feasible: Sequence[PoolState],
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
    max_candidates: int,
) -> List[PoolState]:
    ranked: List[Tuple[int, PoolState]] = []
    for pool in feasible:
        try:
            out_full = _quote_exact_in(pool, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in_total)
        except ValueError:
            continue
        ranked.append((int(out_full), pool))
    ranked.sort(key=lambda item: (-int(item[0]), item[1].pool_id))
    candidates = [pool for _out, pool in ranked[: min(int(max_candidates), len(ranked))]]
    candidates.sort(key=lambda pool: pool.pool_id)
    return candidates


def _min_valid_exact_in_by_pool(
    candidates: Sequence[PoolState],
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
) -> Dict[str, int]:
    min_valid: Dict[str, int] = {}
    for pool in candidates:
        amount = _min_valid_amount(pool, asset_in=asset_in, asset_out=asset_out, amount_in_total=amount_in_total)
        if amount is not None:
            min_valid[pool.pool_id] = int(amount)
    return min_valid


def _seed_exact_in_allocation(
    *,
    context: _ExactInManyPoolContext,
    amount_in_total: Amount,
    max_legs: int,
) -> Tuple[Dict[str, int], set[str], int]:
    alloc: Dict[str, int] = {pool_id: 0 for pool_id in context.pools_by_id.keys()}
    used: set[str] = set()
    remaining = int(amount_in_total)
    seed_order = sorted(
        context.pools_by_id.keys(),
        key=lambda pool_id: (-int(context.quote(pool_id, int(amount_in_total)) or 0), pool_id),
    )

    for pool_id in seed_order:
        if remaining <= 0:
            break
        if len(used) >= int(max_legs):
            break
        min_amount = int(context.min_valid[pool_id])
        if min_amount <= 0 or min_amount > remaining:
            continue
        alloc[pool_id] = min_amount
        remaining -= min_amount
        used.add(pool_id)

    if not used:
        pool_id = seed_order[0]
        min_amount = int(context.min_valid[pool_id])
        increment = min_amount if min_amount <= remaining else remaining
        if increment <= 0:
            raise ValueError("no feasible allocation")
        alloc[pool_id] = increment
        remaining -= increment
        used.add(pool_id)

    return alloc, used, int(remaining)


def _candidate_exact_in_increment(
    pool_id: str,
    *,
    context: _ExactInManyPoolContext,
    alloc: Dict[str, int],
    used: set[str],
    remaining: int,
    base_increment: int,
    max_legs: int,
) -> Optional[_ExactInStepCandidate]:
    current = int(alloc.get(pool_id, 0))
    if current == 0 and pool_id not in used and len(used) >= int(max_legs):
        return None

    increment = int(base_increment)
    if current == 0:
        min_amount = int(context.min_valid[pool_id])
        if min_amount > increment:
            increment = min_amount
    if increment <= 0 or increment > int(remaining):
        return None

    out_before = context.quote(pool_id, current) or 0
    out_after = context.quote(pool_id, current + increment)
    if out_after is None:
        return None
    delta = int(out_after - out_before)
    if delta < 0:
        return None
    return (pool_id, int(delta), int(increment), int(current))


def _is_better_exact_in_increment(
    candidate: _ExactInStepCandidate,
    best: Optional[_ExactInStepCandidate],
) -> bool:
    if best is None:
        return True

    pool_id, delta, increment, current = candidate
    best_pool_id, best_delta, best_increment, best_current = best
    lhs = int(delta) * int(best_increment)
    rhs = int(best_delta) * int(increment)
    if lhs != rhs:
        return lhs > rhs
    if delta != best_delta:
        return delta > best_delta
    if current != best_current:
        return current < best_current
    return pool_id < best_pool_id


def _choose_exact_in_increment(
    *,
    context: _ExactInManyPoolContext,
    alloc: Dict[str, int],
    used: set[str],
    remaining: int,
    base_increment: int,
    max_legs: int,
) -> _ExactInStepCandidate:
    best: Optional[_ExactInStepCandidate] = None
    for pool_id in context.pools_by_id.keys():
        candidate = _candidate_exact_in_increment(
            pool_id,
            context=context,
            alloc=alloc,
            used=used,
            remaining=int(remaining),
            base_increment=int(base_increment),
            max_legs=int(max_legs),
        )
        if candidate is not None and _is_better_exact_in_increment(candidate, best):
            best = candidate
    if best is None:
        raise ValueError("no feasible allocation step (unexpected)")
    return best


def _greedy_allocate_exact_in_many_pools(
    step: int,
    *,
    context: _ExactInManyPoolContext,
    amount_in_total: Amount,
    max_legs: int,
) -> Dict[str, int]:
    if step <= 0:
        raise ValueError("step must be positive")

    alloc, used, remaining = _seed_exact_in_allocation(
        context=context,
        amount_in_total=amount_in_total,
        max_legs=int(max_legs),
    )

    while remaining > 0:
        base_increment = min(int(step), int(remaining))
        pool_id, _delta, increment, _current = _choose_exact_in_increment(
            context=context,
            alloc=alloc,
            used=used,
            remaining=int(remaining),
            base_increment=int(base_increment),
            max_legs=int(max_legs),
        )
        was_zero = alloc[pool_id] == 0
        alloc[pool_id] = int(alloc[pool_id] + increment)
        remaining -= int(increment)
        if was_zero:
            used.add(pool_id)

    return alloc


def _score_exact_in_allocation(alloc: Dict[str, int], *, context: _ExactInManyPoolContext) -> int:
    total_out = 0
    for pool_id, amount in alloc.items():
        if amount <= 0:
            continue
        out_amount = context.quote(pool_id, int(amount))
        if out_amount is None:
            continue
        total_out += int(out_amount)
    return int(total_out)


def _positive_exact_in_legs(alloc: Dict[str, int]) -> List[Tuple[str, int]]:
    return sorted([(pool_id, int(amount)) for pool_id, amount in alloc.items() if int(amount) > 0], key=lambda item: item[0])


def _is_better_exact_in_allocation(
    *,
    total_out: int,
    alloc: Dict[str, int],
    best_out: int,
    best_alloc: Optional[Dict[str, int]],
) -> bool:
    if total_out > best_out:
        return True
    if total_out != best_out or best_alloc is None:
        return False
    current_legs = _positive_exact_in_legs(alloc)
    best_legs = _positive_exact_in_legs(best_alloc)
    return len(current_legs) < len(best_legs) or (len(current_legs) == len(best_legs) and current_legs < best_legs)


def _build_exact_in_many_pool_quote(
    *,
    best_alloc: Dict[str, int],
    amount_in_total: Amount,
    context: _ExactInManyPoolContext,
) -> SplitManyPoolsQuote:
    legs: List[SplitLegQuote] = []
    out_total = 0
    in_total = 0
    for pool_id in sorted(best_alloc.keys()):
        amount = int(best_alloc[pool_id])
        if amount <= 0:
            continue
        out_amount = context.quote(pool_id, amount)
        if out_amount is None:
            continue
        legs.append(SplitLegQuote(pool_id=pool_id, amount_in=int(amount), amount_out=int(out_amount)))
        in_total += int(amount)
        out_total += int(out_amount)

    if in_total != int(amount_in_total):
        raise ValueError("split allocation did not consume full input (unexpected)")

    return SplitManyPoolsQuote(amount_in_total=int(amount_in_total), amount_out_total=int(out_total), legs=tuple(legs))


def _build_exact_in_many_pool_context(
    pools: Sequence[PoolState],
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
    max_candidates: int,
) -> _ExactInManyPoolContext:
    feasible = _feasible_exact_in_pools(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in_total=amount_in_total,
    )
    if not feasible:
        raise ValueError("no feasible pools for split")

    candidates = _rank_exact_in_candidate_pools(
        feasible,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in_total=amount_in_total,
        max_candidates=int(max_candidates),
    )
    if not candidates:
        raise ValueError("no feasible pools for split")

    min_valid = _min_valid_exact_in_by_pool(
        candidates,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in_total=amount_in_total,
    )
    if not min_valid:
        raise ValueError("no feasible pools for split")

    return _ExactInManyPoolContext(
        asset_in=asset_in,
        asset_out=asset_out,
        pools_by_id={pool.pool_id: pool for pool in candidates if pool.pool_id in min_valid},
        min_valid=min_valid,
        quote_cache={},
    )


def _search_exact_in_many_pool_best_allocation(
    *,
    context: _ExactInManyPoolContext,
    amount_in_total: Amount,
    max_legs: int,
    max_iters: int,
) -> Dict[str, int]:
    amount_total = int(amount_in_total)
    step_min = max(1, amount_total // int(max_iters))
    step = max(step_min, max(1, amount_total // 256))
    best_alloc: Optional[Dict[str, int]] = None
    best_out = -1

    while True:
        alloc = _greedy_allocate_exact_in_many_pools(
            int(step),
            context=context,
            amount_in_total=amount_in_total,
            max_legs=int(max_legs),
        )
        total_out = _score_exact_in_allocation(alloc, context=context)
        if _is_better_exact_in_allocation(
            total_out=int(total_out),
            alloc=alloc,
            best_out=int(best_out),
            best_alloc=best_alloc,
        ):
            best_out = int(total_out)
            best_alloc = alloc

        if step <= step_min:
            break
        step = max(step_min, step // 2)

    if best_alloc is None:
        raise RuntimeError("split allocation search produced no candidate")
    return best_alloc


def best_split_many_pools_exact_in_for_pools(
    pools: Sequence[PoolState],
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
    max_legs: int = 4,
    max_candidates: int = 16,
    max_iters: int = 4096,
) -> SplitManyPoolsQuote:
    """
    Deterministic N-way split router for *parallel* pools on the same asset pair direction.

    This is an execution improvement over "pick best single pool" and "split across two pools" in
    fragmented liquidity regimes.

    Approach:
    - Treat each pool as an exact-in oracle `f_i(a)`.
    - Solve `max Σ f_i(a_i)` s.t. `Σ a_i = D`, `a_i ∈ ℕ`.
    - Use a bounded multi-stage greedy allocator (marginal-output-per-input), with deterministic tie-breaks.
    - Limit to at most `max_legs` non-zero legs and `max_candidates` candidate pools.
    """
    _validate_many_pool_exact_in_args(
        amount_in_total=amount_in_total,
        max_legs=int(max_legs),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
    )

    context = _build_exact_in_many_pool_context(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in_total=amount_in_total,
        max_candidates=int(max_candidates),
    )
    best_alloc = _search_exact_in_many_pool_best_allocation(
        context=context,
        amount_in_total=amount_in_total,
        max_legs=int(max_legs),
        max_iters=int(max_iters),
    )
    return _build_exact_in_many_pool_quote(best_alloc=best_alloc, amount_in_total=amount_in_total, context=context)


def best_split_many_pools_exact_out_for_pools(
    pools: Sequence[PoolState],
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out_total: Amount,
    max_legs: int = 3,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
) -> SplitManyPoolsExactOutQuote:
    """
    Deterministic N-way exact-out split router for *parallel* pools on the same asset pair direction.

    Problem:
      minimize Σ in_i(q_i) subject to Σ q_i = Q, q_i ∈ ℕ, 0 <= q_i < reserve_out_i.

    Approach (bounded canonical domain):
    - On audited feasible-pool domains, choose the pool subset with the repaired
      bounded cover-search selector.
    - Otherwise fall back to the older deterministic heuristic prefilter.
    - Enumerate the bounded exact-out candidate domain over the selected pool subset.
    - Return the canonical winner under
      `route_key_out = (amount_in_total, leg_count, legs_lex)`.

    Notes:
    - This is a UX improvement for fragmented liquidity when a single pool (or 2-pool split) is insufficient.
    - The emitted winner over the selected domain is exact.
    - The repaired pool prefilter is used only when the feasible-pool set stays within
      the explicit audited bound `max_full_domain_pools`; outside that bound this path
      preserves the older heuristic prefilter.
    - If the selected domain exceeds the bounded enumeration budget, this path fails closed.
    """
    if amount_out_total <= 0:
        raise ValueError("amount_out_total must be positive")
    if max_legs <= 0:
        raise ValueError("max_legs must be positive")
    if max_candidates <= 0:
        raise ValueError("max_candidates must be positive")
    if max_iters <= 0:
        raise ValueError("max_iters must be positive")
    if window < 0:
        raise ValueError("window must be non-negative")
    if brute_force_max < 0:
        raise ValueError("brute_force_max must be non-negative")
    if max_full_domain_pools <= 0:
        raise ValueError("max_full_domain_pools must be positive")

    Q = int(amount_out_total)

    # Filter to feasible direct pools and compute per-pool output caps.
    feasible: list[tuple[PoolState, int, int]] = []
    for p in pools:
        if p.status.value != "ACTIVE":
            continue
        reserves = _reserves_for(p, asset_in=asset_in, asset_out=asset_out)
        if reserves is None:
            continue
        _rin, rout = reserves
        cap = int(rout) - 1
        if cap <= 0:
            continue
        out_i = min(int(Q), int(cap))
        try:
            in_i = _quote_exact_out(p, asset_in=asset_in, asset_out=asset_out, amount_out=int(out_i))
        except ValueError:
            continue
        feasible.append((p, int(cap), int(in_i)))

    if not feasible:
        raise ValueError("no feasible pools for exact-out split")

    capacity_guard = _build_exact_out_capacity_guard(
        tuple((pool.pool_id, int(cap)) for pool, cap, _in_i in feasible),
        amount_out_total=int(Q),
        max_legs=int(max_legs),
    )
    if not capacity_guard.feasible:
        raise ValueError(
            "no feasible split under max_legs constraint: "
            f"requested={Q} capacity_upper_bound={capacity_guard.capacity_upper_bound} max_legs={max_legs}"
        )

    feasible_pools = tuple(pool for pool, _cap, _in_i in feasible)
    candidates: list[PoolState] = []
    if len(feasible_pools) <= int(max_full_domain_pools):
        try:
            candidates = list(
                _kernel_select_many_pool_repaired_prefilter_candidates(
                    feasible_pools,
                    asset_in=str(asset_in),
                    asset_out=str(asset_out),
                    amount_out_total=int(Q),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidates),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=max(
                        int(DEFAULT_EXACT_OUT_MANY_POOL_MAX_ENUMERATED_CANDIDATES),
                        int(max_iters) * max(1, int(max_legs)),
                    ),
                )
            )
        except ValueError:
            candidates = []

    if not candidates:
        # Rank pools by estimated unit cost (in_i / out_i), then by input, then pool_id.
        ranked: list[tuple[int, int, PoolState, int]] = []
        for p, cap, in_i in feasible:
            out_i = min(int(Q), int(cap))
            # scaled unit cost: floor(in_i * 1e6 / out_i)
            scaled = (int(in_i) * 1_000_000) // max(1, int(out_i))
            ranked.append((int(scaled), int(in_i), p, int(cap)))
        ranked.sort(key=lambda t: (t[0], t[1], t[2].pool_id))

        # Select candidates until (a) we hit max_candidates or (b) the top max_legs capacities cover Q.
        caps: dict[str, int] = {}
        for _scaled, _in_i, p, cap in ranked:
            if p.pool_id in caps:
                continue
            candidates.append(p)
            caps[p.pool_id] = int(cap)
            if len(candidates) >= int(max_candidates):
                break
            top_caps = sorted(caps.values(), reverse=True)
            if sum(top_caps[: min(int(max_legs), len(top_caps))]) >= int(Q) and len(candidates) >= min(int(max_legs), len(feasible)):
                # Enough capacity to satisfy Q with <= max_legs pools.
                break

    if not candidates:
        raise ValueError("no feasible candidates for exact-out split")

    # Canonicalize candidate pool order for deterministic tie-breaks.
    candidates.sort(key=lambda p: p.pool_id)
    max_enumerated_candidates = max(
        int(DEFAULT_EXACT_OUT_MANY_POOL_MAX_ENUMERATED_CANDIDATES),
        int(max_iters) * max(1, int(max_legs)),
    )
    selected_domain = _kernel_build_exact_out_many_pool_selected_domain(
        tuple(candidates),
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(Q),
        max_legs=int(max_legs),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )

    return SplitManyPoolsExactOutQuote(
        amount_out_total=int(selected_domain.canonical_quote.amount_out_total),
        amount_in_total=int(selected_domain.canonical_quote.amount_in_total),
        legs=tuple(
            SplitLegExactOutQuote(
                pool_id=leg.pool_id,
                amount_out=int(leg.amount_out),
                amount_in=int(leg.amount_in),
            )
            for leg in selected_domain.canonical_quote.legs
        ),
    )
