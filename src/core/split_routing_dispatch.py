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


@dataclass(frozen=True)
class SplitTwoPoolsQuote:
    pool0_id: str
    pool1_id: str
    amount_in_total: Amount
    amount_out_total: Amount
    amount_in_0: Amount
    amount_out_0: Amount
    amount_in_1: Amount
    amount_out_1: Amount


@dataclass(frozen=True)
class SplitLegQuote:
    pool_id: str
    amount_in: Amount
    amount_out: Amount

    def __post_init__(self) -> None:
        if not self.pool_id:
            raise ValueError("pool_id must be non-empty")
        if int(self.amount_in) <= 0:
            raise ValueError("amount_in must be positive")
        if int(self.amount_out) <= 0:
            raise ValueError("amount_out must be positive")


@dataclass(frozen=True)
class SplitManyPoolsQuote:
    amount_in_total: Amount
    amount_out_total: Amount
    legs: Tuple[SplitLegQuote, ...]

    def __post_init__(self) -> None:
        if int(self.amount_in_total) <= 0:
            raise ValueError("amount_in_total must be positive")
        if int(self.amount_out_total) <= 0:
            raise ValueError("amount_out_total must be positive")
        if not self.legs:
            raise ValueError("split quote must contain at least one leg")
        seen: set[str] = set()
        total_in = 0
        total_out = 0
        for leg in self.legs:
            if leg.pool_id in seen:
                raise ValueError("split quote must not repeat pool_id")
            seen.add(leg.pool_id)
            total_in += int(leg.amount_in)
            total_out += int(leg.amount_out)
        if total_in != int(self.amount_in_total):
            raise ValueError("amount_in_total must equal sum of leg inputs")
        if total_out != int(self.amount_out_total):
            raise ValueError("amount_out_total must equal sum of leg outputs")


@dataclass(frozen=True)
class SplitLegExactOutQuote:
    pool_id: str
    amount_out: Amount
    amount_in: Amount

    def __post_init__(self) -> None:
        if not self.pool_id:
            raise ValueError("pool_id must be non-empty")
        if int(self.amount_out) <= 0:
            raise ValueError("amount_out must be positive")
        if int(self.amount_in) <= 0:
            raise ValueError("amount_in must be positive")


@dataclass(frozen=True)
class SplitManyPoolsExactOutQuote:
    amount_out_total: Amount
    amount_in_total: Amount
    legs: Tuple[SplitLegExactOutQuote, ...]

    def __post_init__(self) -> None:
        if int(self.amount_out_total) <= 0:
            raise ValueError("amount_out_total must be positive")
        if int(self.amount_in_total) <= 0:
            raise ValueError("amount_in_total must be positive")
        if not self.legs:
            raise ValueError("split quote must contain at least one leg")
        seen: set[str] = set()
        total_out = 0
        total_in = 0
        for leg in self.legs:
            if leg.pool_id in seen:
                raise ValueError("split quote must not repeat pool_id")
            seen.add(leg.pool_id)
            total_out += int(leg.amount_out)
            total_in += int(leg.amount_in)
        if total_out != int(self.amount_out_total):
            raise ValueError("amount_out_total must equal sum of leg outputs")
        if total_in != int(self.amount_in_total):
            raise ValueError("amount_in_total must equal sum of leg inputs")


@dataclass(frozen=True)
class ExactOutCapacityGuard:
    amount_out_total: Amount
    max_legs: int
    top_caps: Tuple[Tuple[str, Amount], ...]
    capacity_upper_bound: Amount

    def __post_init__(self) -> None:
        if int(self.amount_out_total) <= 0:
            raise ValueError("amount_out_total must be positive")
        if int(self.max_legs) <= 0:
            raise ValueError("max_legs must be positive")
        if len(self.top_caps) > int(self.max_legs):
            raise ValueError("top_caps must not exceed max_legs")
        seen: set[str] = set()
        total = 0
        for pool_id, cap in self.top_caps:
            if not pool_id:
                raise ValueError("top_caps pool_id must be non-empty")
            if pool_id in seen:
                raise ValueError("top_caps must not repeat pool_id")
            if int(cap) <= 0:
                raise ValueError("top_caps capacities must be positive")
            seen.add(pool_id)
            total += int(cap)
        if total != int(self.capacity_upper_bound):
            raise ValueError("capacity_upper_bound must equal sum of top_caps")

    @property
    def feasible(self) -> bool:
        return int(self.capacity_upper_bound) >= int(self.amount_out_total)


@dataclass(frozen=True, order=True)
class ExactOutRouteCanonicalKey:
    amount_in_total: Amount
    leg_count: int
    legs_lex: Tuple[Tuple[str, Amount], ...]

    def __post_init__(self) -> None:
        if int(self.amount_in_total) <= 0:
            raise ValueError("amount_in_total must be positive")
        if int(self.leg_count) <= 0:
            raise ValueError("leg_count must be positive")
        if len(self.legs_lex) != int(self.leg_count):
            raise ValueError("leg_count must equal len(legs_lex)")
        if tuple(sorted(self.legs_lex, key=lambda item: item[0])) != self.legs_lex:
            raise ValueError("legs_lex must be sorted by pool_id")
        seen: set[str] = set()
        for pool_id, amount_out in self.legs_lex:
            if not pool_id:
                raise ValueError("legs_lex pool_id must be non-empty")
            if pool_id in seen:
                raise ValueError("legs_lex must not repeat pool_id")
            if int(amount_out) <= 0:
                raise ValueError("legs_lex amounts must be positive")
            seen.add(pool_id)



def exact_out_route_canonical_key_for_legs(
    *,
    amount_in_total: Amount,
    legs: Sequence[Tuple[str, Amount]],
) -> ExactOutRouteCanonicalKey:
    legs_lex = tuple(sorted(((str(pool_id), int(amount_out)) for pool_id, amount_out in legs), key=lambda item: item[0]))
    return ExactOutRouteCanonicalKey(
        amount_in_total=int(amount_in_total),
        leg_count=len(legs_lex),
        legs_lex=legs_lex,
    )



def exact_out_route_canonical_key(quote: SplitManyPoolsExactOutQuote) -> ExactOutRouteCanonicalKey:
    return exact_out_route_canonical_key_for_legs(
        amount_in_total=int(quote.amount_in_total),
        legs=tuple((leg.pool_id, int(leg.amount_out)) for leg in quote.legs),
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
    except Exception:
        return False
    return True


def _is_valid(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_in: Amount) -> bool:
    if amount_in <= 0:
        return False
    try:
        _quote_exact_in(pool, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in)
    except Exception:
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
        except Exception:
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
        except Exception:
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
        except Exception:
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
    if amount_in_total <= 0:
        raise ValueError("amount_in_total must be positive")
    if max_legs <= 0:
        raise ValueError("max_legs must be positive")
    if max_candidates <= 0:
        raise ValueError("max_candidates must be positive")
    if max_iters <= 0:
        raise ValueError("max_iters must be positive")

    # Filter to feasible direct pools (direction + active + nonzero output at full amount).
    feasible: List[PoolState] = []
    for p in pools:
        if p.status.value != "ACTIVE":
            continue
        if _reserves_for(p, asset_in=asset_in, asset_out=asset_out) is None:
            continue
        if not _is_valid(p, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in_total):
            continue
        feasible.append(p)

    if not feasible:
        raise ValueError("no feasible pools for split")

    # Rank pools by single-pool output at full amount (desc), then pool_id (asc).
    ranked: List[Tuple[int, PoolState]] = []
    for p in feasible:
        try:
            out_full = _quote_exact_in(p, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in_total)
        except Exception:
            continue
        ranked.append((int(out_full), p))
    if not ranked:
        raise ValueError("no feasible pools for split")
    ranked.sort(key=lambda t: (-int(t[0]), t[1].pool_id))
    candidates: List[PoolState] = [p for _out, p in ranked[: min(int(max_candidates), len(ranked))]]

    # Canonicalize pool order for deterministic tie-breaks.
    candidates.sort(key=lambda p: p.pool_id)

    min_valid: Dict[str, int] = {}
    for p in candidates:
        mv = _min_valid_amount(p, asset_in=asset_in, asset_out=asset_out, amount_in_total=amount_in_total)
        if mv is None:
            continue
        min_valid[p.pool_id] = int(mv)
    if not min_valid:
        raise ValueError("no feasible pools for split")

    pools_by_id: Dict[str, PoolState] = {p.pool_id: p for p in candidates if p.pool_id in min_valid}

    quote_cache: Dict[Tuple[str, int], int] = {}

    def quote(pid: str, amt: int) -> Optional[int]:
        if amt < 0:
            return None
        if amt == 0:
            return 0
        mv = min_valid.get(pid)
        if mv is None or amt < mv:
            return None
        key = (pid, int(amt))
        if key in quote_cache:
            return quote_cache[key]
        out = _quote_exact_in(pools_by_id[pid], asset_in=asset_in, asset_out=asset_out, amount_in=int(amt))
        quote_cache[key] = int(out)
        return int(out)

    def greedy_allocate(step: int) -> Dict[str, int]:
        if step <= 0:
            raise ValueError("step must be positive")

        alloc: Dict[str, int] = {pid: 0 for pid in pools_by_id.keys()}
        used: set[str] = set()
        remaining = int(amount_in_total)

        # Seed: allocate min_valid to the best-looking pools first to allow splitting.
        seed_order = sorted(
            pools_by_id.keys(),
            key=lambda pid: (-int(quote(pid, int(amount_in_total)) or 0), pid),
        )
        for pid in seed_order:
            if remaining <= 0:
                break
            if len(used) >= int(max_legs):
                break
            mv = int(min_valid[pid])
            if mv <= 0 or mv > remaining:
                continue
            alloc[pid] = mv
            remaining -= mv
            used.add(pid)

        # If seeding chose nothing (should be rare), start with the best pool.
        if not used:
            pid0 = seed_order[0]
            mv0 = int(min_valid[pid0])
            inc0 = mv0 if mv0 <= remaining else remaining
            if inc0 <= 0:
                raise ValueError("no feasible allocation")
            alloc[pid0] = inc0
            remaining -= inc0
            used.add(pid0)

        # Greedy remainder allocation.
        while remaining > 0:
            base = min(int(step), int(remaining))
            best_pid: Optional[str] = None
            best_delta = -1
            best_inc = 1
            best_curr = 0

            for pid in pools_by_id.keys():
                curr = int(alloc.get(pid, 0))
                if curr == 0 and pid not in used and len(used) >= int(max_legs):
                    continue

                inc = int(base)
                if curr == 0:
                    mv = int(min_valid[pid])
                    if mv > inc:
                        inc = mv
                if inc <= 0 or inc > remaining:
                    continue

                out_before = quote(pid, curr) or 0
                out_after = quote(pid, curr + inc)
                if out_after is None:
                    continue
                delta = int(out_after - out_before)
                if delta < 0:
                    continue

                if best_pid is None:
                    best_pid, best_delta, best_inc, best_curr = pid, delta, inc, curr
                    continue

                # Compare marginal efficiency delta/inc as rationals: delta*best_inc ? best_delta*inc.
                lhs = int(delta) * int(best_inc)
                rhs = int(best_delta) * int(inc)
                if lhs > rhs:
                    best_pid, best_delta, best_inc, best_curr = pid, delta, inc, curr
                    continue
                if lhs < rhs:
                    continue

                # Tie-break: higher delta, then smaller current allocation (encourage splitting), then pool_id.
                if delta > best_delta:
                    best_pid, best_delta, best_inc, best_curr = pid, delta, inc, curr
                    continue
                if delta < best_delta:
                    continue
                if curr < best_curr:
                    best_pid, best_delta, best_inc, best_curr = pid, delta, inc, curr
                    continue
                if curr > best_curr:
                    continue
                if pid < best_pid:
                    best_pid, best_delta, best_inc, best_curr = pid, delta, inc, curr

            if best_pid is None:
                raise ValueError("no feasible allocation step (unexpected)")

            was_zero = alloc[best_pid] == 0
            alloc[best_pid] = int(alloc[best_pid] + best_inc)
            remaining -= int(best_inc)
            if was_zero:
                used.add(best_pid)

        return alloc

    # Multi-stage schedule: start coarse, refine until step yields <= max_iters increments.
    D = int(amount_in_total)
    step_min = max(1, D // int(max_iters))
    step = max(step_min, max(1, D // 256))

    best_alloc: Optional[Dict[str, int]] = None
    best_out = -1

    while True:
        alloc = greedy_allocate(int(step))
        total_out = 0
        legs_tmp: List[Tuple[str, int, int]] = []
        for pid, amt in alloc.items():
            if amt <= 0:
                continue
            out_amt = quote(pid, int(amt))
            if out_amt is None:
                continue
            total_out += int(out_amt)
            legs_tmp.append((pid, int(amt), int(out_amt)))

        legs_tmp.sort(key=lambda t: t[0])
        if total_out > best_out:
            best_out = int(total_out)
            best_alloc = alloc
        elif total_out == best_out and best_alloc is not None:
            # Deterministic tie-break: fewer legs, then lexicographic (pool_id, amount_in) sequence.
            best_legs = sorted([(pid, int(a)) for pid, a in best_alloc.items() if int(a) > 0], key=lambda t: t[0])
            cur_legs = sorted([(pid, int(a)) for pid, a in alloc.items() if int(a) > 0], key=lambda t: t[0])
            if len(cur_legs) < len(best_legs) or (len(cur_legs) == len(best_legs) and cur_legs < best_legs):
                best_alloc = alloc

        if step <= step_min:
            break
        step = max(step_min, step // 2)

    # Invariant: the first while-pass has total_out >= 0 > best_out (-1), so best_alloc
    # is set on iteration 1. Explicit guard (not `assert`) so it survives `python -O`.
    if best_alloc is None:
        raise AssertionError("internal: grid search left best_alloc unset")
    legs: List[SplitLegQuote] = []
    out_total = 0
    in_total = 0
    for pid in sorted(best_alloc.keys()):
        amt = int(best_alloc[pid])
        if amt <= 0:
            continue
        out_amt = quote(pid, amt)
        if out_amt is None:
            continue
        legs.append(SplitLegQuote(pool_id=pid, amount_in=int(amt), amount_out=int(out_amt)))
        in_total += int(amt)
        out_total += int(out_amt)

    # All input must be allocated.
    if in_total != int(amount_in_total):
        raise ValueError("split allocation did not consume full input (unexpected)")

    return SplitManyPoolsQuote(amount_in_total=int(amount_in_total), amount_out_total=int(out_total), legs=tuple(legs))


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
        except Exception:
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
        except Exception:
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
