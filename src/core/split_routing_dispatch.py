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

from typing import Sequence, Tuple

from ..state.balances import Amount, AssetId
from ..state.pools import CURVE_TAG_CPMM, PoolState
from .domain_limits import is_strict_int
from .split_routing import (
    PoolXY,
    best_split_two_pools_exact_in,
    exact_out_for_pool_exact_in,
    resolve_two_pool_split_search_params,
)
from .split_routing_generic_exact_in import (
    GenericExactInSplitRequest,
    best_generic_two_pool_exact_in,
)
from .split_routing_many_exact_in import ManyPoolExactInRequest, best_many_pool_exact_in_split
from .split_routing_many_exact_out import (
    ManyPoolExactOutRequest,
    best_many_pool_exact_out_split,
    build_exact_out_capacity_guard_from_caps,
)
from .split_routing_pool_quotes import (
    quote_exact_in_for_pool as _quote_exact_in,
)
from .split_routing_pool_quotes import (
    quote_exact_out_for_pool as _quote_exact_out,
)
from .split_routing_pool_quotes import (
    reserves_for_pool as _reserves_for,
)
from .split_routing_two_exact_out import TwoPoolExactOutRequest, best_two_pool_exact_out_split
from .split_routing_types import (
    ExactOutCapacityGuard,
    SplitManyPoolsExactOutQuote,
    SplitManyPoolsQuote,
    SplitTwoPoolsQuote,
)
from .split_routing_types import (
    ExactOutRouteCanonicalKey as ExactOutRouteCanonicalKey,
)
from .split_routing_types import (
    SplitLegExactOutQuote as SplitLegExactOutQuote,
)
from .split_routing_types import (
    SplitLegQuote as SplitLegQuote,
)
from .split_routing_types import (
    exact_out_route_canonical_key as exact_out_route_canonical_key,
)
from .split_routing_types import (
    exact_out_route_canonical_key_for_legs as exact_out_route_canonical_key_for_legs,
)


def _require_positive_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) <= 0:
        raise ValueError(f"{name} must be positive")
    return int(value)


def _require_nonnegative_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def exact_out_capacity_guard_for_pools(
    pools: Sequence[PoolState],
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out_total: Amount,
    max_legs: int,
) -> ExactOutCapacityGuard:
    target_out = _require_positive_control(amount_out_total, name="amount_out_total")
    max_legs_i = _require_positive_control(max_legs, name="max_legs")
    caps_by_pool: list[tuple[str, int]] = []
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
    return build_exact_out_capacity_guard_from_caps(
        caps_by_pool,
        amount_out_total=int(target_out),
        max_legs=max_legs_i,
    )


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
    amount_in_total_i = _require_positive_control(amount_in_total, name="amount_in_total")
    window_i = _require_nonnegative_control(window, name="window")
    brute_force_max_i = _require_nonnegative_control(brute_force_max, name="brute_force_max")

    def quote0(amount_in: int) -> int:
        return _quote_exact_in(pool0, asset_in=asset_in, asset_out=asset_out, amount_in=int(amount_in))

    def quote1(amount_in: int) -> int:
        return _quote_exact_in(pool1, asset_in=asset_in, asset_out=asset_out, amount_in=int(amount_in))

    return best_generic_two_pool_exact_in(
        GenericExactInSplitRequest(
            amount_in_total=amount_in_total_i,
            window=window_i,
            brute_force_max=brute_force_max_i,
            quote0=quote0,
            quote1=quote1,
        )
    )


def _best_cpmm_split_two_pools_exact_in_quote(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
    window: int,
    search_profile: str,
) -> SplitTwoPoolsQuote:
    r0 = _reserves_for(pool0, asset_in=asset_in, asset_out=asset_out)
    r1 = _reserves_for(pool1, asset_in=asset_in, asset_out=asset_out)
    if r0 is None or r1 is None:
        raise ValueError("pools do not support this direction (or are inactive)")
    rin0, rout0 = r0
    rin1, rout1 = r1
    xy0 = PoolXY(x=int(rin0), y=int(rout0), fee_bps=int(pool0.fee_bps))
    xy1 = PoolXY(x=int(rin1), y=int(rout1), fee_bps=int(pool1.fee_bps))
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
        pool0_id=pool0.pool_id,
        pool1_id=pool1.pool_id,
        amount_in_total=int(amount_in_total),
        amount_out_total=int(best_out),
        amount_in_0=int(best_a),
        amount_out_0=int(out0),
        amount_in_1=int(amount_in_total) - int(best_a),
        amount_out_1=int(out1),
    )


def _best_generic_split_two_pools_exact_in_quote(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
    window: int,
) -> SplitTwoPoolsQuote:
    best_out, best_a = _generic_best_split_two_pools_exact_in(
        pool0,
        pool1,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in_total=amount_in_total,
        window=int(window),
        brute_force_max=2048,
    )
    amount_in_1 = int(amount_in_total) - int(best_a)
    out0 = _quote_exact_in(pool0, asset_in=asset_in, asset_out=asset_out, amount_in=int(best_a)) if best_a > 0 else 0
    out1 = _quote_exact_in(pool1, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in_1) if amount_in_1 > 0 else 0
    if int(out0 + out1) != int(best_out):
        # Defensive: recompute total from per-leg quotes.
        best_out = int(out0 + out1)
    return SplitTwoPoolsQuote(
        pool0_id=pool0.pool_id,
        pool1_id=pool1.pool_id,
        amount_in_total=int(amount_in_total),
        amount_out_total=int(best_out),
        amount_in_0=int(best_a),
        amount_out_0=int(out0),
        amount_in_1=int(amount_in_1),
        amount_out_1=int(out1),
    )


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
    amount_in_total_i = _require_positive_control(amount_in_total, name="amount_in_total")
    window_i = _require_nonnegative_control(window, name="window")

    # Canonicalize pool order.
    p0, p1 = (pool0, pool1) if pool0.pool_id <= pool1.pool_id else (pool1, pool0)

    # Fast path: CPMM uses the dedicated solver.
    if p0.curve_tag == CURVE_TAG_CPMM and p1.curve_tag == CURVE_TAG_CPMM:
        return _best_cpmm_split_two_pools_exact_in_quote(
            p0,
            p1,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in_total=amount_in_total_i,
            window=window_i,
            search_profile=str(search_profile),
        )

    return _best_generic_split_two_pools_exact_in_quote(
        p0,
        p1,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in_total=amount_in_total_i,
        window=window_i,
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
    amount_out_total_i = _require_positive_control(amount_out_total, name="amount_out_total")
    window_i = _require_nonnegative_control(window, name="window")
    brute_force_max_i = _require_nonnegative_control(brute_force_max, name="brute_force_max")

    def reserves_for(pool: PoolState) -> tuple[int, int] | None:
        return _reserves_for(pool, asset_in=asset_in, asset_out=asset_out)

    def quote_exact_out(pool: PoolState, amount_out: int) -> int:
        return _quote_exact_out(pool, asset_in=asset_in, asset_out=asset_out, amount_out=int(amount_out))

    return best_two_pool_exact_out_split(
        TwoPoolExactOutRequest(
            pool0=pool0,
            pool1=pool1,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=amount_out_total_i,
            window=window_i,
            brute_force_max=brute_force_max_i,
            reserves_for=reserves_for,
            quote_exact_out=quote_exact_out,
        )
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
    - For small bounded domains, solve `max Σ f_i(a_i)` s.t. `Σ a_i = D`, `a_i ∈ ℕ`.
    - For larger domains, use the existing bounded multi-stage greedy allocator.
    - Apply deterministic tie-breaks: higher output, fewer legs, then lexicographic legs.
    - Limit to at most `max_legs` non-zero legs and `max_candidates` candidate pools.
    """
    amount_in_total_i = _require_positive_control(amount_in_total, name="amount_in_total")
    max_legs_i = _require_positive_control(max_legs, name="max_legs")
    max_candidates_i = _require_positive_control(max_candidates, name="max_candidates")
    max_iters_i = _require_positive_control(max_iters, name="max_iters")

    def reserves_for(pool: PoolState) -> tuple[int, int] | None:
        return _reserves_for(pool, asset_in=asset_in, asset_out=asset_out)

    def quote_exact_in(pool: PoolState, amount_in: int) -> int:
        return _quote_exact_in(pool, asset_in=asset_in, asset_out=asset_out, amount_in=int(amount_in))

    return best_many_pool_exact_in_split(
        ManyPoolExactInRequest(
            pools=pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in_total=amount_in_total_i,
            max_legs=max_legs_i,
            max_candidates=max_candidates_i,
            max_iters=max_iters_i,
            reserves_for=reserves_for,
            quote_exact_in=quote_exact_in,
        )
    )


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
    amount_out_total_i = _require_positive_control(amount_out_total, name="amount_out_total")
    max_legs_i = _require_positive_control(max_legs, name="max_legs")
    max_candidates_i = _require_positive_control(max_candidates, name="max_candidates")
    max_iters_i = _require_positive_control(max_iters, name="max_iters")
    window_i = _require_nonnegative_control(window, name="window")
    brute_force_max_i = _require_nonnegative_control(brute_force_max, name="brute_force_max")
    max_full_domain_pools_i = _require_positive_control(max_full_domain_pools, name="max_full_domain_pools")

    def reserves_for(pool: PoolState) -> tuple[int, int] | None:
        return _reserves_for(pool, asset_in=asset_in, asset_out=asset_out)

    def quote_exact_out(pool: PoolState, amount_out: int) -> int:
        return _quote_exact_out(pool, asset_in=asset_in, asset_out=asset_out, amount_out=int(amount_out))

    return best_many_pool_exact_out_split(
        ManyPoolExactOutRequest(
            pools=pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=amount_out_total_i,
            max_legs=max_legs_i,
            max_candidates=max_candidates_i,
            max_iters=max_iters_i,
            window=window_i,
            brute_force_max=brute_force_max_i,
            max_full_domain_pools=max_full_domain_pools_i,
            reserves_for=reserves_for,
            quote_exact_out=quote_exact_out,
        )
    )
