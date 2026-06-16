"""Exact-in route search implementation."""

from __future__ import annotations

from typing import Any, Callable, Dict, List, Optional, Tuple

from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from .routing_types import RouteHop, RouteLeg, RouteQuote


def best_route_exact_in_2hop(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    build_asset_pool_index: Callable[[Tuple[PoolState, ...]], Dict[AssetId, Tuple[int, ...]]],
    pool_connects: Callable[[PoolState, AssetId, AssetId], bool],
    pool_quote_exact_in: Callable[..., Optional[Tuple[Amount, str]]],
    quote_key: Callable[[RouteQuote], tuple],
    split_many_exact_in: Callable[..., Any],
    split_two_exact_in: Callable[..., Any],
    mixed_split_direct_vs_twohop: Callable[..., Optional[RouteQuote]],
    split_search_profile: str = "adaptive_v6",
    enable_mixed_direct_twohop_split: bool = False,
) -> Optional[RouteQuote]:
    """Compute the best exact-in route up to 2 hops."""
    if amount_in <= 0:
        return None
    if asset_in == asset_out:
        return None

    pools: Tuple[PoolState, ...] = tuple(sorted(pools_by_id.values(), key=lambda p: p.pool_id))
    by_asset: Dict[AssetId, Tuple[int, ...]] = build_asset_pool_index(pools)

    best: Optional[RouteQuote] = None
    best_direct_1hop: Optional[RouteQuote] = None
    twohop_candidates: List[Tuple[RouteQuote, PoolState, PoolState, AssetId]] = []

    best, best_direct_1hop = _scan_direct_exact_in(
        best=best,
        best_direct_1hop=best_direct_1hop,
        pools=pools,
        by_asset=by_asset,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        pool_connects=pool_connects,
        pool_quote_exact_in=pool_quote_exact_in,
        quote_key=quote_key,
    )
    best = _scan_two_hop_exact_in(
        best=best,
        twohop_candidates=twohop_candidates,
        pools=pools,
        by_asset=by_asset,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        pool_quote_exact_in=pool_quote_exact_in,
        quote_key=quote_key,
    )
    best = _scan_parallel_split_exact_in(
        best=best,
        pools=pools,
        by_asset=by_asset,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        pool_connects=pool_connects,
        pool_quote_exact_in=pool_quote_exact_in,
        quote_key=quote_key,
        split_many_exact_in=split_many_exact_in,
        split_two_exact_in=split_two_exact_in,
        split_search_profile=split_search_profile,
    )
    if enable_mixed_direct_twohop_split and best_direct_1hop is not None and twohop_candidates:
        best = _scan_mixed_direct_twohop_split(
            best=best,
            best_direct_1hop=best_direct_1hop,
            twohop_candidates=twohop_candidates,
            pools_by_id=pools_by_id,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
            quote_key=quote_key,
            mixed_split_direct_vs_twohop=mixed_split_direct_vs_twohop,
        )
    return best


def _scan_direct_exact_in(
    *,
    best: Optional[RouteQuote],
    best_direct_1hop: Optional[RouteQuote],
    pools: Tuple[PoolState, ...],
    by_asset: Dict[AssetId, Tuple[int, ...]],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    pool_connects: Callable[[PoolState, AssetId, AssetId], bool],
    pool_quote_exact_in: Callable[..., Optional[Tuple[Amount, str]]],
    quote_key: Callable[[RouteQuote], tuple],
) -> tuple[Optional[RouteQuote], Optional[RouteQuote]]:
    for idx in by_asset.get(asset_in, ()):
        pool = pools[idx]
        if not pool_connects(pool, asset_in, asset_out):
            continue
        quote = pool_quote_exact_in(
            pool,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
        )
        if quote is None:
            continue
        amount_out, _pool_id = quote
        route = _single_hop_exact_in_quote(
            pool=pool,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
            amount_out=amount_out,
        )
        if _is_better_exact_in(route, best, quote_key=quote_key):
            best = route
        if _is_better_exact_in(route, best_direct_1hop, quote_key=quote_key):
            best_direct_1hop = route
    return best, best_direct_1hop


def _single_hop_exact_in_quote(
    *,
    pool: PoolState,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    amount_out: Amount,
) -> RouteQuote:
    hop = RouteHop(pool.pool_id, asset_in, asset_out, amount_in, amount_out)
    return RouteQuote(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        amount_out=amount_out,
        legs=(RouteLeg(hops=(hop,), amount_in=amount_in, amount_out=amount_out),),
    )


def _scan_two_hop_exact_in(
    *,
    best: Optional[RouteQuote],
    twohop_candidates: List[Tuple[RouteQuote, PoolState, PoolState, AssetId]],
    pools: Tuple[PoolState, ...],
    by_asset: Dict[AssetId, Tuple[int, ...]],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    pool_quote_exact_in: Callable[..., Optional[Tuple[Amount, str]]],
    quote_key: Callable[[RouteQuote], tuple],
) -> Optional[RouteQuote]:
    for idx1 in by_asset.get(asset_in, ()):
        pool1 = pools[idx1]
        mid = _first_hop_mid_asset(pool1, asset_in=asset_in)
        if mid is None or mid == asset_out or mid == asset_in:
            continue
        first_quote = pool_quote_exact_in(
            pool1,
            asset_in=asset_in,
            asset_out=mid,
            amount_in=amount_in,
        )
        if first_quote is None:
            continue
        mid_amount, _pool_id = first_quote
        best = _scan_second_hop_exact_in(
            best=best,
            twohop_candidates=twohop_candidates,
            pool1=pool1,
            pools=pools,
            second_hop_indices=by_asset.get(mid, ()),
            asset_in=asset_in,
            mid=mid,
            asset_out=asset_out,
            amount_in=amount_in,
            mid_amount=mid_amount,
            pool_quote_exact_in=pool_quote_exact_in,
            quote_key=quote_key,
        )
    return best


def _first_hop_mid_asset(pool: PoolState, *, asset_in: AssetId) -> AssetId | None:
    if asset_in == pool.asset0:
        return pool.asset1
    if asset_in == pool.asset1:
        return pool.asset0
    return None


def _scan_second_hop_exact_in(
    *,
    best: Optional[RouteQuote],
    twohop_candidates: List[Tuple[RouteQuote, PoolState, PoolState, AssetId]],
    pool1: PoolState,
    pools: Tuple[PoolState, ...],
    second_hop_indices: Tuple[int, ...],
    asset_in: AssetId,
    mid: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    mid_amount: Amount,
    pool_quote_exact_in: Callable[..., Optional[Tuple[Amount, str]]],
    quote_key: Callable[[RouteQuote], tuple],
) -> Optional[RouteQuote]:
    for idx2 in second_hop_indices:
        pool2 = pools[idx2]
        route = _two_hop_exact_in_quote(
            pool1=pool1,
            pool2=pool2,
            asset_in=asset_in,
            mid=mid,
            asset_out=asset_out,
            amount_in=amount_in,
            mid_amount=mid_amount,
            pool_quote_exact_in=pool_quote_exact_in,
        )
        if route is None:
            continue
        if _is_better_exact_in(route, best, quote_key=quote_key):
            best = route
        twohop_candidates.append((route, pool1, pool2, mid))
    return best


def _two_hop_exact_in_quote(
    *,
    pool1: PoolState,
    pool2: PoolState,
    asset_in: AssetId,
    mid: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    mid_amount: Amount,
    pool_quote_exact_in: Callable[..., Optional[Tuple[Amount, str]]],
) -> Optional[RouteQuote]:
    second_quote = pool_quote_exact_in(
        pool2,
        asset_in=mid,
        asset_out=asset_out,
        amount_in=mid_amount,
    )
    if second_quote is None:
        return None
    amount_out, _pool_id = second_quote
    hop1 = RouteHop(pool1.pool_id, asset_in, mid, amount_in, mid_amount)
    hop2 = RouteHop(pool2.pool_id, mid, asset_out, mid_amount, amount_out)
    return RouteQuote(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        amount_out=amount_out,
        legs=(RouteLeg(hops=(hop1, hop2), amount_in=amount_in, amount_out=amount_out),),
    )


def _scan_parallel_split_exact_in(
    *,
    best: Optional[RouteQuote],
    pools: Tuple[PoolState, ...],
    by_asset: Dict[AssetId, Tuple[int, ...]],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    pool_connects: Callable[[PoolState, AssetId, AssetId], bool],
    pool_quote_exact_in: Callable[..., Optional[Tuple[Amount, str]]],
    quote_key: Callable[[RouteQuote], tuple],
    split_many_exact_in: Callable[..., Any],
    split_two_exact_in: Callable[..., Any],
    split_search_profile: str,
) -> Optional[RouteQuote]:
    direct_pools = _direct_split_candidates(
        pools=pools,
        by_asset=by_asset,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        pool_connects=pool_connects,
        pool_quote_exact_in=pool_quote_exact_in,
    )
    if len(direct_pools) < 2:
        return best
    candidates = [pool for _amount_out, pool in direct_pools[: min(16, len(direct_pools))]]
    best = _scan_many_pool_split_exact_in(
        best=best,
        candidates=candidates,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        quote_key=quote_key,
        split_many_exact_in=split_many_exact_in,
    )
    return _scan_two_pool_split_exact_in(
        best=best,
        candidates=candidates,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        quote_key=quote_key,
        split_two_exact_in=split_two_exact_in,
        split_search_profile=split_search_profile,
    )


def _direct_split_candidates(
    *,
    pools: Tuple[PoolState, ...],
    by_asset: Dict[AssetId, Tuple[int, ...]],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    pool_connects: Callable[[PoolState, AssetId, AssetId], bool],
    pool_quote_exact_in: Callable[..., Optional[Tuple[Amount, str]]],
) -> List[Tuple[Amount, PoolState]]:
    direct_pools: List[Tuple[Amount, PoolState]] = []
    for idx in by_asset.get(asset_in, ()):
        pool = pools[idx]
        if not pool_connects(pool, asset_in, asset_out):
            continue
        quote = pool_quote_exact_in(
            pool,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
        )
        if quote is not None:
            amount_out, _pool_id = quote
            direct_pools.append((amount_out, pool))
    direct_pools.sort(key=lambda item: (-int(item[0]), item[1].pool_id))
    return direct_pools


def _scan_many_pool_split_exact_in(
    *,
    best: Optional[RouteQuote],
    candidates: List[PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    quote_key: Callable[[RouteQuote], tuple],
    split_many_exact_in: Callable[..., Any],
) -> Optional[RouteQuote]:
    try:
        split_many = split_many_exact_in(
            candidates,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in_total=amount_in,
            max_legs=4,
            max_candidates=len(candidates),
            max_iters=4096,
        )
    except ValueError:
        return best
    if split_many is None or split_many.amount_out_total <= 0:
        return best
    route = _many_pool_split_quote(
        split_many=split_many,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
    )
    return route if _is_better_exact_in(route, best, quote_key=quote_key) else best


def _many_pool_split_quote(
    *,
    split_many: Any,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
) -> RouteQuote:
    legs: List[RouteLeg] = []
    for leg in split_many.legs:
        legs.append(
            RouteLeg(
                hops=(RouteHop(leg.pool_id, asset_in, asset_out, leg.amount_in, leg.amount_out),),
                amount_in=leg.amount_in,
                amount_out=leg.amount_out,
            )
        )
    return RouteQuote(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        amount_out=split_many.amount_out_total,
        legs=tuple(legs),
    )


def _scan_two_pool_split_exact_in(
    *,
    best: Optional[RouteQuote],
    candidates: List[PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    quote_key: Callable[[RouteQuote], tuple],
    split_two_exact_in: Callable[..., Any],
    split_search_profile: str,
) -> Optional[RouteQuote]:
    pair_count = min(12, len(candidates))
    pair_candidates = candidates[:pair_count]
    for i in range(pair_count):
        for j in range(i + 1, pair_count):
            route = _two_pool_split_exact_in_quote(
                pool0=pair_candidates[i],
                pool1=pair_candidates[j],
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=amount_in,
                split_two_exact_in=split_two_exact_in,
                split_search_profile=split_search_profile,
            )
            if route is not None and _is_better_exact_in(route, best, quote_key=quote_key):
                best = route
    return best


def _two_pool_split_exact_in_quote(
    *,
    pool0: PoolState,
    pool1: PoolState,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    split_two_exact_in: Callable[..., Any],
    split_search_profile: str,
) -> Optional[RouteQuote]:
    try:
        split = split_two_exact_in(
            pool0,
            pool1,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in_total=amount_in,
            search_profile=str(split_search_profile),
        )
    except ValueError:
        return None
    if split.amount_out_total <= 0:
        return None
    leg0 = RouteLeg(
        hops=(RouteHop(split.pool0_id, asset_in, asset_out, split.amount_in_0, split.amount_out_0),),
        amount_in=split.amount_in_0,
        amount_out=split.amount_out_0,
    )
    leg1 = RouteLeg(
        hops=(RouteHop(split.pool1_id, asset_in, asset_out, split.amount_in_1, split.amount_out_1),),
        amount_in=split.amount_in_1,
        amount_out=split.amount_out_1,
    )
    return RouteQuote(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        amount_out=split.amount_out_total,
        legs=(leg0, leg1),
    )


def _scan_mixed_direct_twohop_split(
    *,
    best: Optional[RouteQuote],
    best_direct_1hop: RouteQuote,
    twohop_candidates: List[Tuple[RouteQuote, PoolState, PoolState, AssetId]],
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    quote_key: Callable[[RouteQuote], tuple],
    mixed_split_direct_vs_twohop: Callable[..., Optional[RouteQuote]],
) -> Optional[RouteQuote]:
    direct_pool_id = best_direct_1hop.legs[0].hops[0].pool_id
    direct_pool = pools_by_id.get(direct_pool_id)
    if direct_pool is None:
        return best
    twohop_candidates.sort(key=lambda item: (-int(item[0].amount_out), quote_key(item[0])))
    for _route, pool1, pool2, mid in twohop_candidates[: min(4, len(twohop_candidates))]:
        mixed = mixed_split_direct_vs_twohop(
            direct_pool=direct_pool,
            hop1_pool=pool1,
            hop2_pool=pool2,
            asset_in=asset_in,
            mid=mid,
            asset_out=asset_out,
            amount_in_total=amount_in,
        )
        if mixed is not None and _is_better_exact_in(mixed, best, quote_key=quote_key):
            best = mixed
    return best


def _is_better_exact_in(
    candidate: RouteQuote,
    current: Optional[RouteQuote],
    *,
    quote_key: Callable[[RouteQuote], tuple],
) -> bool:
    if current is None:
        return True
    return candidate.amount_out > current.amount_out or (
        candidate.amount_out == current.amount_out and quote_key(candidate) < quote_key(current)
    )
