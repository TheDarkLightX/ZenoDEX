"""Exact-in parallel split route search helpers."""

from __future__ import annotations

from typing import Any, Callable, Dict, List, Optional, Tuple

from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from .routing_types import RouteHop, RouteLeg, RouteQuote


def scan_parallel_split_exact_in(
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
