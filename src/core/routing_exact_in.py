"""Exact-in route search implementation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Optional, Tuple

from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from . import routing_exact_in_split as _exact_in_split
from .domain_limits import is_strict_int
from .routing_types import RouteHop, RouteLeg, RouteQuote


def _require_int_control(value: object, *, name: str) -> int:
    if not is_strict_int(value):
        raise ValueError(f"{name} must be an int")
    return int(value)


def _require_bool_control(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise ValueError(f"{name} must be a bool")
    return bool(value)


@dataclass(frozen=True)
class _ExactInScanContext:
    pools: Tuple[PoolState, ...]
    by_asset: Dict[AssetId, Tuple[int, ...]]
    asset_in: AssetId
    asset_out: AssetId
    amount_in: Amount
    pool_connects: Callable[[PoolState, AssetId, AssetId], bool]
    pool_quote_exact_in: Callable[..., Optional[Tuple[Amount, str]]]
    quote_key: Callable[[RouteQuote], tuple]


@dataclass(frozen=True)
class _MixedDirectTwoHopContext:
    pools_by_id: Dict[str, PoolState]
    asset_in: AssetId
    asset_out: AssetId
    amount_in: Amount
    quote_key: Callable[[RouteQuote], tuple]
    mixed_split_direct_vs_twohop: Callable[..., Optional[RouteQuote]]


@dataclass(frozen=True)
class _SecondHopProbe:
    pool1: PoolState
    mid: AssetId
    mid_amount: Amount


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
    amount_in_i = _require_int_control(amount_in, name="amount_in")
    mixed_split_enabled = _require_bool_control(
        enable_mixed_direct_twohop_split,
        name="enable_mixed_direct_twohop_split",
    )
    if amount_in_i <= 0:
        return None
    if asset_in == asset_out:
        return None

    context = _build_exact_in_scan_context(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in_i,
        build_asset_pool_index=build_asset_pool_index,
        pool_connects=pool_connects,
        pool_quote_exact_in=pool_quote_exact_in,
        quote_key=quote_key,
    )
    best, best_direct_1hop, twohop_candidates = _scan_direct_and_twohop_exact_in(context)
    best = _scan_parallel_split_exact_in(
        context=context,
        best=best,
        split_many_exact_in=split_many_exact_in,
        split_two_exact_in=split_two_exact_in,
        split_search_profile=split_search_profile,
    )
    if mixed_split_enabled and best_direct_1hop is not None and twohop_candidates:
        best = _scan_mixed_direct_twohop_split(
            best=best,
            best_direct_1hop=best_direct_1hop,
            twohop_candidates=twohop_candidates,
            context=_MixedDirectTwoHopContext(
                pools_by_id=pools_by_id,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=amount_in_i,
                quote_key=quote_key,
                mixed_split_direct_vs_twohop=mixed_split_direct_vs_twohop,
            ),
    )
    return best


def _build_exact_in_scan_context(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    build_asset_pool_index: Callable[[Tuple[PoolState, ...]], Dict[AssetId, Tuple[int, ...]]],
    pool_connects: Callable[[PoolState, AssetId, AssetId], bool],
    pool_quote_exact_in: Callable[..., Optional[Tuple[Amount, str]]],
    quote_key: Callable[[RouteQuote], tuple],
) -> _ExactInScanContext:
    pools: Tuple[PoolState, ...] = tuple(sorted(pools_by_id.values(), key=lambda p: p.pool_id))
    return _ExactInScanContext(
        pools=pools,
        by_asset=build_asset_pool_index(pools),
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        pool_connects=pool_connects,
        pool_quote_exact_in=pool_quote_exact_in,
        quote_key=quote_key,
    )


def _scan_direct_and_twohop_exact_in(
    context: _ExactInScanContext,
) -> tuple[Optional[RouteQuote], Optional[RouteQuote], List[Tuple[RouteQuote, PoolState, PoolState, AssetId]]]:
    best: Optional[RouteQuote] = None
    best_direct_1hop: Optional[RouteQuote] = None
    twohop_candidates: List[Tuple[RouteQuote, PoolState, PoolState, AssetId]] = []

    best, best_direct_1hop = _scan_direct_exact_in(
        best=best,
        best_direct_1hop=best_direct_1hop,
        context=context,
    )
    best = _scan_two_hop_exact_in(
        best=best,
        twohop_candidates=twohop_candidates,
        context=context,
    )
    return best, best_direct_1hop, twohop_candidates


def _scan_parallel_split_exact_in(
    *,
    context: _ExactInScanContext,
    best: Optional[RouteQuote],
    split_many_exact_in: Callable[..., Any],
    split_two_exact_in: Callable[..., Any],
    split_search_profile: str,
) -> Optional[RouteQuote]:
    return _exact_in_split.scan_parallel_split_exact_in(
        best=best,
        pools=context.pools,
        by_asset=context.by_asset,
        asset_in=context.asset_in,
        asset_out=context.asset_out,
        amount_in=context.amount_in,
        pool_connects=context.pool_connects,
        pool_quote_exact_in=context.pool_quote_exact_in,
        quote_key=context.quote_key,
        split_many_exact_in=split_many_exact_in,
        split_two_exact_in=split_two_exact_in,
        split_search_profile=split_search_profile,
    )


def _scan_direct_exact_in(
    *,
    best: Optional[RouteQuote],
    best_direct_1hop: Optional[RouteQuote],
    context: _ExactInScanContext,
) -> tuple[Optional[RouteQuote], Optional[RouteQuote]]:
    for idx in context.by_asset.get(context.asset_in, ()):
        pool = context.pools[idx]
        if not context.pool_connects(pool, context.asset_in, context.asset_out):
            continue
        quote = context.pool_quote_exact_in(
            pool,
            asset_in=context.asset_in,
            asset_out=context.asset_out,
            amount_in=context.amount_in,
        )
        if quote is None:
            continue
        amount_out, _pool_id = quote
        route = _single_hop_exact_in_quote(
            context=context,
            pool=pool,
            amount_out=amount_out,
        )
        if _is_better_exact_in(route, best, quote_key=context.quote_key):
            best = route
        if _is_better_exact_in(route, best_direct_1hop, quote_key=context.quote_key):
            best_direct_1hop = route
    return best, best_direct_1hop


def _single_hop_exact_in_quote(
    *,
    context: _ExactInScanContext,
    pool: PoolState,
    amount_out: Amount,
) -> RouteQuote:
    hop = RouteHop(
        pool.pool_id,
        context.asset_in,
        context.asset_out,
        context.amount_in,
        amount_out,
    )
    return RouteQuote(
        asset_in=context.asset_in,
        asset_out=context.asset_out,
        amount_in=context.amount_in,
        amount_out=amount_out,
        legs=(RouteLeg(hops=(hop,), amount_in=context.amount_in, amount_out=amount_out),),
    )


def _scan_two_hop_exact_in(
    *,
    best: Optional[RouteQuote],
    twohop_candidates: List[Tuple[RouteQuote, PoolState, PoolState, AssetId]],
    context: _ExactInScanContext,
) -> Optional[RouteQuote]:
    for idx1 in context.by_asset.get(context.asset_in, ()):
        pool1 = context.pools[idx1]
        mid = _first_hop_mid_asset(pool1, asset_in=context.asset_in)
        if mid is None or mid == context.asset_out or mid == context.asset_in:
            continue
        first_quote = context.pool_quote_exact_in(
            pool1,
            asset_in=context.asset_in,
            asset_out=mid,
            amount_in=context.amount_in,
        )
        if first_quote is None:
            continue
        mid_amount, _pool_id = first_quote
        best = _scan_second_hop_exact_in(
            best=best,
            twohop_candidates=twohop_candidates,
            context=context,
            probe=_SecondHopProbe(pool1=pool1, mid=mid, mid_amount=mid_amount),
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
    context: _ExactInScanContext,
    probe: _SecondHopProbe,
) -> Optional[RouteQuote]:
    for idx2 in context.by_asset.get(probe.mid, ()):
        pool2 = context.pools[idx2]
        route = _two_hop_exact_in_quote(
            context=context,
            pool2=pool2,
            probe=probe,
        )
        if route is None:
            continue
        if _is_better_exact_in(route, best, quote_key=context.quote_key):
            best = route
        twohop_candidates.append((route, probe.pool1, pool2, probe.mid))
    return best


def _two_hop_exact_in_quote(
    *,
    context: _ExactInScanContext,
    pool2: PoolState,
    probe: _SecondHopProbe,
) -> Optional[RouteQuote]:
    second_quote = context.pool_quote_exact_in(
        pool2,
        asset_in=probe.mid,
        asset_out=context.asset_out,
        amount_in=probe.mid_amount,
    )
    if second_quote is None:
        return None
    amount_out, _pool_id = second_quote
    hop1 = RouteHop(probe.pool1.pool_id, context.asset_in, probe.mid, context.amount_in, probe.mid_amount)
    hop2 = RouteHop(pool2.pool_id, probe.mid, context.asset_out, probe.mid_amount, amount_out)
    return RouteQuote(
        asset_in=context.asset_in,
        asset_out=context.asset_out,
        amount_in=context.amount_in,
        amount_out=amount_out,
        legs=(RouteLeg(hops=(hop1, hop2), amount_in=context.amount_in, amount_out=amount_out),),
    )


def _scan_mixed_direct_twohop_split(
    *,
    best: Optional[RouteQuote],
    best_direct_1hop: RouteQuote,
    twohop_candidates: List[Tuple[RouteQuote, PoolState, PoolState, AssetId]],
    context: _MixedDirectTwoHopContext,
) -> Optional[RouteQuote]:
    direct_pool_id = best_direct_1hop.legs[0].hops[0].pool_id
    direct_pool = context.pools_by_id.get(direct_pool_id)
    if direct_pool is None:
        return best
    twohop_candidates.sort(key=lambda item: (-int(item[0].amount_out), context.quote_key(item[0])))
    for _route, pool1, pool2, mid in twohop_candidates[: min(4, len(twohop_candidates))]:
        mixed = context.mixed_split_direct_vs_twohop(
            direct_pool=direct_pool,
            hop1_pool=pool1,
            hop2_pool=pool2,
            asset_in=context.asset_in,
            mid=mid,
            asset_out=context.asset_out,
            amount_in_total=context.amount_in,
        )
        if mixed is not None and _is_better_exact_in(mixed, best, quote_key=context.quote_key):
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
