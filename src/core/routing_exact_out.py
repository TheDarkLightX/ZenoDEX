"""Exact-out route search implementation."""

from __future__ import annotations

from typing import Any, Callable, Dict, List, Optional, Tuple

from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from .routing_exact_out_gate import ExactOutTwoHopGateConfig
from .routing_types import RouteHop, RouteLeg, RouteQuote


def best_route_exact_out_2hop(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out: Amount,
    build_asset_pool_index: Callable[[Tuple[PoolState, ...]], Dict[AssetId, Tuple[int, ...]]],
    pool_connects: Callable[[PoolState, AssetId, AssetId], bool],
    pool_quote_exact_out: Callable[..., Optional[Tuple[Amount, str, Amount]]],
    quote_key: Callable[[RouteQuote], tuple],
    should_consider_exact_out_two_hop: Callable[..., bool],
    split_two_pools_exact_out: Callable[..., Any],
    apply_two_hop_gate: bool = False,
    gate_config: ExactOutTwoHopGateConfig | None = None,
) -> Optional[RouteQuote]:
    """Compute the best exact-out route up to 2 hops."""
    if amount_out <= 0:
        return None
    if asset_in == asset_out:
        return None

    pools: Tuple[PoolState, ...] = tuple(sorted(pools_by_id.values(), key=lambda p: p.pool_id))
    by_asset: Dict[AssetId, Tuple[int, ...]] = build_asset_pool_index(pools)

    best_direct, direct_candidates, gate_inputs = _direct_exact_out_candidates(
        pools=pools,
        by_asset=by_asset,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out=amount_out,
        pool_connects=pool_connects,
        pool_quote_exact_out=pool_quote_exact_out,
        quote_key=quote_key,
    )
    consider_two_hop = _should_scan_two_hop(
        amount_out=amount_out,
        best_direct=best_direct,
        gate_inputs=gate_inputs,
        apply_two_hop_gate=apply_two_hop_gate,
        gate_config=gate_config,
        should_consider_exact_out_two_hop=should_consider_exact_out_two_hop,
    )

    best: Optional[RouteQuote] = best_direct
    best = _best_parallel_split_exact_out(
        best=best,
        direct_candidates=direct_candidates,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out=amount_out,
        quote_key=quote_key,
        split_two_pools_exact_out=split_two_pools_exact_out,
    )
    if consider_two_hop:
        best = _best_two_hop_exact_out(
            best=best,
            pools=pools,
            by_asset=by_asset,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out=amount_out,
            pool_connects=pool_connects,
            pool_quote_exact_out=pool_quote_exact_out,
            quote_key=quote_key,
        )
    return best


def _direct_exact_out_candidates(
    *,
    pools: Tuple[PoolState, ...],
    by_asset: Dict[AssetId, Tuple[int, ...]],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out: Amount,
    pool_connects: Callable[[PoolState, AssetId, AssetId], bool],
    pool_quote_exact_out: Callable[..., Optional[Tuple[Amount, str, Amount]]],
    quote_key: Callable[[RouteQuote], tuple],
) -> tuple[Optional[RouteQuote], List[PoolState], tuple[Amount | None, int | None]]:
    best_direct: Optional[RouteQuote] = None
    best_direct_reserve_out: Amount | None = None
    best_direct_fee_bps: int | None = None
    direct_candidates: List[PoolState] = []

    for idx in by_asset.get(asset_in, ()):
        pool = pools[idx]
        if not pool_connects(pool, asset_in, asset_out):
            continue
        direct_candidates.append(pool)
        quote = pool_quote_exact_out(
            pool,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out=amount_out,
        )
        if quote is None:
            continue
        amount_in, _pool_id, reserve_out = quote
        route = _single_hop_exact_out_quote(
            pool=pool,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
            amount_out=amount_out,
        )
        if _is_better_exact_out(route, best_direct, quote_key=quote_key):
            best_direct = route
            best_direct_reserve_out = reserve_out
            best_direct_fee_bps = int(pool.fee_bps)
    return best_direct, direct_candidates, (best_direct_reserve_out, best_direct_fee_bps)


def _single_hop_exact_out_quote(
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


def _should_scan_two_hop(
    *,
    amount_out: Amount,
    best_direct: Optional[RouteQuote],
    gate_inputs: tuple[Amount | None, int | None],
    apply_two_hop_gate: bool,
    gate_config: ExactOutTwoHopGateConfig | None,
    should_consider_exact_out_two_hop: Callable[..., bool],
) -> bool:
    if not apply_two_hop_gate:
        return True
    best_direct_reserve_out, best_direct_fee_bps = gate_inputs
    if best_direct is None or best_direct_reserve_out is None:
        return True
    return should_consider_exact_out_two_hop(
        amount_out=amount_out,
        direct_reserve_out=int(best_direct_reserve_out),
        direct_amount_in=int(best_direct.amount_in),
        direct_fee_bps=int(best_direct_fee_bps or 0),
        config=gate_config,
    )


def _best_parallel_split_exact_out(
    *,
    best: Optional[RouteQuote],
    direct_candidates: List[PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out: Amount,
    quote_key: Callable[[RouteQuote], tuple],
    split_two_pools_exact_out: Callable[..., Any],
) -> Optional[RouteQuote]:
    if len(direct_candidates) < 2:
        return best
    candidates = _bounded_direct_candidates(
        direct_candidates=direct_candidates,
        asset_in=asset_in,
        asset_out=asset_out,
    )
    for i in range(len(candidates)):
        for j in range(i + 1, len(candidates)):
            route = _parallel_split_exact_out_quote(
                pool0=candidates[i],
                pool1=candidates[j],
                asset_in=asset_in,
                asset_out=asset_out,
                amount_out=amount_out,
                split_two_pools_exact_out=split_two_pools_exact_out,
            )
            if route is not None and _is_better_exact_out(route, best, quote_key=quote_key):
                best = route
    return best


def _bounded_direct_candidates(
    *,
    direct_candidates: List[PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
) -> List[PoolState]:
    max_split_candidates = 8
    if len(direct_candidates) <= max_split_candidates:
        return direct_candidates

    def direct_reserve_out(pool: PoolState) -> int:
        if asset_in == pool.asset0 and asset_out == pool.asset1:
            return int(pool.reserve1)
        if asset_in == pool.asset1 and asset_out == pool.asset0:
            return int(pool.reserve0)
        return 0

    candidates = sorted(
        direct_candidates,
        key=lambda pool: (-direct_reserve_out(pool), pool.pool_id),
    )[:max_split_candidates]
    return sorted(candidates, key=lambda pool: pool.pool_id)


def _parallel_split_exact_out_quote(
    *,
    pool0: PoolState,
    pool1: PoolState,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out: Amount,
    split_two_pools_exact_out: Callable[..., Any],
) -> Optional[RouteQuote]:
    try:
        split = split_two_pools_exact_out(
            pool0,
            pool1,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=amount_out,
        )
    except ValueError:
        return None
    if split.amount_in_total <= 0:
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
        amount_in=split.amount_in_total,
        amount_out=amount_out,
        legs=(leg0, leg1),
    )


def _best_two_hop_exact_out(
    *,
    best: Optional[RouteQuote],
    pools: Tuple[PoolState, ...],
    by_asset: Dict[AssetId, Tuple[int, ...]],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out: Amount,
    pool_connects: Callable[[PoolState, AssetId, AssetId], bool],
    pool_quote_exact_out: Callable[..., Optional[Tuple[Amount, str, Amount]]],
    quote_key: Callable[[RouteQuote], tuple],
) -> Optional[RouteQuote]:
    for idx1 in by_asset.get(asset_in, ()):
        pool1 = pools[idx1]
        mid = _first_hop_mid_asset(pool1, asset_in=asset_in)
        if mid is None or mid == asset_out or mid == asset_in:
            continue
        best = _best_second_hop_exact_out(
            best=best,
            pool1=pool1,
            pools=pools,
            second_hop_indices=by_asset.get(mid, ()),
            asset_in=asset_in,
            mid=mid,
            asset_out=asset_out,
            amount_out=amount_out,
            pool_connects=pool_connects,
            pool_quote_exact_out=pool_quote_exact_out,
            quote_key=quote_key,
        )
    return best


def _first_hop_mid_asset(pool: PoolState, *, asset_in: AssetId) -> AssetId | None:
    if asset_in == pool.asset0:
        return pool.asset1
    if asset_in == pool.asset1:
        return pool.asset0
    return None


def _best_second_hop_exact_out(
    *,
    best: Optional[RouteQuote],
    pool1: PoolState,
    pools: Tuple[PoolState, ...],
    second_hop_indices: Tuple[int, ...],
    asset_in: AssetId,
    mid: AssetId,
    asset_out: AssetId,
    amount_out: Amount,
    pool_connects: Callable[[PoolState, AssetId, AssetId], bool],
    pool_quote_exact_out: Callable[..., Optional[Tuple[Amount, str, Amount]]],
    quote_key: Callable[[RouteQuote], tuple],
) -> Optional[RouteQuote]:
    for idx2 in second_hop_indices:
        pool2 = pools[idx2]
        if not pool_connects(pool2, mid, asset_out):
            continue
        route = _two_hop_exact_out_quote(
            pool1=pool1,
            pool2=pool2,
            asset_in=asset_in,
            mid=mid,
            asset_out=asset_out,
            amount_out=amount_out,
            pool_quote_exact_out=pool_quote_exact_out,
        )
        if route is not None and _is_better_exact_out(route, best, quote_key=quote_key):
            best = route
    return best


def _two_hop_exact_out_quote(
    *,
    pool1: PoolState,
    pool2: PoolState,
    asset_in: AssetId,
    mid: AssetId,
    asset_out: AssetId,
    amount_out: Amount,
    pool_quote_exact_out: Callable[..., Optional[Tuple[Amount, str, Amount]]],
) -> Optional[RouteQuote]:
    second_quote = pool_quote_exact_out(
        pool2,
        asset_in=mid,
        asset_out=asset_out,
        amount_out=amount_out,
    )
    if second_quote is None:
        return None
    mid_in, _pool_id, _reserve_out = second_quote
    first_quote = pool_quote_exact_out(
        pool1,
        asset_in=asset_in,
        asset_out=mid,
        amount_out=mid_in,
    )
    if first_quote is None:
        return None
    amount_in, _pool_id, _reserve_out = first_quote

    hop1 = RouteHop(pool1.pool_id, asset_in, mid, amount_in, mid_in)
    hop2 = RouteHop(pool2.pool_id, mid, asset_out, mid_in, amount_out)
    return RouteQuote(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        amount_out=amount_out,
        legs=(RouteLeg(hops=(hop1, hop2), amount_in=amount_in, amount_out=amount_out),),
    )


def _is_better_exact_out(
    candidate: RouteQuote,
    current: Optional[RouteQuote],
    *,
    quote_key: Callable[[RouteQuote], tuple],
) -> bool:
    if current is None:
        return True
    return candidate.amount_in < current.amount_in or (
        candidate.amount_in == current.amount_in and quote_key(candidate) < quote_key(current)
    )
