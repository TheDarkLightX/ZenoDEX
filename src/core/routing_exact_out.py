"""Exact-out route search implementation."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Any, Callable, Dict, List, Optional, Tuple

from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from .domain_limits import is_strict_int
from .routing_exact_out_gate import ExactOutTwoHopGateConfig
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
class ExactOutRouteRequest:
    pools_by_id: Dict[str, PoolState]
    asset_in: AssetId
    asset_out: AssetId
    amount_out: Amount
    apply_two_hop_gate: bool = False
    gate_config: ExactOutTwoHopGateConfig | None = None


@dataclass(frozen=True)
class ExactOutRouteDependencies:
    build_asset_pool_index: Callable[[Tuple[PoolState, ...]], Dict[AssetId, Tuple[int, ...]]]
    pool_connects: Callable[[PoolState, AssetId, AssetId], bool]
    pool_quote_exact_out: Callable[..., Optional[Tuple[Amount, str, Amount]]]
    quote_key: Callable[[RouteQuote], tuple]
    should_consider_exact_out_two_hop: Callable[..., bool]
    split_two_pools_exact_out: Callable[..., Any]


@dataclass(frozen=True)
class _ExactOutScanContext:
    pools: Tuple[PoolState, ...]
    by_asset: Dict[AssetId, Tuple[int, ...]]
    asset_in: AssetId
    asset_out: AssetId
    amount_out: Amount
    pool_connects: Callable[[PoolState, AssetId, AssetId], bool]
    pool_quote_exact_out: Callable[..., Optional[Tuple[Amount, str, Amount]]]
    quote_key: Callable[[RouteQuote], tuple]


@dataclass(frozen=True)
class _ExactOutTwoHopGateSettings:
    apply_two_hop_gate: bool
    config: ExactOutTwoHopGateConfig | None


@dataclass(frozen=True)
class _ExactOutDirectGateEvidence:
    best_direct: Optional[RouteQuote]
    direct_reserve_out: Amount | None
    direct_fee_bps: int | None


@dataclass(frozen=True)
class _ExactOutSecondHopProbe:
    pool1: PoolState
    mid: AssetId


def best_route_exact_out_2hop(
    *,
    request: ExactOutRouteRequest,
    dependencies: ExactOutRouteDependencies,
) -> Optional[RouteQuote]:
    """Compute the best exact-out route up to 2 hops."""
    amount_out_i = _require_int_control(request.amount_out, name="amount_out")
    gate_settings = _ExactOutTwoHopGateSettings(
        apply_two_hop_gate=_require_bool_control(
            request.apply_two_hop_gate,
            name="apply_two_hop_gate",
        ),
        config=request.gate_config,
    )
    if amount_out_i <= 0:
        return None
    if request.asset_in == request.asset_out:
        return None

    context = _build_exact_out_scan_context(
        amount_out=amount_out_i,
        request=request,
        dependencies=dependencies,
    )
    best_direct, direct_candidates, gate_evidence = _direct_exact_out_candidates(
        context=context,
    )
    consider_two_hop = _should_scan_two_hop(
        amount_out=amount_out_i,
        gate_evidence=gate_evidence,
        gate_settings=gate_settings,
        dependencies=dependencies,
    )

    best: Optional[RouteQuote] = best_direct
    best = _best_parallel_split_exact_out(
        best=best,
        direct_candidates=direct_candidates,
        context=context,
        dependencies=dependencies,
    )
    if consider_two_hop:
        best = _best_two_hop_exact_out(
            best=best,
            context=context,
        )
    return best


def _build_exact_out_scan_context(
    *,
    amount_out: Amount,
    request: ExactOutRouteRequest,
    dependencies: ExactOutRouteDependencies,
) -> _ExactOutScanContext:
    pools: Tuple[PoolState, ...] = tuple(sorted(request.pools_by_id.values(), key=lambda p: p.pool_id))
    return _ExactOutScanContext(
        pools=pools,
        by_asset=dependencies.build_asset_pool_index(pools),
        asset_in=request.asset_in,
        asset_out=request.asset_out,
        amount_out=amount_out,
        pool_connects=dependencies.pool_connects,
        pool_quote_exact_out=dependencies.pool_quote_exact_out,
        quote_key=dependencies.quote_key,
    )


def _direct_exact_out_candidates(
    *,
    context: _ExactOutScanContext,
) -> tuple[Optional[RouteQuote], List[PoolState], _ExactOutDirectGateEvidence]:
    best_direct: Optional[RouteQuote] = None
    best_direct_reserve_out: Amount | None = None
    best_direct_fee_bps: int | None = None
    direct_candidates: List[PoolState] = []

    for idx in context.by_asset.get(context.asset_in, ()):
        pool = context.pools[idx]
        if not context.pool_connects(pool, context.asset_in, context.asset_out):
            continue
        direct_candidates.append(pool)
        quote = context.pool_quote_exact_out(
            pool,
            asset_in=context.asset_in,
            asset_out=context.asset_out,
            amount_out=context.amount_out,
        )
        if quote is None:
            continue
        amount_in, _pool_id, reserve_out = quote
        route = _single_hop_exact_out_quote(
            context=context,
            pool=pool,
            amount_in=amount_in,
        )
        if _is_better_exact_out(route, best_direct, quote_key=context.quote_key):
            best_direct = route
            best_direct_reserve_out = reserve_out
            best_direct_fee_bps = int(pool.fee_bps)
    return (
        best_direct,
        direct_candidates,
        _ExactOutDirectGateEvidence(
            best_direct=best_direct,
            direct_reserve_out=best_direct_reserve_out,
            direct_fee_bps=best_direct_fee_bps,
        ),
    )


def _single_hop_exact_out_quote(
    *,
    context: _ExactOutScanContext,
    pool: PoolState,
    amount_in: Amount,
) -> RouteQuote:
    hop = RouteHop(pool.pool_id, context.asset_in, context.asset_out, amount_in, context.amount_out)
    return RouteQuote(
        asset_in=context.asset_in,
        asset_out=context.asset_out,
        amount_in=amount_in,
        amount_out=context.amount_out,
        legs=(RouteLeg(hops=(hop,), amount_in=amount_in, amount_out=context.amount_out),),
    )


def _should_scan_two_hop(
    *,
    amount_out: Amount,
    gate_evidence: _ExactOutDirectGateEvidence,
    gate_settings: _ExactOutTwoHopGateSettings,
    dependencies: ExactOutRouteDependencies,
) -> bool:
    if not gate_settings.apply_two_hop_gate:
        return True
    if gate_evidence.best_direct is None or gate_evidence.direct_reserve_out is None:
        return True
    return dependencies.should_consider_exact_out_two_hop(
        amount_out=amount_out,
        direct_reserve_out=int(gate_evidence.direct_reserve_out),
        direct_amount_in=int(gate_evidence.best_direct.amount_in),
        direct_fee_bps=int(gate_evidence.direct_fee_bps or 0),
        config=gate_settings.config,
    )


def _best_parallel_split_exact_out(
    *,
    best: Optional[RouteQuote],
    direct_candidates: List[PoolState],
    context: _ExactOutScanContext,
    dependencies: ExactOutRouteDependencies,
) -> Optional[RouteQuote]:
    if len(direct_candidates) < 2:
        return best
    candidates = _bounded_direct_candidates(
        direct_candidates=direct_candidates,
        asset_in=context.asset_in,
        asset_out=context.asset_out,
    )
    for pool0, pool1 in combinations(candidates, 2):
        route = _parallel_split_exact_out_quote(
            context=context,
            pool0=pool0,
            pool1=pool1,
            split_two_pools_exact_out=dependencies.split_two_pools_exact_out,
        )
        if route is not None and _is_better_exact_out(route, best, quote_key=context.quote_key):
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

    candidates = sorted(
        direct_candidates,
        key=lambda pool: (-_direct_reserve_out(pool, asset_in=asset_in, asset_out=asset_out), pool.pool_id),
    )[:max_split_candidates]
    return sorted(candidates, key=lambda pool: pool.pool_id)


def _direct_reserve_out(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId) -> int:
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve0)
    return 0


def _parallel_split_exact_out_quote(
    *,
    context: _ExactOutScanContext,
    pool0: PoolState,
    pool1: PoolState,
    split_two_pools_exact_out: Callable[..., Any],
) -> Optional[RouteQuote]:
    try:
        split = split_two_pools_exact_out(
            pool0,
            pool1,
            asset_in=context.asset_in,
            asset_out=context.asset_out,
            amount_out_total=context.amount_out,
        )
    except ValueError:
        return None
    if split.amount_in_total <= 0:
        return None
    leg0 = RouteLeg(
        hops=(RouteHop(split.pool0_id, context.asset_in, context.asset_out, split.amount_in_0, split.amount_out_0),),
        amount_in=split.amount_in_0,
        amount_out=split.amount_out_0,
    )
    leg1 = RouteLeg(
        hops=(RouteHop(split.pool1_id, context.asset_in, context.asset_out, split.amount_in_1, split.amount_out_1),),
        amount_in=split.amount_in_1,
        amount_out=split.amount_out_1,
    )
    return RouteQuote(
        asset_in=context.asset_in,
        asset_out=context.asset_out,
        amount_in=split.amount_in_total,
        amount_out=context.amount_out,
        legs=(leg0, leg1),
    )


def _best_two_hop_exact_out(
    *,
    best: Optional[RouteQuote],
    context: _ExactOutScanContext,
) -> Optional[RouteQuote]:
    for idx1 in context.by_asset.get(context.asset_in, ()):
        pool1 = context.pools[idx1]
        mid = _first_hop_mid_asset(pool1, asset_in=context.asset_in)
        if mid is None or mid == context.asset_out or mid == context.asset_in:
            continue
        best = _best_second_hop_exact_out(
            best=best,
            context=context,
            probe=_ExactOutSecondHopProbe(pool1=pool1, mid=mid),
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
    context: _ExactOutScanContext,
    probe: _ExactOutSecondHopProbe,
) -> Optional[RouteQuote]:
    for idx2 in context.by_asset.get(probe.mid, ()):
        pool2 = context.pools[idx2]
        if not context.pool_connects(pool2, probe.mid, context.asset_out):
            continue
        route = _two_hop_exact_out_quote(
            context=context,
            pool2=pool2,
            probe=probe,
        )
        if route is not None and _is_better_exact_out(route, best, quote_key=context.quote_key):
            best = route
    return best


def _two_hop_exact_out_quote(
    *,
    context: _ExactOutScanContext,
    pool2: PoolState,
    probe: _ExactOutSecondHopProbe,
) -> Optional[RouteQuote]:
    second_quote = context.pool_quote_exact_out(
        pool2,
        asset_in=probe.mid,
        asset_out=context.asset_out,
        amount_out=context.amount_out,
    )
    if second_quote is None:
        return None
    mid_in, _pool_id, _reserve_out = second_quote
    first_quote = context.pool_quote_exact_out(
        probe.pool1,
        asset_in=context.asset_in,
        asset_out=probe.mid,
        amount_out=mid_in,
    )
    if first_quote is None:
        return None
    amount_in, _pool_id, _reserve_out = first_quote

    hop1 = RouteHop(probe.pool1.pool_id, context.asset_in, probe.mid, amount_in, mid_in)
    hop2 = RouteHop(pool2.pool_id, probe.mid, context.asset_out, mid_in, context.amount_out)
    return RouteQuote(
        asset_in=context.asset_in,
        asset_out=context.asset_out,
        amount_in=amount_in,
        amount_out=context.amount_out,
        legs=(RouteLeg(hops=(hop1, hop2), amount_in=amount_in, amount_out=context.amount_out),),
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
