"""
Deterministic swap routing (state-of-the-art, certifiable baseline).

We start with a **2-hop exact-in router**:
- Enumerate best direct swap.
- Enumerate best 2-hop swap via an intermediate asset.
- Optionally consider **1-hop split routing** across parallel pools (2 legs, 1 hop each).

Why 2-hop first?
- It captures most real routing wins in early DEX deployments.
- It is easy to certify: brute-force verification is cheap and deterministic.
- It provides a clean "Rust compute / Tau verify" boundary:
    Rust can compute a proposed route and per-hop quotes,
    Tau can verify per-hop constraints and path well-formedness.

Determinism:
- Ties are broken lexicographically by (hop_count, pool_id sequence, intermediate_asset).

Complexity:
- Time: O(P + D) where D is number of candidate 2-hop paths considered.
- Space: O(1) extra (besides input pools).
"""

from __future__ import annotations

from typing import Dict, Optional, Tuple, TypeAlias

from ..core.split_routing_dispatch import (
    best_split_many_pools_exact_in_for_pools,
    best_split_two_pools_exact_in_for_pools,
    best_split_two_pools_exact_out_for_pools,
)
from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from . import routing_common as _routing_common
from . import routing_exact_in as _routing_exact_in
from . import routing_exact_out as _routing_exact_out
from . import routing_exact_out_gate as _exact_out_gate
from . import routing_mixed_split as _routing_mixed_split
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .routing_types import RouteHop as RouteHop
from .routing_types import RouteLeg as RouteLeg
from .routing_types import RouteQuote
from .routing_types import quote_key as _quote_key

ExactOutTwoHopGateConfig: TypeAlias = _exact_out_gate.ExactOutTwoHopGateConfig
ExactOutTwoHopGateDecision: TypeAlias = _exact_out_gate.ExactOutTwoHopGateDecision
decide_exact_out_two_hop_gate = _exact_out_gate.decide_exact_out_two_hop_gate
should_consider_exact_out_two_hop = _exact_out_gate.should_consider_exact_out_two_hop
_pool_reserves_direction = _routing_common.pool_reserves_direction
_pool_connects = _routing_common.pool_connects
_build_asset_pool_index = _routing_common.build_asset_pool_index


def _pool_quote_exact_in(
    pool: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
) -> Optional[Tuple[Amount, str]]:
    return _routing_common.pool_quote_exact_in(
        pool,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        quote_exact_in=swap_exact_in_for_pool,
    )


def _pool_quote_exact_out(
    pool: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out: Amount,
) -> Optional[Tuple[Amount, str, Amount]]:
    return _routing_common.pool_quote_exact_out(
        pool,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out=amount_out,
        quote_exact_out=swap_exact_out_for_pool,
    )


def best_route_exact_in_2hop(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    split_search_profile: str = "adaptive_v6",
    enable_mixed_direct_twohop_split: bool = False,
) -> Optional[RouteQuote]:
    return _routing_exact_in.best_route_exact_in_2hop(
        request=_routing_exact_in.ExactInRouteRequest(
            pools_by_id=pools_by_id,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
            split_search_profile=split_search_profile,
            enable_mixed_direct_twohop_split=enable_mixed_direct_twohop_split,
        ),
        dependencies=_routing_exact_in.ExactInRouteDependencies(
            build_asset_pool_index=_build_asset_pool_index,
            pool_connects=_pool_connects,
            pool_quote_exact_in=_pool_quote_exact_in,
            quote_key=_quote_key,
            split_many_exact_in=best_split_many_pools_exact_in_for_pools,
            split_two_exact_in=best_split_two_pools_exact_in_for_pools,
            mixed_split_direct_vs_twohop=_best_split_direct_vs_twohop_exact_in,
        ),
    )


def _best_split_direct_vs_twohop_exact_in(
    *,
    request: _routing_exact_in.ExactInMixedSplitRequest,
) -> Optional[RouteQuote]:
    mixed_request = _routing_mixed_split.MixedSplitExactInRequest(
        direct_pool=request.direct_pool,
        hop1_pool=request.hop1_pool,
        hop2_pool=request.hop2_pool,
        asset_in=request.asset_in,
        mid=request.mid,
        asset_out=request.asset_out,
        quote_exact_in=_pool_quote_exact_in,
        reserves_direction=_pool_reserves_direction,
    )
    return _routing_mixed_split.best_split_direct_vs_twohop_exact_in_for_request(
        request=mixed_request,
        amount_in_total=request.amount_in_total,
        window=request.window,
        brute_force_max=request.brute_force_max,
    )


def best_route_exact_out_2hop(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out: Amount,
    apply_two_hop_gate: bool = False,
    gate_config: ExactOutTwoHopGateConfig | None = None,
) -> Optional[RouteQuote]:
    return _routing_exact_out.best_route_exact_out_2hop(
        request=_routing_exact_out.ExactOutRouteRequest(
            pools_by_id=pools_by_id,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out=amount_out,
            apply_two_hop_gate=apply_two_hop_gate,
            gate_config=gate_config,
        ),
        dependencies=_routing_exact_out.ExactOutRouteDependencies(
            build_asset_pool_index=_build_asset_pool_index,
            pool_connects=_pool_connects,
            pool_quote_exact_out=_pool_quote_exact_out,
            quote_key=_quote_key,
            should_consider_exact_out_two_hop=should_consider_exact_out_two_hop,
            split_two_pools_exact_out=best_split_two_pools_exact_out_for_pools,
        ),
    )
