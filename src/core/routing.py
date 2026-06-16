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

from typing import Dict, List, Optional, Tuple

from ..core.split_routing_dispatch import (
    best_split_many_pools_exact_in_for_pools,
    best_split_two_pools_exact_in_for_pools,
    best_split_two_pools_exact_out_for_pools,
)
from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from . import routing_common as _routing_common
from . import routing_exact_out_gate as _exact_out_gate
from . import routing_mixed_split as _routing_mixed_split
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .routing_types import RouteHop, RouteLeg, RouteQuote
from .routing_types import quote_key as _quote_key

ExactOutTwoHopGateConfig = _exact_out_gate.ExactOutTwoHopGateConfig
ExactOutTwoHopGateDecision = _exact_out_gate.ExactOutTwoHopGateDecision
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
    """
    Compute the best exact-in route up to 2 hops.

    Returns a RouteQuote including per-hop amounts.
    """
    if amount_in <= 0:
        return None
    if asset_in == asset_out:
        return None

    # Deterministic indexed representation (array backend).
    pools: Tuple[PoolState, ...] = tuple(sorted(pools_by_id.values(), key=lambda p: p.pool_id))
    by_asset: Dict[AssetId, Tuple[int, ...]] = _build_asset_pool_index(pools)

    best: Optional[RouteQuote] = None
    best_direct_1hop: Optional[RouteQuote] = None
    # Keep top-K 2-hop candidates by full-amount quote for optional mixed splitting.
    twohop_candidates: List[Tuple[RouteQuote, PoolState, PoolState, AssetId]] = []

    # 1-hop candidates
    for idx in by_asset.get(asset_in, ()):
        p = pools[idx]
        if not _pool_connects(p, asset_in, asset_out):
            continue
        out = _pool_quote_exact_in(p, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in)
        if out is None:
            continue
        amount_out, _pid = out
        hop = RouteHop(p.pool_id, asset_in, asset_out, amount_in, amount_out)
        q = RouteQuote(
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
            amount_out=amount_out,
            legs=(RouteLeg(hops=(hop,), amount_in=amount_in, amount_out=amount_out),),
        )
        if best is None or (q.amount_out > best.amount_out) or (
            q.amount_out == best.amount_out and _quote_key(q) < _quote_key(best)
        ):
            best = q
        if best_direct_1hop is None or (q.amount_out > best_direct_1hop.amount_out) or (
            q.amount_out == best_direct_1hop.amount_out and _quote_key(q) < _quote_key(best_direct_1hop)
        ):
            best_direct_1hop = q

    # 2-hop candidates: asset_in -> mid -> asset_out
    # Enumerate mid assets implicitly by enumerating first-hop pools connected to asset_in.
    for idx1 in by_asset.get(asset_in, ()):
        p1 = pools[idx1]
        # p1 must connect asset_in to some mid
        if asset_in == p1.asset0:
            mid = p1.asset1
        elif asset_in == p1.asset1:
            mid = p1.asset0
        else:
            continue
        if mid == asset_out or mid == asset_in:
            continue
        out1 = _pool_quote_exact_in(p1, asset_in=asset_in, asset_out=mid, amount_in=amount_in)
        if out1 is None:
            continue
        amt_mid, _ = out1
        # second hop pools that connect mid to asset_out
        for idx2 in by_asset.get(mid, ()):
            p2 = pools[idx2]
            out2 = _pool_quote_exact_in(p2, asset_in=mid, asset_out=asset_out, amount_in=amt_mid)
            if out2 is None:
                continue
            amt_out, _ = out2
            hop1 = RouteHop(p1.pool_id, asset_in, mid, amount_in, amt_mid)
            hop2 = RouteHop(p2.pool_id, mid, asset_out, amt_mid, amt_out)
            q = RouteQuote(
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=amount_in,
                amount_out=amt_out,
                legs=(RouteLeg(hops=(hop1, hop2), amount_in=amount_in, amount_out=amt_out),),
            )
            if best is None or (q.amount_out > best.amount_out) or (
                q.amount_out == best.amount_out and _quote_key(q) < _quote_key(best)
            ):
                best = q
            twohop_candidates.append((q, p1, p2, mid))

    # 1-hop split routing across parallel pools (N legs).
    direct_pools: List[Tuple[Amount, PoolState]] = []
    for idx in by_asset.get(asset_in, ()):
        p = pools[idx]
        if not _pool_connects(p, asset_in, asset_out):
            continue
        out = _pool_quote_exact_in(p, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in)
        if out is None:
            continue
        amount_out, _ = out
        direct_pools.append((amount_out, p))

    if len(direct_pools) >= 2:
        direct_pools.sort(key=lambda t: (-int(t[0]), t[1].pool_id))
        # Limit split search to the best K pools by single-pool quote.
        k = min(16, len(direct_pools))
        candidates = [p for _out, p in direct_pools[:k]]

        # N-way split (bounded legs).
        try:
            splitN = best_split_many_pools_exact_in_for_pools(
                candidates,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in_total=amount_in,
                max_legs=4,
                max_candidates=k,
                max_iters=4096,
            )
        except ValueError:
            splitN = None
        if splitN is not None and splitN.amount_out_total > 0:
            legs: List[RouteLeg] = []
            for leg in splitN.legs:
                legs.append(
                    RouteLeg(
                        hops=(RouteHop(leg.pool_id, asset_in, asset_out, leg.amount_in, leg.amount_out),),
                        amount_in=leg.amount_in,
                        amount_out=leg.amount_out,
                    )
                )
            q = RouteQuote(
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=amount_in,
                amount_out=splitN.amount_out_total,
                legs=tuple(legs),
            )
            if best is None or (q.amount_out > best.amount_out) or (
                q.amount_out == best.amount_out and _quote_key(q) < _quote_key(best)
            ):
                best = q

        # 2-way split pair search (strong baseline on small K).
        k2 = min(12, k)
        candidates2 = candidates[:k2]
        for i in range(k2):
            for j in range(i + 1, k2):
                p0 = candidates2[i]
                p1 = candidates2[j]
                try:
                    split = best_split_two_pools_exact_in_for_pools(
                        p0,
                        p1,
                        asset_in=asset_in,
                        asset_out=asset_out,
                        amount_in_total=amount_in,
                        search_profile=str(split_search_profile),
                    )
                except ValueError:
                    continue
                if split.amount_out_total <= 0:
                    continue
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
                q = RouteQuote(
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=amount_in,
                    amount_out=split.amount_out_total,
                    legs=(leg0, leg1),
                )
                if best is None or (q.amount_out > best.amount_out) or (
                    q.amount_out == best.amount_out and _quote_key(q) < _quote_key(best)
                ):
                    best = q

    # Optional mixed split: direct (1-hop) + one 2-hop route (disjoint pools) for exact-in.
    #
    # This is deliberately behind a flag because it increases quote cost. It is useful when:
    # - the best direct pool and the best 2-hop route each dominate in different size regimes, and
    # - splitting captures both concave frontiers.
    if enable_mixed_direct_twohop_split and best_direct_1hop is not None and twohop_candidates:
        # Choose a canonical direct pool id from best_direct_1hop (it is a single hop).
        direct_pool_id = best_direct_1hop.legs[0].hops[0].pool_id
        direct_pool = pools_by_id.get(direct_pool_id)
        if direct_pool is not None:
            # Deterministic cap: consider only the top-K 2-hop routes by full-amount quote.
            twohop_candidates.sort(key=lambda t: (-int(t[0].amount_out), _quote_key(t[0])))
            K = min(4, len(twohop_candidates))
            for _q2, p1, p2, mid in twohop_candidates[:K]:
                mixed = _best_split_direct_vs_twohop_exact_in(
                    direct_pool=direct_pool,
                    hop1_pool=p1,
                    hop2_pool=p2,
                    asset_in=asset_in,
                    mid=mid,
                    asset_out=asset_out,
                    amount_in_total=amount_in,
                )
                if mixed is None:
                    continue
                if best is None or (mixed.amount_out > best.amount_out) or (
                    mixed.amount_out == best.amount_out and _quote_key(mixed) < _quote_key(best)
                ):
                    best = mixed

    return best


def _best_split_direct_vs_twohop_exact_in(
    *,
    direct_pool: PoolState,
    hop1_pool: PoolState,
    hop2_pool: PoolState,
    asset_in: AssetId,
    mid: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
    window: int = 64,
    brute_force_max: int = 512,
) -> Optional[RouteQuote]:
    return _routing_mixed_split.best_split_direct_vs_twohop_exact_in(
        direct_pool=direct_pool,
        hop1_pool=hop1_pool,
        hop2_pool=hop2_pool,
        asset_in=asset_in,
        mid=mid,
        asset_out=asset_out,
        amount_in_total=amount_in_total,
        quote_exact_in=_pool_quote_exact_in,
        reserves_direction=_pool_reserves_direction,
        window=window,
        brute_force_max=brute_force_max,
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
    """
    Compute the best exact-out route up to 2 hops (min input for desired output).

    If apply_two_hop_gate=True, use `should_consider_exact_out_two_hop` to decide whether to
    consider 2-hop candidates, based on the best direct pool quote.
    """
    if amount_out <= 0:
        return None
    if asset_in == asset_out:
        return None

    pools: Tuple[PoolState, ...] = tuple(sorted(pools_by_id.values(), key=lambda p: p.pool_id))
    by_asset: Dict[AssetId, Tuple[int, ...]] = _build_asset_pool_index(pools)

    best_direct: Optional[RouteQuote] = None
    best_direct_reserve_out: Amount | None = None
    best_direct_fee_bps: int | None = None
    direct_candidates: List[PoolState] = []

    # 1-hop candidates (direct pools).
    for idx in by_asset.get(asset_in, ()):
        p = pools[idx]
        if not _pool_connects(p, asset_in, asset_out):
            continue
        direct_candidates.append(p)
        out = _pool_quote_exact_out(p, asset_in=asset_in, asset_out=asset_out, amount_out=amount_out)
        if out is None:
            continue
        amt_in, _pid, rout = out
        hop = RouteHop(p.pool_id, asset_in, asset_out, amt_in, amount_out)
        q = RouteQuote(
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amt_in,
            amount_out=amount_out,
            legs=(RouteLeg(hops=(hop,), amount_in=amt_in, amount_out=amount_out),),
        )
        if best_direct is None or (q.amount_in < best_direct.amount_in) or (
            q.amount_in == best_direct.amount_in and _quote_key(q) < _quote_key(best_direct)
        ):
            best_direct = q
            best_direct_reserve_out = rout
            best_direct_fee_bps = int(p.fee_bps)

    consider_two_hop = True
    if apply_two_hop_gate and best_direct is not None and best_direct_reserve_out is not None:
        consider_two_hop = should_consider_exact_out_two_hop(
            amount_out=amount_out,
            direct_reserve_out=int(best_direct_reserve_out),
            direct_amount_in=int(best_direct.amount_in),
            direct_fee_bps=int(best_direct_fee_bps or 0),
            config=gate_config,
        )

    best: Optional[RouteQuote] = best_direct

    # Split exact-out across parallel pools (2 legs, 1 hop each).
    #
    # Note: we consider pools even if they cannot individually satisfy the full amount_out; splitting can still be feasible.
    if len(direct_candidates) >= 2:
        # Deterministic cap: avoid O(k^2) blowups when many direct pools exist for the same pair.
        MAX_SPLIT_CANDIDATES = 8
        if len(direct_candidates) > MAX_SPLIT_CANDIDATES:
            def _direct_rout(p: PoolState) -> int:
                if asset_in == p.asset0 and asset_out == p.asset1:
                    return int(p.reserve1)
                if asset_in == p.asset1 and asset_out == p.asset0:
                    return int(p.reserve0)
                return 0

            direct_candidates = sorted(
                direct_candidates,
                key=lambda p: (-_direct_rout(p), p.pool_id),
            )[:MAX_SPLIT_CANDIDATES]
            direct_candidates.sort(key=lambda p: p.pool_id)

        for i in range(len(direct_candidates)):
            for j in range(i + 1, len(direct_candidates)):
                p0 = direct_candidates[i]
                p1 = direct_candidates[j]
                try:
                    split = best_split_two_pools_exact_out_for_pools(
                        p0,
                        p1,
                        asset_in=asset_in,
                        asset_out=asset_out,
                        amount_out_total=amount_out,
                    )
                except ValueError:
                    continue
                if split.amount_in_total <= 0:
                    continue
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
                q = RouteQuote(
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=split.amount_in_total,
                    amount_out=amount_out,
                    legs=(leg0, leg1),
                )
                if best is None or (q.amount_in < best.amount_in) or (
                    q.amount_in == best.amount_in and _quote_key(q) < _quote_key(best)
                ):
                    best = q

    if consider_two_hop:
        # 2-hop candidates: asset_in -> mid -> asset_out
        for idx1 in by_asset.get(asset_in, ()):
            p1 = pools[idx1]
            if asset_in == p1.asset0:
                mid = p1.asset1
            elif asset_in == p1.asset1:
                mid = p1.asset0
            else:
                continue
            if mid == asset_out or mid == asset_in:
                continue

            for idx2 in by_asset.get(mid, ()):
                p2 = pools[idx2]
                if not _pool_connects(p2, mid, asset_out):
                    continue

                out2 = _pool_quote_exact_out(p2, asset_in=mid, asset_out=asset_out, amount_out=amount_out)
                if out2 is None:
                    continue
                mid_in, _pid2, _rout2 = out2

                out1 = _pool_quote_exact_out(p1, asset_in=asset_in, asset_out=mid, amount_out=mid_in)
                if out1 is None:
                    continue
                amt_in, _pid1, _rout1 = out1

                hop1 = RouteHop(p1.pool_id, asset_in, mid, amt_in, mid_in)
                hop2 = RouteHop(p2.pool_id, mid, asset_out, mid_in, amount_out)
                q = RouteQuote(
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=amt_in,
                    amount_out=amount_out,
                    legs=(RouteLeg(hops=(hop1, hop2), amount_in=amt_in, amount_out=amount_out),),
                )
                if best is None or (q.amount_in < best.amount_in) or (
                    q.amount_in == best.amount_in and _quote_key(q) < _quote_key(best)
                ):
                    best = q

    return best
