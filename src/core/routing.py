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

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from ..core.amm_dispatch import swap_exact_in_for_pool
from ..core.split_routing_dispatch import best_split_two_pools_exact_in_for_pools
from ..state.balances import Amount, AssetId
from ..state.pools import PoolState


@dataclass(frozen=True)
class RouteHop:
    pool_id: str
    asset_in: AssetId
    asset_out: AssetId
    amount_in: Amount
    amount_out: Amount


@dataclass(frozen=True)
class RouteLeg:
    hops: Tuple[RouteHop, ...]
    amount_in: Amount
    amount_out: Amount


@dataclass(frozen=True)
class RouteQuote:
    asset_in: AssetId
    asset_out: AssetId
    amount_in: Amount
    amount_out: Amount
    legs: Tuple[RouteLeg, ...]


def _pool_quote_exact_in(
    pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_in: Amount
) -> Optional[Tuple[Amount, str]]:
    if amount_in <= 0:
        return None
    if pool.status.value != "ACTIVE":
        return None
    # Determine reserves direction.
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        rin, rout = pool.reserve0, pool.reserve1
    elif asset_in == pool.asset1 and asset_out == pool.asset0:
        rin, rout = pool.reserve1, pool.reserve0
    else:
        return None
    try:
        amount_out, _ = swap_exact_in_for_pool(pool, reserve_in=rin, reserve_out=rout, amount_in=amount_in)
    except Exception:
        return None
    return amount_out, pool.pool_id


def _quote_key(q: RouteQuote) -> Tuple[int, int, str, str, str]:
    # Prefer fewer sequential hops, then fewer legs, then lexicographic pool_id sequence.
    hop_count = sum(len(leg.hops) for leg in q.legs)
    leg_count = len(q.legs)
    pool_seq = ";".join(",".join(h.pool_id for h in leg.hops) for leg in q.legs)
    mid = ""
    if leg_count == 1 and hop_count == 2:
        mid = q.legs[0].hops[0].asset_out
    return (int(hop_count), int(leg_count), pool_seq, mid, q.asset_out)


def best_route_exact_in_2hop(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
) -> Optional[RouteQuote]:
    """
    Compute the best exact-in route up to 2 hops.

    Returns a RouteQuote including per-hop amounts.
    """
    if amount_in <= 0:
        return None
    if asset_in == asset_out:
        return None

    pools: List[PoolState] = list(pools_by_id.values())

    best: Optional[RouteQuote] = None

    # 1-hop candidates
    for p in pools:
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

    # 2-hop candidates: asset_in -> mid -> asset_out
    # Enumerate mid assets implicitly by enumerating first-hop pools connected to asset_in.
    for p1 in pools:
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
        for p2 in pools:
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

    # 1-hop split routing across parallel pools (2 legs).
    direct_pools: List[Tuple[Amount, PoolState]] = []
    for p in pools:
        out = _pool_quote_exact_in(p, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in)
        if out is None:
            continue
        amount_out, _ = out
        direct_pools.append((amount_out, p))

    if len(direct_pools) >= 2:
        direct_pools.sort(key=lambda t: (-int(t[0]), t[1].pool_id))
        # Limit pair enumeration to the best K pools by single-pool quote.
        k = min(12, len(direct_pools))
        candidates = [p for _out, p in direct_pools[:k]]
        for i in range(k):
            for j in range(i + 1, k):
                p0 = candidates[i]
                p1 = candidates[j]
                try:
                    split = best_split_two_pools_exact_in_for_pools(
                        p0,
                        p1,
                        asset_in=asset_in,
                        asset_out=asset_out,
                        amount_in_total=amount_in,
                    )
                except Exception:
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

    return best
