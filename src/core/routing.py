"""
Deterministic swap routing (state-of-the-art, certifiable baseline).

We start with a **2-hop exact-in router**:
- Enumerate best direct swap.
- Enumerate best 2-hop swap via an intermediate asset.

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
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from ..core.amm_dispatch import swap_exact_in_for_pool
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
class RouteQuote:
    asset_in: AssetId
    asset_out: AssetId
    amount_in: Amount
    amount_out: Amount
    hops: Tuple[RouteHop, ...]


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


def _quote_key(q: RouteQuote) -> Tuple[int, str, str, str]:
    # Prefer fewer hops, then lexicographic pool_id sequence, then mid asset (if any).
    hop_count = len(q.hops)
    pool_seq = ",".join(h.pool_id for h in q.hops)
    mid = q.hops[0].asset_out if hop_count == 2 else ""
    return (hop_count, pool_seq, mid, q.asset_out)


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
        q = RouteQuote(
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
            amount_out=amount_out,
            hops=(RouteHop(p.pool_id, asset_in, asset_out, amount_in, amount_out),),
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
            q = RouteQuote(
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=amount_in,
                amount_out=amt_out,
                hops=(
                    RouteHop(p1.pool_id, asset_in, mid, amount_in, amt_mid),
                    RouteHop(p2.pool_id, mid, asset_out, amt_mid, amt_out),
                ),
            )
            if best is None or (q.amount_out > best.amount_out) or (
                q.amount_out == best.amount_out and _quote_key(q) < _quote_key(best)
            ):
                best = q

    return best
