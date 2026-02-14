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
from ..core.split_routing_dispatch import (
    best_split_many_pools_exact_in_for_pools,
    best_split_two_pools_exact_in_for_pools,
)
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


@dataclass(frozen=True)
class ExactOutTwoHopGateConfig:
    """
    Deterministic gate for deciding whether exact-out 2-hop evaluation should run.

    Policies:
    - "stress":          amount_out / direct_reserve_out >= stress_threshold
    - "pressure":        direct_amount_in / amount_out >= pressure_threshold
    - "stress_or_pressure": (stress condition) OR (pressure condition)
    """

    policy: str = "stress_or_pressure"
    stress_threshold: float = 0.4
    pressure_threshold: float = 1.6


@dataclass(frozen=True)
class ExactOutTwoHopGateDecision:
    consider_two_hop: bool
    stress: float
    pressure: float
    policy: str


def _normalize_exact_out_gate_policy(policy: str) -> str:
    p = str(policy).strip().lower()
    if p in {"stress", "pressure", "stress_or_pressure"}:
        return p
    raise ValueError(f"unsupported exact-out gate policy: {policy}")


def decide_exact_out_two_hop_gate(
    *,
    amount_out: Amount,
    direct_reserve_out: Amount,
    direct_amount_in: Amount,
    config: ExactOutTwoHopGateConfig | None = None,
) -> ExactOutTwoHopGateDecision:
    if amount_out <= 0:
        raise ValueError("amount_out must be positive")
    if direct_reserve_out <= 0:
        raise ValueError("direct_reserve_out must be positive")
    if direct_amount_in <= 0:
        raise ValueError("direct_amount_in must be positive")
    cfg = config or ExactOutTwoHopGateConfig()
    policy = _normalize_exact_out_gate_policy(cfg.policy)
    stress = float(amount_out) / float(direct_reserve_out)
    pressure = float(direct_amount_in) / float(amount_out)
    if policy == "stress":
        consider = bool(stress >= float(cfg.stress_threshold))
    elif policy == "pressure":
        consider = bool(pressure >= float(cfg.pressure_threshold))
    else:
        consider = bool(
            stress >= float(cfg.stress_threshold)
            or pressure >= float(cfg.pressure_threshold)
        )
    return ExactOutTwoHopGateDecision(
        consider_two_hop=consider,
        stress=stress,
        pressure=pressure,
        policy=policy,
    )


def should_consider_exact_out_two_hop(
    *,
    amount_out: Amount,
    direct_reserve_out: Amount,
    direct_amount_in: Amount,
    config: ExactOutTwoHopGateConfig | None = None,
) -> bool:
    return decide_exact_out_two_hop_gate(
        amount_out=amount_out,
        direct_reserve_out=direct_reserve_out,
        direct_amount_in=direct_amount_in,
        config=config,
    ).consider_two_hop


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


def _pool_connects(pool: PoolState, a: AssetId, b: AssetId) -> bool:
    return (a == pool.asset0 and b == pool.asset1) or (a == pool.asset1 and b == pool.asset0)


def _build_asset_pool_index(pools: Tuple[PoolState, ...]) -> Dict[AssetId, Tuple[int, ...]]:
    """
    Build deterministic asset -> pool-index adjacency for indexed routing scans.
    """
    temp: Dict[AssetId, List[int]] = {}
    for idx, pool in enumerate(pools):
        temp.setdefault(pool.asset0, []).append(idx)
        temp.setdefault(pool.asset1, []).append(idx)
    out: Dict[AssetId, Tuple[int, ...]] = {}
    for asset, indices in temp.items():
        indices.sort(key=lambda i: pools[i].pool_id)
        out[asset] = tuple(indices)
    return out


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
    split_search_profile: str = "baseline",
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
        except Exception:
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
