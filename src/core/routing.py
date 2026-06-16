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

from ..core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from ..core.split_routing_dispatch import (
    best_split_many_pools_exact_in_for_pools,
    best_split_two_pools_exact_in_for_pools,
    best_split_two_pools_exact_out_for_pools,
)
from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from . import routing_exact_out_gate as _exact_out_gate
from .routing_types import RouteHop, RouteLeg, RouteQuote
from .routing_types import quote_key as _quote_key

ExactOutTwoHopGateConfig = _exact_out_gate.ExactOutTwoHopGateConfig
ExactOutTwoHopGateDecision = _exact_out_gate.ExactOutTwoHopGateDecision
decide_exact_out_two_hop_gate = _exact_out_gate.decide_exact_out_two_hop_gate
should_consider_exact_out_two_hop = _exact_out_gate.should_consider_exact_out_two_hop


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
    except ValueError:
        return None
    return amount_out, pool.pool_id


def _pool_quote_exact_out(
    pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_out: Amount
) -> Optional[Tuple[Amount, str, Amount]]:
    """
    Exact-out quote helper.

    Returns (amount_in, pool_id, direct_reserve_out) for this direction.
    """
    if amount_out <= 0:
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
        amount_in, _ = swap_exact_out_for_pool(pool, reserve_in=rin, reserve_out=rout, amount_out=amount_out)
    except ValueError:
        return None
    return amount_in, pool.pool_id, rout


def _pool_reserves_direction(
    pool: PoolState, *, asset_in: AssetId, asset_out: AssetId
) -> Optional[Tuple[int, int, int]]:
    """
    Return (reserve_in, reserve_out, fee_bps) for the requested direction, or None if unsupported/inactive.
    """
    if pool.status.value != "ACTIVE":
        return None
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1), int(pool.fee_bps)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0), int(pool.fee_bps)
    return None


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
    """
    Experimental: best split of exact-in input across two disjoint legs:
    - direct: asset_in -> asset_out (1 hop)
    - twohop: asset_in -> mid -> asset_out (2 hops)

    Goal: maximize total output for a fixed total input.

    Determinism:
    - Uses a fixed-center window search around a deterministic coarse grid seed (integer-only).
    - Tie-break: choose the smallest direct-leg input among maximizers (left-biased).
    - Legs are canonicalized by lexicographic pool-id sequence.
    """
    D = int(amount_in_total)
    if D <= 1:
        return None
    if window < 0 or brute_force_max < 0:
        raise ValueError("window/brute_force_max must be non-negative")

    # Quick direction support check (fail-closed).
    if (
        _pool_reserves_direction(direct_pool, asset_in=asset_in, asset_out=asset_out) is None
        or _pool_reserves_direction(hop1_pool, asset_in=asset_in, asset_out=mid) is None
        or _pool_reserves_direction(hop2_pool, asset_in=mid, asset_out=asset_out) is None
    ):
        return None

    def total_out(a: int) -> int | None:
        if not (0 <= a <= D):
            return None
        b = D - int(a)
        # Reject degenerate splits; router already considers pure direct and pure 2-hop legs.
        if a == 0 or b == 0:
            return None
        out_d = _pool_quote_exact_in(direct_pool, asset_in=asset_in, asset_out=asset_out, amount_in=int(a))
        if out_d is None:
            return None
        out1 = _pool_quote_exact_in(hop1_pool, asset_in=asset_in, asset_out=mid, amount_in=int(b))
        if out1 is None:
            return None
        amt_mid, _pid1 = out1
        out2 = _pool_quote_exact_in(hop2_pool, asset_in=mid, asset_out=asset_out, amount_in=int(amt_mid))
        if out2 is None:
            return None
        out_b, _pid2 = out2
        return int(out_d[0] + out_b)

    def scan_range(lo: int, hi: int) -> tuple[int, int] | None:
        if lo > hi:
            return None
        best_out: int | None = None
        best_a = int(lo)
        for a in range(int(lo), int(hi) + 1):
            tot = total_out(int(a))
            if tot is None:
                continue
            if best_out is None or int(tot) > int(best_out) or (int(tot) == int(best_out) and int(a) < int(best_a)):
                best_out = int(tot)
                best_a = int(a)
        return None if best_out is None else (int(best_out), int(best_a))

    # Brute force for small totals: exact maximizer + canonical left bias.
    if D <= int(brute_force_max):
        brute = scan_range(1, D - 1)
        if brute is None:
            return None
        best_out, best_a = brute
    else:
        # Deterministic coarse grid centers (integer-only).
        lo = 1
        hi = D - 1
        span = hi - lo
        grid_n = 16
        centers = {lo, hi, (lo + hi) // 2}
        if span > 0:
            for i in range(1, int(grid_n)):
                centers.add(lo + (span * int(i)) // int(grid_n))

        best_out = 0
        best_a = 1
        best_found = False
        for c in sorted(centers):
            r_lo = max(1, int(c) - int(window))
            r_hi = min(D - 1, int(c) + int(window))
            cand = scan_range(int(r_lo), int(r_hi))
            if cand is None:
                continue
            cand_out, cand_a = cand
            if (not best_found) or cand_out > best_out or (cand_out == best_out and cand_a < best_a):
                best_out, best_a = int(cand_out), int(cand_a)
                best_found = True
        if not best_found:
            return None

        # Canonicalize within a local plateau: pick the smallest `a` with equal best_out.
        a_c = int(best_a)
        while a_c > int(lo):
            prev = total_out(int(a_c) - 1)
            if prev is None or int(prev) != int(best_out):
                break
            a_c -= 1
        best_a = int(a_c)

    # Recompute the winning split and construct a route quote.
    b = int(D) - int(best_a)
    out_d = _pool_quote_exact_in(direct_pool, asset_in=asset_in, asset_out=asset_out, amount_in=int(best_a))
    out1 = _pool_quote_exact_in(hop1_pool, asset_in=asset_in, asset_out=mid, amount_in=int(b))
    if out_d is None or out1 is None:
        return None
    amt_out_d, _ = out_d
    amt_mid, _ = out1
    out2 = _pool_quote_exact_in(hop2_pool, asset_in=mid, asset_out=asset_out, amount_in=int(amt_mid))
    if out2 is None:
        return None
    amt_out_b, _ = out2

    hop_d = RouteHop(direct_pool.pool_id, asset_in, asset_out, int(best_a), int(amt_out_d))
    hop1 = RouteHop(hop1_pool.pool_id, asset_in, mid, int(b), int(amt_mid))
    hop2 = RouteHop(hop2_pool.pool_id, mid, asset_out, int(amt_mid), int(amt_out_b))
    leg_d = RouteLeg(hops=(hop_d,), amount_in=int(best_a), amount_out=int(amt_out_d))
    leg_2 = RouteLeg(hops=(hop1, hop2), amount_in=int(b), amount_out=int(amt_out_b))

    # Canonicalize leg ordering for deterministic quote keys.
    legs = [leg_d, leg_2]
    legs.sort(key=lambda leg: ",".join(h.pool_id for h in leg.hops))
    total_out_amt = int(amt_out_d + amt_out_b)
    return RouteQuote(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=int(D),
        amount_out=total_out_amt,
        legs=tuple(legs),
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
