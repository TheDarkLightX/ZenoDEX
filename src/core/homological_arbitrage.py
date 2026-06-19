"""Homological arbitrage routing (salvage): exact marginal-arbitrage detection.

A prior ideation pass claimed you can "solve global arbitrage" by evaluating only
a cycle basis (Betti-1 generators). That strong claim is false for fee-bearing
AMM edges.

What *is* salvageable and high-ROI:
- Treat the DEX ecosystem as a graph.
- Use the *marginal (infinitesimal)* exchange rates implied by pools as directed
  edge weights.
- Detect any marginal-arbitrage opportunity as a directed cycle with product > 1.

This module implements a deterministic, exact (Fraction-based) marginal arbitrage
cycle detector for CPMM pools, returning a concrete cycle witness when one exists.

Important scope limits:
- Marginal only (dx -> 0). This is a diagnostic / candidate generator, not a
  size-aware router.
- CPMM only (other curves can be added once marginal-rate formulas are defined).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from ..state.balances import AssetId
from ..state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


@dataclass(frozen=True)
class MarginalEdge:
    pool_id: str
    asset_in: AssetId
    asset_out: AssetId
    rate: Fraction  # asset_out per 1 unit of asset_in (dx -> 0)


@dataclass(frozen=True)
class MarginalArbitrageCycle:
    """Cycle witness for marginal arbitrage (product of rates strictly > 1)."""

    edges: Tuple[MarginalEdge, ...]
    gain: Fraction

    def __post_init__(self) -> None:
        if not self.edges:
            raise ValueError("cycle must contain at least one edge")
        if self.gain <= 1:
            raise ValueError(f"cycle gain must be > 1, got {self.gain}")


def cpmm_marginal_rate(*, reserve_in: int, reserve_out: int, fee_bps: int) -> Fraction:
    """Exact marginal rate for CPMM (dx -> 0) as a rational number.

    For CPMM exact-in:
      out = reserve_out * net_in / (reserve_in + net_in)

    For infinitesimal dx, net_in ~= dx * (1 - fee), so:
      d(out)/d(dx) = (1 - fee) * reserve_out / reserve_in

    We represent (1 - fee) exactly as (10_000 - fee_bps) / 10_000.
    """
    if reserve_in <= 0 or reserve_out <= 0:
        raise ValueError("reserves must be positive for a finite marginal rate")
    if not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps must be in [0, 10000]: {fee_bps}")
    fee_mul_num = 10_000 - int(fee_bps)
    fee_mul_den = 10_000
    return Fraction(fee_mul_num * int(reserve_out), fee_mul_den * int(reserve_in))


def cpmm_pool_marginal_edge(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId) -> MarginalEdge:
    if pool.curve_tag != CURVE_TAG_CPMM:
        raise ValueError(f"unsupported curve_tag for marginal CPMM rate: {pool.curve_tag}")
    if pool.status != PoolStatus.ACTIVE:
        raise ValueError(f"pool is not ACTIVE: {pool.status}")
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        r_in, r_out = int(pool.reserve0), int(pool.reserve1)
    elif asset_in == pool.asset1 and asset_out == pool.asset0:
        r_in, r_out = int(pool.reserve1), int(pool.reserve0)
    else:
        raise ValueError(f"assets ({asset_in},{asset_out}) not in pool {pool.pool_id}")
    return MarginalEdge(
        pool_id=pool.pool_id,
        asset_in=asset_in,
        asset_out=asset_out,
        rate=cpmm_marginal_rate(reserve_in=r_in, reserve_out=r_out, fee_bps=int(pool.fee_bps)),
    )


def build_cpmm_marginal_edges(
    pools: Iterable[PoolState],
    *,
    only_active: bool = True,
) -> List[MarginalEdge]:
    edges: List[MarginalEdge] = []
    for p in pools:
        if p.curve_tag != CURVE_TAG_CPMM:
            continue
        if only_active and p.status != PoolStatus.ACTIVE:
            continue
        # Skip zero-reserve edges (undefined marginal rate).
        if int(p.reserve0) <= 0 or int(p.reserve1) <= 0:
            continue
        edges.append(cpmm_pool_marginal_edge(p, asset_in=p.asset0, asset_out=p.asset1))
        edges.append(cpmm_pool_marginal_edge(p, asset_in=p.asset1, asset_out=p.asset0))
    edges.sort(key=lambda e: (e.asset_in, e.asset_out, e.pool_id))
    return edges


def _canonicalize_cycle(edges: Tuple[MarginalEdge, ...]) -> Tuple[MarginalEdge, ...]:
    if len(edges) <= 1:
        return edges
    n = len(edges)
    # Choose lexicographically minimal rotation under (pool_id, asset_in, asset_out).
    def rot_key(rot: Sequence[MarginalEdge]) -> List[Tuple[str, AssetId, AssetId]]:
        return [(e.pool_id, e.asset_in, e.asset_out) for e in rot]

    best = edges
    best_key = rot_key(best)
    for i in range(1, n):
        r = edges[i:] + edges[:i]
        k = rot_key(r)
        if k < best_key:
            best = r
            best_key = k
    return best


def _predecessor_edge_key(edge: MarginalEdge) -> Tuple[str, AssetId, AssetId]:
    return edge.pool_id, edge.asset_in, edge.asset_out


def _relax_marginal_edges(
    *,
    edges_sorted: Sequence[MarginalEdge],
    best: Dict[AssetId, Fraction],
    pred: Dict[AssetId, Tuple[AssetId, MarginalEdge] | None],
) -> AssetId | None:
    improved: AssetId | None = None
    for edge in edges_sorted:
        asset_in, asset_out = edge.asset_in, edge.asset_out
        candidate = best[asset_in] * edge.rate
        current = best[asset_out]
        if candidate > current:
            best[asset_out] = candidate
            pred[asset_out] = (asset_in, edge)
            improved = asset_out
        elif candidate == current and pred[asset_out] is not None:
            _prev_asset, prev_edge = pred[asset_out]
            if _predecessor_edge_key(edge) < _predecessor_edge_key(prev_edge):
                pred[asset_out] = (asset_in, edge)
    return improved


def _rewind_into_cycle(
    *,
    start: AssetId,
    steps: int,
    pred: Dict[AssetId, Tuple[AssetId, MarginalEdge] | None],
) -> AssetId | None:
    current = start
    for _ in range(steps):
        predecessor = pred.get(current)
        if predecessor is None:
            return None
        current = predecessor[0]
    return current


def _collect_cycle_edges(
    *,
    start: AssetId,
    max_edges: int,
    pred: Dict[AssetId, Tuple[AssetId, MarginalEdge] | None],
) -> Tuple[MarginalEdge, ...] | None:
    cycle_edges_rev: List[MarginalEdge] = []
    current = start
    for _ in range(max_edges + 1):
        predecessor = pred.get(current)
        if predecessor is None:
            return None
        prev_asset, edge = predecessor
        cycle_edges_rev.append(edge)
        current = prev_asset
        if current == start:
            return tuple(reversed(cycle_edges_rev))
    return None


def _cycle_gain(edges: Sequence[MarginalEdge]) -> Fraction:
    gain = Fraction(1, 1)
    for edge in edges:
        gain *= edge.rate
    return gain


def find_marginal_arbitrage_cycle(edges: Sequence[MarginalEdge]) -> Optional[MarginalArbitrageCycle]:
    """Find any marginal-arbitrage cycle using multiplicative Bellman-Ford.

    Returns:
      None if no cycle with product(rate) > 1 exists.
      Otherwise returns a cycle witness with exact rational gain > 1.

    Determinism:
    - Edge iteration is sorted by (asset_in, asset_out, pool_id).
    - Ties on equal best[v] pick the lexicographically smallest predecessor edge.
    """
    if not edges:
        return None

    nodes = sorted({e.asset_in for e in edges} | {e.asset_out for e in edges})
    if not nodes:
        return None

    edges_sorted = sorted(edges, key=lambda e: (e.asset_in, e.asset_out, e.pool_id))

    best: Dict[AssetId, Fraction] = {n: Fraction(1, 1) for n in nodes}
    pred: Dict[AssetId, Tuple[AssetId, MarginalEdge] | None] = {n: None for n in nodes}

    improved: AssetId | None = None
    for _ in range(len(nodes)):
        improved = _relax_marginal_edges(edges_sorted=edges_sorted, best=best, pred=pred)
        if improved is None:
            return None

    # Improvement on the V-th iteration implies a profitable cycle exists.
    if improved is None:
        return None
    start = _rewind_into_cycle(start=improved, steps=len(nodes), pred=pred)
    if start is None:
        # Should not happen, but treat as inconclusive rather than claiming "no arb".
        return None

    cycle_edges = _collect_cycle_edges(start=start, max_edges=len(nodes), pred=pred)
    if cycle_edges is None:
        return None
    cycle_edges = _canonicalize_cycle(cycle_edges)

    gain = _cycle_gain(cycle_edges)
    if gain <= 1:
        # Defensive: if this happens, treat as inconclusive.
        return None
    return MarginalArbitrageCycle(edges=cycle_edges, gain=gain)


def find_cpmm_marginal_arbitrage_cycle(
    pools_by_id: Dict[str, PoolState],
    *,
    only_active: bool = True,
) -> Optional[MarginalArbitrageCycle]:
    edges = build_cpmm_marginal_edges(pools_by_id.values(), only_active=only_active)
    return find_marginal_arbitrage_cycle(edges)
