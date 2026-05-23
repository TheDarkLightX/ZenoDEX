from __future__ import annotations

from fractions import Fraction

import pytest

from src.core.homological_arbitrage import (
    cpmm_marginal_rate,
    find_cpmm_marginal_arbitrage_cycle,
)
from src.state.pools import PoolState, PoolStatus


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _pool_rate(p: PoolState, a_in: str, a_out: str) -> Fraction:
    if a_in == p.asset0 and a_out == p.asset1:
        r_in, r_out = p.reserve0, p.reserve1
    elif a_in == p.asset1 and a_out == p.asset0:
        r_in, r_out = p.reserve1, p.reserve0
    else:
        raise ValueError("assets not in pool")
    return cpmm_marginal_rate(reserve_in=int(r_in), reserve_out=int(r_out), fee_bps=int(p.fee_bps))


def _basis_only_fundamental_cycles_profitable(
    *,
    pools_by_id: dict[str, PoolState],
    tree_pool_ids: set[str],
) -> bool:
    """Model the (false) claim: only check a chosen cycle basis (fundamental cycles)."""

    # Build tree adjacency using the provided spanning tree pool IDs.
    adj: dict[str, list[tuple[str, str]]] = {}
    for pid in tree_pool_ids:
        p = pools_by_id[pid]
        adj.setdefault(p.asset0, []).append((p.asset1, pid))
        adj.setdefault(p.asset1, []).append((p.asset0, pid))

    def find_tree_path(start: str, goal: str) -> list[tuple[str, str, str]]:
        # BFS in a tree/forest (deterministic by lex neighbor order).
        if start == goal:
            return []
        from collections import deque

        q = deque([start])
        prev: dict[str, tuple[str, str] | None] = {start: None}  # node -> (parent, pool_id)
        while q:
            u = q.popleft()
            for v, pid in sorted(adj.get(u, []), key=lambda t: (t[0], t[1])):
                if v in prev:
                    continue
                prev[v] = (u, pid)
                if v == goal:
                    q.clear()
                    break
                q.append(v)
        if goal not in prev:
            raise ValueError("tree path not found (forest disconnected)")

        path: list[tuple[str, str, str]] = []
        cur = goal
        while cur != start:
            pu = prev[cur]
            assert pu is not None
            parent, pid = pu
            # edge from parent -> cur uses pid
            path.append((parent, cur, pid))
            cur = parent
        path.reverse()
        return path

    # For each non-tree edge, evaluate the two fundamental cycle orientations.
    for pid, chord in sorted(pools_by_id.items(), key=lambda kv: kv[0]):
        if pid in tree_pool_ids:
            continue
        u, v = chord.asset0, chord.asset1
        path = find_tree_path(u, v)

        # Orientation 1: u -> ... -> v, then v -> u (chord reversed)
        gain1 = Fraction(1, 1)
        for a, b, ppid in path:
            gain1 *= _pool_rate(pools_by_id[ppid], a, b)
        gain1 *= _pool_rate(chord, v, u)

        # Orientation 2: v -> ... -> u, then u -> v (chord forward)
        gain2 = Fraction(1, 1)
        for a, b, ppid in reversed([(a, b, ppid) for (a, b, ppid) in path]):
            # reverse the tree path direction
            gain2 *= _pool_rate(pools_by_id[ppid], b, a)
        gain2 *= _pool_rate(chord, u, v)

        if gain1 > 1 or gain2 > 1:
            return True
    return False


def test_cpmm_marginal_rate_bva_boundaries() -> None:
    # BVA: reserves
    with pytest.raises(ValueError):
        cpmm_marginal_rate(reserve_in=0, reserve_out=1, fee_bps=0)
    with pytest.raises(ValueError):
        cpmm_marginal_rate(reserve_in=1, reserve_out=0, fee_bps=0)
    with pytest.raises(ValueError):
        cpmm_marginal_rate(reserve_in=-1, reserve_out=1, fee_bps=0)

    # BVA: fee_bps
    with pytest.raises(ValueError):
        cpmm_marginal_rate(reserve_in=1, reserve_out=1, fee_bps=-1)
    assert cpmm_marginal_rate(reserve_in=1, reserve_out=1, fee_bps=0) == Fraction(1, 1)
    assert cpmm_marginal_rate(reserve_in=1, reserve_out=1, fee_bps=1) == Fraction(9999, 10_000)
    assert cpmm_marginal_rate(reserve_in=1, reserve_out=1, fee_bps=9999) == Fraction(1, 10_000)
    assert cpmm_marginal_rate(reserve_in=1, reserve_out=1, fee_bps=10_000) == Fraction(0, 1)
    with pytest.raises(ValueError):
        cpmm_marginal_rate(reserve_in=1, reserve_out=1, fee_bps=10_001)


def test_homological_basis_only_strong_claim_is_falsified() -> None:
    # Counterexample to the strong claim:
    # "Only checking a cycle basis (fundamental loops) is sufficient to find all arbitrage."
    #
    # Construct a 4-node, 5-edge graph with two independent cycles. Choose a spanning tree
    # that forces both basis cycles to include a high-fee edge (so both basis cycles are
    # unprofitable), while a different simple cycle avoids that edge and is profitable.
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 100, 100, 0),  # A->B rate 1
        "p_bc": _pool("p_bc", "B", "C", 100, 100, 9000),  # fee factor 0.1 => heavy loss
        "p_cd": _pool("p_cd", "C", "D", 100, 100, 0),  # C<->D rate 1
        "p_ac": _pool("p_ac", "A", "C", 100, 200, 0),  # A->C rate 2, C->A rate 1/2
        "p_bd": _pool("p_bd", "B", "D", 100, 400, 0),  # B->D rate 4, D->B rate 1/4
    }
    tree = {"p_ab", "p_bc", "p_cd"}
    assert _basis_only_fundamental_cycles_profitable(pools_by_id=pools, tree_pool_ids=tree) is False

    cyc = find_cpmm_marginal_arbitrage_cycle(pools_by_id=pools)
    assert cyc is not None
    assert cyc.gain == Fraction(2, 1)
    # Expected profitable cycle: A->B (p_ab), B->D (p_bd), D->C (p_cd), C->A (p_ac)
    assert [(e.pool_id, e.asset_in, e.asset_out) for e in cyc.edges] == [
        ("p_ab", "A", "B"),
        ("p_bd", "B", "D"),
        ("p_cd", "D", "C"),
        ("p_ac", "C", "A"),
    ]


def test_marginal_arbitrage_detector_finds_triangle_cycle_when_present() -> None:
    # Triangle with marginal gain > 1:
    # A->B = 2, B->C = 2, C->A = 2/5 => gain = 8/5.
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 100, 200, 0),
        "p_bc": _pool("p_bc", "B", "C", 100, 200, 0),
        "p_ac": _pool("p_ac", "A", "C", 100, 250, 0),
    }
    cyc = find_cpmm_marginal_arbitrage_cycle(pools_by_id=pools)
    assert cyc is not None
    assert cyc.gain == Fraction(8, 5)
    assert [(e.pool_id, e.asset_in, e.asset_out) for e in cyc.edges] == [
        ("p_ab", "A", "B"),
        ("p_bc", "B", "C"),
        ("p_ac", "C", "A"),
    ]


def test_marginal_arbitrage_detector_handles_zero_reserve_pools_fail_closed() -> None:
    # BVA: reserve just below/at/above the "finite marginal rate" boundary.
    pools = {
        "p_ab0": _pool("p_ab0", "A", "B", 0, 10, 0),  # invalid marginal rate, should be skipped
        "p_ab1": _pool("p_ab1", "A", "B", 1, 10, 0),  # valid
    }
    cyc = find_cpmm_marginal_arbitrage_cycle(pools_by_id=pools)
    assert cyc is None

