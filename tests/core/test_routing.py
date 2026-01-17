from __future__ import annotations

from src.core.routing import best_route_exact_in_2hop
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


def test_best_route_picks_direct_if_best():
    # A-B direct pool is very good; A-C-B path is worse.
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 10, 0),
        "p_cb": _pool("p_cb", "C", "B", 10, 1000, 0),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=10)
    assert q is not None
    assert len(q.hops) == 1
    assert q.hops[0].pool_id == "p_ab"


def test_best_route_uses_2hop_when_better():
    # Direct A-B is shallow; A-C and C-B are deep.
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 0),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=10)
    assert q is not None
    assert len(q.hops) == 2
    assert q.hops[0].asset_in == "A"
    assert q.hops[-1].asset_out == "B"


def test_tie_break_is_deterministic():
    # Two identical direct pools should tie; choose lexicographically by pool_id.
    pools = {
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=10)
    assert q is not None
    assert len(q.hops) == 1
    assert q.hops[0].pool_id == "p1"

