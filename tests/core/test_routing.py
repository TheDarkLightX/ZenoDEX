from __future__ import annotations

import pytest

import src.core.routing as routing_module
from src.core.routing import _pool_quote_exact_in, best_route_exact_in_2hop
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
    assert len(q.legs) == 1
    assert len(q.legs[0].hops) == 1
    assert q.legs[0].hops[0].pool_id == "p_ab"


def test_best_route_uses_2hop_when_better():
    # Direct A-B is shallow; A-C and C-B are deep.
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 0),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=10)
    assert q is not None
    assert len(q.legs) == 1
    assert len(q.legs[0].hops) == 2
    assert q.legs[0].hops[0].asset_in == "A"
    assert q.legs[0].hops[-1].asset_out == "B"


def test_tie_break_is_deterministic():
    # Two identical direct pools should tie; choose lexicographically by pool_id.
    pools = {
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=10)
    assert q is not None
    assert len(q.legs) == 1
    assert len(q.legs[0].hops) == 1
    assert q.legs[0].hops[0].pool_id == "p1"


def test_pool_quote_exact_in_suppresses_domain_reject(monkeypatch):
    pool = _pool("p_ab", "A", "B", 1000, 1000, 0)

    def _domain_reject(*_args, **_kwargs):
        raise ValueError("domain reject")

    monkeypatch.setattr(routing_module, "swap_exact_in_for_pool", _domain_reject)

    assert _pool_quote_exact_in(pool, asset_in="A", asset_out="B", amount_in=10) is None


def test_pool_quote_exact_in_propagates_programmer_error(monkeypatch):
    pool = _pool("p_ab", "A", "B", 1000, 1000, 0)

    def _programmer_error(*_args, **_kwargs):
        raise RuntimeError("unexpected bug")

    monkeypatch.setattr(routing_module, "swap_exact_in_for_pool", _programmer_error)

    with pytest.raises(RuntimeError, match="unexpected bug"):
        _pool_quote_exact_in(pool, asset_in="A", asset_out="B", amount_in=10)


def test_best_route_can_split_across_parallel_pools():
    # Two identical pools: splitting strictly improves output vs using only one pool.
    pools = {
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
    }
    single = best_route_exact_in_2hop(pools_by_id={"p1": pools["p1"]}, asset_in="A", asset_out="B", amount_in=500)
    assert single is not None
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=500)
    assert q is not None
    # Split route => 2 legs, each a direct hop.
    assert len(q.legs) == 2
    assert all(len(leg.hops) == 1 for leg in q.legs)
    assert q.amount_out > single.amount_out


def test_best_route_can_split_direct_plus_twohop_when_enabled():
    # Construct a small witness where neither pure direct nor pure 2-hop dominates,
    # but splitting across the disjoint legs strictly improves total output.
    #
    # Witness (fee=0, total_in=4):
    # - Direct A->B pool: x=y=2 yields out=1 for dx=4.
    # - 2-hop A->C->B pools: (2,2) then (2,3) also yields out=1 for dx=4.
    # - Split dx=2 direct + dx=2 twohop yields out=1+1=2.
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 2, 2, 0),
        "p_ac": _pool("p_ac", "A", "C", 2, 2, 0),
        "p_cb": _pool("p_cb", "C", "B", 2, 3, 0),
    }

    q_base = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=4)
    assert q_base is not None
    assert q_base.amount_out == 1

    q = best_route_exact_in_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=4,
        enable_mixed_direct_twohop_split=True,
    )
    assert q is not None
    assert q.amount_out == 2
    assert len(q.legs) == 2
    # One leg is a direct hop; the other is 2-hop.
    hop_counts = sorted(len(leg.hops) for leg in q.legs)
    assert hop_counts == [1, 2]


def test_mixed_direct_twohop_split_bva_amount_in_boundary() -> None:
    # BVA for the mixed-split feature on a fixed witness:
    # - Just below the smallest total where the split becomes feasible (D=3): should not split.
    # - Exactly at the first feasible total (D=4): should split and improve.
    # - Just above (D=5): should still split (improvement persists).
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 2, 2, 0),
        "p_ac": _pool("p_ac", "A", "C", 2, 2, 0),
        "p_cb": _pool("p_cb", "C", "B", 2, 3, 0),
    }

    q1 = best_route_exact_in_2hop(
        pools_by_id=pools, asset_in="A", asset_out="B", amount_in=1, enable_mixed_direct_twohop_split=True
    )
    assert q1 is None  # both legs are invalid at this size

    q3 = best_route_exact_in_2hop(
        pools_by_id=pools, asset_in="A", asset_out="B", amount_in=3, enable_mixed_direct_twohop_split=True
    )
    assert q3 is not None
    assert q3.amount_out == 1
    assert len(q3.legs) == 1  # split not feasible due to per-leg min-trade output=0 discontinuities

    q4 = best_route_exact_in_2hop(
        pools_by_id=pools, asset_in="A", asset_out="B", amount_in=4, enable_mixed_direct_twohop_split=True
    )
    assert q4 is not None
    assert q4.amount_out == 2
    assert len(q4.legs) == 2

    q5 = best_route_exact_in_2hop(
        pools_by_id=pools, asset_in="A", asset_out="B", amount_in=5, enable_mixed_direct_twohop_split=True
    )
    assert q5 is not None
    assert q5.amount_out >= 2
    assert len(q5.legs) == 2


def test_best_route_can_split_across_three_parallel_pools():
    pools = {
        "p3": _pool("p3", "A", "B", 1000, 1000, 0),
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
    }
    q3 = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=750)
    assert q3 is not None
    assert len(q3.legs) == 3

    # Best we can do with only two pools is strictly worse for CPMM (concavity).
    best2_out = -1
    pool_items = list(pools.items())
    for i in range(len(pool_items)):
        for j in range(i + 1, len(pool_items)):
            pid_i, pi = pool_items[i]
            pid_j, pj = pool_items[j]
            q2 = best_route_exact_in_2hop(
                pools_by_id={pid_i: pi, pid_j: pj}, asset_in="A", asset_out="B", amount_in=750
            )
            assert q2 is not None
            best2_out = max(best2_out, q2.amount_out)

    assert q3.amount_out > best2_out


def test_best_route_split_profile_dense_is_not_worse_than_baseline():
    # Counterexample-style pair where dense split probing should be at least as good as baseline probing.
    pools = {
        "p0": _pool("p0", "A", "B", 87, 80, 75),
        "p1": _pool("p1", "A", "B", 46, 66, 11),
    }
    q_base = best_route_exact_in_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=6539,
        split_search_profile="baseline",
    )
    q_dense = best_route_exact_in_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=6539,
        split_search_profile="dense24",
    )
    assert q_base is not None
    assert q_dense is not None
    assert q_dense.amount_out >= q_base.amount_out


def test_best_route_default_split_profile_matches_dense24_on_known_gap_case():
    # Known counterexample-style pair where baseline probing misses by 1 on large trades.
    #
    # We promote a safer UX default: use dense split probing unless explicitly overridden.
    pools = {
        "p0": _pool("p0", "A", "B", 87, 80, 75),
        "p1": _pool("p1", "A", "B", 46, 66, 11),
    }
    q_default = best_route_exact_in_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=6539,
    )
    q_dense = best_route_exact_in_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=6539,
        split_search_profile="dense24",
    )
    assert q_default is not None
    assert q_dense is not None
    assert q_default.amount_out == q_dense.amount_out
    assert q_default.amount_out == 143
