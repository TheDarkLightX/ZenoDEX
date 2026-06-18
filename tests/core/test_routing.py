from __future__ import annotations

import ast
from pathlib import Path
from typing import Any, cast

import pytest

import src.core.routing as routing
import src.core.routing_mixed_split as routing_mixed_split
import src.core.split_routing_dispatch as split_routing_dispatch
from src.core.routing import (
    best_route_exact_in_2hop,
    best_route_exact_out_2hop,
)
from src.core.routing_common import (
    pool_quote_exact_in,
    pool_quote_exact_out,
    pool_reserves_direction,
)
from src.integration.exact_in_route_certificate import (
    enumerate_route_candidates_exact_in_2hop,
    exact_in_route_canonical_key,
)
from src.state.pools import PoolState, PoolStatus


def test_routing_does_not_broadly_suppress_unexpected_exceptions() -> None:
    modules = (routing, split_routing_dispatch)
    broad_handlers: list[str] = []
    for module in modules:
        assert module.__file__ is not None
        tree = ast.parse(Path(module.__file__).read_text(encoding="utf-8"))
        broad_handlers.extend(
            f"{module.__name__}:{node.lineno}"
            for node in ast.walk(tree)
            if isinstance(node, ast.ExceptHandler)
            and isinstance(node.type, ast.Name)
            and node.type.id in {"Exception", "BaseException"}
        )
    assert broad_handlers == []


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


def test_best_route_propagates_unexpected_quote_errors(monkeypatch: pytest.MonkeyPatch) -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 0),
    }

    def _boom(*_args: object, **_kwargs: object) -> None:
        raise RuntimeError("unexpected quote bug")

    monkeypatch.setattr(routing, "swap_exact_in_for_pool", _boom)
    with pytest.raises(RuntimeError, match="unexpected quote bug"):
        best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=10)


def test_best_route_rejects_same_asset_round_trip_boundary():
    # A same-asset request must not be "helpfully" converted into a pool round trip.
    # That keeps quote search from inventing self-referential routes such as A->B->A.
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 0),
    }

    assert best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="A", amount_in=10) is None
    assert best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="A", amount_out=10) is None


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"amount_in": True}, "amount_in must be an int"),
        ({"amount_in": "10"}, "amount_in must be an int"),
        ({"amount_in": 10, "enable_mixed_direct_twohop_split": 1}, "enable_mixed_direct_twohop_split must be a bool"),
    ],
)
def test_best_route_exact_in_rejects_non_strict_entrypoint_controls(
    kwargs: dict[str, object],
    message: str,
) -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 0),
    }
    values: dict[str, object] = {"amount_in": 10}
    values.update(kwargs)

    with pytest.raises(ValueError, match=message):
        best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", **cast(Any, values))


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"amount_out": True}, "amount_out must be an int"),
        ({"amount_out": "10"}, "amount_out must be an int"),
        ({"amount_out": 10, "apply_two_hop_gate": 1}, "apply_two_hop_gate must be a bool"),
    ],
)
def test_best_route_exact_out_rejects_non_strict_entrypoint_controls(
    kwargs: dict[str, object],
    message: str,
) -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 0),
    }
    values: dict[str, object] = {"amount_out": 10}
    values.update(kwargs)

    with pytest.raises(ValueError, match=message):
        best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", **cast(Any, values))


def test_best_route_keeps_zero_amount_as_no_route() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 0),
    }

    assert best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=0) is None
    assert best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=0) is None


@pytest.mark.parametrize(
    ("quote", "kwargs", "message"),
    [
        (pool_quote_exact_in, {"amount_in": True}, "amount_in must be an int"),
        (pool_quote_exact_in, {"amount_in": "10"}, "amount_in must be an int"),
        (pool_quote_exact_out, {"amount_out": True}, "amount_out must be an int"),
        (pool_quote_exact_out, {"amount_out": "10"}, "amount_out must be an int"),
    ],
)
def test_routing_common_quote_helpers_reject_non_strict_amounts(
    quote,
    kwargs: dict[str, object],
    message: str,
) -> None:
    pool = _pool("p_ab", "A", "B", 1000, 1000, 0)

    with pytest.raises(ValueError, match=message):
        quote(pool, asset_in="A", asset_out="B", **kwargs)


def test_routing_common_quote_helpers_keep_zero_as_no_quote() -> None:
    pool = _pool("p_ab", "A", "B", 1000, 1000, 0)

    assert pool_quote_exact_in(pool, asset_in="A", asset_out="B", amount_in=0) is None
    assert pool_quote_exact_out(pool, asset_in="A", asset_out="B", amount_out=0) is None


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


def test_exact_in_split_domain_errors_are_suppressed(monkeypatch: pytest.MonkeyPatch) -> None:
    pools = {
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
    }

    def infeasible_candidate(*_args: object, **_kwargs: object) -> object:
        raise ValueError("domain-infeasible candidate")

    monkeypatch.setattr(routing, "best_split_many_pools_exact_in_for_pools", infeasible_candidate)

    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=50)
    assert q is not None
    assert q.amount_out > 0


def test_exact_in_split_runtime_errors_propagate(monkeypatch: pytest.MonkeyPatch) -> None:
    pools = {
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
    }

    def broken_candidate_generator(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("split generator bug")

    monkeypatch.setattr(routing, "best_split_many_pools_exact_in_for_pools", broken_candidate_generator)

    with pytest.raises(RuntimeError, match="split generator bug"):
        best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=50)


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


def test_mixed_direct_twohop_request_rejects_negative_search_bounds() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 2, 2, 0),
        "p_ac": _pool("p_ac", "A", "C", 2, 2, 0),
        "p_cb": _pool("p_cb", "C", "B", 2, 3, 0),
    }
    request = routing_mixed_split.MixedSplitExactInRequest(
        direct_pool=pools["p_ab"],
        hop1_pool=pools["p_ac"],
        hop2_pool=pools["p_cb"],
        asset_in="A",
        mid="C",
        asset_out="B",
        quote_exact_in=pool_quote_exact_in,
        reserves_direction=pool_reserves_direction,
    )

    with pytest.raises(ValueError, match="window/brute_force_max must be non-negative"):
        routing_mixed_split.best_split_direct_vs_twohop_exact_in_for_request(
            request=request,
            amount_in_total=4,
            window=-1,
        )
    with pytest.raises(ValueError, match="window/brute_force_max must be non-negative"):
        routing_mixed_split.best_split_direct_vs_twohop_exact_in_for_request(
            request=request,
            amount_in_total=4,
            brute_force_max=-1,
        )


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


def test_exact_in_route_selector_matches_minimum_canonical_key() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 800, 0),
        "p_ac": _pool("p_ac", "A", "C", 900, 900, 0),
        "p_cb": _pool("p_cb", "C", "B", 900, 900, 0),
        "p_ab2": _pool("p_ab2", "A", "B", 1000, 780, 0),
    }

    candidates = enumerate_route_candidates_exact_in_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=100,
        enable_mixed_direct_twohop_split=True,
    )
    assert candidates

    selected = min(candidates, key=exact_in_route_canonical_key)
    best = best_route_exact_in_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=100,
        enable_mixed_direct_twohop_split=True,
    )

    assert selected is not None
    assert best is not None
    assert selected == best
    assert selected == min(candidates, key=exact_in_route_canonical_key)
