from __future__ import annotations

from src.kernels.python.exact_out_many_pool_repaired_prefilter_v1 import (
    build_many_pool_repaired_prefilter_selection,
    select_many_pool_repaired_prefilter_candidates,
)
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


def _pool(*, pid: str, r0: int, r1: int) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0="A",
        asset1="B",
        reserve0=int(r0),
        reserve1=int(r1),
        fee_bps=0,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
        curve_params=None,
    )


def test_repaired_prefilter_selects_repaired_subset_on_mixed_pool_counterexample() -> None:
    pools = (
        _pool(pid="p0", r0=20, r1=10),
        _pool(pid="p1", r0=20, r1=10),
        _pool(pid="p2", r0=30, r1=15),
        _pool(pid="p3", r0=30, r1=15),
    )

    selection = build_many_pool_repaired_prefilter_selection(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    selected_pools = select_many_pool_repaired_prefilter_candidates(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    assert selection.strategy == "bounded_cover_search"
    assert selection.current_selected_pool_ids == ("p0", "p2", "p3")
    assert selection.selected_pool_ids == ("p0", "p1")
    assert tuple(pool.pool_id for pool in selected_pools) == ("p0", "p1")


def test_repaired_prefilter_can_shrink_already_good_domain() -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
        _pool(pid="pool_c", r0=40, r1=20),
    )

    selection = build_many_pool_repaired_prefilter_selection(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=8_000,
    )

    assert selection.strategy == "bounded_cover_search"
    assert selection.current_selected_pool_ids == ("pool_a", "pool_b", "pool_c")
    assert selection.selected_pool_ids == ("pool_b",)
