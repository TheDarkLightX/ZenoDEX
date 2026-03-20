from __future__ import annotations

from src.kernels.python.exact_out_many_pool_prefilter_contraction_audit_v1 import (
    audit_exact_out_many_pool_prefilter_contraction,
    audit_exact_out_many_pool_selected_subset_contraction,
)
from src.kernels.python.exact_out_many_pool_prefilter_subset_search_v1 import (
    select_many_pool_cover_search_candidates,
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


def test_prefilter_contraction_audit_accepts_identical_pool_witness() -> None:
    pools = tuple(_pool(pid=f"p{i}", r0=40, r1=20) for i in range(4))

    audit = audit_exact_out_many_pool_prefilter_contraction(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=2,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=10_000,
    )

    assert audit.feasible_pool_ids == ("p0", "p1", "p2", "p3")
    assert audit.selected_pool_ids == ("p0", "p1", "p2")
    assert audit.contraction_holds is True
    assert audit.counterexample_quote is None
    assert audit.full_domain_canonical_quote == audit.selected_domain_canonical_quote
    assert audit.full_domain_canonical_quote.amount_in_total == 5
    assert tuple(
        (leg.pool_id, int(leg.amount_out), int(leg.amount_in))
        for leg in audit.full_domain_canonical_quote.legs
    ) == (("p0", 2, 5),)


def test_prefilter_contraction_audit_finds_mixed_pool_counterexample() -> None:
    pools = (
        _pool(pid="p0", r0=20, r1=10),
        _pool(pid="p1", r0=20, r1=10),
        _pool(pid="p2", r0=30, r1=15),
        _pool(pid="p3", r0=30, r1=15),
    )

    audit = audit_exact_out_many_pool_prefilter_contraction(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    assert audit.feasible_pool_ids == ("p0", "p1", "p2", "p3")
    assert audit.selected_pool_ids == ("p0", "p2", "p3")
    assert audit.contraction_holds is False
    assert audit.full_domain_canonical_quote == audit.counterexample_quote
    assert tuple(
        (leg.pool_id, int(leg.amount_out), int(leg.amount_in))
        for leg in audit.full_domain_canonical_quote.legs
    ) == (("p0", 2, 5), ("p1", 2, 5))
    assert tuple(
        (leg.pool_id, int(leg.amount_out), int(leg.amount_in))
        for leg in audit.selected_domain_canonical_quote.legs
    ) == (("p0", 2, 5), ("p2", 2, 5))


def test_selected_subset_contraction_audit_accepts_repaired_mixed_pool_subset() -> None:
    pools = (
        _pool(pid="p0", r0=20, r1=10),
        _pool(pid="p1", r0=20, r1=10),
        _pool(pid="p2", r0=30, r1=15),
        _pool(pid="p3", r0=30, r1=15),
    )
    selection = select_many_pool_cover_search_candidates(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    selected_pools = tuple(pool for pool in pools if pool.pool_id in set(selection.selected_pool_ids))

    audit = audit_exact_out_many_pool_selected_subset_contraction(
        pools,
        selected_pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    assert selection.selected_pool_ids == ("p0", "p1")
    assert audit.selected_pool_ids == ("p0", "p1")
    assert audit.contraction_holds is True
    assert audit.counterexample_quote is None
    assert audit.selected_domain_canonical_quote == audit.full_domain_canonical_quote
