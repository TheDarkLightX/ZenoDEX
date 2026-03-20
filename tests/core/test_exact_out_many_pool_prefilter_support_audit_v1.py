from __future__ import annotations

from src.kernels.python.exact_out_many_pool_prefilter_support_audit_v1 import (
    audit_exact_out_many_pool_prefilter_support,
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


def test_prefilter_support_audit_accepts_when_feasible_domain_equals_selected_domain() -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
        _pool(pid="pool_c", r0=40, r1=20),
    )

    audit = audit_exact_out_many_pool_prefilter_support(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=8_000,
    )

    assert audit.support_sound is True
    assert audit.counterexample_quote is None
    assert audit.selected_pool_ids == ("pool_a", "pool_b", "pool_c")
    assert audit.feasible_pool_ids == ("pool_a", "pool_b", "pool_c")


def test_prefilter_support_audit_finds_bounded_counterexample() -> None:
    pools = (
        _pool(pid="p0", r0=40, r1=20),
        _pool(pid="p1", r0=40, r1=20),
        _pool(pid="p2", r0=40, r1=20),
        _pool(pid="p3", r0=40, r1=20),
    )

    audit = audit_exact_out_many_pool_prefilter_support(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=2,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=8,
        max_enumerated_candidates=8_000,
    )

    assert audit.support_sound is False
    assert audit.selected_pool_ids == ("p0", "p1", "p2")
    assert audit.feasible_pool_ids == ("p0", "p1", "p2", "p3")
    assert audit.counterexample_quote is not None
    assert tuple((leg.pool_id, int(leg.amount_out), int(leg.amount_in)) for leg in audit.counterexample_quote.legs) == (
        ("p3", 2, 5),
    )
    assert audit.counterexample_quote.amount_in_total == 5
