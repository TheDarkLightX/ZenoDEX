from __future__ import annotations

import pytest

import src.kernels.python.exact_out_many_pool_bounded_oracle_v1 as bounded_oracle
from src.integration.exact_out_route_certificate import build_exact_out_route_canonical_certificate
from src.kernels.python.exact_out_many_pool_bounded_oracle_v1 import (
    bounded_exact_out_many_pool_runtime_domain,
    enumerate_exact_out_many_pool_candidates,
    select_many_pool_audit_candidates,
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


def test_select_many_pool_audit_candidates_returns_sorted_ids_within_budget() -> None:
    pools = (
        _pool(pid="pool_b", r0=100, r1=34),
        _pool(pid="pool_a", r0=120, r1=40),
        _pool(pid="pool_c", r0=160, r1=60),
    )
    selected = select_many_pool_audit_candidates(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
    )
    assert tuple(pool.pool_id for pool in selected) == ("pool_a", "pool_b", "pool_c")


def test_enumerate_exact_out_many_pool_candidates_returns_complete_candidates() -> None:
    pools = (
        _pool(pid="pool_b", r0=100, r1=34),
        _pool(pid="pool_a", r0=120, r1=40),
        _pool(pid="pool_c", r0=160, r1=60),
    )
    candidates = enumerate_exact_out_many_pool_candidates(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_enumerated_candidates=2000,
    )
    assert candidates
    for candidate in candidates:
        assert candidate.amount_out_total == 6
        assert sum(int(leg.amount_out) for leg in candidate.legs) == 6
        assert 1 <= len(candidate.legs) <= 3
        assert tuple(leg.pool_id for leg in candidate.legs) == tuple(sorted(leg.pool_id for leg in candidate.legs))


def test_bounded_exact_out_many_pool_runtime_domain_aligns_runtime_to_canonical_quote() -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
        _pool(pid="pool_c", r0=40, r1=20),
    )
    bounded = bounded_exact_out_many_pool_runtime_domain(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8000,
    )
    certificate = build_exact_out_route_canonical_certificate(bounded.candidates)
    assert bounded.audit_pool_ids == ("pool_b",)
    assert bounded.runtime_quote.amount_in_total == 2
    assert bounded.canonical_quote == certificate.winner_quote
    assert certificate.winner_quote.amount_in_total == 2
    assert bounded.runtime_quote == certificate.winner_quote


def test_bounded_exact_out_many_pool_runtime_domain_uses_repaired_subset_within_audited_bound() -> None:
    pools = (
        _pool(pid="p0", r0=20, r1=10),
        _pool(pid="p1", r0=20, r1=10),
        _pool(pid="p2", r0=30, r1=15),
        _pool(pid="p3", r0=30, r1=15),
    )

    bounded = bounded_exact_out_many_pool_runtime_domain(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    certificate = build_exact_out_route_canonical_certificate(bounded.candidates)

    assert bounded.audit_pool_ids == ("p0", "p1")
    assert bounded.runtime_quote == bounded.canonical_quote
    assert bounded.canonical_quote == certificate.winner_quote
    assert tuple((leg.pool_id, int(leg.amount_out), int(leg.amount_in)) for leg in bounded.runtime_quote.legs) == (
        ("p0", 2, 5),
        ("p1", 2, 5),
    )


def test_candidate_enumeration_propagates_prefilter_programmer_bug(monkeypatch: pytest.MonkeyPatch) -> None:
    def _bug(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("prefilter bug")

    monkeypatch.setattr(bounded_oracle, "select_many_pool_repaired_prefilter_candidates", _bug)

    with pytest.raises(RuntimeError, match="prefilter bug"):
        enumerate_exact_out_many_pool_candidates(
            (_pool(pid="pool_a", r0=40, r1=20),),
            asset_in="A",
            asset_out="B",
            amount_out_total=3,
            max_legs=1,
            max_candidate_pools=1,
            max_enumerated_candidates=100,
        )


def test_runtime_domain_propagates_prefilter_programmer_bug(monkeypatch: pytest.MonkeyPatch) -> None:
    def _bug(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("prefilter bug")

    monkeypatch.setattr(bounded_oracle, "select_many_pool_repaired_prefilter_candidates", _bug)

    with pytest.raises(RuntimeError, match="prefilter bug"):
        bounded_exact_out_many_pool_runtime_domain(
            (_pool(pid="pool_a", r0=40, r1=20),),
            asset_in="A",
            asset_out="B",
            amount_out_total=3,
            max_legs=1,
            max_candidate_pools=1,
            max_candidates=1,
            max_enumerated_candidates=100,
        )
