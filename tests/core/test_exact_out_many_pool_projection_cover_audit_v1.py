from __future__ import annotations

import pytest

from src.kernels.python import exact_out_many_pool_projection_cover_audit_v1
from src.kernels.python.exact_out_many_pool_projection_cover_audit_v1 import (
    audit_exact_out_many_pool_projection_cover,
    audit_exact_out_many_pool_cpmm_projection_cover,
    audit_exact_out_many_pool_selected_domain_projection_cover,
    audit_exact_out_many_pool_selected_domain_cpmm_projection_cover,
    enumerate_exact_out_many_pool_reachable_projected_paths,
    enumerate_exact_out_many_pool_cpmm_reachable_projected_paths,
)
from src.state.pools import CURVE_TAG_CPMM, CURVE_TAG_SUM_BOOST_V1, PoolState, PoolStatus


def _pool(
    *,
    pid: str,
    r0: int,
    r1: int,
    curve_tag: str = CURVE_TAG_CPMM,
    curve_params: object | None = None,
) -> PoolState:
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
        curve_tag=curve_tag,
        curve_params=curve_params,
    )


def test_selected_domain_cpmm_projection_cover_holds_on_known_counterexample() -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
        _pool(pid="pool_c", r0=40, r1=20),
    )

    audit = audit_exact_out_many_pool_selected_domain_cpmm_projection_cover(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_selected_pools=3,
        max_enumerated_candidates=8_000,
    )

    assert audit.selected_pool_ids == ("pool_a", "pool_b", "pool_c")
    assert audit.projection_cover_holds is True
    assert audit.sound_holds is True
    assert audit.complete_holds is True
    assert audit.extra_emitted_path is None
    assert audit.missing_reachable_path is None
    assert audit.emitted_candidate_count == audit.emitted_projected_path_count
    assert audit.emitted_projected_path_count == audit.reachable_projected_path_count
    assert audit.canonical_quote_projected_path == (("pool_b", 3, 2),)
    assert audit.canonical_quote_covered is True


def test_runtime_cpmm_projection_cover_wrapper_holds_after_selection() -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
        _pool(pid="pool_c", r0=40, r1=20),
        _pool(pid="pool_d", r0=10, r1=2),
    )

    audit = audit_exact_out_many_pool_cpmm_projection_cover(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_selected_pools=3,
        max_enumerated_candidates=8_000,
    )

    assert audit.projection_cover_holds is True
    assert audit.canonical_quote_covered is True
    assert audit.selected_pool_ids == ("pool_a", "pool_b", "pool_c")


def test_selected_domain_projection_cover_holds_on_mixed_curve_selected_domain() -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(
            pid="pool_b",
            r0=40,
            r1=20,
            curve_tag=CURVE_TAG_SUM_BOOST_V1,
        ),
    )

    reachable = enumerate_exact_out_many_pool_reachable_projected_paths(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=2,
        max_selected_pools=3,
    )
    audit = audit_exact_out_many_pool_selected_domain_projection_cover(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=2,
        max_selected_pools=3,
        max_enumerated_candidates=8_000,
    )

    assert reachable
    assert audit.projection_cover_holds is True
    assert audit.canonical_quote_projected_path == (("pool_b", 3, 5),)
    assert audit.canonical_quote_covered is True


def test_runtime_projection_cover_wrapper_holds_after_mixed_curve_selection() -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=20, curve_tag=CURVE_TAG_SUM_BOOST_V1),
        _pool(pid="pool_c", r0=10, r1=2),
    )

    audit = audit_exact_out_many_pool_projection_cover(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=2,
        max_candidate_pools=2,
        max_selected_pools=2,
        max_enumerated_candidates=8_000,
    )

    assert audit.projection_cover_holds is True
    assert audit.selected_pool_ids == ("pool_a", "pool_b")


def test_reachable_projected_paths_skip_expected_quote_domain_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
    )

    def _quote_or_reject(pool: PoolState, **kwargs: object) -> tuple[int, tuple[int, int]]:
        amount_out = kwargs["amount_out"]
        if not isinstance(amount_out, int):
            raise TypeError("amount_out must be int")
        if amount_out != 3:
            raise ValueError("projection quote domain")
        return 2 if pool.pool_id == "pool_b" else 5, (1, 1)

    monkeypatch.setattr(
        exact_out_many_pool_projection_cover_audit_v1,
        "swap_exact_out_for_pool",
        _quote_or_reject,
    )

    reachable = enumerate_exact_out_many_pool_reachable_projected_paths(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=2,
        max_selected_pools=3,
    )

    assert reachable == (
        (("pool_a", 3, 5),),
        (("pool_b", 3, 2),),
    )


def test_reachable_projected_paths_surface_unexpected_quote_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
    )

    def _quote_or_boom(_pool: PoolState, **kwargs: object) -> tuple[int, tuple[int, int]]:
        amount_out = kwargs["amount_out"]
        if not isinstance(amount_out, int):
            raise TypeError("amount_out must be int")
        if amount_out == 3:
            return 2, (1, 1)
        raise RuntimeError("projection quote internal fault")

    monkeypatch.setattr(
        exact_out_many_pool_projection_cover_audit_v1,
        "swap_exact_out_for_pool",
        _quote_or_boom,
    )

    with pytest.raises(RuntimeError, match="projection quote internal fault"):
        enumerate_exact_out_many_pool_reachable_projected_paths(
            pools,
            asset_in="A",
            asset_out="B",
            amount_out_total=3,
            max_legs=2,
            max_selected_pools=3,
        )


def test_selected_domain_cpmm_projection_cover_enforces_selected_pool_bound() -> None:
    pools = (
        _pool(pid="pool_a", r0=100, r1=40),
        _pool(pid="pool_b", r0=110, r1=50),
        _pool(pid="pool_c", r0=120, r1=60),
    )

    with pytest.raises(ValueError, match="exceeded max_selected_pools"):
        audit_exact_out_many_pool_selected_domain_cpmm_projection_cover(
            pools,
            asset_in="A",
            asset_out="B",
            amount_out_total=6,
            max_legs=3,
            max_selected_pools=2,
            max_enumerated_candidates=2_000,
        )
