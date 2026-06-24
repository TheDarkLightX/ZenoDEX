from __future__ import annotations

from collections.abc import Sequence
from typing import Any

import pytest

from src.kernels.python import exact_out_many_pool_prefilter_subset_search_v1 as subset_search
from src.kernels.python.exact_out_many_pool_canonical_domain_v1 import (
    ExactOutManyPoolSelectedDomain,
)
from src.kernels.python.exact_out_many_pool_prefilter_subset_search_v1 import (
    search_exact_out_many_pool_prefilter_subset,
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


def test_prefilter_subset_search_finds_bounded_repair_for_mixed_pool_counterexample() -> None:
    pools = (
        _pool(pid="p0", r0=20, r1=10),
        _pool(pid="p1", r0=20, r1=10),
        _pool(pid="p2", r0=30, r1=15),
        _pool(pid="p3", r0=30, r1=15),
    )

    result = search_exact_out_many_pool_prefilter_subset(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    assert result.feasible_pool_ids == ("p0", "p1", "p2", "p3")
    assert result.current_selected_pool_ids == ("p0", "p2", "p3")
    assert result.current_selected_matches_full_canonical is False
    assert result.best_cover_subset_ids == ("p0", "p1")
    assert result.best_cover_canonical_quote == result.full_domain_canonical_quote
    assert tuple(
        (leg.pool_id, int(leg.amount_out), int(leg.amount_in))
        for leg in result.full_domain_canonical_quote.legs
    ) == (("p0", 2, 5), ("p1", 2, 5))


def test_prefilter_subset_search_detects_when_current_prefilter_already_covers_canonical() -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
        _pool(pid="pool_c", r0=40, r1=20),
    )

    result = search_exact_out_many_pool_prefilter_subset(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=8_000,
    )

    assert result.current_selected_pool_ids == ("pool_a", "pool_b", "pool_c")
    assert result.current_selected_matches_full_canonical is True
    assert result.current_selected_canonical_quote == result.full_domain_canonical_quote
    assert result.best_cover_subset_ids == ("pool_b",)
    assert result.best_cover_canonical_quote == result.full_domain_canonical_quote


def test_cover_search_selector_prefers_repaired_subset_on_mixed_pool_counterexample() -> None:
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

    assert selection.strategy == "bounded_cover_search"
    assert selection.current_selected_pool_ids == ("p0", "p2", "p3")
    assert selection.selected_pool_ids == ("p0", "p1")
    assert selection.selected_domain_canonical_quote == selection.full_domain_canonical_quote


def test_cover_search_selector_can_shrink_already_good_domain() -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
        _pool(pid="pool_c", r0=40, r1=20),
    )

    selection = select_many_pool_cover_search_candidates(
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
    assert selection.selected_domain_canonical_quote == selection.full_domain_canonical_quote


def test_prefilter_subset_search_skips_expected_subset_domain_reject(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
        _pool(pid="pool_c", r0=40, r1=20),
    )
    original = subset_search.build_exact_out_many_pool_selected_domain

    def _domain_or_reject(
        selected_pools: Sequence[PoolState],
        **kwargs: Any,
    ) -> ExactOutManyPoolSelectedDomain:
        selected = tuple(selected_pools)
        if len(selected) == 1:
            raise ValueError("subset domain unavailable")
        return original(selected, **kwargs)

    monkeypatch.setattr(
        subset_search,
        "build_exact_out_many_pool_selected_domain",
        _domain_or_reject,
    )

    result = search_exact_out_many_pool_prefilter_subset(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=8_000,
    )

    assert result.searched_subset_count == 7
    assert result.best_cover_subset_ids is not None
    assert len(result.best_cover_subset_ids) > 1
    assert result.best_cover_canonical_quote == result.full_domain_canonical_quote


def test_prefilter_subset_search_surfaces_unexpected_subset_domain_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
        _pool(pid="pool_c", r0=40, r1=20),
    )
    original = subset_search.build_exact_out_many_pool_selected_domain

    def _domain_or_boom(
        selected_pools: Sequence[PoolState],
        **kwargs: Any,
    ) -> ExactOutManyPoolSelectedDomain:
        selected = tuple(selected_pools)
        if len(selected) == 1:
            raise RuntimeError("subset domain internal fault")
        return original(selected, **kwargs)

    monkeypatch.setattr(
        subset_search,
        "build_exact_out_many_pool_selected_domain",
        _domain_or_boom,
    )

    with pytest.raises(RuntimeError, match="subset domain internal fault"):
        search_exact_out_many_pool_prefilter_subset(
            pools,
            asset_in="A",
            asset_out="B",
            amount_out_total=3,
            max_legs=3,
            max_candidate_pools=3,
            max_full_domain_pools=6,
            max_enumerated_candidates=8_000,
        )
