from __future__ import annotations

import pytest

import src.core.amm_dispatch as amm_dispatch
from src.kernels.python.exact_out_many_pool_canonical_domain_v1 import (
    build_exact_out_many_pool_selected_domain,
    rank_exact_out_feasible_pools,
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


def test_selected_domain_recovers_canonical_winner_on_known_counterexample() -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
        _pool(pid="pool_c", r0=40, r1=20),
    )

    domain = build_exact_out_many_pool_selected_domain(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_enumerated_candidates=8_000,
    )

    assert domain.selected_pool_ids == ("pool_a", "pool_b", "pool_c")
    assert domain.canonical_quote.amount_in_total == 2
    assert tuple((leg.pool_id, int(leg.amount_out), int(leg.amount_in)) for leg in domain.canonical_quote.legs) == (
        ("pool_b", 3, 2),
    )


def test_rank_exact_out_feasible_pools_returns_deterministic_sorted_rows() -> None:
    pools = (
        _pool(pid="pool_b", r0=100, r1=34),
        _pool(pid="pool_a", r0=120, r1=40),
        _pool(pid="pool_c", r0=160, r1=60),
    )

    rows = rank_exact_out_feasible_pools(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
    )

    assert tuple(row.pool_id for row in rows) == ("pool_c", "pool_a", "pool_b")
    assert all(int(row.cap_out) >= int(row.probe_amount_out) > 0 for row in rows)
    assert all(int(row.probe_amount_in) > 0 for row in rows)


def test_selected_domain_rejects_duplicate_pool_ids() -> None:
    pool = _pool(pid="pool_a", r0=40, r1=20)

    with pytest.raises(ValueError, match="selected_pools must not repeat pool_id"):
        build_exact_out_many_pool_selected_domain(
            (pool, pool),
            asset_in="A",
            asset_out="B",
            amount_out_total=3,
            max_legs=2,
            max_enumerated_candidates=100,
        )


def test_rank_exact_out_feasible_pools_propagates_quote_kernel_bug(monkeypatch: pytest.MonkeyPatch) -> None:
    def _bug(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("quote kernel bug")

    monkeypatch.setattr(amm_dispatch, "swap_exact_out_for_pool", _bug)

    with pytest.raises(RuntimeError, match="quote kernel bug"):
        rank_exact_out_feasible_pools(
            (_pool(pid="pool_a", r0=40, r1=20),),
            asset_in="A",
            asset_out="B",
            amount_out_total=3,
        )


def test_selected_domain_propagates_quote_kernel_bug(monkeypatch: pytest.MonkeyPatch) -> None:
    def _bug(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("quote kernel bug")

    monkeypatch.setattr(amm_dispatch, "swap_exact_out_for_pool", _bug)

    with pytest.raises(RuntimeError, match="quote kernel bug"):
        build_exact_out_many_pool_selected_domain(
            (_pool(pid="pool_a", r0=40, r1=20),),
            asset_in="A",
            asset_out="B",
            amount_out_total=3,
            max_legs=1,
            max_enumerated_candidates=100,
        )
