from __future__ import annotations

import pytest

from src.core import amm_dispatch
from src.kernels.python.exact_out_many_pool_canonical_domain_v1 import (
    build_exact_out_many_pool_selected_domain,
    feasible_exact_out_pools,
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


def test_feasible_exact_out_pools_skips_expected_quote_domain_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pools = (
        _pool(pid="pool_a", r0=120, r1=40),
        _pool(pid="pool_b", r0=160, r1=60),
    )

    def _quote_or_reject(pool: PoolState, **kwargs: object) -> tuple[int, tuple[int, int]]:
        if pool.pool_id == "pool_a":
            raise ValueError("quote domain")
        amount_out = kwargs["amount_out"]
        if not isinstance(amount_out, int):
            raise TypeError("amount_out must be int")
        return amount_out + 1, (1, 1)

    monkeypatch.setattr(amm_dispatch, "swap_exact_out_for_pool", _quote_or_reject)

    feasible = feasible_exact_out_pools(pools, asset_in="A", asset_out="B", amount_out_total=6)

    assert tuple(pool.pool_id for pool, _cap, _amount_in in feasible) == ("pool_b",)


def test_feasible_exact_out_pools_surfaces_unexpected_quote_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pools = (_pool(pid="pool_a", r0=120, r1=40),)

    def _boom_quote(*_args: object, **_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise RuntimeError("quote probe internal fault")

    monkeypatch.setattr(amm_dispatch, "swap_exact_out_for_pool", _boom_quote)

    with pytest.raises(RuntimeError, match="quote probe internal fault"):
        feasible_exact_out_pools(pools, asset_in="A", asset_out="B", amount_out_total=6)


def test_selected_domain_skips_expected_allocation_quote_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pools = (
        _pool(pid="pool_a", r0=40, r1=20),
        _pool(pid="pool_b", r0=40, r1=63),
    )

    def _quote_or_reject(_pool: PoolState, **kwargs: object) -> tuple[int, tuple[int, int]]:
        amount_out = kwargs["amount_out"]
        if not isinstance(amount_out, int):
            raise TypeError("amount_out must be int")
        if amount_out != 3:
            raise ValueError("allocation quote domain")
        return 2, (1, 1)

    monkeypatch.setattr(amm_dispatch, "swap_exact_out_for_pool", _quote_or_reject)

    domain = build_exact_out_many_pool_selected_domain(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=2,
        max_enumerated_candidates=100,
    )

    assert domain.canonical_quote.amount_out_total == 3
    assert tuple(leg.amount_out for leg in domain.canonical_quote.legs) == (3,)


def test_selected_domain_surfaces_unexpected_allocation_quote_fault(
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
        raise RuntimeError("allocation quote internal fault")

    monkeypatch.setattr(amm_dispatch, "swap_exact_out_for_pool", _quote_or_boom)

    with pytest.raises(RuntimeError, match="allocation quote internal fault"):
        build_exact_out_many_pool_selected_domain(
            pools,
            asset_in="A",
            asset_out="B",
            amount_out_total=3,
            max_legs=2,
            max_enumerated_candidates=100,
        )


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
