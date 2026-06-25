"""Many-pool exact-in tests for the opt-in k-pool adaptive solver profile."""

from __future__ import annotations

import pytest

from src.core.split_routing import PoolXY, exact_out_for_pool_exact_in
from src.core.split_routing_many_exact_in import (
    EXACT_IN_SOLVER_GREEDY,
    EXACT_IN_SOLVER_KPOOL_ADAPTIVE,
    ManyPoolExactInRequest,
    best_many_pool_exact_in_split,
)
from src.core.split_routing_many_exact_in_small import best_small_domain_many_pool_exact_in
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


def _pool_state(pool_id: str, pool: PoolXY) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0="A",
        asset1="B",
        reserve0=int(pool.x),
        reserve1=int(pool.y),
        fee_bps=int(pool.fee_bps),
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
    )


def _request(
    pools: list[tuple[str, PoolXY]],
    *,
    amount_in: int,
    max_legs: int,
    exact_solver_profile: str,
) -> ManyPoolExactInRequest:
    pool_states = [_pool_state(pid, pool) for pid, pool in pools]

    def reserves_for(pool: PoolState) -> tuple[int, int] | None:
        return (int(pool.reserve0), int(pool.reserve1))

    def quote_exact_in(pool: PoolState, amount: int) -> int:
        return int(
            exact_out_for_pool_exact_in(
                PoolXY(
                    x=int(pool.reserve0),
                    y=int(pool.reserve1),
                    fee_bps=int(pool.fee_bps),
                ),
                int(amount),
            )
        )

    return ManyPoolExactInRequest(
        pools=pool_states,
        asset_in="A",
        asset_out="B",
        amount_in_total=int(amount_in),
        max_legs=int(max_legs),
        max_candidates=len(pool_states),
        max_iters=64,
        reserves_for=reserves_for,
        quote_exact_in=quote_exact_in,
        exact_solver_profile=exact_solver_profile,
    )


def _expected_small_domain_alloc(
    pools: list[tuple[str, PoolXY]],
    *,
    amount_in: int,
    max_legs: int,
) -> dict[str, int]:
    pools_by_id = dict(pools)

    def quote_for_pool_id(pool_id: str, amount: int) -> int | None:
        if int(amount) <= 0:
            return 0
        try:
            return int(exact_out_for_pool_exact_in(pools_by_id[pool_id], int(amount)))
        except ValueError:
            return None

    return best_small_domain_many_pool_exact_in(
        pool_ids=sorted(pools_by_id.keys()),
        amount_in_total=int(amount_in),
        max_legs=int(max_legs),
        quote_for_pool_id=quote_for_pool_id,
    )


def _total_out(pools: list[tuple[str, PoolXY]], alloc: dict[str, int]) -> int:
    total = 0
    for pool_id, pool in pools:
        amount = int(alloc.get(pool_id, 0))
        if amount <= 0:
            continue
        total += int(exact_out_for_pool_exact_in(pool, amount))
    return int(total)


def test_many_pool_kpool_adaptive_profile_matches_exact_small_domain() -> None:
    pools = [
        ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("pool-b", PoolXY(x=8_000, y=12_000, fee_bps=50)),
        ("pool-c", PoolXY(x=12_000, y=8_000, fee_bps=30)),
    ]
    expected_alloc = _expected_small_domain_alloc(pools, amount_in=150, max_legs=3)
    request = _request(
        pools,
        amount_in=150,
        max_legs=3,
        exact_solver_profile=EXACT_IN_SOLVER_KPOOL_ADAPTIVE,
    )

    quote = best_many_pool_exact_in_split(request)
    got_alloc = {leg.pool_id: int(leg.amount_in) for leg in quote.legs}

    assert got_alloc == {
        pid: amount for pid, amount in expected_alloc.items() if amount > 0
    }
    assert int(quote.amount_in_total) == 150
    assert int(quote.amount_out_total) == _total_out(pools, expected_alloc)


def test_many_pool_default_profile_still_accepts_greedy_mode() -> None:
    pools = [
        ("pool-a", PoolXY(x=1, y=100_000, fee_bps=0)),
        ("pool-b", PoolXY(x=100_000, y=100_000, fee_bps=0)),
    ]
    request = _request(
        pools,
        amount_in=300,
        max_legs=2,
        exact_solver_profile=EXACT_IN_SOLVER_GREEDY,
    )

    quote = best_many_pool_exact_in_split(request)

    assert int(quote.amount_in_total) == 300
    assert sum(int(leg.amount_in) for leg in quote.legs) == 300


def test_many_pool_rejects_unknown_exact_solver_profile() -> None:
    pools = [("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30))]
    request = _request(
        pools,
        amount_in=100,
        max_legs=1,
        exact_solver_profile="unknown",
    )

    with pytest.raises(ValueError, match="exact_solver_profile"):
        best_many_pool_exact_in_split(request)
