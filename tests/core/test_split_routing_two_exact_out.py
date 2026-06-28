from __future__ import annotations

from src.core.split_routing_pool_quotes import quote_exact_out_for_pool, reserves_for_pool
from src.core.split_routing_two_exact_out import (
    TwoPoolExactOutRequest,
    best_two_pool_exact_out_split,
)
from src.state.pools import PoolState, PoolStatus


def _pool(pool_id: str, reserve_in: int, reserve_out: int, fee_bps: int) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0="A",
        asset1="B",
        reserve0=int(reserve_in),
        reserve1=int(reserve_out),
        fee_bps=int(fee_bps),
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def test_two_pool_exact_out_public_api_does_not_return_window_sample_as_exact() -> None:
    pool0 = _pool("p0", reserve_in=138, reserve_out=1167, fee_bps=5000)
    pool1 = _pool("p1", reserve_in=868, reserve_out=1645, fee_bps=0)

    def reserves_for(pool: PoolState) -> tuple[int, int] | None:
        return reserves_for_pool(pool, asset_in="A", asset_out="B")

    def quote_exact_out(pool: PoolState, amount_out: int) -> int:
        return quote_exact_out_for_pool(
            pool,
            asset_in="A",
            asset_out="B",
            amount_out=int(amount_out),
        )

    quote = best_two_pool_exact_out_split(
        TwoPoolExactOutRequest(
            pool0=pool0,
            pool1=pool1,
            asset_in="A",
            asset_out="B",
            amount_out_total=131,
            window=0,
            brute_force_max=0,
            reserves_for=reserves_for,
            quote_exact_out=quote_exact_out,
        )
    )

    assert quote.amount_out_0 == 126
    assert quote.amount_out_1 == 5
    assert quote.amount_in_total == 37
