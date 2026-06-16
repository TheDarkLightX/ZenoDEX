"""Pool-object quote helpers for split routing dispatch."""

from __future__ import annotations

from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool


def reserves_for_pool(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId) -> tuple[int, int] | None:
    if pool.status.value != "ACTIVE":
        return None
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    return None


def quote_exact_in_for_pool(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_in: Amount) -> int:
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    reserves = reserves_for_pool(pool, asset_in=asset_in, asset_out=asset_out)
    if reserves is None:
        raise ValueError("pool does not support this direction (or is inactive)")
    reserve_in, reserve_out = reserves
    out, _next_reserves = swap_exact_in_for_pool(
        pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=int(amount_in),
    )
    return int(out)


def quote_exact_out_for_pool(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_out: Amount) -> int:
    if amount_out <= 0:
        raise ValueError("amount_out must be positive")
    reserves = reserves_for_pool(pool, asset_in=asset_in, asset_out=asset_out)
    if reserves is None:
        raise ValueError("pool does not support this direction (or is inactive)")
    reserve_in, reserve_out = reserves
    amount_in, _next_reserves = swap_exact_out_for_pool(
        pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=int(amount_out),
    )
    return int(amount_in)
