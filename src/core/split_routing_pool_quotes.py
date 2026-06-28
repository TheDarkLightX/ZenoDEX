"""Pool-object quote helpers for split routing dispatch."""

from __future__ import annotations

from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .domain_limits import is_strict_int


def _require_positive_amount(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) <= 0:
        raise ValueError(f"{name} must be positive")
    return int(value)


def reserves_for_pool(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId) -> tuple[int, int] | None:
    if pool.status.value != "ACTIVE":
        return None
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    return None


def quote_exact_in_for_pool(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_in: Amount) -> int:
    amount_in_i = _require_positive_amount(amount_in, name="amount_in")
    reserves = reserves_for_pool(pool, asset_in=asset_in, asset_out=asset_out)
    if reserves is None:
        raise ValueError("pool does not support this direction (or is inactive)")
    reserve_in, reserve_out = reserves
    out, _next_reserves = swap_exact_in_for_pool(
        pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in_i,
    )
    return int(out)


def quote_exact_out_for_pool(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_out: Amount) -> int:
    amount_out_i = _require_positive_amount(amount_out, name="amount_out")
    reserves = reserves_for_pool(pool, asset_in=asset_in, asset_out=asset_out)
    if reserves is None:
        raise ValueError("pool does not support this direction (or is inactive)")
    reserve_in, reserve_out = reserves
    amount_in, _next_reserves = swap_exact_out_for_pool(
        pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out_i,
    )
    return int(amount_in)
