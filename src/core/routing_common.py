"""Shared deterministic routing helpers."""

from __future__ import annotations

from typing import Callable, Dict, List, Optional, Tuple

from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .domain_limits import is_strict_int


def _require_int_control(value: object, *, name: str) -> int:
    if not is_strict_int(value):
        raise ValueError(f"{name} must be an int")
    return int(value)


def pool_quote_exact_in(
    pool: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    quote_exact_in: Callable[..., tuple[Amount, tuple[Amount, Amount]]] = swap_exact_in_for_pool,
) -> Optional[Tuple[Amount, str]]:
    amount_in_i = _require_int_control(amount_in, name="amount_in")
    if amount_in_i <= 0:
        return None
    if pool.status.value != "ACTIVE":
        return None
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        reserve_in, reserve_out = pool.reserve0, pool.reserve1
    elif asset_in == pool.asset1 and asset_out == pool.asset0:
        reserve_in, reserve_out = pool.reserve1, pool.reserve0
    else:
        return None
    try:
        amount_out, _ = quote_exact_in(
            pool,
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in_i,
        )
    except ValueError:
        return None
    return amount_out, pool.pool_id


def pool_quote_exact_out(
    pool: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out: Amount,
    quote_exact_out: Callable[..., tuple[Amount, tuple[Amount, Amount]]] = swap_exact_out_for_pool,
) -> Optional[Tuple[Amount, str, Amount]]:
    """Return (amount_in, pool_id, direct_reserve_out) for this direction."""
    amount_out_i = _require_int_control(amount_out, name="amount_out")
    if amount_out_i <= 0:
        return None
    if pool.status.value != "ACTIVE":
        return None
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        reserve_in, reserve_out = pool.reserve0, pool.reserve1
    elif asset_in == pool.asset1 and asset_out == pool.asset0:
        reserve_in, reserve_out = pool.reserve1, pool.reserve0
    else:
        return None
    try:
        amount_in, _ = quote_exact_out(
            pool,
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out_i,
        )
    except ValueError:
        return None
    return amount_in, pool.pool_id, reserve_out


def pool_reserves_direction(
    pool: PoolState, *, asset_in: AssetId, asset_out: AssetId
) -> Optional[Tuple[int, int, int]]:
    """Return (reserve_in, reserve_out, fee_bps), or None if unsupported/inactive."""
    if pool.status.value != "ACTIVE":
        return None
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1), int(pool.fee_bps)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0), int(pool.fee_bps)
    return None


def pool_connects(pool: PoolState, asset_a: AssetId, asset_b: AssetId) -> bool:
    return (asset_a == pool.asset0 and asset_b == pool.asset1) or (
        asset_a == pool.asset1 and asset_b == pool.asset0
    )


def build_asset_pool_index(pools: Tuple[PoolState, ...]) -> Dict[AssetId, Tuple[int, ...]]:
    """Build deterministic asset -> pool-index adjacency for indexed routing scans."""
    temp: Dict[AssetId, List[int]] = {}
    for idx, pool in enumerate(pools):
        temp.setdefault(pool.asset0, []).append(idx)
        temp.setdefault(pool.asset1, []).append(idx)
    out: Dict[AssetId, Tuple[int, ...]] = {}
    for asset, indices in temp.items():
        indices.sort(key=lambda i: pools[i].pool_id)
        out[asset] = tuple(indices)
    return out
