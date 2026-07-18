"""
Liquidity management operations: create pool, add/remove liquidity.
"""

from typing import Optional, Tuple

from ..kernels.python.lp_math_v7 import optimal_liquidity
from ..state.balances import Amount, AssetId
from ..state.pools import (
    PoolState,
    PoolStatus,
    canonical_pool_asset_id,
    compute_pool_id,
    normalize_curve_config,
)
from .cpmm import MIN_LP_LOCK, compute_lp_burn, compute_lp_mint
from .domain_limits import (
    DEX_LP_AMOUNT_MAX,
    DEX_LP_SUPPLY_MAX,
    DEX_POOL_RESERVE_MAX,
    require_int_range,
)


def _normalize_create_pool_assets(asset0: AssetId, asset1: AssetId) -> tuple[AssetId, AssetId]:
    if not isinstance(asset0, str) or not isinstance(asset1, str):
        raise TypeError("asset ids must be strings")

    asset0_norm = canonical_pool_asset_id(asset0)
    asset1_norm = canonical_pool_asset_id(asset1)
    if asset0_norm >= asset1_norm:
        raise ValueError(f"Assets must be in canonical order: {asset0_norm} < {asset1_norm}")
    return asset0_norm, asset1_norm


def _validate_create_pool_amounts(
    amount0: Amount,
    amount1: Amount,
    fee_bps: int,
    created_at: int,
) -> None:
    require_int_range("amount0", amount0, minimum=1, maximum=DEX_LP_AMOUNT_MAX)
    require_int_range("amount1", amount1, minimum=1, maximum=DEX_LP_AMOUNT_MAX)
    require_int_range("fee_bps", fee_bps, minimum=0, maximum=10000)
    require_int_range("created_at", created_at, minimum=0)


def _validate_active_liquidity_pool(pool_state: PoolState) -> None:
    if pool_state.status != PoolStatus.ACTIVE:
        raise ValueError(f"Pool is not active: {pool_state.status}")

    require_int_range("pool_state.reserve0", pool_state.reserve0, minimum=0, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("pool_state.reserve1", pool_state.reserve1, minimum=0, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("pool_state.lp_supply", pool_state.lp_supply, minimum=0, maximum=DEX_LP_SUPPLY_MAX)
    if pool_state.reserve0 == 0 or pool_state.reserve1 == 0:
        raise ValueError("Cannot add liquidity to empty pool")
    if pool_state.lp_supply == 0:
        raise ValueError(
            "Cannot add liquidity to nonempty pool with zero LP supply"
        )


def _validate_add_liquidity_amounts(
    amount0_desired: Amount,
    amount1_desired: Amount,
    amount0_min: Amount,
    amount1_min: Amount,
) -> None:
    require_int_range("amount0_desired", amount0_desired, minimum=1, maximum=DEX_LP_AMOUNT_MAX)
    require_int_range("amount1_desired", amount1_desired, minimum=1, maximum=DEX_LP_AMOUNT_MAX)
    require_int_range("amount0_min", amount0_min, minimum=0, maximum=DEX_LP_AMOUNT_MAX)
    require_int_range("amount1_min", amount1_min, minimum=0, maximum=DEX_LP_AMOUNT_MAX)


def _raise_if_below_minimum(name: str, used: Amount, minimum: Amount) -> None:
    if used < minimum:
        raise ValueError(f"{name}_used ({used}) < {name}_min ({minimum})")


def create_pool(
    asset0: AssetId,
    asset1: AssetId,
    amount0: Amount,
    amount1: Amount,
    fee_bps: int,
    creator_pubkey: str,
    created_at: int = 0,
    *,
    curve_tag: Optional[str] = None,
    curve_params: Optional[object] = None,
) -> Tuple[str, PoolState, Amount]:
    """
    Create a pool with canonical asset text and deterministic initial LP minting.

    The pool ID is the hash of canonical assets, fee, curve tag, and canonical
    curve parameters. The initial LP mint follows `compute_lp_mint`.
    """
    asset0, asset1 = _normalize_create_pool_assets(asset0, asset1)
    _validate_create_pool_amounts(amount0, amount1, fee_bps, created_at)
    curve_tag_norm, curve_params_norm = normalize_curve_config(curve_tag=curve_tag, curve_params=curve_params)
    pool_id = compute_pool_id(asset0, asset1, fee_bps, curve_tag=curve_tag_norm, curve_params=curve_params_norm)
    lp_minted = compute_lp_mint(amount0, amount1, amount0, amount1, 0)

    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=amount0,
        reserve1=amount1,
        fee_bps=fee_bps,
        curve_tag=curve_tag_norm,
        curve_params=curve_params_norm,
        lp_supply=lp_minted + MIN_LP_LOCK,
        status=PoolStatus.ACTIVE,
        created_at=created_at,
    )

    return pool_id, pool_state, lp_minted


def add_liquidity(
    pool_state: PoolState,
    amount0_desired: Amount,
    amount1_desired: Amount,
    amount0_min: Amount,
    amount1_min: Amount,
) -> Tuple[Amount, Amount, Amount]:
    """
    Add liquidity while preserving the pool reserve ratio within integer dust.

    Returns `(amount0_used, amount1_used, lp_minted)`.
    """
    _validate_active_liquidity_pool(pool_state)
    _validate_add_liquidity_amounts(amount0_desired, amount1_desired, amount0_min, amount1_min)

    opt = optimal_liquidity(
        reserve0=pool_state.reserve0,
        reserve1=pool_state.reserve1,
        amount0_desired=amount0_desired,
        amount1_desired=amount1_desired,
    )
    amount0_used = opt.amount0_used
    amount1_used = opt.amount1_used
    _raise_if_below_minimum("amount0", amount0_used, amount0_min)
    _raise_if_below_minimum("amount1", amount1_used, amount1_min)

    lp_minted = compute_lp_mint(
        pool_state.reserve0,
        pool_state.reserve1,
        amount0_used,
        amount1_used,
        pool_state.lp_supply,
    )

    return amount0_used, amount1_used, lp_minted


def remove_liquidity(
    pool_state: PoolState,
    lp_amount: Amount,
    amount0_min: Amount,
    amount1_min: Amount,
) -> Tuple[Amount, Amount]:
    """
    Remove liquidity from a pool.

    Outputs:
        amount0_out = floor(lp_amount * reserve0 / lp_supply)
        amount1_out = floor(lp_amount * reserve1 / lp_supply)
    """
    if pool_state.status != PoolStatus.ACTIVE:
        raise ValueError(f"Pool is not active: {pool_state.status}")

    require_int_range("pool_state.reserve0", pool_state.reserve0, minimum=0, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("pool_state.reserve1", pool_state.reserve1, minimum=0, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("pool_state.lp_supply", pool_state.lp_supply, minimum=1, maximum=DEX_LP_SUPPLY_MAX)
    require_int_range("lp_amount", lp_amount, minimum=1, maximum=DEX_LP_SUPPLY_MAX)
    require_int_range("amount0_min", amount0_min, minimum=0, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("amount1_min", amount1_min, minimum=0, maximum=DEX_POOL_RESERVE_MAX)

    if lp_amount > pool_state.lp_supply:
        raise ValueError(
            f"Cannot burn more LP than supply: {lp_amount} > {pool_state.lp_supply}"
        )

    amount0_out, amount1_out = compute_lp_burn(
        lp_amount,
        pool_state.reserve0,
        pool_state.reserve1,
        pool_state.lp_supply,
    )

    if amount0_out < amount0_min:
        raise ValueError(
            f"amount0_out ({amount0_out}) < amount0_min ({amount0_min})"
        )
    if amount1_out < amount1_min:
        raise ValueError(
            f"amount1_out ({amount1_out}) < amount1_min ({amount1_min})"
        )

    return amount0_out, amount1_out
