"""
Liquidity management operations: create pool, add/remove liquidity.
"""

from typing import Optional, Tuple

from ..state.pools import PoolState, PoolStatus, compute_pool_id, normalize_curve_config
from ..state.balances import AssetId, Amount
from .cpmm import compute_lp_mint, compute_lp_burn, MIN_LP_LOCK
from ..kernels.python.lp_math_v7 import optimal_liquidity


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
    Create a new CPMM pool.
    
    Pool ID is deterministic:
        pool_id = H("TauSwapPool" || asset0 || asset1 || fee_bps || curve_tag || curve_params)
    
    For v0.1 (default):
        curve_tag = "CPMM"
        curve_params = "" (no additional params)
    
    LP minting for first deposit:
        lp = floor(sqrt(amount0 * amount1)) - MIN_LP_LOCK
    
    Args:
        asset0: First asset (must be < asset1 lexicographically)
        asset1: Second asset
        amount0: Initial deposit of asset0
        amount1: Initial deposit of asset1
        fee_bps: Fee in basis points (0-10000)
        creator_pubkey: Public key of pool creator
        created_at: Block height or timestamp
        
    Returns:
        Tuple of (pool_id, PoolState, lp_minted)
        
    Raises:
        ValueError: If inputs are invalid
    """
    # Validate canonical ordering
    if asset0 >= asset1:
        raise ValueError(f"Assets must be in canonical order: {asset0} < {asset1}")
    
    if amount0 <= 0 or amount1 <= 0:
        raise ValueError(f"Initial deposits must be positive: ({amount0}, {amount1})")
    
    if not (0 <= fee_bps <= 10000):
        raise ValueError(f"fee_bps must be in [0, 10000]: {fee_bps}")
    
    curve_tag_norm, curve_params_norm = normalize_curve_config(curve_tag=curve_tag, curve_params=curve_params)
    pool_id = compute_pool_id(asset0, asset1, fee_bps, curve_tag=curve_tag_norm, curve_params=curve_params_norm)
    
    # Compute LP to mint
    lp_minted = compute_lp_mint(amount0, amount1, amount0, amount1, 0)
    
    # Create pool state
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=amount0,
        reserve1=amount1,
        fee_bps=fee_bps,
        curve_tag=curve_tag_norm,
        curve_params=curve_params_norm,
        lp_supply=lp_minted + MIN_LP_LOCK,  # Include locked LP
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
    Add liquidity to an existing pool.
    
    The settlement MUST choose actual used amounts such that:
        amount0_used / amount1_used = reserve0 / reserve1
        (within integer rounding constraints)
    
    LP minted:
        lp = min(floor(amount0_used * lp_supply / reserve0),
                 floor(amount1_used * lp_supply / reserve1))
    
    Args:
        pool_state: Current pool state
        amount0_desired: Desired amount of asset0
        amount1_desired: Desired amount of asset1
        amount0_min: Minimum acceptable amount0
        amount1_min: Minimum acceptable amount1
        
    Returns:
        Tuple of (amount0_used, amount1_used, lp_minted)
        
    Raises:
        ValueError: If inputs are invalid or pool is empty
    """
    if pool_state.status != PoolStatus.ACTIVE:
        raise ValueError(f"Pool is not active: {pool_state.status}")
    
    if pool_state.reserve0 == 0 or pool_state.reserve1 == 0:
        raise ValueError("Cannot add liquidity to empty pool")
    
    if amount0_desired <= 0 or amount1_desired <= 0:
        raise ValueError(f"Desired amounts must be positive: ({amount0_desired}, {amount1_desired})")
    
    opt = optimal_liquidity(
        reserve0=pool_state.reserve0,
        reserve1=pool_state.reserve1,
        amount0_desired=amount0_desired,
        amount1_desired=amount1_desired,
    )
    amount0_used = opt.amount0_used
    amount1_used = opt.amount1_used
    
    # Check minimums
    if amount0_used < amount0_min:
        raise ValueError(
            f"amount0_used ({amount0_used}) < amount0_min ({amount0_min})"
        )
    if amount1_used < amount1_min:
        raise ValueError(
            f"amount1_used ({amount1_used}) < amount1_min ({amount1_min})"
        )
    
    # Compute LP to mint
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
    
    Args:
        pool_state: Current pool state
        lp_amount: Amount of LP tokens to burn
        amount0_min: Minimum acceptable amount0
        amount1_min: Minimum acceptable amount1
        
    Returns:
        Tuple of (amount0_out, amount1_out)
        
    Raises:
        ValueError: If inputs are invalid
    """
    if pool_state.status != PoolStatus.ACTIVE:
        raise ValueError(f"Pool is not active: {pool_state.status}")
    
    if lp_amount <= 0:
        raise ValueError(f"LP amount must be positive: {lp_amount}")
    
    if lp_amount > pool_state.lp_supply:
        raise ValueError(
            f"Cannot burn more LP than supply: {lp_amount} > {pool_state.lp_supply}"
        )
    
    # Compute output amounts
    amount0_out, amount1_out = compute_lp_burn(
        lp_amount,
        pool_state.reserve0,
        pool_state.reserve1,
        pool_state.lp_supply,
    )
    
    # Check minimums
    if amount0_out < amount0_min:
        raise ValueError(
            f"amount0_out ({amount0_out}) < amount0_min ({amount0_min})"
        )
    if amount1_out < amount1_min:
        raise ValueError(
            f"amount1_out ({amount1_out}) < amount1_min ({amount1_min})"
        )
    
    return amount0_out, amount1_out
