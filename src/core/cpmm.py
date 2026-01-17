"""
Constant Product Market Maker (CPMM) algorithm implementation.

This module implements the core CPMM mathematical operations with
deterministic rounding rules that are consensus-critical.

Algorithm Design:
- Type: Fixed-Point Integer Arithmetic / Deterministic Rounding
- Time Complexity: O(1) per swap operation
- Space Complexity: O(1) auxiliary
- Invariant: After each swap, x' * y' >= k (where k = x * y before swap, adjusted for fees)
"""

import math
from typing import Tuple

from ..state.balances import Amount
from ..kernels.python.cpmm_swap_v8 import compute_fee_total as _kernel_compute_fee_total_v8
from ..kernels.python.cpmm_swap_v8 import swap_exact_in as _kernel_swap_exact_in_v8
from ..kernels.python.cpmm_swap_v8 import swap_exact_out as _kernel_swap_exact_out_v8

# Minimum LP lock to prevent division by zero attacks
MIN_LP_LOCK = 1000


def compute_fee_total(gross_amount: Amount, fee_bps: int) -> Amount:
    """
    Deterministic fee computation (ceil rounding).

    This matches the fee rule used by the v8 swap kernel:
        fee_total = ceil(gross_amount * fee_bps / 10_000)
    """
    if gross_amount < 0:
        raise ValueError(f"gross_amount must be non-negative: {gross_amount}")
    return _kernel_compute_fee_total_v8(gross_in=gross_amount, fee_bps=fee_bps)


def swap_exact_in(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_in: Amount,
    fee_bps: int,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    """
    Compute output amount for exact-in swap with deterministic rounding.
    
    This implements the CPMM formula:
        k = reserve_in * reserve_out (constant product)
        fee = ceil(amount_in * fee_bps / 10_000)
        net_in = amount_in - fee
        amount_out = floor(reserve_out * net_in / (reserve_in + net_in))
        
    Post-swap reserves:
        new_reserve_in = reserve_in + amount_in  (fee stays in pool)
        new_reserve_out = reserve_out - amount_out
        
    Invariant: new_reserve_in * new_reserve_out >= k
    
    Args:
        reserve_in: Current reserve of input asset
        reserve_out: Current reserve of output asset
        amount_in: Exact input amount
        fee_bps: Fee in basis points (0-10000)
        
    Returns:
        Tuple of (amount_out, (new_reserve_in, new_reserve_out))
        
    Raises:
        ValueError: If inputs are invalid or would violate invariants
    """
    # Input validation
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError(f"Reserves must be non-negative: ({reserve_in}, {reserve_out})")
    if amount_in <= 0:
        raise ValueError(f"amount_in must be positive: {amount_in}")
    if not (0 <= fee_bps <= 10000):
        raise ValueError(f"fee_bps must be in [0, 10000]: {fee_bps}")
    
    res = _kernel_swap_exact_in_v8(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        protocol_fee_share_bps=0,
    )

    # Verify invariant: with protocol_fee_share_bps=0, k must not decrease.
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")

    return res.amount_out, (res.new_reserve_in, res.new_reserve_out)


def swap_exact_out(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_out: Amount,
    fee_bps: int,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    """
    Compute required input amount for exact-out swap with deterministic rounding.
    
    This implements the reverse CPMM formula:
        k = reserve_in * reserve_out
        net_in = ceil(reserve_in * amount_out / (reserve_out - amount_out))
        amount_in = ceil(net_in / (1 - fee_bps/10_000))
        
    In integer math:
        amount_in = floor_div(net_in * 10_000 + (10_000 - fee_bps) - 1, (10_000 - fee_bps))
    
    Args:
        reserve_in: Current reserve of input asset
        reserve_out: Current reserve of output asset
        amount_out: Exact output amount desired
        fee_bps: Fee in basis points (0-10000)
        
    Returns:
        Tuple of (amount_in, (new_reserve_in, new_reserve_out))
        
    Raises:
        ValueError: If inputs are invalid or would violate invariants
    """
    # Input validation
    if reserve_in < 0 or reserve_out < 0:
        raise ValueError(f"Reserves must be non-negative: ({reserve_in}, {reserve_out})")
    if amount_out <= 0:
        raise ValueError(f"amount_out must be positive: {amount_out}")
    if amount_out >= reserve_out:
        raise ValueError(
            f"Cannot drain full reserve: amount_out ({amount_out}) >= reserve_out ({reserve_out})"
        )
    if not (0 <= fee_bps <= 10000):
        raise ValueError(f"fee_bps must be in [0, 10000]: {fee_bps}")
    
    res = _kernel_swap_exact_out_v8(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
    )

    # Verify invariant: with protocol_fee_share_bps=0, k must not decrease.
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")

    return res.amount_in, (res.new_reserve_in, res.new_reserve_out)


def compute_lp_mint(
    reserve0: Amount,
    reserve1: Amount,
    amount0: Amount,
    amount1: Amount,
    lp_supply: Amount,
) -> Amount:
    """
    Compute LP tokens to mint for liquidity deposit.
    
    For first deposit (lp_supply == 0):
        lp = floor(sqrt(amount0 * amount1)) - MIN_LP_LOCK
        
    For subsequent deposits:
        lp = min(floor(amount0 * lp_supply / reserve0), floor(amount1 * lp_supply / reserve1))
    
    Args:
        reserve0: Current reserve of asset0
        reserve1: Current reserve of asset1
        amount0: Amount of asset0 being deposited
        amount1: Amount of asset1 being deposited
        lp_supply: Current LP token supply
        
    Returns:
        Amount of LP tokens to mint
        
    Raises:
        ValueError: If inputs are invalid
    """
    if reserve0 < 0 or reserve1 < 0:
        raise ValueError(f"Reserves must be non-negative: ({reserve0}, {reserve1})")
    if amount0 <= 0 or amount1 <= 0:
        raise ValueError(f"Deposit amounts must be positive: ({amount0}, {amount1})")
    if lp_supply < 0:
        raise ValueError(f"LP supply must be non-negative: {lp_supply}")
    
    if lp_supply == 0:
        # First deposit: lp = floor(sqrt(amount0 * amount1)) - MIN_LP_LOCK
        #
        # Uniswap-v2-style behavior: require enough liquidity to cover the lock,
        # otherwise the pool would start in a pathological state.
        product = amount0 * amount1
        lp = math.isqrt(product)
        if lp <= MIN_LP_LOCK:
            raise ValueError("Insufficient initial liquidity: sqrt(amount0*amount1) <= MIN_LP_LOCK")
        lp = lp - MIN_LP_LOCK
    else:
        # Subsequent deposits: proportional to existing supply
        if reserve0 == 0 or reserve1 == 0:
            raise ValueError("Cannot add liquidity to empty pool")
        
        # Compute proportional LP for each asset (round down)
        lp0 = (amount0 * lp_supply) // reserve0
        lp1 = (amount1 * lp_supply) // reserve1
        
        # Take minimum to maintain ratio
        lp = min(lp0, lp1)
    
    if lp <= 0:
        raise ValueError(f"Computed LP amount is non-positive: {lp}")
    
    return lp


def compute_lp_burn(
    lp_amount: Amount,
    reserve0: Amount,
    reserve1: Amount,
    lp_supply: Amount,
) -> Tuple[Amount, Amount]:
    """
    Compute asset amounts to return for LP token burn.
    
    Formula:
        amount0 = floor(lp_amount * reserve0 / lp_supply)
        amount1 = floor(lp_amount * reserve1 / lp_supply)
    
    Args:
        lp_amount: Amount of LP tokens to burn
        reserve0: Current reserve of asset0
        reserve1: Current reserve of asset1
        lp_supply: Current LP token supply
        
    Returns:
        Tuple of (amount0, amount1) to return
        
    Raises:
        ValueError: If inputs are invalid
    """
    if lp_amount <= 0:
        raise ValueError(f"LP amount must be positive: {lp_amount}")
    if lp_amount > lp_supply:
        raise ValueError(f"Cannot burn more LP than supply: {lp_amount} > {lp_supply}")
    if reserve0 < 0 or reserve1 < 0:
        raise ValueError(f"Reserves must be non-negative: ({reserve0}, {reserve1})")
    if lp_supply <= 0:
        raise ValueError(f"LP supply must be positive: {lp_supply}")
    
    # Compute proportional amounts (round down)
    amount0 = (lp_amount * reserve0) // lp_supply
    amount1 = (lp_amount * reserve1) // lp_supply
    
    if amount0 < 0 or amount1 < 0:
        raise ValueError(f"Computed amounts are negative: ({amount0}, {amount1})")
    
    return amount0, amount1
