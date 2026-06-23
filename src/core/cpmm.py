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

from dataclasses import dataclass
from typing import Tuple

from ..kernels.python.cpmm_swap_v8 import compute_fee_total as _kernel_compute_fee_total_v8
from ..kernels.python.cpmm_swap_v8 import swap_exact_in as _kernel_swap_exact_in_v8
from ..kernels.python.cpmm_swap_v8 import swap_exact_out as _kernel_swap_exact_out_v8
from ..kernels.python.lp_math_v7 import burn_liquidity as _kernel_burn_liquidity_v7
from ..kernels.python.lp_math_v7 import mint_liquidity_initial as _kernel_mint_liquidity_initial_v7
from ..state.balances import Amount
from .domain_limits import (
    DEX_LP_AMOUNT_MAX,
    DEX_LP_SUPPLY_MAX,
    DEX_POOL_RESERVE_MAX,
    DEX_SWAP_AMOUNT_MAX,
    require_int_range,
)

# Minimum LP lock to prevent division by zero attacks
MIN_LP_LOCK = 1000


@dataclass(frozen=True)
class SwapExactInProtocolFeeResult:
    amount_out: Amount
    fee_total: Amount
    protocol_fee: Amount
    lp_fee: Amount
    net_in: Amount
    new_reserve_in: Amount
    new_reserve_out: Amount
    k_before: int
    k_after: int


def compute_fee_total(gross_amount: Amount, fee_bps: int) -> Amount:
    """
    Deterministic fee computation (ceil rounding).

    This matches the fee rule used by the v8 swap kernel:
        fee_total = ceil(gross_amount * fee_bps / 10_000)
    """
    require_int_range("gross_amount", gross_amount, minimum=0, maximum=DEX_SWAP_AMOUNT_MAX)
    require_int_range("fee_bps", fee_bps, minimum=0, maximum=10000)
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
    require_int_range("reserve_in", reserve_in, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("reserve_out", reserve_out, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("amount_in", amount_in, minimum=1, maximum=DEX_SWAP_AMOUNT_MAX)
    require_int_range("fee_bps", fee_bps, minimum=0, maximum=10000)
    if reserve_in + amount_in > DEX_POOL_RESERVE_MAX:
        raise ValueError(
            f"swap would exceed reserve_in domain max {DEX_POOL_RESERVE_MAX}: "
            f"{reserve_in} + {amount_in}"
        )
    
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


def swap_exact_in_with_protocol_fee(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_in: Amount,
    fee_bps: int,
    protocol_fee_share_bps: int,
) -> SwapExactInProtocolFeeResult:
    """
    Compute exact-in CPMM output while removing a protocol fee share from reserves.

    The existing `swap_exact_in` entry point keeps `protocol_fee_share_bps=0`.
    This helper exposes the same v8 kernel path for callers that need explicit
    protocol-fee capture, such as tokenomics buyback/burn accounting.

    Post-swap reserves:
        new_reserve_in = reserve_in + amount_in - protocol_fee
        new_reserve_out = reserve_out - amount_out
    """
    require_int_range("reserve_in", reserve_in, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("reserve_out", reserve_out, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("amount_in", amount_in, minimum=1, maximum=DEX_SWAP_AMOUNT_MAX)
    require_int_range("fee_bps", fee_bps, minimum=0, maximum=10000)
    require_int_range("protocol_fee_share_bps", protocol_fee_share_bps, minimum=0, maximum=10000)
    if reserve_in + amount_in > DEX_POOL_RESERVE_MAX:
        raise ValueError(
            f"swap would exceed reserve_in domain max {DEX_POOL_RESERVE_MAX}: "
            f"{reserve_in} + {amount_in}"
        )

    res = _kernel_swap_exact_in_v8(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        protocol_fee_share_bps=protocol_fee_share_bps,
    )
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")

    return SwapExactInProtocolFeeResult(
        amount_out=int(res.amount_out),
        fee_total=int(res.fee_total),
        protocol_fee=int(res.protocol_fee),
        lp_fee=int(res.lp_fee),
        net_in=int(res.net_in),
        new_reserve_in=int(res.new_reserve_in),
        new_reserve_out=int(res.new_reserve_out),
        k_before=int(res.k_before),
        k_after=int(res.k_after),
    )


def swap_exact_out(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_out: Amount,
    fee_bps: int,
    max_overdelivery_gap_abs: Amount | None = None,
    max_overdelivery_gap_bps: int | None = None,
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
        
    Args:
        max_overdelivery_gap_abs: Optional absolute cap on exact-out overdelivery gap
            (`amount_out_quote - amount_out`) under exact-in semantics.
        max_overdelivery_gap_bps: Optional relative cap on overdelivery gap in bps
            of requested `amount_out`.

    Returns:
        Tuple of (amount_in, (new_reserve_in, new_reserve_out))
        
    Raises:
        ValueError: If inputs are invalid or would violate invariants
    """
    # Input validation
    require_int_range("reserve_in", reserve_in, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("reserve_out", reserve_out, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("amount_out", amount_out, minimum=1, maximum=DEX_SWAP_AMOUNT_MAX)
    if amount_out >= reserve_out:
        raise ValueError(
            f"Cannot drain full reserve: amount_out ({amount_out}) >= reserve_out ({reserve_out})"
        )
    require_int_range("fee_bps", fee_bps, minimum=0, maximum=10000)
    if max_overdelivery_gap_abs is not None:
        require_int_range(
            "max_overdelivery_gap_abs",
            max_overdelivery_gap_abs,
            minimum=0,
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
    if max_overdelivery_gap_bps is not None:
        require_int_range("max_overdelivery_gap_bps", max_overdelivery_gap_bps, minimum=0, maximum=10000)
    
    res = _kernel_swap_exact_out_v8(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
    )

    # Optional policy guard for exact-out quote quality in small-reserve regimes.
    if max_overdelivery_gap_abs is not None and res.overdelivery_gap > max_overdelivery_gap_abs:
        raise ValueError(
            f"overdelivery gap exceeds absolute policy: gap={res.overdelivery_gap} > {max_overdelivery_gap_abs}"
        )
    if max_overdelivery_gap_bps is not None:
        # ceil(overdelivery_gap * 10_000 / amount_out)
        gap_bps = ((res.overdelivery_gap * 10_000) + amount_out - 1) // amount_out
        if gap_bps > max_overdelivery_gap_bps:
            raise ValueError(
                f"overdelivery gap exceeds bps policy: gap_bps={gap_bps} > {max_overdelivery_gap_bps}"
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
    require_int_range("reserve0", reserve0, minimum=0, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("reserve1", reserve1, minimum=0, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("amount0", amount0, minimum=1, maximum=DEX_LP_AMOUNT_MAX)
    require_int_range("amount1", amount1, minimum=1, maximum=DEX_LP_AMOUNT_MAX)
    require_int_range("lp_supply", lp_supply, minimum=0, maximum=DEX_LP_SUPPLY_MAX)

    if lp_supply == 0:
        # Delegate initial mint math to the (auditable) v7 kernel helper.
        lp, _total_supply = _kernel_mint_liquidity_initial_v7(
            amount0=int(amount0),
            amount1=int(amount1),
            min_lp_lock=int(MIN_LP_LOCK),
        )
    else:
        # Subsequent deposits: proportional to existing supply
        if reserve0 == 0 or reserve1 == 0:
            raise ValueError("Cannot add liquidity to empty pool")
        if reserve0 + amount0 > DEX_POOL_RESERVE_MAX:
            raise ValueError(
                f"deposit would exceed reserve0 domain max {DEX_POOL_RESERVE_MAX}: "
                f"{reserve0} + {amount0}"
            )
        if reserve1 + amount1 > DEX_POOL_RESERVE_MAX:
            raise ValueError(
                f"deposit would exceed reserve1 domain max {DEX_POOL_RESERVE_MAX}: "
                f"{reserve1} + {amount1}"
            )
        
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
    require_int_range("lp_amount", lp_amount, minimum=1, maximum=DEX_LP_SUPPLY_MAX)
    if lp_amount > lp_supply:
        raise ValueError(f"Cannot burn more LP than supply: {lp_amount} > {lp_supply}")
    require_int_range("reserve0", reserve0, minimum=0, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("reserve1", reserve1, minimum=0, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("lp_supply", lp_supply, minimum=1, maximum=DEX_LP_SUPPLY_MAX)

    # Delegate burn math to the (auditable) v7 kernel helper.
    res = _kernel_burn_liquidity_v7(
        lp_amount=int(lp_amount),
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        total_supply=int(lp_supply),
    )
    return int(res.amount0_out), int(res.amount1_out)
