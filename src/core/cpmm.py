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


@dataclass(frozen=True)
class _ExactOutInputs:
    reserve_in: Amount
    reserve_out: Amount
    amount_out: Amount
    fee_bps: int
    max_overdelivery_gap_abs: Amount | None
    max_overdelivery_gap_bps: int | None


@dataclass(frozen=True)
class _LpMintInputs:
    reserve0: Amount
    reserve1: Amount
    amount0: Amount
    amount1: Amount
    lp_supply: Amount


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

    res = _kernel_swap_exact_in_v8(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        protocol_fee_share_bps=0,
    )
    _validate_swap_post_reserves(
        new_reserve_in=res.new_reserve_in,
        new_reserve_out=res.new_reserve_out,
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

    res = _kernel_swap_exact_in_v8(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        protocol_fee_share_bps=protocol_fee_share_bps,
    )
    _validate_swap_post_reserves(
        new_reserve_in=res.new_reserve_in,
        new_reserve_out=res.new_reserve_out,
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


def _validate_exact_out_inputs(
    params: _ExactOutInputs,
) -> None:
    require_int_range("reserve_in", params.reserve_in, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("reserve_out", params.reserve_out, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("amount_out", params.amount_out, minimum=1, maximum=DEX_SWAP_AMOUNT_MAX)
    if params.amount_out >= params.reserve_out:
        raise ValueError(
            f"Cannot drain full reserve: amount_out ({params.amount_out}) >= reserve_out ({params.reserve_out})"
        )
    require_int_range("fee_bps", params.fee_bps, minimum=0, maximum=10000)
    if params.max_overdelivery_gap_abs is not None:
        require_int_range(
            "max_overdelivery_gap_abs",
            params.max_overdelivery_gap_abs,
            minimum=0,
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
    if params.max_overdelivery_gap_bps is not None:
        require_int_range("max_overdelivery_gap_bps", params.max_overdelivery_gap_bps, minimum=0, maximum=10000)


def _enforce_exact_out_overdelivery_policy(
    *,
    requested_amount_out: Amount,
    overdelivery_gap: Amount,
    max_overdelivery_gap_abs: Amount | None,
    max_overdelivery_gap_bps: int | None,
) -> None:
    if max_overdelivery_gap_abs is not None and overdelivery_gap > max_overdelivery_gap_abs:
        raise ValueError(
            f"overdelivery gap exceeds absolute policy: gap={overdelivery_gap} > {max_overdelivery_gap_abs}"
        )
    if max_overdelivery_gap_bps is None:
        return
    # ceil(overdelivery_gap * 10_000 / requested_amount_out)
    gap_bps = ((overdelivery_gap * 10_000) + requested_amount_out - 1) // requested_amount_out
    if gap_bps > max_overdelivery_gap_bps:
        raise ValueError(
            f"overdelivery gap exceeds bps policy: gap_bps={gap_bps} > {max_overdelivery_gap_bps}"
        )


def _raise_if_k_decreased(*, k_before: int, k_after: int) -> None:
    if k_after < k_before:
        raise ValueError(f"Invariant violation: new_k ({k_after}) < old_k ({k_before})")


def _validate_swap_post_reserves(*, new_reserve_in: object, new_reserve_out: object) -> None:
    """Keep every accepted swap inside the authoritative pool-state domain."""
    if type(new_reserve_in) is not int:
        raise TypeError("new_reserve_in must be an int")
    if new_reserve_in > DEX_POOL_RESERVE_MAX:
        raise ValueError(
            f"swap would exceed reserve_in domain max {DEX_POOL_RESERVE_MAX}: "
            f"post-state {new_reserve_in}"
        )
    require_int_range(
        "new_reserve_in",
        new_reserve_in,
        minimum=1,
        maximum=DEX_POOL_RESERVE_MAX,
    )
    require_int_range(
        "new_reserve_out",
        new_reserve_out,
        minimum=1,
        maximum=DEX_POOL_RESERVE_MAX,
    )


def _validate_lp_mint_inputs(params: _LpMintInputs) -> None:
    require_int_range("reserve0", params.reserve0, minimum=0, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("reserve1", params.reserve1, minimum=0, maximum=DEX_POOL_RESERVE_MAX)
    require_int_range("amount0", params.amount0, minimum=1, maximum=DEX_LP_AMOUNT_MAX)
    require_int_range("amount1", params.amount1, minimum=1, maximum=DEX_LP_AMOUNT_MAX)
    require_int_range("lp_supply", params.lp_supply, minimum=0, maximum=DEX_LP_SUPPLY_MAX)


def _compute_initial_lp_mint(params: _LpMintInputs) -> Amount:
    lp, _total_supply = _kernel_mint_liquidity_initial_v7(
        amount0=int(params.amount0),
        amount1=int(params.amount1),
        min_lp_lock=int(MIN_LP_LOCK),
    )
    return int(lp)


def _raise_if_deposit_exceeds_reserve_domain(name: str, reserve: Amount, amount: Amount) -> None:
    if reserve + amount > DEX_POOL_RESERVE_MAX:
        raise ValueError(f"deposit would exceed {name} domain max {DEX_POOL_RESERVE_MAX}: {reserve} + {amount}")


def _compute_existing_lp_mint(params: _LpMintInputs) -> Amount:
    if params.reserve0 == 0 or params.reserve1 == 0:
        raise ValueError("Cannot add liquidity to empty pool")

    _raise_if_deposit_exceeds_reserve_domain("reserve0", params.reserve0, params.amount0)
    _raise_if_deposit_exceeds_reserve_domain("reserve1", params.reserve1, params.amount1)

    lp0 = (params.amount0 * params.lp_supply) // params.reserve0
    lp1 = (params.amount1 * params.lp_supply) // params.reserve1
    return min(lp0, lp1)


def swap_exact_out(
    reserve_in: Amount,
    reserve_out: Amount,
    amount_out: Amount,
    fee_bps: int,
    max_overdelivery_gap_abs: Amount | None = None,
    max_overdelivery_gap_bps: int | None = None,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    """
    Compute required input for an exact-out CPMM swap.

    The v8 kernel owns the deterministic ceil-rounding formula. This wrapper
    validates domains, applies optional overdelivery policy, and checks that the
    post-swap constant product did not decrease.
    """
    params = _ExactOutInputs(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
        max_overdelivery_gap_abs=max_overdelivery_gap_abs,
        max_overdelivery_gap_bps=max_overdelivery_gap_bps,
    )
    _validate_exact_out_inputs(params)

    res = _kernel_swap_exact_out_v8(
        reserve_in=params.reserve_in,
        reserve_out=params.reserve_out,
        amount_out=params.amount_out,
        fee_bps=params.fee_bps,
    )
    require_int_range(
        "amount_in",
        res.amount_in,
        minimum=1,
        maximum=DEX_SWAP_AMOUNT_MAX,
    )
    _validate_swap_post_reserves(
        new_reserve_in=res.new_reserve_in,
        new_reserve_out=res.new_reserve_out,
    )

    # Optional policy guard for exact-out quote quality in small-reserve regimes.
    _enforce_exact_out_overdelivery_policy(
        requested_amount_out=params.amount_out,
        overdelivery_gap=res.overdelivery_gap,
        max_overdelivery_gap_abs=params.max_overdelivery_gap_abs,
        max_overdelivery_gap_bps=params.max_overdelivery_gap_bps,
    )

    # Verify invariant: with protocol_fee_share_bps=0, k must not decrease.
    _raise_if_k_decreased(k_before=res.k_before, k_after=res.k_after)

    return res.amount_in, (res.new_reserve_in, res.new_reserve_out)


def compute_lp_mint(
    reserve0: Amount,
    reserve1: Amount,
    amount0: Amount,
    amount1: Amount,
    lp_supply: Amount,
) -> Amount:
    """
    Compute LP tokens to mint for an initial or proportional liquidity deposit.
    """
    params = _LpMintInputs(
        reserve0=reserve0,
        reserve1=reserve1,
        amount0=amount0,
        amount1=amount1,
        lp_supply=lp_supply,
    )
    _validate_lp_mint_inputs(params)

    lp = _compute_initial_lp_mint(params) if params.lp_supply == 0 else _compute_existing_lp_mint(params)
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
