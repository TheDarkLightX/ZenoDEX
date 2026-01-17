"""
Liquidity math kernel (v7 semantics).

This module mirrors the intent of:
- `src/kernels/dex/lp_ratio_calculator_v7.yaml`
- `src/kernels/dex/lp_mint_v7.yaml`

It is written as a small set of pure functions with explicit rounding rules.
"""

from __future__ import annotations

import math
from dataclasses import dataclass


MIN_LP_LOCK = 1000


def _require_int(name: str, value: int) -> None:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")


@dataclass(frozen=True)
class OptimalLiquidityResult:
    amount0_used: int
    amount1_used: int
    amount0_refund: int
    amount1_refund: int


@dataclass(frozen=True)
class MintLiquidityResult:
    liquidity_minted: int
    amount0_used: int
    amount1_used: int
    amount0_refund: int
    amount1_refund: int
    new_reserve0: int
    new_reserve1: int
    new_total_supply: int


@dataclass(frozen=True)
class BurnLiquidityResult:
    amount0_out: int
    amount1_out: int


def optimal_liquidity(
    *,
    reserve0: int,
    reserve1: int,
    amount0_desired: int,
    amount1_desired: int,
) -> OptimalLiquidityResult:
    """
    Compute ratio-preserving used amounts and refunds.

    For an empty pool (reserve0 == 0 or reserve1 == 0), uses everything and refunds nothing.
    """
    for name, v in (
        ("reserve0", reserve0),
        ("reserve1", reserve1),
        ("amount0_desired", amount0_desired),
        ("amount1_desired", amount1_desired),
    ):
        _require_int(name, v)

    if reserve0 < 0 or reserve1 < 0:
        raise ValueError("reserves must be non-negative")
    if amount0_desired <= 0 or amount1_desired <= 0:
        raise ValueError("desired amounts must be positive")

    if reserve0 == 0 or reserve1 == 0:
        return OptimalLiquidityResult(
            amount0_used=amount0_desired,
            amount1_used=amount1_desired,
            amount0_refund=0,
            amount1_refund=0,
        )

    amount1_from_amount0 = (amount0_desired * reserve1) // reserve0
    if amount1_from_amount0 <= amount1_desired:
        amount0_used = amount0_desired
        amount1_used = amount1_from_amount0
    else:
        amount0_used = (amount1_desired * reserve0) // reserve1
        amount1_used = amount1_desired

    if amount0_used <= 0 or amount1_used <= 0:
        raise ValueError("computed used amounts must be positive")
    if amount0_used > amount0_desired or amount1_used > amount1_desired:
        raise AssertionError("used amounts exceed desired amounts")

    return OptimalLiquidityResult(
        amount0_used=amount0_used,
        amount1_used=amount1_used,
        amount0_refund=amount0_desired - amount0_used,
        amount1_refund=amount1_desired - amount1_used,
    )


def mint_liquidity_initial(*, amount0: int, amount1: int, min_lp_lock: int = MIN_LP_LOCK) -> tuple[int, int]:
    """
    Initial liquidity mint (pool creation).

    Returns (liquidity_minted_to_creator, total_supply_including_lock).
    """
    _require_int("amount0", amount0)
    _require_int("amount1", amount1)
    _require_int("min_lp_lock", min_lp_lock)
    if amount0 <= 0 or amount1 <= 0:
        raise ValueError("initial amounts must be positive")
    if min_lp_lock <= 0:
        raise ValueError("min_lp_lock must be positive")

    sqrt_product = math.isqrt(amount0 * amount1)
    if sqrt_product <= min_lp_lock:
        raise ValueError("insufficient initial liquidity (sqrt(amount0*amount1) <= MIN_LP_LOCK)")

    minted = sqrt_product - min_lp_lock
    total_supply = minted + min_lp_lock
    return minted, total_supply


def mint_liquidity(
    *,
    reserve0: int,
    reserve1: int,
    total_supply: int,
    amount0_desired: int,
    amount1_desired: int,
    min_liquidity: int = 0,
) -> MintLiquidityResult:
    """
    Mint LP tokens for a ratio-preserving deposit (Uniswap-v2 style).

    `total_supply` is the total LP supply including the MIN_LP_LOCK amount.
    """
    for name, v in (
        ("reserve0", reserve0),
        ("reserve1", reserve1),
        ("total_supply", total_supply),
        ("amount0_desired", amount0_desired),
        ("amount1_desired", amount1_desired),
        ("min_liquidity", min_liquidity),
    ):
        _require_int(name, v)

    if reserve0 < 0 or reserve1 < 0:
        raise ValueError("reserves must be non-negative")
    if total_supply < 0:
        raise ValueError("total_supply must be non-negative")
    if amount0_desired <= 0 or amount1_desired <= 0:
        raise ValueError("desired amounts must be positive")
    if min_liquidity < 0:
        raise ValueError("min_liquidity must be non-negative")

    if total_supply == 0:
        if reserve0 != 0 or reserve1 != 0:
            raise ValueError("cannot mint initial liquidity when reserves are non-zero")
        minted, new_total_supply = mint_liquidity_initial(amount0=amount0_desired, amount1=amount1_desired)
        return MintLiquidityResult(
            liquidity_minted=minted,
            amount0_used=amount0_desired,
            amount1_used=amount1_desired,
            amount0_refund=0,
            amount1_refund=0,
            new_reserve0=amount0_desired,
            new_reserve1=amount1_desired,
            new_total_supply=new_total_supply,
        )

    if reserve0 == 0 or reserve1 == 0:
        raise ValueError("cannot mint into an empty pool when total_supply > 0")

    opt = optimal_liquidity(
        reserve0=reserve0,
        reserve1=reserve1,
        amount0_desired=amount0_desired,
        amount1_desired=amount1_desired,
    )

    liquidity0 = (opt.amount0_used * total_supply) // reserve0
    liquidity1 = (opt.amount1_used * total_supply) // reserve1
    minted = min(liquidity0, liquidity1)
    if minted <= 0:
        raise ValueError("liquidity_minted is zero (deposit too small)")
    if minted < min_liquidity:
        raise ValueError("liquidity_minted below min_liquidity")

    return MintLiquidityResult(
        liquidity_minted=minted,
        amount0_used=opt.amount0_used,
        amount1_used=opt.amount1_used,
        amount0_refund=opt.amount0_refund,
        amount1_refund=opt.amount1_refund,
        new_reserve0=reserve0 + opt.amount0_used,
        new_reserve1=reserve1 + opt.amount1_used,
        new_total_supply=total_supply + minted,
    )


def burn_liquidity(*, lp_amount: int, reserve0: int, reserve1: int, total_supply: int) -> BurnLiquidityResult:
    """
    Burn LP tokens for underlying assets (floor rounding).
    """
    for name, v in (
        ("lp_amount", lp_amount),
        ("reserve0", reserve0),
        ("reserve1", reserve1),
        ("total_supply", total_supply),
    ):
        _require_int(name, v)

    if lp_amount <= 0:
        raise ValueError("lp_amount must be positive")
    if reserve0 < 0 or reserve1 < 0:
        raise ValueError("reserves must be non-negative")
    if total_supply <= 0:
        raise ValueError("total_supply must be positive")
    if lp_amount > total_supply:
        raise ValueError("cannot burn more than total_supply")

    amount0_out = (lp_amount * reserve0) // total_supply
    amount1_out = (lp_amount * reserve1) // total_supply
    if amount0_out < 0 or amount1_out < 0:
        raise ValueError("computed outputs must be non-negative")
    return BurnLiquidityResult(amount0_out=amount0_out, amount1_out=amount1_out)
