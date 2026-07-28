"""Exact liquidity kernels over committed pool values and integer scalars."""

from __future__ import annotations

from dataclasses import dataclass
from typing import final

from ..kernels.python.lp_math_v7 import (
    MIN_LP_LOCK,
    burn_liquidity,
    mint_liquidity_initial,
    optimal_liquidity,
)
from ..state.state_snapshot_values import (
    POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1,
    POOL_STATUS_MEMBER_VALUES_V1,
    CommittedPoolStateV1,
)
from .domain_limits import (
    DEX_LP_AMOUNT_MAX,
    DEX_LP_SUPPLY_MAX,
    DEX_POOL_RESERVE_MAX,
    require_int_range,
)


@final
@dataclass(frozen=True, slots=True)
class AddLiquidityKernelInputV1:
    amount0_desired: int
    amount1_desired: int
    amount0_min: int
    amount1_min: int

    def __post_init__(self) -> None:
        require_int_range(
            "amount0_desired",
            self.amount0_desired,
            minimum=1,
            maximum=DEX_LP_AMOUNT_MAX,
        )
        require_int_range(
            "amount1_desired",
            self.amount1_desired,
            minimum=1,
            maximum=DEX_LP_AMOUNT_MAX,
        )
        require_int_range(
            "amount0_min",
            self.amount0_min,
            minimum=0,
            maximum=DEX_LP_AMOUNT_MAX,
        )
        require_int_range(
            "amount1_min",
            self.amount1_min,
            minimum=0,
            maximum=DEX_LP_AMOUNT_MAX,
        )


@final
@dataclass(frozen=True, slots=True)
class RemoveLiquidityKernelInputV1:
    lp_amount: int
    amount0_min: int
    amount1_min: int

    def __post_init__(self) -> None:
        require_int_range(
            "lp_amount",
            self.lp_amount,
            minimum=1,
            maximum=DEX_LP_SUPPLY_MAX,
        )
        require_int_range(
            "amount0_min",
            self.amount0_min,
            minimum=0,
            maximum=DEX_POOL_RESERVE_MAX,
        )
        require_int_range(
            "amount1_min",
            self.amount1_min,
            minimum=0,
            maximum=DEX_POOL_RESERVE_MAX,
        )


def _revalidate_add_inputs_v1(inputs: AddLiquidityKernelInputV1) -> None:
    if type(inputs) is not AddLiquidityKernelInputV1:
        raise TypeError("inputs must be exact AddLiquidityKernelInputV1")
    inputs.__post_init__()


def _revalidate_remove_inputs_v1(inputs: RemoveLiquidityKernelInputV1) -> None:
    if type(inputs) is not RemoveLiquidityKernelInputV1:
        raise TypeError("inputs must be exact RemoveLiquidityKernelInputV1")
    inputs.__post_init__()


def _compute_lp_mint_v1(
    *,
    reserve0: int,
    reserve1: int,
    amount0: int,
    amount1: int,
    lp_supply: int,
) -> int:
    if lp_supply == 0:
        minted, _total_supply = mint_liquidity_initial(
            amount0=amount0,
            amount1=amount1,
            min_lp_lock=MIN_LP_LOCK,
        )
    else:
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
        minted = min(
            (amount0 * lp_supply) // reserve0,
            (amount1 * lp_supply) // reserve1,
        )
    if minted <= 0:
        raise ValueError(f"Computed LP amount is non-positive: {minted}")
    return minted


def initial_liquidity_for_pool_creation_v1(
    amount0: int,
    amount1: int,
) -> int:
    """Return the creator LP amount for one exact initial deposit."""

    amount0 = require_int_range(
        "amount0",
        amount0,
        minimum=1,
        maximum=DEX_LP_AMOUNT_MAX,
    )
    amount1 = require_int_range(
        "amount1",
        amount1,
        minimum=1,
        maximum=DEX_LP_AMOUNT_MAX,
    )
    minted, total_supply = mint_liquidity_initial(
        amount0=amount0,
        amount1=amount1,
        min_lp_lock=MIN_LP_LOCK,
    )
    if total_supply != minted + MIN_LP_LOCK:
        raise ValueError("initial liquidity kernel returned an inconsistent supply")
    return minted


def add_liquidity_kernel_v1(
    *,
    reserve0: int,
    reserve1: int,
    lp_supply: int,
    inputs: AddLiquidityKernelInputV1,
) -> tuple[int, int, int]:
    """Return ratio-preserving deposits and minted LP from exact scalars."""

    _revalidate_add_inputs_v1(inputs)
    reserve0 = require_int_range(
        "pool_state.reserve0",
        reserve0,
        minimum=0,
        maximum=DEX_POOL_RESERVE_MAX,
    )
    reserve1 = require_int_range(
        "pool_state.reserve1",
        reserve1,
        minimum=0,
        maximum=DEX_POOL_RESERVE_MAX,
    )
    lp_supply = require_int_range(
        "pool_state.lp_supply",
        lp_supply,
        minimum=0,
        maximum=DEX_LP_SUPPLY_MAX,
    )
    if reserve0 == 0 or reserve1 == 0:
        raise ValueError("Cannot add liquidity to empty pool")

    optimal = optimal_liquidity(
        reserve0=reserve0,
        reserve1=reserve1,
        amount0_desired=inputs.amount0_desired,
        amount1_desired=inputs.amount1_desired,
    )
    amount0_used = optimal.amount0_used
    amount1_used = optimal.amount1_used
    if amount0_used < inputs.amount0_min:
        raise ValueError(f"amount0_used ({amount0_used}) < amount0_min ({inputs.amount0_min})")
    if amount1_used < inputs.amount1_min:
        raise ValueError(f"amount1_used ({amount1_used}) < amount1_min ({inputs.amount1_min})")
    minted = _compute_lp_mint_v1(
        reserve0=reserve0,
        reserve1=reserve1,
        amount0=amount0_used,
        amount1=amount1_used,
        lp_supply=lp_supply,
    )
    return amount0_used, amount1_used, minted


def remove_liquidity_kernel_v1(
    *,
    reserve0: int,
    reserve1: int,
    lp_supply: int,
    inputs: RemoveLiquidityKernelInputV1,
) -> tuple[int, int]:
    """Return exact reserve withdrawals for one LP burn."""

    _revalidate_remove_inputs_v1(inputs)
    reserve0 = require_int_range(
        "pool_state.reserve0",
        reserve0,
        minimum=0,
        maximum=DEX_POOL_RESERVE_MAX,
    )
    reserve1 = require_int_range(
        "pool_state.reserve1",
        reserve1,
        minimum=0,
        maximum=DEX_POOL_RESERVE_MAX,
    )
    lp_supply = require_int_range(
        "pool_state.lp_supply",
        lp_supply,
        minimum=1,
        maximum=DEX_LP_SUPPLY_MAX,
    )
    if inputs.lp_amount > lp_supply:
        raise ValueError(f"Cannot burn more LP than supply: {inputs.lp_amount} > {lp_supply}")

    result = burn_liquidity(
        lp_amount=inputs.lp_amount,
        reserve0=reserve0,
        reserve1=reserve1,
        total_supply=lp_supply,
    )
    amount0_out = result.amount0_out
    amount1_out = result.amount1_out
    if amount0_out < inputs.amount0_min:
        raise ValueError(f"amount0_out ({amount0_out}) < amount0_min ({inputs.amount0_min})")
    if amount1_out < inputs.amount1_min:
        raise ValueError(f"amount1_out ({amount1_out}) < amount1_min ({inputs.amount1_min})")
    return amount0_out, amount1_out


def _require_active_committed_pool_v1(pool_state: CommittedPoolStateV1) -> None:
    if type(pool_state) is not CommittedPoolStateV1:
        raise TypeError("pool_state must be an exact committed pool")
    pool_state.__post_init__()
    if pool_state.status.member_ordinal != POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1:
        status = POOL_STATUS_MEMBER_VALUES_V1[pool_state.status.member_ordinal]
        raise ValueError(f"Pool is not active: PoolStatus.{status}")


def add_liquidity_for_committed_pool_v1(
    pool_state: CommittedPoolStateV1,
    inputs: AddLiquidityKernelInputV1,
) -> tuple[int, int, int]:
    _require_active_committed_pool_v1(pool_state)
    return add_liquidity_kernel_v1(
        reserve0=pool_state.reserve0,
        reserve1=pool_state.reserve1,
        lp_supply=pool_state.lp_supply,
        inputs=inputs,
    )


def remove_liquidity_for_committed_pool_v1(
    pool_state: CommittedPoolStateV1,
    inputs: RemoveLiquidityKernelInputV1,
) -> tuple[int, int]:
    _require_active_committed_pool_v1(pool_state)
    return remove_liquidity_kernel_v1(
        reserve0=pool_state.reserve0,
        reserve1=pool_state.reserve1,
        lp_supply=pool_state.lp_supply,
        inputs=inputs,
    )
