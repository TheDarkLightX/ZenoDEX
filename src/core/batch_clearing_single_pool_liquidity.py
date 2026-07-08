"""Liquidity-intent replay helpers for single-pool batch clearing."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Callable, List, Protocol, Tuple

from ..state.balances import Amount, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.pools import PoolState
from .settlement import Fill, FillAction
from .settlement_fill_fields import read_optional_non_negative_fill_int

_AnyFn = Callable[..., Any]


class _SinglePoolRuntimeProtocol(Protocol):
    balances_scratch: BalanceTable
    lp_scratch: LPTable
    current_reserves: Tuple[Amount, Amount]
    current_lp_supply: Amount
    fills: List[Fill]


@dataclass(frozen=True)
class _SinglePoolLiquidityContext:
    pool_state: PoolState
    runtime: _SinglePoolRuntimeProtocol
    process_liquidity_intent_fn: _AnyFn


@dataclass(frozen=True)
class _LiquidityRuntimeRequest:
    intent: Intent
    fill: Fill
    snap_pool: PoolState
    runtime: _SinglePoolRuntimeProtocol
    recipient: PubKey


@dataclass(frozen=True)
class _AddLiquidityFillAmounts:
    amount0_used: int
    amount1_used: int
    lp_minted: int


@dataclass(frozen=True)
class _RemoveLiquidityFillAmounts:
    amount0_out: int
    amount1_out: int
    lp_burned: int


def _process_liquidity_for_single_pool(
    liquidity_intents: List[Intent],
    context: _SinglePoolLiquidityContext,
) -> None:
    runtime = context.runtime
    for intent in liquidity_intents:
        snap_pool = replace(
            context.pool_state,
            reserve0=runtime.current_reserves[0],
            reserve1=runtime.current_reserves[1],
            lp_supply=runtime.current_lp_supply,
        )
        fill = context.process_liquidity_intent_fn(
            intent,
            snap_pool,
            runtime.lp_scratch,
            runtime.balances_scratch,
        )
        runtime.fills.append(fill)

        if fill.action != FillAction.FILL:
            continue
        recipient = intent.get_field("recipient", intent.sender_pubkey)
        request = _LiquidityRuntimeRequest(
            intent=intent,
            fill=fill,
            snap_pool=snap_pool,
            runtime=runtime,
            recipient=recipient,
        )
        if intent.kind == IntentKind.ADD_LIQUIDITY:
            _apply_add_liquidity_to_single_pool_runtime(request)
        else:
            _apply_remove_liquidity_to_single_pool_runtime(request)


def _apply_add_liquidity_to_single_pool_runtime(request: _LiquidityRuntimeRequest) -> None:
    amounts = _read_add_liquidity_fill_amounts(request.fill)
    runtime = request.runtime
    snap_pool = request.snap_pool
    runtime.current_reserves = (
        runtime.current_reserves[0] + amounts.amount0_used,
        runtime.current_reserves[1] + amounts.amount1_used,
    )
    runtime.current_lp_supply += amounts.lp_minted
    runtime.balances_scratch.subtract(request.intent.sender_pubkey, snap_pool.asset0, amounts.amount0_used)
    runtime.balances_scratch.subtract(request.intent.sender_pubkey, snap_pool.asset1, amounts.amount1_used)
    runtime.lp_scratch.add(request.recipient, snap_pool.pool_id, amounts.lp_minted)


def _apply_remove_liquidity_to_single_pool_runtime(request: _LiquidityRuntimeRequest) -> None:
    amounts = _read_remove_liquidity_fill_amounts(request.fill)
    runtime = request.runtime
    snap_pool = request.snap_pool
    runtime.current_reserves = (
        runtime.current_reserves[0] - amounts.amount0_out,
        runtime.current_reserves[1] - amounts.amount1_out,
    )
    runtime.current_lp_supply -= amounts.lp_burned
    runtime.lp_scratch.subtract(request.intent.sender_pubkey, snap_pool.pool_id, amounts.lp_burned)
    runtime.balances_scratch.add(request.recipient, snap_pool.asset0, amounts.amount0_out)
    runtime.balances_scratch.add(request.recipient, snap_pool.asset1, amounts.amount1_out)


def _read_add_liquidity_fill_amounts(fill: Fill) -> _AddLiquidityFillAmounts:
    return _AddLiquidityFillAmounts(
        amount0_used=_read_single_pool_fill_int(
            fill.amount0_used,
            operation="ADD_LIQUIDITY",
            field_name="amount0_used",
            fill=fill,
        ),
        amount1_used=_read_single_pool_fill_int(
            fill.amount1_used,
            operation="ADD_LIQUIDITY",
            field_name="amount1_used",
            fill=fill,
        ),
        lp_minted=_read_single_pool_fill_int(
            fill.lp_minted,
            operation="ADD_LIQUIDITY",
            field_name="lp_minted",
            fill=fill,
        ),
    )


def _read_remove_liquidity_fill_amounts(fill: Fill) -> _RemoveLiquidityFillAmounts:
    return _RemoveLiquidityFillAmounts(
        amount0_out=_read_single_pool_fill_int(
            fill.amount0_out,
            operation="REMOVE_LIQUIDITY",
            field_name="amount0_out",
            fill=fill,
        ),
        amount1_out=_read_single_pool_fill_int(
            fill.amount1_out,
            operation="REMOVE_LIQUIDITY",
            field_name="amount1_out",
            fill=fill,
        ),
        lp_burned=_read_single_pool_fill_int(
            fill.lp_burned,
            operation="REMOVE_LIQUIDITY",
            field_name="lp_burned",
            fill=fill,
        ),
    )


def _read_single_pool_fill_int(value: object, *, operation: str, field_name: str, fill: Fill) -> int:
    parsed, err = read_optional_non_negative_fill_int(
        value,
        operation=operation,
        field_name=field_name,
        intent_id=fill.intent_id,
    )
    if err is not None:
        raise TypeError(err)
    return int(parsed)
