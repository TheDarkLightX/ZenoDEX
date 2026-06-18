"""Single-pool batch clearing orchestration helpers."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Callable, List, Optional, Tuple

from ..state.balances import Amount, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.pools import PoolState
from .batch_clearing_swaps import _SwapFillReserveRequest
from .domain_limits import is_strict_int
from .settlement import Fill, FillAction
from .settlement_fill_fields import read_optional_non_negative_fill_int

_AnyFn = Callable[..., Any]


@dataclass(frozen=True)
class _SinglePoolOrderingPolicy:
    swap_ordering: str
    ordering_choices: frozenset[str]
    limit_price: str
    optimal_ab_bounded: str
    greedy_ab: str
    greedy_ab_refined: str
    greedy_ab_global: str
    mci_ab_global: str
    cow_pair_netting_v1: str
    max_brute_force_n: int


@dataclass(frozen=True)
class _SinglePoolFactories:
    copy_balance_table_fn: _AnyFn
    copy_lp_table_fn: _AnyFn
    cow_pair_netting_fn: _AnyFn
    order_limit_price_fn: _AnyFn
    order_optimal_ab_bounded_fn: _AnyFn
    order_greedy_ab_fn: _AnyFn
    order_mci_ab_fn: _AnyFn
    refine_b_ordering_fn: _AnyFn
    refine_ab_ordering_global_fn: _AnyFn
    process_swap_intent_fn: _AnyFn
    reserves_after_swap_fill_fn: _AnyFn
    apply_swap_fill_to_scratch_balances_fn: _AnyFn
    process_liquidity_intent_fn: _AnyFn


@dataclass
class _SinglePoolRuntime:
    balances_scratch: BalanceTable
    lp_scratch: LPTable
    current_reserves: Tuple[Amount, Amount]
    current_lp_supply: Amount
    fills: List[Fill]


def _validate_single_pool_policy(
    policy: _SinglePoolOrderingPolicy,
    *,
    protocol_fee_share_bps: int,
    protocol_fee_recipient_pubkey: Optional[PubKey],
) -> None:
    if policy.swap_ordering not in policy.ordering_choices:
        raise ValueError(f"unsupported swap_ordering: {policy.swap_ordering!r}")
    if not is_strict_int(protocol_fee_share_bps) or not (0 <= protocol_fee_share_bps <= 10000):
        raise ValueError("protocol_fee_share_bps must be an int in [0, 10000]")
    if protocol_fee_share_bps > 0 and not protocol_fee_recipient_pubkey:
        raise ValueError("protocol_fee_recipient_pubkey is required when protocol_fee_share_bps > 0")


def _partition_single_pool_intents(intents: List[Intent]) -> Tuple[List[Intent], List[Intent]]:
    swap_intents = [
        intent for intent in intents if intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT)
    ]
    liquidity_intents = [
        intent for intent in intents if intent.kind in (IntentKind.ADD_LIQUIDITY, IntentKind.REMOVE_LIQUIDITY)
    ]
    return swap_intents, liquidity_intents


def _apply_cow_pair_netting_pass(
    swap_intents: List[Intent],
    pool_state: PoolState,
    runtime: _SinglePoolRuntime,
    policy: _SinglePoolOrderingPolicy,
    factories: _SinglePoolFactories,
) -> Tuple[str, List[Intent]]:
    if policy.swap_ordering != policy.cow_pair_netting_v1:
        return policy.swap_ordering, swap_intents

    netted_fills, remaining_swaps = factories.cow_pair_netting_fn(
        swap_intents,
        pool_state=pool_state,
        balances=runtime.balances_scratch,
    )
    runtime.fills.extend(netted_fills)
    post_swap_ordering = (
        policy.optimal_ab_bounded if len(remaining_swaps) <= policy.max_brute_force_n else policy.greedy_ab_refined
    )
    return post_swap_ordering, remaining_swaps


def _order_swaps_for_single_pool(
    swap_intents: List[Intent],
    pool_state: PoolState,
    runtime: _SinglePoolRuntime,
    post_swap_ordering: str,
    policy: _SinglePoolOrderingPolicy,
    factories: _SinglePoolFactories,
) -> List[Intent]:
    if post_swap_ordering == policy.optimal_ab_bounded:
        return factories.order_optimal_ab_bounded_fn(
            swap_intents,
            pool_state=pool_state,
            balances=runtime.balances_scratch,
            reserves=runtime.current_reserves,
        )
    if post_swap_ordering == policy.greedy_ab:
        return factories.order_greedy_ab_fn(swap_intents, pool_state=pool_state, reserves=runtime.current_reserves)
    if post_swap_ordering == policy.greedy_ab_refined:
        greedy = factories.order_greedy_ab_fn(swap_intents, pool_state=pool_state, reserves=runtime.current_reserves)
        return factories.refine_b_ordering_fn(greedy, pool_state=pool_state, reserves=runtime.current_reserves)
    if post_swap_ordering == policy.greedy_ab_global:
        greedy = factories.order_greedy_ab_fn(swap_intents, pool_state=pool_state, reserves=runtime.current_reserves)
        refined = factories.refine_b_ordering_fn(greedy, pool_state=pool_state, reserves=runtime.current_reserves)
        return factories.refine_ab_ordering_global_fn(refined, pool_state=pool_state, reserves=runtime.current_reserves)
    if post_swap_ordering == policy.mci_ab_global:
        mci = factories.order_mci_ab_fn(swap_intents, pool_state=pool_state, reserves=runtime.current_reserves)
        return factories.refine_ab_ordering_global_fn(mci, pool_state=pool_state, reserves=runtime.current_reserves)
    return factories.order_limit_price_fn(swap_intents)


def _process_ordered_swaps_for_single_pool(
    sorted_swaps: List[Intent],
    pool_state: PoolState,
    runtime: _SinglePoolRuntime,
    factories: _SinglePoolFactories,
    *,
    protocol_fee_share_bps: int,
    protocol_fee_recipient_pubkey: Optional[PubKey],
) -> None:
    for intent in sorted_swaps:
        fill = factories.process_swap_intent_fn(
            intent,
            runtime.current_reserves,
            pool_state,
            runtime.balances_scratch,
            protocol_fee_share_bps=protocol_fee_share_bps,
        )
        runtime.fills.append(fill)

        if fill.action != FillAction.FILL:
            continue
        runtime.current_reserves = factories.reserves_after_swap_fill_fn(
            _SwapFillReserveRequest(
                intent=intent,
                fill=fill,
                pool_state=pool_state,
                reserves=runtime.current_reserves,
                protocol_fee_share_bps=protocol_fee_share_bps,
            )
        )
        factories.apply_swap_fill_to_scratch_balances_fn(
            intent,
            fill,
            runtime.balances_scratch,
            protocol_fee_recipient_pubkey,
        )


def _process_liquidity_for_single_pool(
    liquidity_intents: List[Intent],
    pool_state: PoolState,
    runtime: _SinglePoolRuntime,
    factories: _SinglePoolFactories,
) -> None:
    for intent in liquidity_intents:
        snap_pool = replace(
            pool_state,
            reserve0=runtime.current_reserves[0],
            reserve1=runtime.current_reserves[1],
            lp_supply=runtime.current_lp_supply,
        )
        fill = factories.process_liquidity_intent_fn(
            intent,
            snap_pool,
            runtime.lp_scratch,
            runtime.balances_scratch,
        )
        runtime.fills.append(fill)

        if fill.action != FillAction.FILL:
            continue
        recipient = intent.get_field("recipient", intent.sender_pubkey)
        if intent.kind == IntentKind.ADD_LIQUIDITY:
            amount0_used = _read_single_pool_fill_int(
                fill.amount0_used,
                operation="ADD_LIQUIDITY",
                field_name="amount0_used",
                fill=fill,
            )
            amount1_used = _read_single_pool_fill_int(
                fill.amount1_used,
                operation="ADD_LIQUIDITY",
                field_name="amount1_used",
                fill=fill,
            )
            lp_minted = _read_single_pool_fill_int(
                fill.lp_minted,
                operation="ADD_LIQUIDITY",
                field_name="lp_minted",
                fill=fill,
            )
            runtime.current_reserves = (
                runtime.current_reserves[0] + amount0_used,
                runtime.current_reserves[1] + amount1_used,
            )
            runtime.current_lp_supply += lp_minted
            runtime.balances_scratch.subtract(intent.sender_pubkey, snap_pool.asset0, amount0_used)
            runtime.balances_scratch.subtract(intent.sender_pubkey, snap_pool.asset1, amount1_used)
            runtime.lp_scratch.add(recipient, snap_pool.pool_id, lp_minted)
        else:
            amount0_out = _read_single_pool_fill_int(
                fill.amount0_out,
                operation="REMOVE_LIQUIDITY",
                field_name="amount0_out",
                fill=fill,
            )
            amount1_out = _read_single_pool_fill_int(
                fill.amount1_out,
                operation="REMOVE_LIQUIDITY",
                field_name="amount1_out",
                fill=fill,
            )
            lp_burned = _read_single_pool_fill_int(
                fill.lp_burned,
                operation="REMOVE_LIQUIDITY",
                field_name="lp_burned",
                fill=fill,
            )
            runtime.current_reserves = (
                runtime.current_reserves[0] - amount0_out,
                runtime.current_reserves[1] - amount1_out,
            )
            runtime.current_lp_supply -= lp_burned
            runtime.lp_scratch.subtract(intent.sender_pubkey, snap_pool.pool_id, lp_burned)
            runtime.balances_scratch.add(recipient, snap_pool.asset0, amount0_out)
            runtime.balances_scratch.add(recipient, snap_pool.asset1, amount1_out)


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


def clear_batch_single_pool_with_factories(
    intents: List[Intent],
    pool_state: PoolState,
    balances: BalanceTable,
    lp_balances: LPTable,
    *,
    policy: _SinglePoolOrderingPolicy,
    factories: _SinglePoolFactories,
    protocol_fee_share_bps: int,
    protocol_fee_recipient_pubkey: Optional[PubKey],
) -> List[Fill]:
    _validate_single_pool_policy(
        policy,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )
    swap_intents, liquidity_intents = _partition_single_pool_intents(intents)
    runtime = _SinglePoolRuntime(
        balances_scratch=factories.copy_balance_table_fn(balances),
        lp_scratch=factories.copy_lp_table_fn(lp_balances),
        current_reserves=(pool_state.reserve0, pool_state.reserve1),
        current_lp_supply=pool_state.lp_supply,
        fills=[],
    )
    post_swap_ordering, remaining_swaps = _apply_cow_pair_netting_pass(
        swap_intents,
        pool_state,
        runtime,
        policy,
        factories,
    )
    sorted_swaps = _order_swaps_for_single_pool(
        remaining_swaps,
        pool_state,
        runtime,
        post_swap_ordering,
        policy,
        factories,
    )
    _process_ordered_swaps_for_single_pool(
        sorted_swaps,
        pool_state,
        runtime,
        factories,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )
    _process_liquidity_for_single_pool(liquidity_intents, pool_state, runtime, factories)
    return runtime.fills
