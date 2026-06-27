"""Single-pool batch clearing orchestration helpers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, List, Optional, Tuple

from ..state.balances import Amount, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.pools import PoolState
from .batch_clearing_ordering import _OptimalAbBoundedRequest
from .batch_clearing_single_pool_liquidity import (
    _process_liquidity_for_single_pool,
    _SinglePoolLiquidityContext,
)
from .batch_clearing_swaps import _SwapFillReserveRequest, _SwapIntentRuntimeRequest
from .domain_limits import is_strict_int
from .settlement import Fill, FillAction

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


@dataclass(frozen=True)
class _ClearSinglePoolRequest:
    intents: List[Intent]
    pool_state: PoolState
    balances: BalanceTable
    lp_balances: LPTable
    policy: _SinglePoolOrderingPolicy
    factories: _SinglePoolFactories
    protocol_fee_share_bps: int
    protocol_fee_recipient_pubkey: Optional[PubKey]
    # Default-off grinding-resistant tie-break seed (see neutral_tiebreak.py).
    # None => byte-identical to the pre-seam canonical order.
    swap_tiebreak_seed: bytes | None = None


@dataclass
class _SinglePoolRuntime:
    balances_scratch: BalanceTable
    lp_scratch: LPTable
    current_reserves: Tuple[Amount, Amount]
    current_lp_supply: Amount
    fills: List[Fill]


@dataclass(frozen=True)
class _SinglePoolExecutionContext:
    pool_state: PoolState
    runtime: _SinglePoolRuntime
    policy: _SinglePoolOrderingPolicy
    factories: _SinglePoolFactories
    protocol_fee_share_bps: int
    protocol_fee_recipient_pubkey: Optional[PubKey]
    swap_tiebreak_seed: bytes | None = None


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
    context: _SinglePoolExecutionContext,
) -> Tuple[str, List[Intent]]:
    policy = context.policy
    if policy.swap_ordering != policy.cow_pair_netting_v1:
        return policy.swap_ordering, swap_intents

    netted_fills, remaining_swaps = context.factories.cow_pair_netting_fn(
        swap_intents,
        pool_state=context.pool_state,
        balances=context.runtime.balances_scratch,
        swap_tiebreak_seed=context.swap_tiebreak_seed,
    )
    context.runtime.fills.extend(netted_fills)
    post_swap_ordering = (
        policy.optimal_ab_bounded if len(remaining_swaps) <= policy.max_brute_force_n else policy.greedy_ab_refined
    )
    return post_swap_ordering, remaining_swaps


def _order_swaps_for_single_pool(
    swap_intents: List[Intent],
    post_swap_ordering: str,
    context: _SinglePoolExecutionContext,
) -> List[Intent]:
    policy = context.policy
    factories = context.factories
    pool_state = context.pool_state
    runtime = context.runtime
    seed = context.swap_tiebreak_seed  # None => grindable status quo (byte-identical)
    if post_swap_ordering == policy.optimal_ab_bounded:
        return factories.order_optimal_ab_bounded_fn(
            _OptimalAbBoundedRequest(
                intents=swap_intents,
                pool_state=pool_state,
                balances=runtime.balances_scratch,
                reserves=runtime.current_reserves,
                seed=seed,
            )
        )
    if post_swap_ordering == policy.greedy_ab:
        return factories.order_greedy_ab_fn(swap_intents, pool_state=pool_state, reserves=runtime.current_reserves, seed=seed)
    if post_swap_ordering == policy.greedy_ab_refined:
        greedy = factories.order_greedy_ab_fn(swap_intents, pool_state=pool_state, reserves=runtime.current_reserves, seed=seed)
        return factories.refine_b_ordering_fn(greedy, pool_state=pool_state, reserves=runtime.current_reserves)
    if post_swap_ordering == policy.greedy_ab_global:
        greedy = factories.order_greedy_ab_fn(swap_intents, pool_state=pool_state, reserves=runtime.current_reserves, seed=seed)
        refined = factories.refine_b_ordering_fn(greedy, pool_state=pool_state, reserves=runtime.current_reserves)
        return factories.refine_ab_ordering_global_fn(refined, pool_state=pool_state, reserves=runtime.current_reserves)
    if post_swap_ordering == policy.mci_ab_global:
        mci = factories.order_mci_ab_fn(swap_intents, pool_state=pool_state, reserves=runtime.current_reserves, seed=seed)
        return factories.refine_ab_ordering_global_fn(mci, pool_state=pool_state, reserves=runtime.current_reserves)
    return factories.order_limit_price_fn(swap_intents, seed=seed)


def _process_ordered_swaps_for_single_pool(
    sorted_swaps: List[Intent],
    context: _SinglePoolExecutionContext,
) -> None:
    runtime = context.runtime
    factories = context.factories
    for intent in sorted_swaps:
        fill = factories.process_swap_intent_fn(
            _SwapIntentRuntimeRequest(
                intent=intent,
                reserves=runtime.current_reserves,
                pool_state=context.pool_state,
                balances=runtime.balances_scratch,
                protocol_fee_share_bps=context.protocol_fee_share_bps,
            )
        )
        runtime.fills.append(fill)

        if fill.action != FillAction.FILL:
            continue
        runtime.current_reserves = factories.reserves_after_swap_fill_fn(
            _SwapFillReserveRequest(
                intent=intent,
                fill=fill,
                pool_state=context.pool_state,
                reserves=runtime.current_reserves,
                protocol_fee_share_bps=context.protocol_fee_share_bps,
            )
        )
        factories.apply_swap_fill_to_scratch_balances_fn(
            intent,
            fill,
            runtime.balances_scratch,
            context.protocol_fee_recipient_pubkey,
        )


def clear_batch_single_pool_with_factories(request: _ClearSinglePoolRequest) -> List[Fill]:
    _validate_single_pool_policy(
        request.policy,
        protocol_fee_share_bps=request.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=request.protocol_fee_recipient_pubkey,
    )
    swap_intents, liquidity_intents = _partition_single_pool_intents(request.intents)
    runtime = _SinglePoolRuntime(
        balances_scratch=request.factories.copy_balance_table_fn(request.balances),
        lp_scratch=request.factories.copy_lp_table_fn(request.lp_balances),
        current_reserves=(request.pool_state.reserve0, request.pool_state.reserve1),
        current_lp_supply=request.pool_state.lp_supply,
        fills=[],
    )
    context = _SinglePoolExecutionContext(
        pool_state=request.pool_state,
        runtime=runtime,
        policy=request.policy,
        factories=request.factories,
        protocol_fee_share_bps=request.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=request.protocol_fee_recipient_pubkey,
        swap_tiebreak_seed=request.swap_tiebreak_seed,
    )
    post_swap_ordering, remaining_swaps = _apply_cow_pair_netting_pass(
        swap_intents,
        context,
    )
    sorted_swaps = _order_swaps_for_single_pool(
        remaining_swaps,
        post_swap_ordering,
        context,
    )
    _process_ordered_swaps_for_single_pool(
        sorted_swaps,
        context,
    )
    _process_liquidity_for_single_pool(
        liquidity_intents,
        _SinglePoolLiquidityContext(
            pool_state=context.pool_state,
            runtime=context.runtime,
            process_liquidity_intent_fn=context.factories.process_liquidity_intent_fn,
        ),
    )
    return runtime.fills
