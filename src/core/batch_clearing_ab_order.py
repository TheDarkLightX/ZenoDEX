"""Bounded AB-objective swap ordering for batch clearing."""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Optional, Tuple

from ..state.balances import Amount, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.pools import CURVE_TAG_CPMM, PoolState

_AnyFn = Callable[..., Any]


@dataclass(frozen=True)
class _OptimalAbOrderingFactories:
    quote_exact_in_fn: _AnyFn
    quote_exact_out_fn: _AnyFn
    swap_exact_in_fn: _AnyFn
    swap_exact_out_fn: _AnyFn
    order_limit_price_fn: _AnyFn
    ab_ordering_key_fn: _AnyFn
    is_better_ab_key_fn: _AnyFn


@dataclass(frozen=True)
class _OptimalAbObjectiveContext:
    pool_state: PoolState
    first_asset_in: str
    r_in0: int
    r_out0: int
    sender_bal_in: Dict[PubKey, Amount]
    factories: _OptimalAbOrderingFactories


def _same_pool_direction_or_none(
    intents: List[Intent],
    pool_state: PoolState,
) -> Optional[Tuple[str, str]]:
    first_asset_in = intents[0].get_field("asset_in")
    first_asset_out = intents[0].get_field("asset_out")
    if not isinstance(first_asset_in, str) or not isinstance(first_asset_out, str):
        return None
    if first_asset_in == first_asset_out:
        return None
    if not (
        (first_asset_in == pool_state.asset0 and first_asset_out == pool_state.asset1)
        or (first_asset_in == pool_state.asset1 and first_asset_out == pool_state.asset0)
    ):
        return None

    for intent in intents[1:]:
        if intent.get_field("asset_in") != first_asset_in or intent.get_field("asset_out") != first_asset_out:
            return None
    return first_asset_in, first_asset_out


def _directional_reserves(
    first_asset_in: str,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> Tuple[int, int]:
    if first_asset_in == pool_state.asset0:
        return int(reserves[0]), int(reserves[1])
    return int(reserves[1]), int(reserves[0])


def _sender_input_balances(
    intents: List[Intent],
    balances: BalanceTable,
    first_asset_in: str,
) -> Dict[PubKey, Amount]:
    return {intent.sender_pubkey: balances.get(intent.sender_pubkey, first_asset_in) for intent in intents}


def _objective_exact_in_contribution(
    intent: Intent,
    context: _OptimalAbObjectiveContext,
    *,
    r_in: int,
    r_out: int,
    bal_in: Dict[PubKey, Amount],
) -> Optional[Tuple[int, int, int, int]]:
    amount_in = intent.get_field("amount_in")
    min_amount_out = intent.get_field("min_amount_out", 0)
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return None
    if not isinstance(min_amount_out, int) or isinstance(min_amount_out, bool) or min_amount_out < 0:
        return None
    if bal_in.get(intent.sender_pubkey, 0) < amount_in:
        return None

    try:
        if context.pool_state.curve_tag == CURVE_TAG_CPMM:
            quote = context.factories.quote_exact_in_fn(
                reserve_in=r_in,
                reserve_out=r_out,
                amount_in=amount_in,
                fee_bps=context.pool_state.fee_bps,
            )
            amount_out = quote.amount_out
            new_r_in, new_r_out = quote.reserve_in_after, quote.reserve_out_after
        else:
            amount_out, (new_r_in, new_r_out) = context.factories.swap_exact_in_fn(
                context.pool_state,
                reserve_in=r_in,
                reserve_out=r_out,
                amount_in=amount_in,
            )
    except ValueError:
        return None
    if amount_out < min_amount_out:
        return None

    surplus = int(amount_out) - int(min_amount_out)
    return int(amount_in), surplus, int(new_r_in), int(new_r_out)


def _objective_exact_out_contribution(
    intent: Intent,
    context: _OptimalAbObjectiveContext,
    *,
    r_in: int,
    r_out: int,
    bal_in: Dict[PubKey, Amount],
) -> Optional[Tuple[int, int, int]]:
    amount_out = intent.get_field("amount_out")
    max_amount_in = intent.get_field("max_amount_in")
    if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
        return None
    if not isinstance(max_amount_in, int) or isinstance(max_amount_in, bool) or max_amount_in < 0:
        return None

    try:
        if context.pool_state.curve_tag == CURVE_TAG_CPMM:
            quote = context.factories.quote_exact_out_fn(
                reserve_in=r_in,
                reserve_out=r_out,
                amount_out=amount_out,
                fee_bps=context.pool_state.fee_bps,
            )
            amount_in = quote.amount_in
            new_r_in, new_r_out = quote.reserve_in_after, quote.reserve_out_after
        else:
            amount_in, (new_r_in, new_r_out) = context.factories.swap_exact_out_fn(
                context.pool_state,
                reserve_in=r_in,
                reserve_out=r_out,
                amount_out=amount_out,
            )
    except ValueError:
        return None
    if amount_in > max_amount_in:
        return None
    if bal_in.get(intent.sender_pubkey, 0) < amount_in:
        return None

    return int(amount_in), int(new_r_in), int(new_r_out)


def _objective_for_order(
    order: Tuple[Intent, ...],
    context: _OptimalAbObjectiveContext,
) -> Tuple[int, int, Tuple[str, ...]]:
    r_in = context.r_in0
    r_out = context.r_out0
    bal_in = dict(context.sender_bal_in)
    amount_a = 0
    surplus_b = 0

    for intent in order:
        if intent.kind == IntentKind.SWAP_EXACT_IN:
            contribution = _objective_exact_in_contribution(intent, context, r_in=r_in, r_out=r_out, bal_in=bal_in)
            if contribution is None:
                continue
            amount_in, surplus, r_in, r_out = contribution
            amount_a += amount_in
            surplus_b += surplus
            bal_in[intent.sender_pubkey] = int(bal_in.get(intent.sender_pubkey, 0) - amount_in)
            continue

        if intent.kind == IntentKind.SWAP_EXACT_OUT:
            contribution = _objective_exact_out_contribution(intent, context, r_in=r_in, r_out=r_out, bal_in=bal_in)
            if contribution is None:
                continue
            amount_in, r_in, r_out = contribution
            amount_a += amount_in
            bal_in[intent.sender_pubkey] = int(bal_in.get(intent.sender_pubkey, 0) - amount_in)
            continue

    return int(amount_a), int(surplus_b), tuple(intent.intent_id for intent in order)


def _best_order_by_objective(
    intents: List[Intent],
    context: _OptimalAbObjectiveContext,
) -> Optional[Tuple[Intent, ...]]:
    best_a = -1
    best_b = -1
    best_order_ids: Tuple[str, ...] | None = None
    best_order: Tuple[Intent, ...] | None = None

    for perm in itertools.permutations(intents):
        cand_key = context.factories.ab_ordering_key_fn(A_B_order=_objective_for_order(perm, context))
        if best_order is None or context.factories.is_better_ab_key_fn(
            cand_key,
            (best_a, best_b, best_order_ids or tuple()),
        ):
            best_a, best_b, best_order_ids, best_order = cand_key[0], cand_key[1], cand_key[2], perm
    return best_order


def order_swaps_optimal_ab_bounded_with_factories(
    intents: List[Intent],
    *,
    pool_state: PoolState,
    balances: BalanceTable,
    reserves: Tuple[Amount, Amount],
    max_brute_force_n: int,
    factories: _OptimalAbOrderingFactories,
) -> List[Intent]:
    if len(intents) <= 1:
        return list(intents)
    if len(intents) > max_brute_force_n:
        return factories.order_limit_price_fn(intents)

    direction = _same_pool_direction_or_none(intents, pool_state)
    if direction is None:
        return factories.order_limit_price_fn(intents)
    first_asset_in, _first_asset_out = direction
    r_in0, r_out0 = _directional_reserves(first_asset_in, pool_state, reserves)
    context = _OptimalAbObjectiveContext(
        pool_state=pool_state,
        first_asset_in=first_asset_in,
        r_in0=r_in0,
        r_out0=r_out0,
        sender_bal_in=_sender_input_balances(intents, balances, first_asset_in),
        factories=factories,
    )
    best_order = _best_order_by_objective(intents, context)
    return list(best_order) if best_order is not None else factories.order_limit_price_fn(intents)
