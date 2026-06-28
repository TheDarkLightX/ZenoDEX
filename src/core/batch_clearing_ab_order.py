"""Bounded AB-objective swap ordering for batch clearing."""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Optional, Tuple

from ..state.balances import Amount, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.pools import CURVE_TAG_CPMM, PoolState

_AnyFn = Callable[..., Any]
_MAX_AB_BRUTE_FORCE_EXACT_N = 8
_MAX_AB_DP_STATES_PER_SUBSET = 250_000


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
class _SwapReserveSimulationFactories:
    quote_exact_in_fn: _AnyFn
    swap_exact_in_fn: _AnyFn


@dataclass(frozen=True)
class _OptimalAbObjectiveContext:
    pool_state: PoolState
    first_asset_in: str
    r_in0: int
    r_out0: int
    sender_bal_in: Dict[PubKey, Amount]
    factories: _OptimalAbOrderingFactories


@dataclass(frozen=True)
class _AbDpRecord:
    amount_a: int
    surplus_b: int
    order_ids: Tuple[str, ...]


def _simulation_reserve_direction(
    intent: Intent,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> Optional[Tuple[Amount, Amount, bool]]:
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    reserve0, reserve1 = reserves

    if asset_in == pool_state.asset0 and asset_out == pool_state.asset1:
        return reserve0, reserve1, False
    if asset_in == pool_state.asset1 and asset_out == pool_state.asset0:
        return reserve1, reserve0, True
    return None


def simulate_swap_reserves_with_factories(
    intent: Intent,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
    factories: _SwapReserveSimulationFactories,
) -> Tuple[Amount, Amount, Tuple[Amount, Amount]]:
    if intent.kind != IntentKind.SWAP_EXACT_IN:
        return 0, 0, reserves

    direction = _simulation_reserve_direction(intent, pool_state, reserves)
    if direction is None:
        return 0, 0, reserves
    reserve_in, reserve_out, reverse = direction

    amount_in = intent.get_field("amount_in")
    min_amount_out = intent.get_field("min_amount_out", 0)
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return 0, 0, reserves
    if not isinstance(min_amount_out, int) or isinstance(min_amount_out, bool) or min_amount_out < 0:
        return 0, 0, reserves

    try:
        if pool_state.curve_tag == CURVE_TAG_CPMM:
            quote = factories.quote_exact_in_fn(
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_in=amount_in,
                fee_bps=pool_state.fee_bps,
            )
            amount_out = quote.amount_out
            new_r_in, new_r_out = quote.reserve_in_after, quote.reserve_out_after
        else:
            amount_out, (new_r_in, new_r_out) = factories.swap_exact_in_fn(
                pool_state,
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_in=amount_in,
            )
    except ValueError:
        return 0, 0, reserves

    if amount_out < min_amount_out:
        return 0, 0, reserves
    surplus = amount_out - min_amount_out
    new_reserves = (new_r_out, new_r_in) if reverse else (new_r_in, new_r_out)
    return amount_in, surplus, new_reserves


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


def _best_order_by_objective_bruteforce(
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


def _best_order_by_objective_subset_dp(
    intents: List[Intent],
    context: _OptimalAbObjectiveContext,
) -> Optional[Tuple[Intent, ...]]:
    """Explore all AB orderings through a full-state subset DP.

    The state keeps both directional reserves and per-sender remaining input
    balances. This is exact for the existing objective because all future
    transition results are determined by `(processed_set, reserves, balances)`.
    """
    n = len(intents)
    intent_by_id = {intent.intent_id: intent for intent in intents}
    senders = tuple(sorted(context.sender_bal_in))
    sender_index = {sender: idx for idx, sender in enumerate(senders)}
    initial_balances = tuple(int(context.sender_bal_in[sender]) for sender in senders)
    dp: list[dict[tuple[int, int, Tuple[int, ...]], _AbDpRecord]] = [dict() for _ in range(1 << n)]
    dp[0][(int(context.r_in0), int(context.r_out0), initial_balances)] = _AbDpRecord(0, 0, tuple())

    for mask in range(1 << n):
        states = dp[mask]
        if not states:
            continue
        for state, record in list(states.items()):
            r_in, r_out, balance_key = state
            bal_in = {sender: int(balance_key[idx]) for sender, idx in sender_index.items()}
            for idx, intent in enumerate(intents):
                bit = 1 << idx
                if mask & bit:
                    continue
                next_mask = mask | bit
                next_r_in = int(r_in)
                next_r_out = int(r_out)
                next_balance_key = balance_key
                next_a = int(record.amount_a)
                next_b = int(record.surplus_b)

                if intent.kind == IntentKind.SWAP_EXACT_IN:
                    contribution = _objective_exact_in_contribution(
                        intent,
                        context,
                        r_in=int(r_in),
                        r_out=int(r_out),
                        bal_in=bal_in,
                    )
                    if contribution is not None:
                        amount_in, surplus, next_r_in, next_r_out = contribution
                        next_a += int(amount_in)
                        next_b += int(surplus)
                        next_balance_key = _debit_balance_key(
                            next_balance_key,
                            sender_index=sender_index,
                            sender=intent.sender_pubkey,
                            amount=int(amount_in),
                        )

                elif intent.kind == IntentKind.SWAP_EXACT_OUT:
                    contribution = _objective_exact_out_contribution(
                        intent,
                        context,
                        r_in=int(r_in),
                        r_out=int(r_out),
                        bal_in=bal_in,
                    )
                    if contribution is not None:
                        amount_in, next_r_in, next_r_out = contribution
                        next_a += int(amount_in)
                        next_balance_key = _debit_balance_key(
                            next_balance_key,
                            sender_index=sender_index,
                            sender=intent.sender_pubkey,
                            amount=int(amount_in),
                        )

                next_state = (int(next_r_in), int(next_r_out), next_balance_key)
                next_record = _AbDpRecord(
                    amount_a=int(next_a),
                    surplus_b=int(next_b),
                    order_ids=(*record.order_ids, intent.intent_id),
                )
                current = dp[next_mask].get(next_state)
                if current is None or _is_better_ab_dp_record(next_record, current, context):
                    dp[next_mask][next_state] = next_record
                    if len(dp[next_mask]) > _MAX_AB_DP_STATES_PER_SUBSET:
                        return None

    final_records = dp[(1 << n) - 1].values()
    best_record: _AbDpRecord | None = None
    for record in final_records:
        if best_record is None or _is_better_ab_dp_record(record, best_record, context):
            best_record = record
    if best_record is None:
        return None
    return tuple(intent_by_id[intent_id] for intent_id in best_record.order_ids)


def _debit_balance_key(
    balance_key: Tuple[int, ...],
    *,
    sender_index: Dict[PubKey, int],
    sender: PubKey,
    amount: int,
) -> Tuple[int, ...]:
    idx = sender_index.get(sender)
    if idx is None:
        return balance_key
    next_values = list(balance_key)
    next_values[idx] = int(next_values[idx]) - int(amount)
    return tuple(next_values)


def _is_better_ab_dp_record(
    candidate: _AbDpRecord,
    best: _AbDpRecord,
    context: _OptimalAbObjectiveContext,
) -> bool:
    candidate_key = context.factories.ab_ordering_key_fn(
        A_B_order=(candidate.amount_a, candidate.surplus_b, candidate.order_ids)
    )
    best_key = context.factories.ab_ordering_key_fn(
        A_B_order=(best.amount_a, best.surplus_b, best.order_ids)
    )
    return context.factories.is_better_ab_key_fn(candidate_key, best_key)


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
    if len(intents) <= _MAX_AB_BRUTE_FORCE_EXACT_N:
        best_order = _best_order_by_objective_bruteforce(intents, context)
    else:
        best_order = _best_order_by_objective_subset_dp(intents, context)
    return list(best_order) if best_order is not None else factories.order_limit_price_fn(intents)
