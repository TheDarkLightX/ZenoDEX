"""MCI and refinement helpers for deterministic batch swap ordering."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, List, Optional, Tuple

from ..state.balances import Amount
from ..state.intents import Intent
from ..state.pools import PoolState

_AnyFn = Callable[..., Any]


@dataclass(frozen=True)
class _MciOrderingFactories:
    order_limit_price_fn: _AnyFn
    order_greedy_ab_fn: _AnyFn
    refine_b_ordering_fn: _AnyFn
    ab_ordering_key_fn: _AnyFn
    is_better_ab_key_fn: _AnyFn
    tiebreak_token_fn: _AnyFn


@dataclass(frozen=True)
class _GlobalRefineContext:
    pool_state: PoolState
    reserves: Tuple[Amount, Amount]
    eval_ordering_ab_fn: _AnyFn


@dataclass(frozen=True)
class _GlobalRefineConfig:
    max_global_refine_n: int
    refine_b_ordering_fn: _AnyFn


def order_swaps_mci_ab_with_factories(
    intents: List[Intent],
    *,
    pool_state: PoolState,
    max_mci_n: int,
    factories: _MciOrderingFactories,
) -> List[Intent]:
    if len(intents) <= 1:
        return list(intents)
    if len(intents) > max_mci_n:
        greedy = factories.order_greedy_ab_fn(intents)
        return factories.refine_b_ordering_fn(greedy)
    if not _same_pool_direction(intents, pool_state):
        return factories.order_limit_price_fn(intents)

    remaining = sorted(intents, key=lambda it: factories.tiebreak_token_fn(it.intent_id))
    ordered: List[Intent] = []
    while remaining:
        best_idx, best_order = _best_mci_insertion(ordered, remaining, factories)
        if best_order is None or best_idx < 0:
            raise RuntimeError("AB ordering search produced no candidate")
        ordered = best_order
        remaining.pop(best_idx)
    return ordered


def refine_b_ordering_with_eval(
    ordering: List[Intent],
    *,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
    eval_ordering_ab_fn: _AnyFn,
) -> List[Intent]:
    if len(ordering) <= 1:
        return list(ordering)

    result = list(ordering)
    base_a, base_b = eval_ordering_ab_fn(result, pool_state, reserves)

    improved = True
    while improved:
        improved = False
        for i in range(len(result) - 1):
            result[i], result[i + 1] = result[i + 1], result[i]
            new_a, new_b = eval_ordering_ab_fn(result, pool_state, reserves)
            if _is_strict_ab_improvement(new_a, new_b, base_a, base_b):
                base_a = new_a
                base_b = new_b
                improved = True
            else:
                result[i], result[i + 1] = result[i + 1], result[i]
    return result


def refine_ab_ordering_global_with_eval(
    ordering: List[Intent],
    *,
    context: _GlobalRefineContext,
    config: _GlobalRefineConfig,
) -> List[Intent]:
    n = len(ordering)
    if n <= 1:
        return list(ordering)
    if n > config.max_global_refine_n:
        return config.refine_b_ordering_fn(ordering)

    result = list(ordering)
    base_a, base_b = context.eval_ordering_ab_fn(result, context.pool_state, context.reserves)

    for _ in range(n):
        best_pair, best_a, best_b = _best_global_pair_swap(
            result,
            context=context,
            base_a=base_a,
            base_b=base_b,
        )
        if best_pair is None:
            break

        i, j = best_pair
        result[i], result[j] = result[j], result[i]
        base_a, base_b = best_a, best_b
    return result


def _same_pool_direction(intents: List[Intent], pool_state: PoolState) -> bool:
    first_asset_in = intents[0].get_field("asset_in")
    first_asset_out = intents[0].get_field("asset_out")
    if not isinstance(first_asset_in, str) or not isinstance(first_asset_out, str):
        return False
    if first_asset_in == first_asset_out:
        return False
    if not (
        (first_asset_in == pool_state.asset0 and first_asset_out == pool_state.asset1)
        or (first_asset_in == pool_state.asset1 and first_asset_out == pool_state.asset0)
    ):
        return False
    return all(
        intent.get_field("asset_in") == first_asset_in
        and intent.get_field("asset_out") == first_asset_out
        for intent in intents[1:]
    )


def _best_mci_insertion(
    ordered: List[Intent],
    remaining: List[Intent],
    factories: _MciOrderingFactories,
) -> tuple[int, List[Intent] | None]:
    best_idx = -1
    best_order: List[Intent] | None = None
    best_key: Tuple[int, int, Tuple[str, ...]] | None = None

    for rem_idx, candidate in enumerate(remaining):
        for pos in range(len(ordered) + 1):
            trial = ordered[:pos] + [candidate] + ordered[pos:]
            trial_key = factories.ab_ordering_key_fn(trial)
            if best_key is None or factories.is_better_ab_key_fn(trial_key, best_key):
                best_idx = rem_idx
                best_order = trial
                best_key = trial_key
    return best_idx, best_order


def _best_global_pair_swap(
    result: List[Intent],
    *,
    context: _GlobalRefineContext,
    base_a: Amount,
    base_b: Amount,
) -> tuple[Optional[Tuple[int, int]], Amount, Amount]:
    best_pair: Optional[Tuple[int, int]] = None
    best_a: Amount = base_a
    best_b: Amount = base_b

    for i in range(len(result) - 1):
        for j in range(i + 1, len(result)):
            result[i], result[j] = result[j], result[i]
            cand_a, cand_b = context.eval_ordering_ab_fn(result, context.pool_state, context.reserves)
            result[i], result[j] = result[j], result[i]

            if not _is_strict_ab_improvement(cand_a, cand_b, best_a, best_b):
                continue

            best_pair = (i, j)
            best_a = cand_a
            best_b = cand_b
    return best_pair, best_a, best_b


def _is_strict_ab_improvement(
    candidate_a: Amount,
    candidate_b: Amount,
    base_a: Amount,
    base_b: Amount,
) -> bool:
    if candidate_a != base_a:
        return candidate_a > base_a
    return candidate_b > base_b
