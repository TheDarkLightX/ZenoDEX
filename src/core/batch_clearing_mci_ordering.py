"""MCI and refinement helpers for deterministic batch swap ordering."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, List, Optional, Tuple

from ..state.balances import Amount
from ..state.intents import Intent
from ..state.pools import PoolState

_AnyFn = Callable[..., Any]
_ReserveState = Tuple[Amount, Amount]
# Canonical-fold state: (total_a, total_b, reserves) after a prefix of an ordering.
_FoldState = Tuple[Amount, Amount, _ReserveState]


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


@dataclass(frozen=True)
class _PrefixSimulationCache:
    """Canonical-fold state after every prefix of one ordering.

    ``states[k]`` (``0 <= k <= n``) is ``(total_a, total_b, reserves)`` after the first ``k``
    intents; ``states[0]`` is the empty prefix (zero totals, initial reserves). Totals are
    additive over positions and, like reserves, advance only on simulated contributions with
    ``a > 0``, exactly as ``_eval_ordering_ab`` folds them.
    """

    states: Tuple[_FoldState, ...]


@dataclass(frozen=True)
class _AdjacentSwapCandidate:
    """Exact canonical-fold evaluation of an ordering with ``position``/``position + 1`` swapped.

    ``total_a``/``total_b`` are the full totals of the swapped ordering. ``tail_states`` are the
    prefix-cache entries of the swapped ordering from length ``position + 1`` onward: exactly two
    entries when the cached suffix was reused unchanged, ``n - position`` entries when the suffix
    was re-simulated.
    """

    position: int
    total_a: Amount
    total_b: Amount
    tail_states: Tuple[_FoldState, ...]
    suffix_reused: bool


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


def refine_b_ordering_with_simulator(
    ordering: List[Intent],
    *,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
    simulate_swap_fn: _AnyFn,
) -> List[Intent]:
    """Adjacent-swap B refinement with an exact prefix/suffix simulation cache.

    Output contract: the returned list is identical (same intent objects, same positions) to
    ``refine_b_ordering_with_eval`` driven by the canonical fold of ``simulate_swap_fn``, i.e. the
    ``_eval_ordering_ab`` semantics where an intent contributes ``(a, b)`` and advances the
    reserves only when its simulated ``a > 0``. Strict-improvement rule, scan order and tie
    handling are shared with the generic refiner; the caller's list is never mutated.

    Precondition: with fixed intent and pool inputs, ``simulate_swap_fn(intent, pool_state,
    reserves)`` is a pure deterministic partial function over ordinary integer contributions and
    exact ``(int, int)`` reserve tuples. It returns ``(a, b, new_reserves)`` or raises an
    input-dependent exception; this helper makes no totality claim about the real simulator.
    Generic evaluator callbacks are not covered by this helper; they keep the
    ``refine_b_ordering_with_eval`` path.

    Cache lemma: under the canonical fold, a suffix evaluation depends only on its intents and the
    reserves it starts from, and totals are additive over positions. Swapping ``(i, i + 1)``
    leaves the prefix ``[0, i)`` untouched, so only the pair is re-simulated. The suffix
    ``[i + 2, n)`` is reused only when the post-pair reserves are exactly equal to the cached
    post-pair reserves (``_suffix_is_reusable``); otherwise it is re-simulated in full.

    Work bound: ``n`` simulator calls up front, then per candidate ``2`` calls plus
    ``n - i - 2`` on a re-simulated suffix, and no calls on an accepted swap. When every
    candidate re-simulates this is still ``O(n^2)`` calls per pass, the same class as the generic
    refiner; the pass count is identical by construction.
    """
    if len(ordering) <= 1:
        return list(ordering)

    result = list(ordering)
    cache = _build_prefix_cache(result, pool_state, reserves, simulate_swap_fn)

    improved = True
    while improved:
        improved = False
        for i in range(len(result) - 1):
            candidate = _simulate_adjacent_swap(result, i, cache, pool_state, simulate_swap_fn)
            base_a, base_b, _base_reserves = cache.states[-1]
            if _is_strict_ab_improvement(candidate.total_a, candidate.total_b, base_a, base_b):
                result[i], result[i + 1] = result[i + 1], result[i]
                cache = _cache_after_accepted_swap(cache, candidate)
                improved = True
    return result


def _suffix_is_reusable(
    post_pair_reserves: _ReserveState,
    cached_post_pair_reserves: _ReserveState,
) -> bool:
    """Exact-equality guard of the suffix cache lemma.

    Reusing cached suffix totals is sound only when the swapped pair leaves exactly the reserves
    the cached suffix was simulated from. Anything weaker (equal pair totals, "close" reserves)
    is unsound: a one-atom reserve difference can flip a downstream ``min_amount_out`` decision.
    """
    return post_pair_reserves == cached_post_pair_reserves


def _fold_simulated_swap(
    state: _FoldState,
    intent: Intent,
    pool_state: PoolState,
    simulate_swap_fn: _AnyFn,
) -> _FoldState:
    """One canonical-fold step: contribute ``(a, b)`` and advance reserves only when ``a > 0``."""
    total_a, total_b, current_reserves = state
    a, b, new_reserves = simulate_swap_fn(intent, pool_state, current_reserves)
    if a > 0:
        return total_a + a, total_b + b, new_reserves
    return state


def _fold_states(
    state: _FoldState,
    intents: List[Intent],
    pool_state: PoolState,
    simulate_swap_fn: _AnyFn,
) -> List[_FoldState]:
    """Fold ``intents`` from ``state`` and return the state after each of them."""
    states: List[_FoldState] = []
    for intent in intents:
        state = _fold_simulated_swap(state, intent, pool_state, simulate_swap_fn)
        states.append(state)
    return states


def _build_prefix_cache(
    ordering: List[Intent],
    pool_state: PoolState,
    reserves: _ReserveState,
    simulate_swap_fn: _AnyFn,
) -> _PrefixSimulationCache:
    initial: _FoldState = (0, 0, reserves)
    return _PrefixSimulationCache(
        states=(initial, *_fold_states(initial, ordering, pool_state, simulate_swap_fn)),
    )


def _simulate_adjacent_swap(
    result: List[Intent],
    position: int,
    cache: _PrefixSimulationCache,
    pool_state: PoolState,
    simulate_swap_fn: _AnyFn,
) -> _AdjacentSwapCandidate:
    """Evaluate ``result`` with ``position``/``position + 1`` swapped, reusing the prefix cache."""
    suffix_start = position + 2
    swapped_pair = [result[position + 1], result[position]]
    pair_states = _fold_states(cache.states[position], swapped_pair, pool_state, simulate_swap_fn)
    post_pair = pair_states[-1]
    cached_post_pair = cache.states[suffix_start]

    if _suffix_is_reusable(post_pair[2], cached_post_pair[2]):
        end_a, end_b, _end_reserves = cache.states[-1]
        return _AdjacentSwapCandidate(
            position=position,
            total_a=post_pair[0] + (end_a - cached_post_pair[0]),
            total_b=post_pair[1] + (end_b - cached_post_pair[1]),
            tail_states=tuple(pair_states),
            suffix_reused=True,
        )

    suffix_states = _fold_states(post_pair, result[suffix_start:], pool_state, simulate_swap_fn)
    end_state = suffix_states[-1] if suffix_states else post_pair
    return _AdjacentSwapCandidate(
        position=position,
        total_a=end_state[0],
        total_b=end_state[1],
        tail_states=tuple(pair_states + suffix_states),
        suffix_reused=False,
    )


def _cache_after_accepted_swap(
    cache: _PrefixSimulationCache,
    candidate: _AdjacentSwapCandidate,
) -> _PrefixSimulationCache:
    """Prefix cache of the ordering after applying the candidate's adjacent swap.

    Entries up to length ``position`` are untouched; the pair entries (and any re-simulated
    suffix entries) come from the candidate. A reused suffix keeps its reserves and shifts its
    totals by the pair's total delta: identical suffix contributions differ only by the totals
    they start from.
    """
    keep = candidate.position + 1
    states = list(cache.states[:keep]) + list(candidate.tail_states)
    if candidate.suffix_reused:
        suffix_start = candidate.position + 2
        old_post_pair = cache.states[suffix_start]
        new_post_pair = candidate.tail_states[-1]
        delta_a = new_post_pair[0] - old_post_pair[0]
        delta_b = new_post_pair[1] - old_post_pair[1]
        states.extend(
            (total_a + delta_a, total_b + delta_b, suffix_reserves)
            for total_a, total_b, suffix_reserves in cache.states[suffix_start + 1:]
        )
    return _PrefixSimulationCache(states=tuple(states))


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
