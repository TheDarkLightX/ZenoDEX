"""Swap ordering policies for deterministic batch clearing."""

from __future__ import annotations

import functools
from dataclasses import dataclass
from typing import List, Tuple

from ..kernels.python.settlement_swap_runtime_v1 import (
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from ..state.balances import Amount, BalanceTable
from ..state.intents import Intent, IntentKind
from ..state.pools import PoolState
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .batch_clearing_ab_order import (
    _OptimalAbOrderingFactories,
    _SwapReserveSimulationFactories,
    order_swaps_optimal_ab_bounded_with_factories,
    simulate_swap_reserves_with_factories,
)
from .batch_clearing_mci_ordering import (
    _GlobalRefineConfig,
    _GlobalRefineContext,
    _MciOrderingFactories,
    order_swaps_mci_ab_with_factories,
    refine_ab_ordering_global_with_eval,
    refine_b_ordering_with_eval,
    refine_b_ordering_with_simulator,
)
from .neutral_tiebreak import tiebreak_token

# Bounded brute-force safety cap for AB-optimal ordering.
# For N > this limit, greedy_ab should be used instead.
_MAX_SWAP_ORDERING_BRUTE_FORCE_N = 12
# Global pair-swap refinement can be expensive; cap intent count for this mode.
_MAX_SWAP_ORDERING_GLOBAL_REFINE_N = 24
# MCI insertion is heavier than greedy seeding; keep it opt-in and bounded.
_MAX_SWAP_ORDERING_MCI_N = 18


@dataclass(frozen=True)
class _OptimalAbBoundedRequest:
    intents: List[Intent]
    pool_state: PoolState
    balances: BalanceTable
    reserves: Tuple[Amount, Amount]
    seed: bytes | None = None


@dataclass(frozen=True)
class _AbOrderingEvaluationRequest:
    ordering: List[Intent]
    pool_state: PoolState
    reserves: Tuple[Amount, Amount]
    seed: bytes | None = None


@dataclass(frozen=True)
class _AbOrderingTotalsRequest:
    amount_a: Amount
    surplus_b: Amount
    intent_ids: Tuple[str, ...]
    seed: bytes | None = None


def _order_swaps_limit_price(intents: List[Intent], *, seed: bytes | None = None) -> List[Intent]:
    return sorted(
        intents,
        key=lambda i: (
            -_get_limit_price(i),  # Best price first (descending)
            tiebreak_token(i.intent_id, seed),  # Tie-break (grindable id unless seeded)
        ),
    )


def _order_swaps_optimal_ab_bounded(request: _OptimalAbBoundedRequest) -> List[Intent]:
    """
    Choose a deterministic swap order that maximizes the (A,B)+tie-break key:

      A = total executed input volume (sum(amount_in_filled))
      B = total surplus (sum(amount_out_filled - min_amount_out)) for exact-in swaps
      tie-break = lexicographically smallest tuple(intent_id, ...)

    Uses brute-force search only in bounded regimes and otherwise falls back to
    the standard limit-price ordering.

    To keep the objective meaningful, AB optimization is only attempted when all
    swaps share the same direction (same asset_in/out). Mixed-direction batches
    fall back to limit-price ordering.
    """
    return order_swaps_optimal_ab_bounded_with_factories(
        request.intents,
        pool_state=request.pool_state,
        balances=request.balances,
        reserves=request.reserves,
        max_brute_force_n=_MAX_SWAP_ORDERING_BRUTE_FORCE_N,
        factories=_OptimalAbOrderingFactories(
            quote_exact_in_fn=quote_cpmm_swap_exact_in,
            quote_exact_out_fn=quote_cpmm_swap_exact_out,
            swap_exact_in_fn=swap_exact_in_for_pool,
            swap_exact_out_fn=swap_exact_out_for_pool,
            order_limit_price_fn=functools.partial(_order_swaps_limit_price, seed=request.seed),
            ab_ordering_key_fn=functools.partial(_ab_ordering_key_from_totals, seed=request.seed),
            is_better_ab_key_fn=_is_better_ab_key,
        ),
    )


def _get_limit_price(intent: Intent) -> int:
    """
    Get effective limit price for sorting.

    For SWAP_EXACT_IN: min_amount_out / amount_in (higher is better)
    For SWAP_EXACT_OUT: amount_out / max_amount_in (higher is better)
    """
    if intent.kind == IntentKind.SWAP_EXACT_IN:
        amount_in = intent.get_field("amount_in", 1)
        min_amount_out = intent.get_field("min_amount_out", 0)
        return (min_amount_out * 10**18) // amount_in if amount_in > 0 else 0
    if intent.kind == IntentKind.SWAP_EXACT_OUT:
        amount_out = intent.get_field("amount_out", 1)
        max_amount_in = intent.get_field("max_amount_in", 10**18)
        return (amount_out * 10**18) // max_amount_in if max_amount_in > 0 else 0
    return 0


def _simulate_swap_reserves(
    intent: Intent,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> Tuple[Amount, Amount, Tuple[Amount, Amount]]:
    """Simulate a single swap and return (A_contrib, B_contrib, new_reserves).

    A = amount_in executed
    B = amount_out - min_amount_out (surplus)

    NOTE: This simulator evaluates AMM executability only (reserves, slippage).
    It does not check user balance sufficiency; a swap ordered by greedy may
    fail during actual execution if a prior swap consumed the user's balance.
    Non-executable swaps are appended in limit-price order by the caller.

    Returns (0, 0, reserves) if swap cannot execute.
    """
    return simulate_swap_reserves_with_factories(
        intent,
        pool_state,
        reserves,
        _SwapReserveSimulationFactories(
            quote_exact_in_fn=quote_cpmm_swap_exact_in,
            swap_exact_in_fn=swap_exact_in_for_pool,
        ),
    )


def _eval_ordering_ab(
    ordering: List[Intent],
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> Tuple[Amount, Amount]:
    """Simulate an ordering and return total (A, B) achieved."""
    total_a: Amount = 0
    total_b: Amount = 0
    current_reserves = reserves
    for intent in ordering:
        a, b, new_r = _simulate_swap_reserves(intent, pool_state, current_reserves)
        if a > 0:
            total_a += a
            total_b += b
            current_reserves = new_r
    return total_a, total_b


# Identity of the canonical evaluator. `_refine_b_ordering` may use the simulation cache only
# while the module evaluator is still this exact fold of `_simulate_swap_reserves`.
_CANONICAL_EVAL_ORDERING_AB = _eval_ordering_ab


def _ab_ordering_key(
    request: _AbOrderingEvaluationRequest | _AbOrderingTotalsRequest,
) -> Tuple[int, int, Tuple[str, ...]]:
    # `seed is None` (the default, and the only value any current caller passes)
    # keeps the tie-break component as the raw intent_id tuple -> byte-identical to
    # the pre-seam canonical order. A non-None seed swaps the grindable intent_id
    # for a grinding-resistant token (neutral_tiebreak.py); enabling that path is a
    # deliberate follow-up gated on an unbiasable seed source. `tiebreak_token` is
    # the identity when seed is None, so this seam is behavior-preserving by default.
    if isinstance(request, _AbOrderingTotalsRequest):
        return int(request.amount_a), int(request.surplus_b), tuple(
            tiebreak_token(str(x), request.seed) for x in request.intent_ids
        )
    amount_a, surplus_b = _eval_ordering_ab(request.ordering, request.pool_state, request.reserves)
    return int(amount_a), int(surplus_b), tuple(
        tiebreak_token(it.intent_id, request.seed) for it in request.ordering
    )


def _ab_ordering_key_from_totals(
    *,
    A_B_order: Tuple[Amount, Amount, Tuple[str, ...]],
    seed: bytes | None = None,
) -> Tuple[int, int, Tuple[str, ...]]:
    return _ab_ordering_key(
        _AbOrderingTotalsRequest(
            amount_a=A_B_order[0],
            surplus_b=A_B_order[1],
            intent_ids=A_B_order[2],
            seed=seed,
        )
    )


def _ab_ordering_key_from_ordering(
    ordering: List[Intent],
    *,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
    seed: bytes | None = None,
) -> Tuple[int, int, Tuple[str, ...]]:
    return _ab_ordering_key(
        _AbOrderingEvaluationRequest(
            ordering=ordering,
            pool_state=pool_state,
            reserves=reserves,
            seed=seed,
        )
    )


def _is_better_ab_key(candidate: Tuple[int, int, Tuple[str, ...]], best: Tuple[int, int, Tuple[str, ...]]) -> bool:
    cand_a, cand_b, cand_ids = candidate
    best_a, best_b, best_ids = best
    if cand_a > best_a:
        return True
    if cand_a < best_a:
        return False
    if cand_b > best_b:
        return True
    if cand_b < best_b:
        return False
    return cand_ids < best_ids


def _greedy_marginal_ab(
    remaining: List[Intent],
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
    *,
    seed: bytes | None = None,
) -> Tuple[int, Amount, Amount, Tuple[Amount, Amount]]:
    """Find the swap with tightest slippage that is still executable.

    Prefers swaps with the lowest absolute surplus (amount_out - min_amount_out)
    so that slippage-sensitive swaps execute while reserves are favorable.
    Ties broken by (amount_in desc, intent_id asc) for determinism.

    Returns (best_index, best_a, best_b, new_reserves).
    Returns (-1, 0, 0, reserves) if no swap can execute.
    """
    best_idx = -1
    best_a: Amount = 0
    best_b: Amount = 0
    best_key: tuple[int, int, str] | None = None
    best_new_reserves = reserves

    for i, intent in enumerate(remaining):
        a, b, new_r = _simulate_swap_reserves(intent, pool_state, reserves)
        if a == 0:
            continue

        # Tightest first: lowest surplus, then highest A, then lowest id.
        candidate_key = (int(b), -int(a), tiebreak_token(str(intent.intent_id), seed))
        if best_key is None or candidate_key < best_key:
            best_idx = i
            best_a = a
            best_b = b
            best_key = candidate_key
            best_new_reserves = new_r

    return best_idx, best_a, best_b, best_new_reserves


def _order_swaps_greedy_ab(
    intents: List[Intent],
    *,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
    seed: bytes | None = None,
) -> List[Intent]:
    """Greedy O(n^2) swap ordering that approximates AB-optimal.

    At each step, picks the swap with tightest slippage (lowest surplus)
    so slippage-sensitive swaps execute while reserves are favorable.
    Falls back to limit_price for mixed-direction batches.

    Reserve-level guarantee: the returned ordering has (A, B) >= limit_price
    ordering when evaluated against pool reserves only (SWAP_EXACT_IN).
    If the greedy ordering is worse, limit_price ordering is returned instead.

    Limitation: this ordering does not model sender balance constraints.
    A swap ordered first by greedy may consume a shared sender's balance,
    causing a later swap to be rejected at execution time. The caller
    (clear_batch_single_pool) handles such rejections via its own
    balance-checking loop.
    """
    if len(intents) <= 1:
        return list(intents)

    # Check all same direction
    first_asset_in = intents[0].get_field("asset_in")
    first_asset_out = intents[0].get_field("asset_out")
    for it in intents[1:]:
        if it.get_field("asset_in") != first_asset_in or it.get_field("asset_out") != first_asset_out:
            return _order_swaps_limit_price(intents, seed=seed)

    remaining = list(intents)
    greedy_ordered: List[Intent] = []
    current_reserves = reserves

    while remaining:
        idx, _a, _b, new_r = _greedy_marginal_ab(remaining, pool_state, current_reserves, seed=seed)
        if idx == -1:
            # No more executable swaps; append rest in limit-price order
            greedy_ordered.extend(_order_swaps_limit_price(remaining, seed=seed))
            break
        greedy_ordered.append(remaining.pop(idx))
        current_reserves = new_r

    # Guarantee: greedy >= limit_price. Compare and take the better.
    limit_ordered = _order_swaps_limit_price(intents, seed=seed)
    greedy_ab = _eval_ordering_ab(greedy_ordered, pool_state, reserves)
    limit_ab = _eval_ordering_ab(limit_ordered, pool_state, reserves)

    if greedy_ab >= limit_ab:
        return greedy_ordered
    return limit_ordered


def _order_swaps_mci_ab(
    intents: List[Intent],
    *,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
    seed: bytes | None = None,
) -> List[Intent]:
    """Marginal-contribution insertion seed for AB ordering.

    Build the ordering incrementally by trying every remaining intent at every
    insertion position and selecting the candidate with the best full `(A, B,
    lex-order)` key. This is an experimental, bounded heuristic intended to
    seed the existing global refinement pass with a stronger starting point
    than the slippage-first greedy order.
    """
    return order_swaps_mci_ab_with_factories(
        intents,
        pool_state=pool_state,
        max_mci_n=_MAX_SWAP_ORDERING_MCI_N,
        factories=_MciOrderingFactories(
            order_limit_price_fn=functools.partial(_order_swaps_limit_price, seed=seed),
            order_greedy_ab_fn=functools.partial(
                _order_swaps_greedy_ab,
                pool_state=pool_state,
                reserves=reserves,
                seed=seed,
            ),
            refine_b_ordering_fn=functools.partial(
                _refine_b_ordering,
                pool_state=pool_state,
                reserves=reserves,
            ),
            ab_ordering_key_fn=functools.partial(
                _ab_ordering_key_from_ordering,
                pool_state=pool_state,
                reserves=reserves,
                seed=seed,
            ),
            is_better_ab_key_fn=_is_better_ab_key,
            tiebreak_token_fn=functools.partial(tiebreak_token, seed=seed),
        ),
    )


def _refine_b_ordering(
    ordering: List[Intent],
    *,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> List[Intent]:
    """Refine an ordering with strict lexicographic ``(A, B)`` adjacent swaps.

    Starting from the supplied ordering, repeated left-to-right passes evaluate each adjacent
    swap and apply it exactly when the resulting ``(A, B)`` pair is strictly greater than the
    current pair. Thus a swap may increase ``A`` or may keep ``A`` equal while increasing ``B``;
    a decrease in ``A`` is rejected. The result is a fresh list containing the original intent
    objects, and the pass scan and tie handling match ``refine_b_ordering_with_eval``.

    Under the deterministic pure simulator premise, termination follows from strict improvement
    over the finite set of permutations. The cached implementation has a worst-case ``O(n^2)``
    simulator-call count per pass, and its pass count is unchanged from the generic refiner.

    Evaluation path: this wrapper is the only production binding of the cached refiner
    (`refine_b_ordering_with_simulator`) to the real reserve simulator. The cache is an exact
    implementation of `refine_b_ordering_with_eval(eval_ordering_ab_fn=_eval_ordering_ab)` only
    while `_eval_ordering_ab` is the canonical simulator fold defined in this module. If that
    name has been rebound (test seams inject evaluator stubs through it), the generic refiner
    runs with the rebound evaluator so the injected semantics are honoured unchanged.
    """
    if _eval_ordering_ab is not _CANONICAL_EVAL_ORDERING_AB:
        return refine_b_ordering_with_eval(
            ordering,
            pool_state=pool_state,
            reserves=reserves,
            eval_ordering_ab_fn=_eval_ordering_ab,
        )
    return refine_b_ordering_with_simulator(
        ordering,
        pool_state=pool_state,
        reserves=reserves,
        simulate_swap_fn=_simulate_swap_reserves,
    )


def _refine_ab_ordering_global(
    ordering: List[Intent],
    *,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> List[Intent]:
    """Global pair-swap AB refinement with deterministic tie-breaks.

    Starts from an existing ordering (typically `greedy_ab_refined`) and applies
    improving non-adjacent pair swaps. A candidate swap is accepted only when it
    strictly improves `(A, B)` lexicographically (maximize A first, then B).

    To avoid pathological runtime, for large batches this function falls back to
    adjacent-only refinement.
    """
    return refine_ab_ordering_global_with_eval(
        ordering,
        context=_GlobalRefineContext(
            pool_state=pool_state,
            reserves=reserves,
            eval_ordering_ab_fn=_eval_ordering_ab,
        ),
        config=_GlobalRefineConfig(
            max_global_refine_n=_MAX_SWAP_ORDERING_GLOBAL_REFINE_N,
            refine_b_ordering_fn=functools.partial(
                _refine_b_ordering,
                pool_state=pool_state,
                reserves=reserves,
            ),
        ),
    )
