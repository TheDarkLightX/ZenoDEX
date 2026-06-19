"""Swap ordering policies for deterministic batch clearing."""

from __future__ import annotations

import functools
from typing import List, Optional, Tuple

from ..kernels.python.settlement_swap_runtime_v1 import (
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from ..state.balances import Amount, BalanceTable
from ..state.intents import Intent, IntentKind
from ..state.pools import PoolState
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .neutral_tiebreak import tiebreak_token
from .batch_clearing_ab_order import (
    _OptimalAbOrderingFactories,
    _SwapReserveSimulationFactories,
    order_swaps_optimal_ab_bounded_with_factories,
    simulate_swap_reserves_with_factories,
)

# Bounded brute-force safety cap for AB-optimal ordering.
# For N > this limit, greedy_ab should be used instead.
_MAX_SWAP_ORDERING_BRUTE_FORCE_N = 12
# Global pair-swap refinement can be expensive; cap intent count for this mode.
_MAX_SWAP_ORDERING_GLOBAL_REFINE_N = 24
# MCI insertion is heavier than greedy seeding; keep it opt-in and bounded.
_MAX_SWAP_ORDERING_MCI_N = 18


def _order_swaps_limit_price(intents: List[Intent], *, seed: bytes | None = None) -> List[Intent]:
    return sorted(
        intents,
        key=lambda i: (
            -_get_limit_price(i),  # Best price first (descending)
            tiebreak_token(i.intent_id, seed),  # Tie-break (grindable id unless seeded)
        ),
    )


def _order_swaps_optimal_ab_bounded(
    intents: List[Intent],
    *,
    pool_state: PoolState,
    balances: BalanceTable,
    reserves: Tuple[Amount, Amount],
    seed: bytes | None = None,
) -> List[Intent]:
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
        intents,
        pool_state=pool_state,
        balances=balances,
        reserves=reserves,
        max_brute_force_n=_MAX_SWAP_ORDERING_BRUTE_FORCE_N,
        factories=_OptimalAbOrderingFactories(
            quote_exact_in_fn=quote_cpmm_swap_exact_in,
            quote_exact_out_fn=quote_cpmm_swap_exact_out,
            swap_exact_in_fn=swap_exact_in_for_pool,
            swap_exact_out_fn=swap_exact_out_for_pool,
            order_limit_price_fn=functools.partial(_order_swaps_limit_price, seed=seed),
            ab_ordering_key_fn=functools.partial(_ab_ordering_key, seed=seed),
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


def _ab_ordering_key(
    ordering: List[Intent] | None = None,
    pool_state: PoolState | None = None,
    reserves: Tuple[Amount, Amount] | None = None,
    *,
    A_B_order: Tuple[Amount, Amount, Tuple[str, ...]] | None = None,
    seed: bytes | None = None,
) -> Tuple[int, int, Tuple[str, ...]]:
    # `seed is None` (the default, and the only value any current caller passes)
    # keeps the tie-break component as the raw intent_id tuple -> byte-identical to
    # the pre-seam canonical order. A non-None seed swaps the grindable intent_id
    # for a grinding-resistant token (neutral_tiebreak.py); enabling that path is a
    # deliberate follow-up gated on an unbiasable seed source. `tiebreak_token` is
    # the identity when seed is None, so this seam is behavior-preserving by default.
    if A_B_order is not None:
        return int(A_B_order[0]), int(A_B_order[1]), tuple(
            tiebreak_token(str(x), seed) for x in A_B_order[2]
        )
    if ordering is None or pool_state is None or reserves is None:
        raise ValueError("ordering, pool_state, and reserves are required unless A_B_order is provided")
    amount_a, surplus_b = _eval_ordering_ab(ordering, pool_state, reserves)
    return int(amount_a), int(surplus_b), tuple(
        tiebreak_token(it.intent_id, seed) for it in ordering
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


def _is_strict_ab_improvement(
    candidate_a: Amount,
    candidate_b: Amount,
    base_a: Amount,
    base_b: Amount,
) -> bool:
    """Return true when `(A, B)` improves lexicographically."""
    if candidate_a != base_a:
        return candidate_a > base_a
    return candidate_b > base_b


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
    if len(intents) <= 1:
        return list(intents)
    if len(intents) > _MAX_SWAP_ORDERING_MCI_N:
        greedy = _order_swaps_greedy_ab(intents, pool_state=pool_state, reserves=reserves, seed=seed)
        return _refine_b_ordering(greedy, pool_state=pool_state, reserves=reserves)

    first_asset_in = intents[0].get_field("asset_in")
    first_asset_out = intents[0].get_field("asset_out")
    if not isinstance(first_asset_in, str) or not isinstance(first_asset_out, str):
        return _order_swaps_limit_price(intents, seed=seed)
    if first_asset_in == first_asset_out:
        return _order_swaps_limit_price(intents, seed=seed)
    if not (
        (first_asset_in == pool_state.asset0 and first_asset_out == pool_state.asset1)
        or (first_asset_in == pool_state.asset1 and first_asset_out == pool_state.asset0)
    ):
        return _order_swaps_limit_price(intents, seed=seed)
    for it in intents[1:]:
        if it.get_field("asset_in") != first_asset_in or it.get_field("asset_out") != first_asset_out:
            return _order_swaps_limit_price(intents, seed=seed)

    remaining = sorted(intents, key=lambda it: tiebreak_token(it.intent_id, seed))
    ordered: List[Intent] = []

    while remaining:
        best_idx = -1
        best_order: List[Intent] | None = None
        best_key: Tuple[int, int, Tuple[str, ...]] | None = None
        for rem_idx, candidate in enumerate(remaining):
            for pos in range(len(ordered) + 1):
                trial = ordered[:pos] + [candidate] + ordered[pos:]
                trial_key = _ab_ordering_key(trial, pool_state, reserves, seed=seed)
                if best_order is None or _is_better_ab_key(
                    trial_key,
                    best_key if best_key is not None else (-1, -1, tuple()),
                ):
                    best_idx = rem_idx
                    best_order = trial
                    best_key = trial_key
        if best_order is None or best_idx < 0:
            raise RuntimeError("AB ordering search produced no candidate")
        ordered = best_order
        remaining.pop(best_idx)

    return ordered


def _refine_b_ordering(
    ordering: List[Intent],
    *,
    pool_state: PoolState,
    reserves: Tuple[Amount, Amount],
) -> List[Intent]:
    """B-refinement pass: improve surplus (B) without decreasing volume (A).

    Takes a greedy-AB ordering and performs repeated adjacent-swap passes.
    For each pair of adjacent intents (i, i+1), if swapping them improves B
    while keeping A equal, the swap is applied. Repeats until a full pass
    produces no improvement (bubble-sort style).

    Complexity: O(n^2) per pass, at most O(n) passes, so O(n^3) worst case.
    In practice converges in 1-2 passes for typical batch sizes.

    This addresses the B-suboptimality of greedy ordering (H-BC-001):
    greedy_ab is A-optimal but B-suboptimal in 39-94% of cases.
    """
    if len(ordering) <= 1:
        return list(ordering)

    result = list(ordering)
    base_a, base_b = _eval_ordering_ab(result, pool_state, reserves)

    improved = True
    while improved:
        improved = False
        for i in range(len(result) - 1):
            # Try swapping adjacent pair (i, i+1)
            result[i], result[i + 1] = result[i + 1], result[i]
            new_a, new_b = _eval_ordering_ab(result, pool_state, reserves)

            if _is_strict_ab_improvement(new_a, new_b, base_a, base_b):
                base_a = new_a
                base_b = new_b
                improved = True
            else:
                result[i], result[i + 1] = result[i + 1], result[i]

    return result


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
    n = len(ordering)
    if n <= 1:
        return list(ordering)
    if n > _MAX_SWAP_ORDERING_GLOBAL_REFINE_N:
        return _refine_b_ordering(ordering, pool_state=pool_state, reserves=reserves)

    result = list(ordering)
    base_a, base_b = _eval_ordering_ab(result, pool_state, reserves)

    # Bounded number of passes; each pass applies at most one best-improving swap.
    max_passes = n
    for _ in range(max_passes):
        best_pair: Optional[Tuple[int, int]] = None
        best_a: Amount = base_a
        best_b: Amount = base_b

        for i in range(n - 1):
            for j in range(i + 1, n):
                result[i], result[j] = result[j], result[i]
                cand_a, cand_b = _eval_ordering_ab(result, pool_state, reserves)
                result[i], result[j] = result[j], result[i]

                if not _is_strict_ab_improvement(cand_a, cand_b, best_a, best_b):
                    continue

                best_pair = (i, j)
                best_a = cand_a
                best_b = cand_b

        if best_pair is None:
            break

        i, j = best_pair
        result[i], result[j] = result[j], result[i]
        base_a, base_b = best_a, best_b

    return result
