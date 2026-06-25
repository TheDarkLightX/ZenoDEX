"""Brute-force oracle for batch clearing A-optimization.

Exhaustively tries all permutations of SWAP_EXACT_IN intents to find the
(A, B)-optimal ordering. Used as a reference for verifying the deadline
scheduling algorithm.

Complexity: O(n! * n) per evaluation. Only suitable for n <= 10.
"""

from __future__ import annotations

import itertools
from typing import Callable, List, Sequence, Tuple

BPS_DENOM = 10_000


def _compute_fee(gross_in: int, fee_bps: int) -> int:
    if gross_in <= 0 or fee_bps <= 0:
        return 0
    return (gross_in * fee_bps + BPS_DENOM - 1) // BPS_DENOM


def _simulate_ordering(
    ordering: List[Tuple[str, int, int]],  # (intent_id, amount_in, min_amount_out)
    *,
    reserve_in_0: int,
    reserve_out_0: int,
    fee_bps: int,
    quote_exact_in_fn: Callable,
) -> Tuple[int, int, Tuple[str, ...]]:
    """Simulate an ordering and return (A, B, intent_id_tuple)."""
    r_in = reserve_in_0
    r_out = reserve_out_0
    total_a = 0
    total_b = 0

    for intent_id, amount_in, min_amount_out in ordering:
        try:
            quote = quote_exact_in_fn(
                reserve_in=r_in,
                reserve_out=r_out,
                amount_in=amount_in,
                fee_bps=fee_bps,
            )
            if quote.amount_out < min_amount_out:
                continue
            total_a += amount_in
            total_b += quote.amount_out - min_amount_out
            r_in = quote.reserve_in_after
            r_out = quote.reserve_out_after
        except ValueError:
            continue

    return total_a, total_b, tuple(iid for iid, _, _ in ordering)


def brute_force_best_ordering(
    intents: List[Tuple[str, int, int]],  # (intent_id, amount_in, min_amount_out)
    *,
    reserve_in_0: int,
    reserve_out_0: int,
    fee_bps: int,
    quote_exact_in_fn: Callable,
) -> Tuple[Tuple[str, ...], int, int]:
    """Find the (A, B, lex)-optimal ordering by exhaustive search.

    Returns (best_intent_id_tuple, best_a, best_b).
    """
    if not intents:
        return (), 0, 0

    best_a = -1
    best_b = -1
    best_ids: Tuple[str, ...] = tuple()

    for perm in itertools.permutations(intents):
        a, b, ids = _simulate_ordering(
            list(perm),
            reserve_in_0=reserve_in_0,
            reserve_out_0=reserve_out_0,
            fee_bps=fee_bps,
            quote_exact_in_fn=quote_exact_in_fn,
        )
        if a > best_a or (a == best_a and b > best_b) or (a == best_a and b == best_b and ids < best_ids):
            best_a = a
            best_b = b
            best_ids = ids

    return best_ids, best_a, best_b


def brute_force_best_subset(
    intents: List[Tuple[str, int, int]],  # (intent_id, amount_in, min_amount_out)
    *,
    reserve_in_0: int,
    reserve_out_0: int,
    fee_bps: int,
    quote_exact_in_fn: Callable,
) -> Tuple[Tuple[str, ...], int, int]:
    """Find the maximum-A subset (any order) by exhaustive search.

    Tries all subsets and all orderings. Returns (best_ids, best_a, best_b).
    This is the true A-optimal, not just the best permutation of all intents.
    """
    if not intents:
        return (), 0, 0

    best_a = -1
    best_b = -1
    best_ids: Tuple[str, ...] = tuple()

    n = len(intents)
    for mask in range(1, 1 << n):
        subset = [intents[i] for i in range(n) if mask & (1 << i)]
        if not subset:
            continue
        for perm in itertools.permutations(subset):
            a, b, ids = _simulate_ordering(
                list(perm),
                reserve_in_0=reserve_in_0,
                reserve_out_0=reserve_out_0,
                fee_bps=fee_bps,
                quote_exact_in_fn=quote_exact_in_fn,
            )
            if a > best_a or (a == best_a and b > best_b) or (a == best_a and b == best_b and ids < best_ids):
                best_a = a
                best_b = b
                best_ids = ids

    return best_ids, best_a, best_b
