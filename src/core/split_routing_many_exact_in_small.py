"""Bounded exact allocator for small many-pool exact-in split domains."""

from __future__ import annotations

from typing import Callable, Sequence

ExactInQuoteForPoolId = Callable[[str, int], int | None]
_ExactState = tuple[int, tuple[tuple[str, int], ...]]


def _allocation_from_legs(legs: tuple[tuple[str, int], ...], pool_ids: Sequence[str]) -> dict[str, int]:
    alloc: dict[str, int] = {pool_id: 0 for pool_id in pool_ids}
    for pool_id, amount in legs:
        alloc[pool_id] = int(amount)
    return alloc


def _quote_table(
    *,
    pool_ids: Sequence[str],
    amount_in_total: int,
    quote_for_pool_id: ExactInQuoteForPoolId,
) -> dict[str, list[int | None]]:
    table: dict[str, list[int | None]] = {}
    for pool_id in pool_ids:
        by_amount: list[int | None] = [0]
        for amount in range(1, int(amount_in_total) + 1):
            by_amount.append(quote_for_pool_id(pool_id, amount))
        table[pool_id] = by_amount
    return table


def _is_better_state(candidate: _ExactState, incumbent: _ExactState | None) -> bool:
    if incumbent is None:
        return True
    candidate_out, candidate_legs = candidate
    incumbent_out, incumbent_legs = incumbent
    if candidate_out != incumbent_out:
        return candidate_out > incumbent_out
    return candidate_legs < incumbent_legs


def _is_better_final(
    *,
    candidate_out: int,
    candidate_legs: tuple[tuple[str, int], ...],
    best_out: int,
    best_legs: tuple[tuple[str, int], ...] | None,
) -> bool:
    if candidate_out != best_out:
        return candidate_out > best_out
    if best_legs is None:
        return True
    if len(candidate_legs) != len(best_legs):
        return len(candidate_legs) < len(best_legs)
    return candidate_legs < best_legs


def best_small_domain_many_pool_exact_in(
    *,
    pool_ids: Sequence[str],
    amount_in_total: int,
    max_legs: int,
    quote_for_pool_id: ExactInQuoteForPoolId,
) -> dict[str, int]:
    """Return the exact best allocation on a bounded selected-pool domain.

    Tie-breaks match the runtime route key: higher output, fewer positive legs,
    then lexicographic `(pool_id, amount_in)` legs.
    """
    canonical_pool_ids = tuple(sorted(pool_ids))
    amount_total = int(amount_in_total)
    quote_table = _quote_table(
        pool_ids=canonical_pool_ids,
        amount_in_total=amount_total,
        quote_for_pool_id=quote_for_pool_id,
    )

    states: dict[tuple[int, int], _ExactState] = {(0, 0): (0, ())}
    for pool_id in canonical_pool_ids:
        next_states = dict(states)
        pool_quotes = quote_table[pool_id]
        for (used_legs, spent), (total_out, legs) in states.items():
            if used_legs >= int(max_legs):
                continue
            for amount in range(1, amount_total - int(spent) + 1):
                out_amount = pool_quotes[amount]
                if out_amount is None:
                    continue
                key = (int(used_legs) + 1, int(spent) + amount)
                candidate = (
                    int(total_out) + int(out_amount),
                    tuple(sorted((*legs, (pool_id, amount)))),
                )
                if _is_better_state(candidate, next_states.get(key)):
                    next_states[key] = candidate
        states = next_states

    best_out = -1
    best_legs: tuple[tuple[str, int], ...] | None = None
    for used_legs in range(1, int(max_legs) + 1):
        state = states.get((used_legs, amount_total))
        if state is None:
            continue
        total_out, legs = state
        if _is_better_final(
            candidate_out=int(total_out),
            candidate_legs=legs,
            best_out=int(best_out),
            best_legs=best_legs,
        ):
            best_out = int(total_out)
            best_legs = legs

    if best_legs is None:
        raise ValueError("no feasible allocation")
    return _allocation_from_legs(best_legs, canonical_pool_ids)
