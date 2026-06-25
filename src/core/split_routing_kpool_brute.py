"""Brute-force oracle for k-pool exact-in split routing.

Reference solver for testing the staircase k-pool optimizer. Enumerates all
feasible allocations with at most `max_legs` positive legs. Exponential in k
but bounded by D for small k. Used only in tests.
"""

from __future__ import annotations

from itertools import combinations_with_replacement, product
from typing import Callable, Protocol, Sequence

from .domain_limits import is_strict_int

BPS_DENOM = 10_000


class _PoolLike(Protocol):
    x: int
    y: int
    fee_bps: int


_QuoteExactIn = Callable[[_PoolLike, int], int]
_PoolId = str


def _require_positive_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) <= 0:
        raise ValueError(f"{name} must be positive")
    return int(value)


def _brute_force_k_pool_split(
    *,
    pools: Sequence[tuple[_PoolId, _PoolLike, int]],
    amount_in_total: int,
    max_legs: int,
    quote_exact_in: _QuoteExactIn,
) -> dict[_PoolId, int]:
    """Brute-force exact k-pool split.

    Enumerates all subsets of pools of size 1..max_legs, and for each subset,
    all compositions of amount_in_total into that many positive parts. Returns
    the canonical-best allocation.
    """
    amount_total = _require_positive_control(amount_in_total, name="amount_in_total")
    max_legs_i = _require_positive_control(max_legs, name="max_legs")

    def quote_pool(pool: _PoolLike, amount: int) -> int | None:
        if amount <= 0:
            return 0
        try:
            return int(quote_exact_in(pool, int(amount)))
        except ValueError:
            return None

    best_out = -1
    best_legs: tuple[tuple[_PoolId, int], ...] | None = None

    pool_list = list(pools)
    for num_legs in range(1, int(max_legs_i) + 1):
        if num_legs > len(pool_list):
            break
        for subset in combinations_with_replacement(range(len(pool_list)), num_legs):
            # Skip subsets with repeated pool indices (a pool can only appear once).
            if len(set(subset)) != num_legs:
                continue
            # Enumerate compositions of amount_total into num_legs positive parts.
            for parts in _compositions(int(amount_total), num_legs):
                legs: list[tuple[_PoolId, int]] = []
                total = 0
                feasible = True
                for idx, part in zip(subset, parts):
                    pool_id, pool, min_valid = pool_list[idx]
                    if int(part) < int(min_valid):
                        feasible = False
                        break
                    out = quote_pool(pool, int(part))
                    if out is None:
                        feasible = False
                        break
                    total += int(out)
                    legs.append((pool_id, int(part)))
                if not feasible:
                    continue
                legs_sorted = tuple(sorted(legs))
                if best_legs is None or total > best_out or (
                    total == best_out and (
                        len(legs_sorted) < len(best_legs) or (
                            len(legs_sorted) == len(best_legs) and legs_sorted < best_legs
                        )
                    )
                ):
                    best_out = int(total)
                    best_legs = legs_sorted

    if best_legs is None:
        raise ValueError("no feasible split")

    alloc: dict[_PoolId, int] = {pool_id: 0 for pool_id, _, _ in pool_list}
    for pool_id, amount in best_legs:
        alloc[pool_id] = int(amount)
    return alloc


def _compositions(n: int, k: int) -> list[tuple[int, ...]]:
    """All compositions of n into k positive integer parts."""
    if k <= 0:
        return [] if n != 0 else [()]
    if k == 1:
        return [(n,)] if n >= 1 else []
    result: list[tuple[int, ...]] = []
    for first in range(1, n - (k - 1) + 1):
        for rest in _compositions(n - first, k - 1):
            result.append((first,) + rest)
    return result
