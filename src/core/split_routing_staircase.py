"""
Exact staircase solver for two-pool CPMM exact-in split routing.

The solver is parameterized by the quote function to keep this module free of a
runtime dependency on `split_routing.py`; the public wrapper passes the live v8
quote implementation.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Protocol

BPS_DENOM = 10_000


class _PoolLike(Protocol):
    x: int
    y: int
    fee_bps: int


_QuoteExactIn = Callable[[_PoolLike, int], int]


@dataclass(frozen=True)
class _TwoPoolQuoteContext:
    pool0: _PoolLike
    pool1: _PoolLike
    amount_in: int
    quote_exact_in: _QuoteExactIn

    def total_out_for_split(self, split_a: int) -> int | None:
        if not (0 <= int(split_a) <= int(self.amount_in)):
            return None
        split_b = int(self.amount_in) - int(split_a)
        try:
            out0 = self.quote_exact_in(self.pool0, int(split_a)) if split_a > 0 else 0
            out1 = self.quote_exact_in(self.pool1, split_b) if split_b > 0 else 0
        except ValueError:
            return None
        return int(out0 + out1)


def _is_better_candidate(cand: tuple[int, int] | None, best: tuple[int, int] | None) -> bool:
    if cand is None:
        return False
    if best is None:
        return True
    return bool(cand[0] > best[0] or (cand[0] == best[0] and cand[1] < best[1]))


def _ceil_div_positive(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    return (int(numerator) + int(denominator) - 1) // int(denominator)


def _min_gross_in_for_output_level(pool: _PoolLike, output_level: int) -> int | None:
    alpha = int(BPS_DENOM) - int(pool.fee_bps)
    target = int(output_level)
    if alpha <= 0 or target <= 0 or target >= int(pool.y):
        return None

    # Invert floor(y*n/(x+n)) >= target to n >= ceil(target*x/(y-target)),
    # then invert net=floor(gross*alpha/BPS_DENOM).
    min_net = _ceil_div_positive(target * int(pool.x), int(pool.y) - target)
    return _ceil_div_positive(min_net * int(BPS_DENOM), alpha)


def _pool_output_jump_candidates(
    pool: _PoolLike,
    amount_in_total: int,
    *,
    quote_exact_in: _QuoteExactIn,
) -> set[int]:
    candidates: set[int] = set()
    try:
        max_output = quote_exact_in(pool, int(amount_in_total))
    except ValueError:
        return candidates

    for output_level in range(1, int(max_output) + 1):
        gross_in = _min_gross_in_for_output_level(pool, output_level)
        if gross_in is not None and gross_in <= int(amount_in_total):
            candidates.add(int(gross_in))
    return candidates


def staircase_jump_best_split_two_pools_exact_in(
    pool0: _PoolLike,
    pool1: _PoolLike,
    amount_in: int,
    *,
    quote_exact_in: _QuoteExactIn,
) -> tuple[int, int]:
    """
    Exact two-pool CPMM split by enumerating pool0 output jump points.

    Complexity is O(J) quotes where J is the number of distinct positive pool0
    outputs reachable with `amount_in`, plus two endpoint checks. This is exact
    because pool0 is constant between jumps and pool1 cannot improve as input is
    shifted away from it.
    """
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")

    quote_context = _TwoPoolQuoteContext(
        pool0=pool0,
        pool1=pool1,
        amount_in=int(amount_in),
        quote_exact_in=quote_exact_in,
    )
    best: tuple[int, int] | None = None
    candidates = {0, int(amount_in)} | _pool_output_jump_candidates(
        pool0,
        int(amount_in),
        quote_exact_in=quote_exact_in,
    )
    for split_a in sorted(candidates):
        total = quote_context.total_out_for_split(int(split_a))
        if total is None:
            continue
        candidate = (int(total), int(split_a))
        if _is_better_candidate(candidate, best):
            best = candidate

    if best is None:
        raise ValueError("no feasible split")
    return int(best[0]), int(best[1])
