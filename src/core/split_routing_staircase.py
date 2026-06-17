"""
Exact staircase solver for two-pool CPMM exact-in split routing.

The solver is parameterized by the quote function to keep this module free of a
runtime dependency on `split_routing.py`; the public wrapper passes the live v8
quote implementation.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Protocol

from .domain_limits import is_strict_int

BPS_DENOM = 10_000


class _PoolLike(Protocol):
    x: int
    y: int
    fee_bps: int


_QuoteExactIn = Callable[[_PoolLike, int], int]


def _require_positive_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) <= 0:
        raise ValueError(f"{name} must be positive")
    return int(value)


@dataclass(frozen=True)
class _TwoPoolQuoteContext:
    pool0: _PoolLike
    pool1: _PoolLike
    amount_in: int
    quote_exact_in: _QuoteExactIn
    known_pool0_outputs: dict[int, int]

    def total_out_for_split(self, split_a: int) -> int | None:
        if not (0 <= int(split_a) <= int(self.amount_in)):
            return None
        split_b = int(self.amount_in) - int(split_a)
        try:
            if split_a <= 0:
                out0 = 0
            else:
                known_pool0_output = self.known_pool0_outputs.get(int(split_a))
                if known_pool0_output is None:
                    out0 = self.quote_exact_in(self.pool0, int(split_a))
                else:
                    out0 = known_pool0_output
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
    if int(pool.x) <= 0 or int(pool.y) <= 0:
        return None
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
) -> dict[int, int]:
    candidates: dict[int, int] = {}
    next_output_level = 1
    while True:
        gross_in = _min_gross_in_for_output_level(pool, next_output_level)
        if gross_in is not None and gross_in <= int(amount_in_total):
            try:
                reached_output = quote_exact_in(pool, int(gross_in))
            except ValueError as exc:
                raise ValueError("quote rejected requested output level") from exc
            if int(reached_output) < int(next_output_level):
                raise ValueError("quote did not reach requested output level")
            candidates[int(gross_in)] = int(reached_output)
            # A single gross input can jump over many output levels. Advance to
            # the next not-yet-reached level so enumeration is bounded by input
            # breakpoints, not by the raw output magnitude.
            next_output_level = int(reached_output) + 1
            continue
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

    Complexity is O(B) quotes where B is the number of distinct positive pool0
    input breakpoints reachable with `amount_in`, plus endpoint checks. B is at
    most `amount_in`, and can be much smaller than the raw output magnitude when
    reserves are skewed. This is exact because pool0 is constant between jumps
    and pool1 cannot improve as input is shifted away from it.
    """
    amount_in_i = _require_positive_control(amount_in, name="amount_in")

    pool0_jump_outputs = _pool_output_jump_candidates(
        pool0,
        amount_in_i,
        quote_exact_in=quote_exact_in,
    )
    quote_context = _TwoPoolQuoteContext(
        pool0=pool0,
        pool1=pool1,
        amount_in=amount_in_i,
        quote_exact_in=quote_exact_in,
        known_pool0_outputs=pool0_jump_outputs,
    )
    best: tuple[int, int] | None = None
    candidates = {0, amount_in_i} | set(pool0_jump_outputs)
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
