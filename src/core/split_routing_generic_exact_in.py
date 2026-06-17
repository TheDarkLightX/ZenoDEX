"""
Pool-agnostic exact-in two-way split solver.

The caller provides deterministic exact-in quote functions for each leg. This
keeps curve-specific pool state out of the bounded search algorithm.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

from .domain_limits import is_strict_int

ExactInQuote = Callable[[int], int]


@dataclass(frozen=True)
class GenericExactInSplitRequest:
    amount_in_total: int
    window: int
    brute_force_max: int
    quote0: ExactInQuote
    quote1: ExactInQuote


def _require_positive_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) <= 0:
        raise ValueError(f"{name} must be positive")
    return int(value)


def _require_nonnegative_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def _total_out(request: GenericExactInSplitRequest, split_a: int) -> int | None:
    if not (0 <= int(split_a) <= int(request.amount_in_total)):
        return None
    split_b = int(request.amount_in_total) - int(split_a)
    try:
        out0 = request.quote0(int(split_a)) if split_a > 0 else 0
        out1 = request.quote1(int(split_b)) if split_b > 0 else 0
    except ValueError:
        return None
    return int(out0 + out1)


def _is_better(candidate: tuple[int, int] | None, best: tuple[int, int] | None) -> bool:
    if candidate is None:
        return False
    if best is None:
        return True
    return bool(candidate[0] > best[0] or (candidate[0] == best[0] and candidate[1] < best[1]))


def _brute_force_best_split(request: GenericExactInSplitRequest) -> tuple[int, int]:
    best: tuple[int, int] | None = None
    for split_a in range(0, int(request.amount_in_total) + 1):
        total = _total_out(request, int(split_a))
        if total is None:
            continue
        candidate = (int(total), int(split_a))
        if _is_better(candidate, best):
            best = candidate
    if best is None:
        raise ValueError("no feasible split")
    return int(best[0]), int(best[1])


def _is_valid_amount(quote: ExactInQuote, amount_in: int) -> bool:
    if amount_in <= 0:
        return False
    try:
        quote(int(amount_in))
    except ValueError:
        return False
    return True


def _min_valid_amount(quote: ExactInQuote, amount_in_total: int) -> int | None:
    if not _is_valid_amount(quote, int(amount_in_total)):
        return None
    lo = 1
    hi = int(amount_in_total)
    while lo < hi:
        mid = (lo + hi) // 2
        if _is_valid_amount(quote, int(mid)):
            hi = mid
        else:
            lo = mid + 1
    return int(lo)


def _scan_range_best(
    request: GenericExactInSplitRequest,
    *,
    lo: int,
    hi: int,
) -> tuple[int, int] | None:
    if lo > hi:
        return None
    best: tuple[int, int] | None = None
    for split_a in range(int(lo), int(hi) + 1):
        total = _total_out(request, int(split_a))
        if total is None:
            continue
        candidate = (int(total), int(split_a))
        if _is_better(candidate, best):
            best = candidate
    return best


def _endpoint_best(request: GenericExactInSplitRequest) -> tuple[int, int] | None:
    best: tuple[int, int] | None = None
    for split_a in (0, int(request.amount_in_total)):
        total = _total_out(request, int(split_a))
        if total is None:
            continue
        candidate = (int(total), int(split_a))
        if _is_better(candidate, best):
            best = candidate
    return best


def _center_splits(*, lo_both: int, hi_both: int, window: int) -> set[int]:
    span = int(hi_both - lo_both)
    centers = {int(lo_both), int(hi_both), int((lo_both + hi_both) // 2)}
    if span > 8 * int(window):
        for i in range(1, 8):
            centers.add(int(lo_both) + (span * i) // 8)
    return centers


def _best_center_scan(
    request: GenericExactInSplitRequest,
    *,
    centers: set[int],
    lo_both: int,
    hi_both: int,
) -> tuple[int, int] | None:
    best: tuple[int, int] | None = None
    for center in sorted(centers):
        candidate = _scan_range_best(
            request,
            lo=max(int(lo_both), int(center) - int(request.window)),
            hi=min(int(hi_both), int(center) + int(request.window)),
        )
        if _is_better(candidate, best):
            best = candidate
    return best


def _refine_best_window(
    request: GenericExactInSplitRequest,
    *,
    candidate: tuple[int, int],
    lo_both: int,
    hi_both: int,
    span: int,
) -> tuple[int, int]:
    refine_out, refine_a = int(candidate[0]), int(candidate[1])
    half = max(1, int(request.window))
    while True:
        r_lo = max(int(lo_both), refine_a - half)
        r_hi = min(int(hi_both), refine_a + half)
        scan_candidate = _scan_range_best(request, lo=r_lo, hi=r_hi)
        if scan_candidate is not None:
            refine_out2, refine_a2 = int(scan_candidate[0]), int(scan_candidate[1])
            if refine_out2 > refine_out or (refine_out2 == refine_out and refine_a2 < refine_a):
                refine_out, refine_a = refine_out2, refine_a2
        if r_lo == int(lo_both) and r_hi == int(hi_both):
            break
        if refine_a in (r_lo, r_hi):
            half *= 2
            if half >= int(span):
                half = int(span)
            continue
        break
    return int(refine_out), int(refine_a)


def _canonicalize_leftmost(
    request: GenericExactInSplitRequest,
    *,
    candidate: tuple[int, int],
    lo_both: int,
) -> tuple[int, int]:
    best_out, best_a = int(candidate[0]), int(candidate[1])
    while best_a > int(lo_both):
        prev = _total_out(request, int(best_a) - 1)
        if prev is None or int(prev) != int(best_out):
            break
        best_a -= 1
    return int(best_out), int(best_a)


def _both_valid_bounds(request: GenericExactInSplitRequest) -> tuple[int, int] | None:
    min0 = _min_valid_amount(request.quote0, int(request.amount_in_total))
    min1 = _min_valid_amount(request.quote1, int(request.amount_in_total))
    if min0 is None or min1 is None:
        return None
    lo_both = int(min0)
    hi_both = int(request.amount_in_total) - int(min1)
    return (lo_both, hi_both) if lo_both <= hi_both else None


def _best_both_valid_split(request: GenericExactInSplitRequest) -> tuple[int, int] | None:
    bounds = _both_valid_bounds(request)
    if bounds is None:
        return None
    lo_both, hi_both = int(bounds[0]), int(bounds[1])
    span = int(hi_both - lo_both)
    best = _best_center_scan(
        request,
        centers=_center_splits(lo_both=lo_both, hi_both=hi_both, window=int(request.window)),
        lo_both=lo_both,
        hi_both=hi_both,
    )
    if best is None:
        return None
    refined = _refine_best_window(
        request,
        candidate=best,
        lo_both=lo_both,
        hi_both=hi_both,
        span=span,
    )
    return _canonicalize_leftmost(request, candidate=refined, lo_both=lo_both)


def best_generic_two_pool_exact_in(request: GenericExactInSplitRequest) -> tuple[int, int]:
    amount_in_total = _require_positive_control(request.amount_in_total, name="amount_in_total")
    _require_nonnegative_control(request.window, name="window")
    brute_force_max = _require_nonnegative_control(request.brute_force_max, name="brute_force_max")

    if amount_in_total <= brute_force_max:
        return _brute_force_best_split(request)

    best = _endpoint_best(request)
    best_both = _best_both_valid_split(request)
    if _is_better(best_both, best):
        best = best_both

    if best is None:
        raise ValueError("no feasible split")
    return int(best[0]), int(best[1])
