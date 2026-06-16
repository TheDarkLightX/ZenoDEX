"""
Windowed two-pool exact-in split-routing search.

The caller supplies the exact split quote cache. This module owns the deterministic
search policy over an already-computed both-valid interval.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Protocol

from .split_routing_dgstr import DgstrSearchRequest, search_dgstr_v1

BPS_DENOM = 10_000
SplitTotalOut = Callable[[int], int | None]


class _PoolLike(Protocol):
    x: int
    y: int
    fee_bps: int


@dataclass(frozen=True)
class WindowSearchPlan:
    pool0: _PoolLike
    pool1: _PoolLike
    amount_in: int
    bounds: tuple[int, int]
    profile: str
    grid_n: int
    force_dense_grid: bool
    left_sweep_k: int
    window: int
    total_out: SplitTotalOut


@dataclass(frozen=True)
class _CenterSearchPolicy:
    lo_both: int
    hi_both: int
    a_star: int
    grid_n: int
    window: int
    force_dense_grid: bool
    left_sweep_k: int


def _is_better_candidate(cand: tuple[int, int] | None, best: tuple[int, int] | None) -> bool:
    if cand is None:
        return False
    if best is None:
        return True
    return bool(cand[0] > best[0] or (cand[0] == best[0] and cand[1] < best[1]))


def _derivative_gt(pool0: _PoolLike, a0: int, pool1: _PoolLike, a1: int) -> bool:
    """
    Compare continuous marginal outputs without floats.

    For the continuous approximation (ignore ceil/floor effects):
      out(a) = y * (alpha*a) / (x + alpha*a), where alpha = (BPS - fee_bps)/BPS.
    The derivative simplifies to:
      out'(a) proportional to (y * alpha_num * x) / (BPS*x + alpha_num*a)^2
    where alpha_num = BPS - fee_bps.

    Returns True iff out0'(a0) > out1'(a1).
    """
    a0 = int(a0)
    a1 = int(a1)
    alpha0 = int(BPS_DENOM) - int(pool0.fee_bps)
    alpha1 = int(BPS_DENOM) - int(pool1.fee_bps)
    if alpha0 <= 0 or alpha1 <= 0:
        return False
    if pool0.x <= 0 or pool0.y <= 0 or pool1.x <= 0 or pool1.y <= 0:
        return False
    # Compare: w0/den0^2 > w1/den1^2 iff w0*den1^2 > w1*den0^2.
    w0 = int(pool0.y) * int(alpha0) * int(pool0.x)
    w1 = int(pool1.y) * int(alpha1) * int(pool1.x)
    den0 = int(BPS_DENOM) * int(pool0.x) + int(alpha0) * int(a0)
    den1 = int(BPS_DENOM) * int(pool1.x) + int(alpha1) * int(a1)
    if den0 <= 0 or den1 <= 0:
        return False
    return int(w0) * int(den1) * int(den1) > int(w1) * int(den0) * int(den0)


def _seed_opt_split_by_derivative(
    pool0: _PoolLike,
    pool1: _PoolLike,
    *,
    amount_in_total: int,
    lo_both: int,
    hi_both: int,
) -> int:
    """
    Deterministic integer seed for the best split under a continuous approximation.

    Binary-search for the first `a` where out0'(a) <= out1'(D-a) inside the
    both-valid interval [lo_both, hi_both].
    """
    amount_in = int(amount_in_total)
    lo = int(lo_both)
    hi = int(hi_both)
    if lo > hi:
        return lo
    if _derivative_gt(pool0, hi, pool1, int(amount_in - hi)):
        return hi
    if not _derivative_gt(pool0, lo, pool1, int(amount_in - lo)):
        return lo

    while lo < hi:
        mid = (lo + hi) // 2
        if _derivative_gt(pool0, mid, pool1, int(amount_in - mid)):
            lo = mid + 1
        else:
            hi = mid
    return int(lo)


def _scan_range_best(
    *,
    lo: int,
    hi: int,
    total_out: SplitTotalOut,
) -> tuple[int, int] | None:
    if lo > hi:
        return None
    best_out = -1
    best_a = 0
    for split_a in range(int(lo), int(hi) + 1):
        total = total_out(int(split_a))
        if total is None:
            continue
        if total > best_out or (total == best_out and int(split_a) < best_a):
            best_out = int(total)
            best_a = int(split_a)
    return None if best_out < 0 else (int(best_out), int(best_a))


def _canonicalize_leftmost(
    *,
    lo_both: int,
    candidate: tuple[int, int],
    total_out: SplitTotalOut,
) -> tuple[int, int]:
    best_out, best_a = int(candidate[0]), int(candidate[1])
    while best_a > int(lo_both):
        prev = total_out(int(best_a) - 1)
        if prev is None or int(prev) != int(best_out):
            break
        best_a -= 1
    return int(best_out), int(best_a)


def _split_search_centers(policy: _CenterSearchPolicy) -> set[int]:
    span = int(policy.hi_both) - int(policy.lo_both)
    centers = {
        int(policy.lo_both),
        int(policy.hi_both),
        int((policy.lo_both + policy.hi_both) // 2),
        int(policy.a_star),
    }
    if span > 0 and (policy.force_dense_grid or span > int(policy.grid_n) * int(policy.window)):
        for i in range(1, int(policy.grid_n)):
            centers.add(int(policy.lo_both) + (span * i) // int(policy.grid_n))

    if int(policy.left_sweep_k) <= 0 or int(policy.window) <= 0:
        return centers
    for k in range(1, int(policy.left_sweep_k) + 1):
        center = int(policy.a_star) - int(k) * int(policy.window)
        if center <= int(policy.lo_both):
            centers.add(int(policy.lo_both))
            break
        centers.add(center)
    return centers


def _scan_centers_best(
    *,
    centers: set[int],
    lo_both: int,
    hi_both: int,
    window: int,
    total_out: SplitTotalOut,
) -> tuple[int, int] | None:
    best: tuple[int, int] | None = None
    for center in sorted(centers):
        candidate = _scan_range_best(
            lo=max(int(lo_both), int(center) - int(window)),
            hi=min(int(hi_both), int(center) + int(window)),
            total_out=total_out,
        )
        if _is_better_candidate(candidate, best):
            best = candidate
    return best


def _refine_window_best(
    *,
    candidate: tuple[int, int],
    lo_both: int,
    hi_both: int,
    span: int,
    window: int,
    total_out: SplitTotalOut,
) -> tuple[int, int]:
    refine_out, refine_a = int(candidate[0]), int(candidate[1])
    half = max(1, int(window))
    while True:
        scan_cand = _scan_range_best(
            lo=max(int(lo_both), refine_a - half),
            hi=min(int(hi_both), refine_a + half),
            total_out=total_out,
        )
        if _is_better_candidate(scan_cand, (refine_out, refine_a)):
            if scan_cand is None:
                raise RuntimeError("internal split-routing candidate ordering invariant violated")
            refine_out, refine_a = int(scan_cand[0]), int(scan_cand[1])

        r_lo = max(int(lo_both), refine_a - half)
        r_hi = min(int(hi_both), refine_a + half)
        if r_lo == int(lo_both) and r_hi == int(hi_both):
            break
        if refine_a in (r_lo, r_hi) and refine_a not in (int(lo_both), int(hi_both)):
            half = min(int(span), half * 2)
            continue
        break
    return refine_out, refine_a


def _dense_profile_leftmost(
    *,
    candidate: tuple[int, int],
    lo_both: int,
    total_out: SplitTotalOut,
    force_dense_grid: bool,
) -> tuple[int, int]:
    best_out, best_a = _canonicalize_leftmost(lo_both=int(lo_both), candidate=candidate, total_out=total_out)
    if not force_dense_grid:
        return best_out, best_a

    for split_a in range(int(lo_both), int(best_a)):
        total = total_out(int(split_a))
        if total is not None and int(total) == int(best_out):
            return int(best_out), int(split_a)
    return int(best_out), int(best_a)


def search_windowed_both_valid(plan: WindowSearchPlan) -> tuple[int, int] | None:
    lo_both, hi_both = int(plan.bounds[0]), int(plan.bounds[1])
    a_star = _seed_opt_split_by_derivative(
        plan.pool0,
        plan.pool1,
        amount_in_total=int(plan.amount_in),
        lo_both=lo_both,
        hi_both=hi_both,
    )
    a_star = max(lo_both, min(hi_both, int(a_star)))
    if plan.profile == "dgstr_v1":
        return search_dgstr_v1(
            DgstrSearchRequest(
                lo=lo_both,
                hi=hi_both,
                a_star=a_star,
                window=int(plan.window),
                total_out=plan.total_out,
            )
        )

    span = hi_both - lo_both
    policy = _CenterSearchPolicy(
        lo_both=lo_both,
        hi_both=hi_both,
        a_star=a_star,
        grid_n=int(plan.grid_n),
        window=int(plan.window),
        force_dense_grid=plan.force_dense_grid,
        left_sweep_k=int(plan.left_sweep_k),
    )
    local_best = _scan_centers_best(
        centers=_split_search_centers(policy),
        lo_both=lo_both,
        hi_both=hi_both,
        window=int(plan.window),
        total_out=plan.total_out,
    )
    if local_best is None:
        return None
    refined = _refine_window_best(
        candidate=local_best,
        lo_both=lo_both,
        hi_both=hi_both,
        span=span,
        window=int(plan.window),
        total_out=plan.total_out,
    )
    return _dense_profile_leftmost(
        candidate=refined,
        lo_both=lo_both,
        total_out=plan.total_out,
        force_dense_grid=plan.force_dense_grid,
    )
