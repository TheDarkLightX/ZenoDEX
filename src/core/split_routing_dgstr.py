"""
Discrete golden-section / ternary-style split-routing search profile.

This module is deliberately independent of CPMM pool types. The caller supplies
the deterministic split quote function for the already-bounded feasible interval.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable

SplitTotalOut = Callable[[int], int | None]


@dataclass(frozen=True)
class DgstrSearchRequest:
    lo: int
    hi: int
    a_star: int
    window: int
    total_out: SplitTotalOut


@dataclass
class _DgstrSearchState:
    request: DgstrSearchRequest
    point_vals: dict[int, int | None] = field(default_factory=dict)

    @property
    def lo(self) -> int:
        return int(self.request.lo)

    @property
    def hi(self) -> int:
        return int(self.request.hi)

    @property
    def a_star(self) -> int:
        return int(self.request.a_star)

    @property
    def window(self) -> int:
        return int(self.request.window)

    def probe(self, split_a: int) -> int | None:
        if not (self.lo <= int(split_a) <= self.hi):
            return None
        key = int(split_a)
        if key not in self.point_vals:
            self.point_vals[key] = self.request.total_out(key)
        return self.point_vals[key]


def _is_better_candidate(cand: tuple[int, int] | None, best: tuple[int, int] | None) -> bool:
    if cand is None:
        return False
    if best is None:
        return True
    return bool(cand[0] > best[0] or (cand[0] == best[0] and cand[1] < best[1]))


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
    lo: int,
    candidate: tuple[int, int],
    total_out: SplitTotalOut,
) -> tuple[int, int]:
    best_out, best_a = int(candidate[0]), int(candidate[1])
    while best_a > int(lo):
        prev = total_out(int(best_a) - 1)
        if prev is None or int(prev) != int(best_out):
            break
        best_a -= 1
    return int(best_out), int(best_a)


def _seed_centers(state: _DgstrSearchState) -> set[int]:
    span = int(state.hi - state.lo)
    centers = {int(state.lo), int(state.hi), int((state.lo + state.hi) // 2), int(state.a_star)}
    if span > 0:
        for i in range(1, 8):
            centers.add(int(state.lo + (span * i) // 8))
    return centers


def _probe_centers(state: _DgstrSearchState, centers: set[int]) -> tuple[int, int] | None:
    best: tuple[int, int] | None = None
    for center in sorted(centers):
        value = state.probe(int(center))
        if value is None:
            continue
        candidate = (int(value), int(center))
        if _is_better_candidate(candidate, best):
            best = candidate
    return best


def _narrow_window(state: _DgstrSearchState) -> tuple[int, int]:
    cur_lo = int(state.lo)
    cur_hi = int(state.hi)
    while cur_hi - cur_lo > max(4 * int(state.window), 160):
        span = int(cur_hi - cur_lo)
        step = max(1, span // 3)
        m1 = int(cur_lo + step)
        m2 = int(cur_hi - step)
        v1 = state.probe(m1)
        v2 = state.probe(m2)
        if v2 is None or (v1 is not None and int(v1) > int(v2)):
            cur_hi = m2
        elif v1 is None or int(v2) > int(v1):
            cur_lo = m1
        else:
            cur_lo = m1
            cur_hi = m2
    return int(cur_lo), int(cur_hi)


def _rescue_centers(state: _DgstrSearchState, cur_lo: int, cur_hi: int) -> list[int]:
    ranked = [(int(value), int(split_a)) for split_a, value in state.point_vals.items() if value is not None]
    ranked.sort(key=lambda t: (int(t[0]), -int(t[1])), reverse=True)
    centers = [int(split_a) for _value, split_a in ranked[:6]]
    centers.extend([int(cur_lo), int(cur_hi), int((cur_lo + cur_hi) // 2), int(state.a_star)])
    return centers


def _scan_rescue_windows(
    state: _DgstrSearchState,
    *,
    best: tuple[int, int] | None,
    rescue_centers: list[int],
) -> tuple[int, int] | None:
    seen: set[int] = set()
    for center in rescue_centers:
        if int(center) in seen:
            continue
        seen.add(int(center))
        candidate = _scan_range_best(
            lo=max(int(state.lo), int(center) - int(state.window)),
            hi=min(int(state.hi), int(center) + int(state.window)),
            total_out=state.request.total_out,
        )
        if _is_better_candidate(candidate, best):
            best = candidate
    return best


def search_dgstr_v1(request: DgstrSearchRequest) -> tuple[int, int] | None:
    """
    Experimental search profile:
    - sparse deterministic probes across the feasible interval,
    - repeated discrete ternary refinement,
    - bounded rescue scans around the strongest probe centers.

    This is intentionally scoped to easy regimes and is not used as the default profile.
    """
    if int(request.lo) > int(request.hi):
        return None

    state = _DgstrSearchState(request=request)
    best = _probe_centers(state, _seed_centers(state))
    cur_lo, cur_hi = _narrow_window(state)
    best = _scan_rescue_windows(
        state,
        best=best,
        rescue_centers=_rescue_centers(state, cur_lo, cur_hi),
    )

    if best is None:
        return None
    return _canonicalize_leftmost(lo=request.lo, candidate=best, total_out=request.total_out)
