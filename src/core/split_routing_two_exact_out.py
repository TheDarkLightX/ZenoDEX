"""
Two-pool exact-out split routing.

The solver minimizes total input for a fixed output target and breaks ties by
the canonical exact-out route key.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

from ..state.balances import AssetId
from ..state.pools import PoolState
from .domain_limits import is_strict_int
from .split_routing_types import (
    ExactOutRouteCanonicalKey,
    SplitTwoPoolsQuote,
    exact_out_route_canonical_key_for_legs,
)

_LOCAL_CERTIFICATION_MAX_HOPS = 16

ExactOutReservesFor = Callable[[PoolState], tuple[int, int] | None]
ExactOutQuoteFor = Callable[[PoolState, int], int]


@dataclass(frozen=True)
class TwoPoolExactOutRequest:
    pool0: PoolState
    pool1: PoolState
    asset_in: AssetId
    asset_out: AssetId
    amount_out_total: int
    window: int
    brute_force_max: int
    reserves_for: ExactOutReservesFor
    quote_exact_out: ExactOutQuoteFor


@dataclass(frozen=True)
class _TwoPoolExactOutContext:
    p0: PoolState
    p1: PoolState
    amount_out_total: int
    reserve_in_0: int
    reserve_out_0: int
    reserve_in_1: int
    reserve_out_1: int
    lo: int
    hi: int
    quote_exact_out: ExactOutQuoteFor

    @property
    def span(self) -> int:
        return int(self.hi - self.lo)

    def total_input_for_split(self, q0: int) -> int | None:
        if q0 < self.lo or q0 > self.hi:
            return None
        q1 = int(self.amount_out_total) - int(q0)
        try:
            in0 = self.quote_exact_out(self.p0, int(q0)) if q0 > 0 else 0
            in1 = self.quote_exact_out(self.p1, int(q1)) if q1 > 0 else 0
        except ValueError:
            return None
        return int(in0 + in1)

    def route_key_for_split(self, q0: int, total_input: int) -> ExactOutRouteCanonicalKey:
        q1 = int(self.amount_out_total) - int(q0)
        legs: list[tuple[str, int]] = []
        if int(q0) > 0:
            legs.append((self.p0.pool_id, int(q0)))
        if int(q1) > 0:
            legs.append((self.p1.pool_id, int(q1)))
        return exact_out_route_canonical_key_for_legs(
            amount_in_total=int(total_input),
            legs=tuple(legs),
        )

    def scan_range(self, range_lo: int, range_hi: int) -> tuple[int, int] | None:
        if range_lo > range_hi:
            return None
        best_in: int | None = None
        best_key: ExactOutRouteCanonicalKey | None = None
        best_q0 = int(range_lo)
        for q0 in range(int(range_lo), int(range_hi) + 1):
            total_input = self.total_input_for_split(int(q0))
            if total_input is None:
                continue
            candidate_key = self.route_key_for_split(int(q0), int(total_input))
            if best_in is None or best_key is None:
                best_in = int(total_input)
                best_key = candidate_key
                best_q0 = int(q0)
                continue
            if int(total_input) < int(best_in) or (int(total_input) == int(best_in) and candidate_key < best_key):
                best_in = int(total_input)
                best_key = candidate_key
                best_q0 = int(q0)
        return None if best_in is None else (int(best_in), int(best_q0))

    def derivative_ge(self, q0: int) -> bool:
        bps = 10_000
        alpha0 = int(bps) - int(self.p0.fee_bps)
        alpha1 = int(bps) - int(self.p1.fee_bps)
        q0 = int(q0)
        q1 = int(self.amount_out_total) - int(q0)
        y0_minus = int(self.reserve_out_0) - int(q0)
        y1_minus = int(self.reserve_out_1) - int(q1)
        if y0_minus <= 0 or y1_minus <= 0:
            return True
        if alpha0 <= 0 or alpha1 <= 0:
            return True
        left = int(self.reserve_in_0) * int(self.reserve_out_0) * int(alpha1) * int(y1_minus) * int(y1_minus)
        right = int(self.reserve_in_1) * int(self.reserve_out_1) * int(alpha0) * int(y0_minus) * int(y0_minus)
        return left >= right

    def seed_q0(self) -> int:
        a = int(self.lo)
        b = int(self.hi)
        if a > b:
            return a
        if self.derivative_ge(a):
            return a
        if not self.derivative_ge(b):
            return b
        while a < b:
            mid = (a + b) // 2
            if self.derivative_ge(mid):
                b = mid
            else:
                a = mid + 1
        return int(a)

    def window_centers(self, window: int) -> set[int]:
        q0_star = self.seed_q0()
        centers = {int(self.lo), int(self.hi), int(q0_star), int((int(self.lo) + int(self.hi)) // 2)}
        if int(self.span) > 8 * int(window):
            # Keep quote costs bounded while still probing endpoint pockets where rounding can improve.
            for i in (1, 3, 5, 7):
                centers.add(int(self.lo) + (int(self.span) * int(i)) // 8)
        return centers

    def materialize_quote(self, best_q0: int) -> SplitTwoPoolsQuote:
        q1 = int(self.amount_out_total) - int(best_q0)
        in0 = self.quote_exact_out(self.p0, int(best_q0)) if best_q0 > 0 else 0
        in1 = self.quote_exact_out(self.p1, int(q1)) if q1 > 0 else 0
        return SplitTwoPoolsQuote(
            pool0_id=self.p0.pool_id,
            pool1_id=self.p1.pool_id,
            amount_in_total=int(in0 + in1),
            amount_out_total=int(self.amount_out_total),
            amount_in_0=int(in0),
            amount_out_0=int(best_q0),
            amount_in_1=int(in1),
            amount_out_1=int(q1),
        )


def _require_positive_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) <= 0:
        raise ValueError(f"{name} must be positive")
    return int(value)


def _require_nonnegative_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def _validate_request(request: TwoPoolExactOutRequest) -> None:
    _require_positive_control(request.amount_out_total, name="amount_out_total")
    _require_nonnegative_control(request.window, name="window")
    _require_nonnegative_control(request.brute_force_max, name="brute_force_max")


def _build_context(request: TwoPoolExactOutRequest) -> _TwoPoolExactOutContext:
    p0, p1 = (request.pool0, request.pool1) if request.pool0.pool_id <= request.pool1.pool_id else (request.pool1, request.pool0)
    reserves0 = request.reserves_for(p0)
    reserves1 = request.reserves_for(p1)
    if reserves0 is None or reserves1 is None:
        raise ValueError("pools do not support this direction (or are inactive)")

    reserve_in_0, reserve_out_0 = reserves0
    reserve_in_1, reserve_out_1 = reserves1
    amount_out = int(request.amount_out_total)
    max0 = max(0, int(reserve_out_0) - 1)
    max1 = max(0, int(reserve_out_1) - 1)
    lo = max(0, int(amount_out) - int(max1))
    hi = min(int(amount_out), int(max0))
    if lo > hi:
        raise ValueError("no feasible split for desired amount_out_total")

    return _TwoPoolExactOutContext(
        p0=p0,
        p1=p1,
        amount_out_total=amount_out,
        reserve_in_0=int(reserve_in_0),
        reserve_out_0=int(reserve_out_0),
        reserve_in_1=int(reserve_in_1),
        reserve_out_1=int(reserve_out_1),
        lo=int(lo),
        hi=int(hi),
        quote_exact_out=request.quote_exact_out,
    )


def _best_windowed_split(
    ctx: _TwoPoolExactOutContext,
    *,
    window: int,
) -> tuple[int, int]:
    best_in = 0
    best_key: ExactOutRouteCanonicalKey | None = None
    best_q0 = int(ctx.lo)
    best_found = False
    for center in sorted(ctx.window_centers(int(window))):
        range_lo = max(int(ctx.lo), int(center) - int(window))
        range_hi = min(int(ctx.hi), int(center) + int(window))
        candidate = ctx.scan_range(int(range_lo), int(range_hi))
        if candidate is None:
            continue
        candidate_in, candidate_q0 = candidate
        candidate_key = ctx.route_key_for_split(int(candidate_q0), int(candidate_in))
        if (
            (not best_found)
            or best_key is None
            or candidate_in < best_in
            or (candidate_in == best_in and candidate_key < best_key)
        ):
            best_in, best_q0 = int(candidate_in), int(candidate_q0)
            best_key = candidate_key
            best_found = True

    if not best_found:
        raise ValueError("no feasible split")

    canon_left = max(128, 4 * int(window))
    sweep_lo = max(int(ctx.lo), int(best_q0) - int(canon_left))
    sweep = ctx.scan_range(int(sweep_lo), int(best_q0))
    if sweep is not None:
        sweep_in, sweep_q0 = sweep
        sweep_key = ctx.route_key_for_split(int(sweep_q0), int(sweep_in))
        if best_key is None or sweep_in < best_in or (sweep_in == best_in and sweep_key < best_key):
            best_in, best_q0 = int(sweep_in), int(sweep_q0)
            best_key = sweep_key

    # Certificate hardening: the returned split gets an explicit local replay
    # window, including plateau-edge winners found by the canonical left sweep.
    for _ in range(_LOCAL_CERTIFICATION_MAX_HOPS):
        local_lo = max(int(ctx.lo), int(best_q0) - int(window))
        local_hi = min(int(ctx.hi), int(best_q0) + int(window))
        local = ctx.scan_range(int(local_lo), int(local_hi))
        if local is None:
            break
        local_in, local_q0 = local
        local_key = ctx.route_key_for_split(int(local_q0), int(local_in))
        if best_key is None or local_in < best_in or (local_in == best_in and local_key < best_key):
            if int(local_q0) == int(best_q0) and int(local_in) == int(best_in):
                best_key = local_key
                break
            best_in, best_q0 = int(local_in), int(local_q0)
            best_key = local_key
            continue
        break
    return int(best_in), int(best_q0)


def _best_split(
    ctx: _TwoPoolExactOutContext,
    *,
    window: int,
    brute_force_max: int,
) -> tuple[int, int]:
    if int(ctx.amount_out_total) <= int(brute_force_max) or ctx.span <= int(brute_force_max):
        brute = ctx.scan_range(int(ctx.lo), int(ctx.hi))
        if brute is None:
            raise ValueError("no feasible split")
        return brute
    return _best_windowed_split(ctx, window=int(window))


def best_two_pool_exact_out_split(request: TwoPoolExactOutRequest) -> SplitTwoPoolsQuote:
    _validate_request(request)
    ctx = _build_context(request)
    _best_in, best_q0 = _best_split(
        ctx,
        window=int(request.window),
        brute_force_max=int(request.brute_force_max),
    )
    return ctx.materialize_quote(int(best_q0))
