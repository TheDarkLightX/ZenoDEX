"""Mixed direct-vs-two-hop exact-in split routing helper."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Optional, Tuple

from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from .routing_types import RouteHop, RouteLeg, RouteQuote

_QuoteExactIn = Callable[..., Optional[Tuple[Amount, str]]]
_ReservesDirection = Callable[..., Optional[Tuple[int, int, int]]]


@dataclass(frozen=True)
class MixedSplitExactInRequest:
    direct_pool: PoolState
    hop1_pool: PoolState
    hop2_pool: PoolState
    asset_in: AssetId
    mid: AssetId
    asset_out: AssetId
    quote_exact_in: _QuoteExactIn
    reserves_direction: _ReservesDirection


@dataclass(frozen=True)
class _SplitQuoteParts:
    direct_amount_in: int
    twohop_amount_in: int
    direct_output: int
    mid_amount: int
    twohop_output: int

    @property
    def total_output(self) -> int:
        return int(self.direct_output + self.twohop_output)


@dataclass(frozen=True)
class _MixedSplitContext:
    request: MixedSplitExactInRequest

    def directions_supported(self) -> bool:
        request = self.request
        return (
            request.reserves_direction(request.direct_pool, asset_in=request.asset_in, asset_out=request.asset_out)
            is not None
            and request.reserves_direction(request.hop1_pool, asset_in=request.asset_in, asset_out=request.mid)
            is not None
            and request.reserves_direction(request.hop2_pool, asset_in=request.mid, asset_out=request.asset_out)
            is not None
        )

    def total_out(self, *, direct_amount_in: int, total_input: int) -> int | None:
        if not (0 <= direct_amount_in <= total_input):
            return None
        twohop_amount_in = total_input - int(direct_amount_in)
        if direct_amount_in == 0 or twohop_amount_in == 0:
            return None
        split_quote = self._quote_split(
            direct_amount_in=int(direct_amount_in),
            twohop_amount_in=int(twohop_amount_in),
        )
        if split_quote is None:
            return None
        return split_quote.total_output

    def build_quote(
        self,
        *,
        total_input: int,
        best_direct_amount: int,
        best_out: int,
    ) -> Optional[RouteQuote]:
        twohop_amount_in = int(total_input) - int(best_direct_amount)
        split_quote = self._quote_split(
            direct_amount_in=int(best_direct_amount),
            twohop_amount_in=int(twohop_amount_in),
        )
        if split_quote is None:
            return None
        legs = self._build_legs(split_quote)
        request = self.request
        return RouteQuote(
            asset_in=request.asset_in,
            asset_out=request.asset_out,
            amount_in=int(total_input),
            amount_out=int(best_out),
            legs=legs,
        )

    def _quote_split(
        self,
        *,
        direct_amount_in: int,
        twohop_amount_in: int,
    ) -> _SplitQuoteParts | None:
        request = self.request
        direct_quote = request.quote_exact_in(
            request.direct_pool,
            asset_in=request.asset_in,
            asset_out=request.asset_out,
            amount_in=int(direct_amount_in),
        )
        if direct_quote is None:
            return None
        hop1_quote = request.quote_exact_in(
            request.hop1_pool,
            asset_in=request.asset_in,
            asset_out=request.mid,
            amount_in=int(twohop_amount_in),
        )
        if hop1_quote is None:
            return None
        direct_output, _pool_id = direct_quote
        mid_amount, _pool_id = hop1_quote
        hop2_quote = request.quote_exact_in(
            request.hop2_pool,
            asset_in=request.mid,
            asset_out=request.asset_out,
            amount_in=int(mid_amount),
        )
        if hop2_quote is None:
            return None
        twohop_output, _pool_id = hop2_quote
        return _SplitQuoteParts(
            direct_amount_in=int(direct_amount_in),
            twohop_amount_in=int(twohop_amount_in),
            direct_output=int(direct_output),
            mid_amount=int(mid_amount),
            twohop_output=int(twohop_output),
        )

    def _build_legs(self, quote: _SplitQuoteParts) -> tuple[RouteLeg, RouteLeg]:
        request = self.request
        direct_hop = RouteHop(
            request.direct_pool.pool_id,
            request.asset_in,
            request.asset_out,
            int(quote.direct_amount_in),
            int(quote.direct_output),
        )
        hop1 = RouteHop(
            request.hop1_pool.pool_id,
            request.asset_in,
            request.mid,
            int(quote.twohop_amount_in),
            int(quote.mid_amount),
        )
        hop2 = RouteHop(
            request.hop2_pool.pool_id,
            request.mid,
            request.asset_out,
            int(quote.mid_amount),
            int(quote.twohop_output),
        )
        direct_leg = RouteLeg(
            hops=(direct_hop,),
            amount_in=int(quote.direct_amount_in),
            amount_out=int(quote.direct_output),
        )
        twohop_leg = RouteLeg(
            hops=(hop1, hop2),
            amount_in=int(quote.twohop_amount_in),
            amount_out=int(quote.twohop_output),
        )
        legs = [direct_leg, twohop_leg]
        legs.sort(key=lambda leg: ",".join(hop.pool_id for hop in leg.hops))
        return legs[0], legs[1]


def best_split_direct_vs_twohop_exact_in_for_request(
    *,
    request: MixedSplitExactInRequest,
    amount_in_total: Amount,
    window: int = 64,
    brute_force_max: int = 512,
) -> Optional[RouteQuote]:
    """
    Best split of exact-in input across direct and two-hop legs.

    This keeps the search integer-only and deterministic. Degenerate pure-direct
    or pure-two-hop allocations are rejected here because the top-level router
    evaluates those candidates separately.
    """
    total_input = int(amount_in_total)
    if total_input <= 1:
        return None
    if window < 0 or brute_force_max < 0:
        raise ValueError("window/brute_force_max must be non-negative")
    context = _MixedSplitContext(request=request)
    if not context.directions_supported():
        return None

    best = _best_split_amount(
        total_input=total_input,
        total_out=lambda direct_amount_in: context.total_out(
            direct_amount_in=direct_amount_in,
            total_input=total_input,
        ),
        window=window,
        brute_force_max=brute_force_max,
    )
    if best is None:
        return None
    best_out, best_direct_amount = best
    return context.build_quote(
        total_input=total_input,
        best_direct_amount=best_direct_amount,
        best_out=best_out,
    )


def _scan_split_range(
    *,
    low: int,
    high: int,
    total_out: Callable[[int], int | None],
) -> tuple[int, int] | None:
    if low > high:
        return None
    best_out: int | None = None
    best_direct_amount = int(low)
    for direct_amount in range(int(low), int(high) + 1):
        candidate_out = total_out(int(direct_amount))
        if candidate_out is None:
            continue
        if best_out is None or int(candidate_out) > int(best_out) or (
            int(candidate_out) == int(best_out) and int(direct_amount) < int(best_direct_amount)
        ):
            best_out = int(candidate_out)
            best_direct_amount = int(direct_amount)
    if best_out is None:
        return None
    return int(best_out), int(best_direct_amount)


def _best_split_amount(
    *,
    total_input: int,
    total_out: Callable[[int], int | None],
    window: int,
    brute_force_max: int,
) -> tuple[int, int] | None:
    if total_input <= int(brute_force_max):
        return _scan_split_range(low=1, high=total_input - 1, total_out=total_out)
    best = _scan_coarse_windows(
        total_input=total_input,
        total_out=total_out,
        window=window,
    )
    if best is None:
        return None
    best_out, best_direct_amount = best
    return best_out, _leftmost_equal_output(
        candidate=best_direct_amount,
        low=1,
        best_out=best_out,
        total_out=total_out,
    )


def _scan_coarse_windows(
    *,
    total_input: int,
    total_out: Callable[[int], int | None],
    window: int,
) -> tuple[int, int] | None:
    low = 1
    high = int(total_input) - 1
    span = high - low
    centers = {low, high, (low + high) // 2}
    if span > 0:
        for i in range(1, 16):
            centers.add(low + (span * int(i)) // 16)

    best_out = 0
    best_direct_amount = 1
    best_found = False
    for center in sorted(centers):
        candidate = _scan_split_range(
            low=max(1, int(center) - int(window)),
            high=min(int(total_input) - 1, int(center) + int(window)),
            total_out=total_out,
        )
        if candidate is None:
            continue
        candidate_out, candidate_direct_amount = candidate
        if (not best_found) or candidate_out > best_out or (
            candidate_out == best_out and candidate_direct_amount < best_direct_amount
        ):
            best_out = int(candidate_out)
            best_direct_amount = int(candidate_direct_amount)
            best_found = True
    if not best_found:
        return None
    return best_out, best_direct_amount


def _leftmost_equal_output(
    *,
    candidate: int,
    low: int,
    best_out: int,
    total_out: Callable[[int], int | None],
) -> int:
    direct_amount = int(candidate)
    while direct_amount > int(low):
        previous = total_out(int(direct_amount) - 1)
        if previous is None or int(previous) != int(best_out):
            break
        direct_amount -= 1
    return int(direct_amount)
