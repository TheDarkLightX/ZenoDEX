"""Mixed direct-vs-two-hop exact-in split routing helper."""

from __future__ import annotations

from typing import Callable, Optional, Tuple

from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from .routing_types import RouteHop, RouteLeg, RouteQuote


def best_split_direct_vs_twohop_exact_in(
    *,
    direct_pool: PoolState,
    hop1_pool: PoolState,
    hop2_pool: PoolState,
    asset_in: AssetId,
    mid: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
    quote_exact_in: Callable[..., Optional[Tuple[Amount, str]]],
    reserves_direction: Callable[..., Optional[Tuple[int, int, int]]],
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
    if not _directions_supported(
        direct_pool=direct_pool,
        hop1_pool=hop1_pool,
        hop2_pool=hop2_pool,
        asset_in=asset_in,
        mid=mid,
        asset_out=asset_out,
        reserves_direction=reserves_direction,
    ):
        return None

    def total_out(direct_amount_in: int) -> int | None:
        return _total_split_output(
            direct_amount_in=direct_amount_in,
            total_input=total_input,
            direct_pool=direct_pool,
            hop1_pool=hop1_pool,
            hop2_pool=hop2_pool,
            asset_in=asset_in,
            mid=mid,
            asset_out=asset_out,
            quote_exact_in=quote_exact_in,
        )

    best = _best_split_amount(
        total_input=total_input,
        total_out=total_out,
        window=window,
        brute_force_max=brute_force_max,
    )
    if best is None:
        return None
    best_out, best_direct_amount = best
    return _build_route_quote(
        total_input=total_input,
        best_direct_amount=best_direct_amount,
        best_out=best_out,
        direct_pool=direct_pool,
        hop1_pool=hop1_pool,
        hop2_pool=hop2_pool,
        asset_in=asset_in,
        mid=mid,
        asset_out=asset_out,
        quote_exact_in=quote_exact_in,
    )


def _directions_supported(
    *,
    direct_pool: PoolState,
    hop1_pool: PoolState,
    hop2_pool: PoolState,
    asset_in: AssetId,
    mid: AssetId,
    asset_out: AssetId,
    reserves_direction: Callable[..., Optional[Tuple[int, int, int]]],
) -> bool:
    return (
        reserves_direction(direct_pool, asset_in=asset_in, asset_out=asset_out) is not None
        and reserves_direction(hop1_pool, asset_in=asset_in, asset_out=mid) is not None
        and reserves_direction(hop2_pool, asset_in=mid, asset_out=asset_out) is not None
    )


def _total_split_output(
    *,
    direct_amount_in: int,
    total_input: int,
    direct_pool: PoolState,
    hop1_pool: PoolState,
    hop2_pool: PoolState,
    asset_in: AssetId,
    mid: AssetId,
    asset_out: AssetId,
    quote_exact_in: Callable[..., Optional[Tuple[Amount, str]]],
) -> int | None:
    if not (0 <= direct_amount_in <= total_input):
        return None
    twohop_amount_in = total_input - int(direct_amount_in)
    if direct_amount_in == 0 or twohop_amount_in == 0:
        return None
    direct_quote = quote_exact_in(
        direct_pool,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=int(direct_amount_in),
    )
    if direct_quote is None:
        return None
    hop1_quote = quote_exact_in(
        hop1_pool,
        asset_in=asset_in,
        asset_out=mid,
        amount_in=int(twohop_amount_in),
    )
    if hop1_quote is None:
        return None
    mid_amount, _pool_id = hop1_quote
    hop2_quote = quote_exact_in(
        hop2_pool,
        asset_in=mid,
        asset_out=asset_out,
        amount_in=int(mid_amount),
    )
    if hop2_quote is None:
        return None
    twohop_output, _pool_id = hop2_quote
    return int(direct_quote[0] + twohop_output)


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


def _build_route_quote(
    *,
    total_input: int,
    best_direct_amount: int,
    best_out: int,
    direct_pool: PoolState,
    hop1_pool: PoolState,
    hop2_pool: PoolState,
    asset_in: AssetId,
    mid: AssetId,
    asset_out: AssetId,
    quote_exact_in: Callable[..., Optional[Tuple[Amount, str]]],
) -> Optional[RouteQuote]:
    twohop_amount_in = int(total_input) - int(best_direct_amount)
    direct_quote = quote_exact_in(
        direct_pool,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=int(best_direct_amount),
    )
    hop1_quote = quote_exact_in(
        hop1_pool,
        asset_in=asset_in,
        asset_out=mid,
        amount_in=int(twohop_amount_in),
    )
    if direct_quote is None or hop1_quote is None:
        return None
    direct_output, _pool_id = direct_quote
    mid_amount, _pool_id = hop1_quote
    hop2_quote = quote_exact_in(
        hop2_pool,
        asset_in=mid,
        asset_out=asset_out,
        amount_in=int(mid_amount),
    )
    if hop2_quote is None:
        return None
    twohop_output, _pool_id = hop2_quote

    direct_hop = RouteHop(
        direct_pool.pool_id,
        asset_in,
        asset_out,
        int(best_direct_amount),
        int(direct_output),
    )
    hop1 = RouteHop(hop1_pool.pool_id, asset_in, mid, int(twohop_amount_in), int(mid_amount))
    hop2 = RouteHop(hop2_pool.pool_id, mid, asset_out, int(mid_amount), int(twohop_output))
    direct_leg = RouteLeg(
        hops=(direct_hop,),
        amount_in=int(best_direct_amount),
        amount_out=int(direct_output),
    )
    twohop_leg = RouteLeg(
        hops=(hop1, hop2),
        amount_in=int(twohop_amount_in),
        amount_out=int(twohop_output),
    )

    legs = [direct_leg, twohop_leg]
    legs.sort(key=lambda leg: ",".join(hop.pool_id for hop in leg.hops))
    return RouteQuote(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=int(total_input),
        amount_out=int(best_out),
        legs=tuple(legs),
    )
