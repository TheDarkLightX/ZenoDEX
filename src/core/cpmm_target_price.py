"""Exact integer CPMM target-price sizing helpers.

The continuous arbitrage literature gives closed-form trade sizes for an
idealized constant-product pool. Consensus execution here uses integer amounts,
ceil fee rounding, and floor output rounding, so this module treats the
continuous formula as design guidance and solves the integer refinement exactly.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple

from ..state.balances import Amount
from .cpmm import swap_exact_in
from .domain_limits import DEX_POOL_RESERVE_MAX, DEX_SWAP_AMOUNT_MAX, require_int_range


@dataclass(frozen=True)
class CpmmTargetPriceResult:
    """Minimum exact-in trade that satisfies a reserve-ratio price bound."""

    amount_in: Amount
    amount_out: Amount
    new_reserves: Tuple[Amount, Amount]


@dataclass(frozen=True)
class CpmmTargetPriceRequest:
    """Inputs for exact integer target-price sizing."""

    reserve_in: Amount
    reserve_out: Amount
    fee_bps: int
    target_price_num: int
    target_price_den: int
    max_amount_in: Amount = DEX_SWAP_AMOUNT_MAX


@dataclass(frozen=True)
class _ValidatedCpmmTargetPriceRequest:
    reserve_in: int
    reserve_out: int
    fee_bps: int
    target_price_num: int
    target_price_den: int
    max_amount_in: int


def _price_at_most(
    *,
    reserve_in: int,
    reserve_out: int,
    target_price_num: int,
    target_price_den: int,
) -> bool:
    """Return whether reserve_out / reserve_in <= target_price_num / target_price_den."""
    return reserve_out * target_price_den <= target_price_num * reserve_in


def _validate_target_price_request(request: CpmmTargetPriceRequest) -> _ValidatedCpmmTargetPriceRequest:
    return _ValidatedCpmmTargetPriceRequest(
        reserve_in=require_int_range(
            "reserve_in",
            request.reserve_in,
            minimum=1,
            maximum=DEX_POOL_RESERVE_MAX,
        ),
        reserve_out=require_int_range(
            "reserve_out",
            request.reserve_out,
            minimum=1,
            maximum=DEX_POOL_RESERVE_MAX,
        ),
        fee_bps=require_int_range("fee_bps", request.fee_bps, minimum=0, maximum=10_000),
        target_price_num=require_int_range(
            "target_price_num",
            request.target_price_num,
            minimum=1,
            maximum=DEX_POOL_RESERVE_MAX,
        ),
        target_price_den=require_int_range(
            "target_price_den",
            request.target_price_den,
            minimum=1,
            maximum=DEX_POOL_RESERVE_MAX,
        ),
        max_amount_in=require_int_range(
            "max_amount_in",
            request.max_amount_in,
            minimum=0,
            maximum=DEX_SWAP_AMOUNT_MAX,
        ),
    )


def _simulate_exact_in(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
) -> CpmmTargetPriceResult:
    if amount_in == 0:
        return CpmmTargetPriceResult(
            amount_in=0,
            amount_out=0,
            new_reserves=(reserve_in, reserve_out),
        )
    amount_out, new_reserves = swap_exact_in(reserve_in, reserve_out, amount_in, fee_bps)
    return CpmmTargetPriceResult(
        amount_in=amount_in,
        amount_out=amount_out,
        new_reserves=new_reserves,
    )


def _result_reaches_target(
    result: CpmmTargetPriceResult,
    request: _ValidatedCpmmTargetPriceRequest,
) -> bool:
    return _price_at_most(
        reserve_in=result.new_reserves[0],
        reserve_out=result.new_reserves[1],
        target_price_num=request.target_price_num,
        target_price_den=request.target_price_den,
    )


def _simulate_for_request(
    *,
    request: _ValidatedCpmmTargetPriceRequest,
    amount_in: int,
) -> CpmmTargetPriceResult:
    return _simulate_exact_in(
        reserve_in=request.reserve_in,
        reserve_out=request.reserve_out,
        amount_in=amount_in,
        fee_bps=request.fee_bps,
    )


def _try_simulate_for_request(
    *,
    request: _ValidatedCpmmTargetPriceRequest,
    amount_in: int,
) -> CpmmTargetPriceResult | None:
    try:
        return _simulate_for_request(request=request, amount_in=amount_in)
    except ValueError as exc:
        if str(exc) not in {
            "net_in must be positive after fees",
            "amount_out is zero (trade too small)",
        }:
            raise
        return None


def _binary_search_minimum_amount(
    *,
    request: _ValidatedCpmmTargetPriceRequest,
    high: int,
) -> CpmmTargetPriceResult:
    low = 1
    while low < high:
        mid = (low + high) // 2
        mid_result = _try_simulate_for_request(request=request, amount_in=mid)
        if mid_result is not None and _result_reaches_target(mid_result, request):
            high = mid
        else:
            low = mid + 1
    result = _simulate_for_request(request=request, amount_in=low)
    if not _result_reaches_target(result, request):
        raise RuntimeError("target-price binary search returned a non-satisfying amount")
    return result


def minimum_exact_in_to_reach_cpmm_price_at_most(
    request: CpmmTargetPriceRequest,
) -> CpmmTargetPriceResult | None:
    """Find the minimum exact-in trade that reaches a CPMM price ceiling.

    The price predicate is:

    ``new_reserve_out / new_reserve_in <= target_price_num / target_price_den``.

    The search is exact under ZenoDEX integer swap semantics, including ceil fee
    rounding and floor output rounding. It runs in ``O(log max_amount_in)`` swap
    simulations by exploiting monotonicity of the post-trade reserve ratio as
    exact-in input increases. Returning ``None`` means the bound is unreachable
    within both ``max_amount_in`` and the reserve-domain cap.
    """
    checked = _validate_target_price_request(request)
    if _price_at_most(
        reserve_in=checked.reserve_in,
        reserve_out=checked.reserve_out,
        target_price_num=checked.target_price_num,
        target_price_den=checked.target_price_den,
    ):
        return _simulate_for_request(request=checked, amount_in=0)

    domain_room = DEX_POOL_RESERVE_MAX - checked.reserve_in
    high = min(checked.max_amount_in, domain_room)
    if high <= 0:
        return None

    high_result = _try_simulate_for_request(request=checked, amount_in=high)
    if high_result is None or not _result_reaches_target(high_result, checked):
        return None

    return _binary_search_minimum_amount(request=checked, high=high)
