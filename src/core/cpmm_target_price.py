"""Exact integer CPMM target-price sizing helpers.

The continuous arbitrage literature gives closed-form trade sizes for an
idealized constant-product pool. Consensus execution here uses integer amounts,
ceil fee rounding, and floor output rounding, so this module treats the
continuous formula as design guidance and solves the integer refinement exactly.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Tuple

from ..state.balances import Amount
from .cpmm import swap_exact_in
from .domain_limits import DEX_POOL_RESERVE_MAX, DEX_SWAP_AMOUNT_MAX, require_int_range

BPS_DENOM = 10_000


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


class CpmmTargetPriceAction(str, Enum):
    """Trade direction selected to cross a target reserve-ratio price."""

    NONE = "none"
    SELL_ASSET0_FOR_ASSET1 = "sell_asset0_for_asset1"
    SELL_ASSET1_FOR_ASSET0 = "sell_asset1_for_asset0"


@dataclass(frozen=True)
class CpmmPoolTargetPriceRequest:
    """Inputs for moving the canonical pool price reserve1 / reserve0."""

    reserve0: Amount
    reserve1: Amount
    fee_bps: int
    target_price_num: int
    target_price_den: int
    max_amount_in: Amount = DEX_SWAP_AMOUNT_MAX


@dataclass(frozen=True)
class CpmmPoolTargetPriceResult:
    """Minimum trade that crosses a target reserve1 / reserve0 price."""

    action: CpmmTargetPriceAction
    amount_in: Amount
    amount_out: Amount
    new_reserves: Tuple[Amount, Amount]


@dataclass(frozen=True)
class _ValidatedCpmmTargetPriceRequest:
    reserve_in: int
    reserve_out: int
    fee_bps: int
    target_price_num: int
    target_price_den: int
    max_amount_in: int


@dataclass(frozen=True)
class _ValidatedCpmmPoolTargetPriceRequest:
    reserve0: int
    reserve1: int
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


def _price_at_least(
    *,
    reserve_in: int,
    reserve_out: int,
    target_price_num: int,
    target_price_den: int,
) -> bool:
    """Return whether reserve_out / reserve_in >= target_price_num / target_price_den."""
    return reserve_out * target_price_den >= target_price_num * reserve_in


def _price_equal(
    *,
    reserve_in: int,
    reserve_out: int,
    target_price_num: int,
    target_price_den: int,
) -> bool:
    return reserve_out * target_price_den == target_price_num * reserve_in


def _ceil_div(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    if numerator < 0:
        raise ValueError("numerator must be non-negative")
    return (numerator + denominator - 1) // denominator


def _minimum_gross_for_net_input(*, net_in: int, fee_bps: int) -> int | None:
    """Return the least gross input whose fee-rounded net input is at least net_in."""
    if net_in <= 0:
        return 0
    fee_multiplier = BPS_DENOM - fee_bps
    if fee_multiplier <= 0:
        return None
    return _ceil_div(net_in * BPS_DENOM, fee_multiplier)


def _minimum_executable_amount(request: _ValidatedCpmmTargetPriceRequest) -> int | None:
    """Return the least gross input that can produce a positive exact-in output."""
    if request.reserve_out <= 1:
        return None
    net_for_positive_output = _ceil_div(request.reserve_in, request.reserve_out - 1)
    return _minimum_gross_for_net_input(
        net_in=net_for_positive_output,
        fee_bps=request.fee_bps,
    )


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


def _validate_pool_target_price_request(
    request: CpmmPoolTargetPriceRequest,
) -> _ValidatedCpmmPoolTargetPriceRequest:
    checked = _validate_target_price_request(
        CpmmTargetPriceRequest(
            reserve_in=request.reserve0,
            reserve_out=request.reserve1,
            fee_bps=request.fee_bps,
            target_price_num=request.target_price_num,
            target_price_den=request.target_price_den,
            max_amount_in=request.max_amount_in,
        )
    )
    return _ValidatedCpmmPoolTargetPriceRequest(
        reserve0=checked.reserve_in,
        reserve1=checked.reserve_out,
        fee_bps=checked.fee_bps,
        target_price_num=checked.target_price_num,
        target_price_den=checked.target_price_den,
        max_amount_in=checked.max_amount_in,
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


def _binary_search_minimum_amount(
    *,
    request: _ValidatedCpmmTargetPriceRequest,
    low: int,
    high: int,
) -> CpmmTargetPriceResult:
    while low < high:
        mid = (low + high) // 2
        mid_result = _simulate_for_request(request=request, amount_in=mid)
        if _result_reaches_target(mid_result, request):
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

    low = _minimum_executable_amount(checked)
    if low is None:
        return None

    domain_room = DEX_POOL_RESERVE_MAX - checked.reserve_in
    high = min(checked.max_amount_in, domain_room)
    if high < low:
        return None

    high_result = _simulate_for_request(request=checked, amount_in=high)
    if not _result_reaches_target(high_result, checked):
        return None

    return _binary_search_minimum_amount(request=checked, low=low, high=high)


def minimum_exact_in_to_reach_cpmm_pool_price(
    request: CpmmPoolTargetPriceRequest,
) -> CpmmPoolTargetPriceResult | None:
    """Find the minimum trade that crosses a target reserve1/reserve0 price.

    If the current pool price is above the target, the selected trade sells
    asset0 into the pool and buys asset1. If it is below the target, the selected
    trade sells asset1 and buys asset0. The result is exact under the same
    integer CPMM semantics as ``minimum_exact_in_to_reach_cpmm_price_at_most``.
    """
    checked = _validate_pool_target_price_request(request)
    if _price_equal(
        reserve_in=checked.reserve0,
        reserve_out=checked.reserve1,
        target_price_num=checked.target_price_num,
        target_price_den=checked.target_price_den,
    ):
        return CpmmPoolTargetPriceResult(
            action=CpmmTargetPriceAction.NONE,
            amount_in=0,
            amount_out=0,
            new_reserves=(checked.reserve0, checked.reserve1),
        )

    if _price_at_most(
        reserve_in=checked.reserve0,
        reserve_out=checked.reserve1,
        target_price_num=checked.target_price_num,
        target_price_den=checked.target_price_den,
    ):
        return _minimum_asset1_in_to_reach_pool_price_at_least(checked)
    return _minimum_asset0_in_to_reach_pool_price_at_most(checked)


def _minimum_asset0_in_to_reach_pool_price_at_most(
    request: _ValidatedCpmmPoolTargetPriceRequest,
) -> CpmmPoolTargetPriceResult | None:
    result = minimum_exact_in_to_reach_cpmm_price_at_most(
        CpmmTargetPriceRequest(
            reserve_in=request.reserve0,
            reserve_out=request.reserve1,
            fee_bps=request.fee_bps,
            target_price_num=request.target_price_num,
            target_price_den=request.target_price_den,
            max_amount_in=request.max_amount_in,
        )
    )
    if result is None:
        return None
    return CpmmPoolTargetPriceResult(
        action=CpmmTargetPriceAction.SELL_ASSET0_FOR_ASSET1,
        amount_in=result.amount_in,
        amount_out=result.amount_out,
        new_reserves=result.new_reserves,
    )


def _minimum_asset1_in_to_reach_pool_price_at_least(
    request: _ValidatedCpmmPoolTargetPriceRequest,
) -> CpmmPoolTargetPriceResult | None:
    result = minimum_exact_in_to_reach_cpmm_price_at_most(
        CpmmTargetPriceRequest(
            reserve_in=request.reserve1,
            reserve_out=request.reserve0,
            fee_bps=request.fee_bps,
            target_price_num=request.target_price_den,
            target_price_den=request.target_price_num,
            max_amount_in=request.max_amount_in,
        )
    )
    if result is None:
        return None
    new_reserve1, new_reserve0 = result.new_reserves
    return CpmmPoolTargetPriceResult(
        action=CpmmTargetPriceAction.SELL_ASSET1_FOR_ASSET0,
        amount_in=result.amount_in,
        amount_out=result.amount_out,
        new_reserves=(new_reserve0, new_reserve1),
    )
