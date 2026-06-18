from __future__ import annotations

import pytest

from src.core.cpmm import swap_exact_in
from src.core.cpmm_target_price import (
    CpmmPoolTargetPriceRequest,
    CpmmPoolTargetPriceResult,
    CpmmTargetPriceAction,
    CpmmTargetPriceRequest,
    CpmmTargetPriceResult,
    minimum_exact_in_to_reach_cpmm_pool_price,
    minimum_exact_in_to_reach_cpmm_price_at_most,
)

BPS_DENOM = 10_000


def _price_at_most(
    *,
    reserve_in: int,
    reserve_out: int,
    target_price_num: int,
    target_price_den: int,
) -> bool:
    return reserve_out * target_price_den <= target_price_num * reserve_in


def _price_at_least(
    *,
    reserve_in: int,
    reserve_out: int,
    target_price_num: int,
    target_price_den: int,
) -> bool:
    return reserve_out * target_price_den >= target_price_num * reserve_in


def _ceil_div(numerator: int, denominator: int) -> int:
    return (numerator + denominator - 1) // denominator


def _minimum_gross_for_net_input(*, net_in: int, fee_bps: int) -> int | None:
    if net_in <= 0:
        return 0
    fee_multiplier = BPS_DENOM - fee_bps
    if fee_multiplier <= 0:
        return None
    return _ceil_div(net_in * BPS_DENOM, fee_multiplier)


def _minimum_executable_amount(*, reserve_in: int, reserve_out: int, fee_bps: int) -> int | None:
    if reserve_out <= 1:
        return None
    net_for_positive_output = _ceil_div(reserve_in, reserve_out - 1)
    return _minimum_gross_for_net_input(net_in=net_for_positive_output, fee_bps=fee_bps)


def _brute_force_minimum(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    target_price_num: int,
    target_price_den: int,
    max_amount_in: int,
) -> CpmmTargetPriceResult | None:
    if _price_at_most(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        target_price_num=target_price_num,
        target_price_den=target_price_den,
    ):
        return CpmmTargetPriceResult(
            amount_in=0,
            amount_out=0,
            new_reserves=(reserve_in, reserve_out),
        )
    start = _minimum_executable_amount(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        fee_bps=fee_bps,
    )
    if start is None:
        return None
    for amount_in in range(start, max_amount_in + 1):
        amount_out, new_reserves = swap_exact_in(
            reserve_in,
            reserve_out,
            amount_in,
            fee_bps,
        )
        if _price_at_most(
            reserve_in=new_reserves[0],
            reserve_out=new_reserves[1],
            target_price_num=target_price_num,
            target_price_den=target_price_den,
        ):
            return CpmmTargetPriceResult(
                amount_in=amount_in,
                amount_out=amount_out,
                new_reserves=new_reserves,
            )
    return None


def _brute_force_pool_target(
    *,
    reserve0: int,
    reserve1: int,
    fee_bps: int,
    target_price_num: int,
    target_price_den: int,
    max_amount_in: int,
) -> CpmmPoolTargetPriceResult | None:
    if reserve1 * target_price_den == target_price_num * reserve0:
        return CpmmPoolTargetPriceResult(
            action=CpmmTargetPriceAction.NONE,
            amount_in=0,
            amount_out=0,
            new_reserves=(reserve0, reserve1),
        )

    if reserve1 * target_price_den > target_price_num * reserve0:
        start = _minimum_executable_amount(
            reserve_in=reserve0,
            reserve_out=reserve1,
            fee_bps=fee_bps,
        )
        if start is None:
            return None
        for amount_in in range(start, max_amount_in + 1):
            amount_out, new_reserves = swap_exact_in(
                reserve0,
                reserve1,
                amount_in,
                fee_bps,
            )
            if _price_at_most(
                reserve_in=new_reserves[0],
                reserve_out=new_reserves[1],
                target_price_num=target_price_num,
                target_price_den=target_price_den,
            ):
                return CpmmPoolTargetPriceResult(
                    action=CpmmTargetPriceAction.SELL_ASSET0_FOR_ASSET1,
                    amount_in=amount_in,
                    amount_out=amount_out,
                    new_reserves=new_reserves,
                )
        return None

    start = _minimum_executable_amount(
        reserve_in=reserve1,
        reserve_out=reserve0,
        fee_bps=fee_bps,
    )
    if start is None:
        return None
    for amount_in in range(start, max_amount_in + 1):
        amount_out, reversed_reserves = swap_exact_in(
            reserve1,
            reserve0,
            amount_in,
            fee_bps,
        )
        new_reserve1, new_reserve0 = reversed_reserves
        if _price_at_least(
            reserve_in=new_reserve0,
            reserve_out=new_reserve1,
            target_price_num=target_price_num,
            target_price_den=target_price_den,
        ):
            return CpmmPoolTargetPriceResult(
                action=CpmmTargetPriceAction.SELL_ASSET1_FOR_ASSET0,
                amount_in=amount_in,
                amount_out=amount_out,
                new_reserves=(new_reserve0, new_reserve1),
            )
    return None


@pytest.mark.parametrize(
    "reserve_in,reserve_out,fee_bps,target_num,target_den,max_amount",
    [
        (100, 200, 0, 1, 1, 200),
        (100, 200, 30, 1, 1, 200),
        (250, 500, 100, 3, 2, 300),
        (75, 300, 50, 2, 1, 500),
        (1_000, 1_000, 30, 9, 10, 600),
        (100, 200, 10_000, 1, 1, 200),
    ],
)
def test_target_price_sizing_matches_bruteforce_oracle(
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    target_num: int,
    target_den: int,
    max_amount: int,
) -> None:
    expected = _brute_force_minimum(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        fee_bps=fee_bps,
        target_price_num=target_num,
        target_price_den=target_den,
        max_amount_in=max_amount,
    )

    got = minimum_exact_in_to_reach_cpmm_price_at_most(
        CpmmTargetPriceRequest(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            target_price_num=target_num,
            target_price_den=target_den,
            max_amount_in=max_amount,
        )
    )

    assert got == expected


def test_target_price_sizing_returns_zero_when_current_price_already_within_bound() -> None:
    got = minimum_exact_in_to_reach_cpmm_price_at_most(
        CpmmTargetPriceRequest(
            reserve_in=100,
            reserve_out=150,
            fee_bps=30,
            target_price_num=2,
            target_price_den=1,
            max_amount_in=50,
        )
    )

    assert got == CpmmTargetPriceResult(
        amount_in=0,
        amount_out=0,
        new_reserves=(100, 150),
    )


def test_target_price_sizing_returns_none_when_bound_unreachable_within_amount_cap() -> None:
    got = minimum_exact_in_to_reach_cpmm_price_at_most(
        CpmmTargetPriceRequest(
            reserve_in=100,
            reserve_out=10_000,
            fee_bps=30,
            target_price_num=1,
            target_price_den=1,
            max_amount_in=5,
        )
    )

    assert got is None


def test_target_price_sizing_returns_none_when_no_positive_output_is_possible() -> None:
    got = minimum_exact_in_to_reach_cpmm_price_at_most(
        CpmmTargetPriceRequest(
            reserve_in=100,
            reserve_out=1,
            fee_bps=30,
            target_price_num=1,
            target_price_den=200,
            max_amount_in=500,
        )
    )

    assert got is None


def test_target_price_sizing_is_monotone_in_target_strictness() -> None:
    easier = minimum_exact_in_to_reach_cpmm_price_at_most(
        CpmmTargetPriceRequest(
            reserve_in=100,
            reserve_out=200,
            fee_bps=30,
            target_price_num=3,
            target_price_den=2,
            max_amount_in=200,
        )
    )
    stricter = minimum_exact_in_to_reach_cpmm_price_at_most(
        CpmmTargetPriceRequest(
            reserve_in=100,
            reserve_out=200,
            fee_bps=30,
            target_price_num=1,
            target_price_den=1,
            max_amount_in=200,
        )
    )

    assert easier is not None
    assert stricter is not None
    assert stricter.amount_in >= easier.amount_in


@pytest.mark.parametrize(
    "kwargs",
    [
        {"reserve_in": True},
        {"reserve_out": True},
        {"fee_bps": True},
        {"target_price_num": True},
        {"target_price_den": True},
        {"max_amount_in": True},
    ],
)
def test_target_price_sizing_rejects_bool_numeric_fields(kwargs: dict[str, object]) -> None:
    base: dict[str, object] = {
        "reserve_in": 100,
        "reserve_out": 200,
        "fee_bps": 30,
        "target_price_num": 1,
        "target_price_den": 1,
        "max_amount_in": 200,
    }
    base.update(kwargs)

    with pytest.raises(TypeError):
        minimum_exact_in_to_reach_cpmm_price_at_most(
            CpmmTargetPriceRequest(**base)  # type: ignore[arg-type]
        )


@pytest.mark.parametrize(
    "reserve0,reserve1,fee_bps,target_num,target_den,max_amount",
    [
        (100, 200, 0, 1, 1, 200),
        (100, 200, 30, 1, 1, 200),
        (200, 100, 30, 1, 1, 200),
        (500, 250, 100, 3, 2, 300),
        (75, 300, 50, 2, 1, 500),
        (1_000, 1_000, 30, 1, 1, 600),
        (100, 200, 10_000, 1, 1, 200),
    ],
)
def test_pool_target_price_sizing_matches_bruteforce_oracle(
    reserve0: int,
    reserve1: int,
    fee_bps: int,
    target_num: int,
    target_den: int,
    max_amount: int,
) -> None:
    expected = _brute_force_pool_target(
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        target_price_num=target_num,
        target_price_den=target_den,
        max_amount_in=max_amount,
    )

    got = minimum_exact_in_to_reach_cpmm_pool_price(
        CpmmPoolTargetPriceRequest(
            reserve0=reserve0,
            reserve1=reserve1,
            fee_bps=fee_bps,
            target_price_num=target_num,
            target_price_den=target_den,
            max_amount_in=max_amount,
        )
    )

    assert got == expected


def test_pool_target_price_sizing_returns_none_when_raising_price_unreachable() -> None:
    got = minimum_exact_in_to_reach_cpmm_pool_price(
        CpmmPoolTargetPriceRequest(
            reserve0=10_000,
            reserve1=100,
            fee_bps=30,
            target_price_num=1,
            target_price_den=1,
            max_amount_in=5,
        )
    )

    assert got is None


@pytest.mark.parametrize(
    "kwargs",
    [
        {"reserve0": True},
        {"reserve1": True},
        {"fee_bps": True},
        {"target_price_num": True},
        {"target_price_den": True},
        {"max_amount_in": True},
    ],
)
def test_pool_target_price_sizing_rejects_bool_numeric_fields(kwargs: dict[str, object]) -> None:
    base: dict[str, object] = {
        "reserve0": 100,
        "reserve1": 200,
        "fee_bps": 30,
        "target_price_num": 1,
        "target_price_den": 1,
        "max_amount_in": 200,
    }
    base.update(kwargs)

    with pytest.raises(TypeError):
        minimum_exact_in_to_reach_cpmm_pool_price(
            CpmmPoolTargetPriceRequest(**base)  # type: ignore[arg-type]
        )
