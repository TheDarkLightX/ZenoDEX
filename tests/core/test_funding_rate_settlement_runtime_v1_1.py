from __future__ import annotations

import pytest

from src.kernels.python.funding_rate_settlement_runtime_v1_1 import (
    compute_funding_rate_settlement,
)


def test_compute_funding_rate_settlement_longs_win_when_realized_meets_implied() -> None:
    result = compute_funding_rate_settlement(
        rate_long_exposure=60_000,
        rate_short_exposure=40_000,
        premium_pool=100_000,
        implied_rate_bps=0,
        funding_cap_bps=100,
        protocol_fee_bps=100,
        mark_price_e8=101_00000000,
        index_price_e8=100_00000000,
    )
    assert result.realized_rate_bps == 100
    assert result.protocol_fee == 1_000
    assert result.distributable_pool == 99_000
    assert result.winning_long is True
    assert result.long_payout == 59_400
    assert result.short_payout == 39_600


def test_compute_funding_rate_settlement_shorts_win_when_realized_below_implied() -> None:
    result = compute_funding_rate_settlement(
        rate_long_exposure=25_000,
        rate_short_exposure=75_000,
        premium_pool=100_000,
        implied_rate_bps=50,
        funding_cap_bps=100,
        protocol_fee_bps=100,
        mark_price_e8=100_00000000,
        index_price_e8=100_00000000,
    )
    assert result.realized_rate_bps == 0
    assert result.winning_long is False
    assert result.long_payout == 74_250
    assert result.short_payout == 24_750


@pytest.mark.parametrize(
    ("field", "value", "exc_type"),
    [
        ("rate_long_exposure", True, TypeError),
        ("rate_short_exposure", -1, ValueError),
        ("premium_pool", 1_000_000_000_001, ValueError),
        ("implied_rate_bps", 10_001, ValueError),
        ("funding_cap_bps", 0, ValueError),
        ("protocol_fee_bps", 10_001, ValueError),
        ("mark_price_e8", 0, ValueError),
        ("index_price_e8", False, TypeError),
    ],
)
def test_compute_funding_rate_settlement_rejects_bad_inputs(
    field: str,
    value: object,
    exc_type: type[Exception],
) -> None:
    kwargs = {
        "rate_long_exposure": 50_000,
        "rate_short_exposure": 50_000,
        "premium_pool": 100_000,
        "implied_rate_bps": 0,
        "funding_cap_bps": 100,
        "protocol_fee_bps": 100,
        "mark_price_e8": 101_00000000,
        "index_price_e8": 100_00000000,
    }
    kwargs[field] = value
    with pytest.raises(exc_type):
        compute_funding_rate_settlement(**kwargs)


def test_compute_funding_rate_settlement_rejects_zero_total_exposure() -> None:
    with pytest.raises(ValueError, match="total exposure"):
        compute_funding_rate_settlement(
            rate_long_exposure=0,
            rate_short_exposure=0,
            premium_pool=0,
            implied_rate_bps=0,
            funding_cap_bps=100,
            protocol_fee_bps=100,
            mark_price_e8=101_00000000,
            index_price_e8=100_00000000,
        )
