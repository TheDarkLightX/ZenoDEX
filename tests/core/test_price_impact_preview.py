from __future__ import annotations

import random

import pytest

from src.core.price_impact_preview import (
    BPS_SCALE,
    compute_isolated_output,
    compute_price_impact_bps,
    compute_spot_price_e8,
    price_impact_preview,
)


def test_compute_isolated_output_matches_manual_example() -> None:
    reserve_in, reserve_out = 1_000_000, 1_000_000
    amount_in = 10_000
    fee_bps = 30
    amount_out, fee = compute_isolated_output(reserve_in, reserve_out, amount_in, fee_bps)
    assert fee == 30
    assert amount_out == reserve_out * (amount_in - fee) // (reserve_in + (amount_in - fee))


def test_preview_bounds_are_ordered() -> None:
    preview = price_impact_preview(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
        pending_volume_same_direction=50_000,
    )
    assert preview.amount_out_best_case >= preview.amount_out_worst_case
    assert preview.amount_out_best_case == preview.amount_out_isolated
    assert preview.amount_out_worst_case <= preview.amount_out_isolated


def test_preview_no_pending_collapses_to_isolated() -> None:
    preview = price_impact_preview(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
        pending_volume_same_direction=0,
    )
    assert preview.amount_out_best_case == preview.amount_out_isolated
    assert preview.amount_out_worst_case == preview.amount_out_isolated


def test_recommended_min_out_within_bounds() -> None:
    rng = random.Random(42)
    for _ in range(1000):
        reserve_in = rng.randint(10_000, 10_000_000)
        reserve_out = rng.randint(10_000, 10_000_000)
        amount_in = rng.randint(1, reserve_in // 2)
        pending_volume = rng.randint(0, reserve_in)
        fee_bps = rng.randint(0, 300)
        confidence_bps = rng.randint(0, BPS_SCALE)
        preview = price_impact_preview(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            fee_bps=fee_bps,
            pending_volume_same_direction=pending_volume,
            confidence_bps=confidence_bps,
        )
        assert 0 <= preview.recommended_min_out <= preview.amount_out_best_case
        assert preview.recommended_min_out >= preview.amount_out_worst_case


def test_confidence_endpoints_match_bounds() -> None:
    args = dict(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=25_000,
        fee_bps=30,
        pending_volume_same_direction=40_000,
    )
    low = price_impact_preview(**args, confidence_bps=0)
    high = price_impact_preview(**args, confidence_bps=BPS_SCALE)
    assert low.recommended_min_out == low.amount_out_best_case
    assert high.recommended_min_out == high.amount_out_worst_case


def test_worst_case_non_increasing_with_pending_volume() -> None:
    rng = random.Random(7)
    for _ in range(300):
        reserve_in = rng.randint(20_000, 2_000_000)
        reserve_out = rng.randint(20_000, 2_000_000)
        amount_in = rng.randint(1, max(1, reserve_in // 5))
        fee_bps = rng.randint(0, 100)
        checkpoints = sorted({0, 1, 10, 100, 1_000, 10_000, 100_000, reserve_in // 2, reserve_in})
        previous = None
        for pending_volume in checkpoints:
            preview = price_impact_preview(
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_in=amount_in,
                fee_bps=fee_bps,
                pending_volume_same_direction=pending_volume,
            )
            if previous is not None:
                assert preview.amount_out_worst_case <= previous
            previous = preview.amount_out_worst_case


def test_price_impact_non_decreasing_in_trade_size() -> None:
    reserve_in, reserve_out, fee_bps = 1_000_000, 1_000_000, 30
    previous = 0
    for amount_in in [1_000, 5_000, 10_000, 100_000, 500_000]:
        impact = compute_price_impact_bps(reserve_in, reserve_out, amount_in, fee_bps)
        assert impact >= previous
        previous = impact


def test_spot_price_is_ratio_e8() -> None:
    assert compute_spot_price_e8(1_000_000, 2_000_000) == 200_000_000


def test_confidence_adjusted_min_out_is_not_linear_interp() -> None:
    preview = price_impact_preview(
        reserve_in=100_000,
        reserve_out=100_000,
        amount_in=5_000,
        fee_bps=30,
        pending_volume_same_direction=80_000,
        confidence_bps=9_500,
    )

    linear = (
        preview.amount_out_worst_case
        + (preview.amount_out_best_case - preview.amount_out_worst_case) * (BPS_SCALE - 9_500) // BPS_SCALE
    )
    assert preview.recommended_min_out == preview.amount_out_at_confidence
    assert preview.recommended_min_out <= linear


@pytest.mark.parametrize(
    ("reserve_in", "reserve_out", "should_raise", "expected"),
    [
        (-1, 1, True, None),
        (0, 1, True, None),
        (1, 0, True, None),
        (1, 1, False, 100_000_000),
        (1, 2, False, 200_000_000),
    ],
)
def test_compute_spot_price_e8_bva(
    reserve_in: int,
    reserve_out: int,
    should_raise: bool,
    expected: int | None,
) -> None:
    if should_raise:
        with pytest.raises(ValueError):
            compute_spot_price_e8(reserve_in, reserve_out)
        return
    assert compute_spot_price_e8(reserve_in, reserve_out) == expected


@pytest.mark.parametrize(
    ("amount_in", "fee_bps", "should_raise", "expected_out", "expected_fee"),
    [
        (-1, 0, True, None, None),
        (0, 0, True, None, None),
        (1, 0, False, 0, 0),
        (1, 10_000, False, 0, 1),
        (1, -1, True, None, None),
        (1, 10_001, True, None, None),
        (1, 1, False, 0, 1),
    ],
)
def test_compute_isolated_output_bva_amount_in_and_fee(
    amount_in: int,
    fee_bps: int,
    should_raise: bool,
    expected_out: int | None,
    expected_fee: int | None,
) -> None:
    if should_raise:
        with pytest.raises(ValueError):
            compute_isolated_output(1_000_000, 1_000_000, amount_in, fee_bps)
        return
    amount_out, fee = compute_isolated_output(1_000_000, 1_000_000, amount_in, fee_bps)
    assert amount_out == expected_out
    assert fee == expected_fee


@pytest.mark.parametrize(
    ("pending_volume", "confidence_bps", "should_raise"),
    [
        (-1, 9500, True),
        (0, 9500, False),
        (1, 9500, False),
        (10, -1, True),
        (10, 0, False),
        (10, 1, False),
        (10, 9999, False),
        (10, 10_000, False),
        (10, 10_001, True),
    ],
)
def test_price_impact_preview_bva_pending_and_confidence_validation(
    pending_volume: int,
    confidence_bps: int,
    should_raise: bool,
) -> None:
    kwargs = dict(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
        pending_volume_same_direction=pending_volume,
        confidence_bps=confidence_bps,
    )
    if should_raise:
        with pytest.raises(ValueError):
            price_impact_preview(**kwargs)
        return
    preview = price_impact_preview(**kwargs)
    assert 0 <= preview.confidence_bps <= 10_000
    assert preview.pending_volume_same_direction == pending_volume
