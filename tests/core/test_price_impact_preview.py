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
    ri, ro = 1_000_000, 1_000_000
    ai = 10_000
    fee_bps = 30
    ao, fee = compute_isolated_output(ri, ro, ai, fee_bps)
    assert fee == 30
    assert ao == (ro * (ai - fee) // (ri + (ai - fee)))


def test_preview_bounds_are_ordered() -> None:
    p = price_impact_preview(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
        pending_volume_same_direction=50_000,
    )
    assert p.amount_out_best_case >= p.amount_out_worst_case
    assert p.amount_out_best_case == p.amount_out_isolated
    assert p.amount_out_worst_case <= p.amount_out_isolated


def test_preview_no_pending_collapses_to_isolated() -> None:
    p = price_impact_preview(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
        pending_volume_same_direction=0,
    )
    assert p.amount_out_best_case == p.amount_out_isolated
    assert p.amount_out_worst_case == p.amount_out_isolated


def test_recommended_min_out_within_bounds() -> None:
    rng = random.Random(42)
    for _ in range(1000):
        ri = rng.randint(10_000, 10_000_000)
        ro = rng.randint(10_000, 10_000_000)
        ai = rng.randint(1, ri // 2)
        pending = rng.randint(0, ri)
        fee_bps = rng.randint(0, 300)
        conf = rng.randint(0, BPS_SCALE)
        p = price_impact_preview(
            reserve_in=ri,
            reserve_out=ro,
            amount_in=ai,
            fee_bps=fee_bps,
            pending_volume_same_direction=pending,
            confidence_bps=conf,
        )
        assert 0 <= p.recommended_min_out <= p.amount_out_best_case
        assert p.recommended_min_out >= p.amount_out_worst_case


def test_confidence_endpoints_match_bounds() -> None:
    args = dict(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=25_000,
        fee_bps=30,
        pending_volume_same_direction=40_000,
    )
    p_low = price_impact_preview(**args, confidence_bps=0)
    p_high = price_impact_preview(**args, confidence_bps=BPS_SCALE)
    assert p_low.recommended_min_out == p_low.amount_out_best_case
    assert p_high.recommended_min_out == p_high.amount_out_worst_case


def test_worst_case_non_increasing_with_pending_volume() -> None:
    rng = random.Random(7)
    for _ in range(300):
        ri = rng.randint(20_000, 2_000_000)
        ro = rng.randint(20_000, 2_000_000)
        ai = rng.randint(1, max(1, ri // 5))
        fee_bps = rng.randint(0, 100)
        checkpoints = sorted(set([0, 1, 10, 100, 1_000, 10_000, 100_000, ri // 2, ri]))
        prev = None
        for pending in checkpoints:
            p = price_impact_preview(
                reserve_in=ri,
                reserve_out=ro,
                amount_in=ai,
                fee_bps=fee_bps,
                pending_volume_same_direction=pending,
            )
            if prev is not None:
                assert p.amount_out_worst_case <= prev
            prev = p.amount_out_worst_case


def test_price_impact_non_decreasing_in_trade_size() -> None:
    ri, ro, fee_bps = 1_000_000, 1_000_000, 30
    prev = 0
    for ai in [1_000, 5_000, 10_000, 100_000, 500_000]:
        impact = compute_price_impact_bps(ri, ro, ai, fee_bps)
        assert impact >= prev
        prev = impact


def test_spot_price_is_ratio_e8() -> None:
    assert compute_spot_price_e8(1_000_000, 2_000_000) == 200_000_000


def test_confidence_adjusted_min_out_is_not_linear_interp() -> None:
    """Regression: linear interpolation can be too optimistic and cause reverts.

    We compute `recommended_min_out` by simulating pending volume at the
    confidence-adjusted level, not by interpolating between (best,worst).
    """
    ri, ro, ai, fee_bps = 100_000, 100_000, 5_000, 30
    pending = 80_000
    conf = 9_500

    p = price_impact_preview(
        reserve_in=ri,
        reserve_out=ro,
        amount_in=ai,
        fee_bps=fee_bps,
        pending_volume_same_direction=pending,
        confidence_bps=conf,
    )

    # Old (too optimistic) linear interpolation.
    safety_margin = BPS_SCALE - conf
    linear = p.amount_out_worst_case + (p.amount_out_best_case - p.amount_out_worst_case) * safety_margin // BPS_SCALE
    assert p.recommended_min_out == p.amount_out_at_confidence
    assert p.recommended_min_out <= linear


@pytest.mark.parametrize(
    "reserve_in,reserve_out,should_raise,expected,reason",
    [
        (-1, 1, True, None, "reserve_in just-below valid range (negative)"),
        (0, 1, True, None, "reserve_in exactly at invalid boundary (0)"),
        (1, 0, True, None, "reserve_out exactly at invalid boundary (0)"),
        (1, 1, False, 100_000_000, "both reserves at smallest valid positive values"),
        (1, 2, False, 200_000_000, "ratio boundary sanity"),
    ],
    ids=lambda x: str(x),
)
def test_compute_spot_price_e8_bva(
    reserve_in: int,
    reserve_out: int,
    should_raise: bool,
    expected: int | None,
    reason: str,
) -> None:
    _ = reason
    if should_raise:
        with pytest.raises(ValueError):
            compute_spot_price_e8(int(reserve_in), int(reserve_out))
        return
    out = compute_spot_price_e8(int(reserve_in), int(reserve_out))
    assert out == int(expected)


@pytest.mark.parametrize(
    "amount_in,fee_bps,should_raise,expected_out,expected_fee,reason",
    [
        (-1, 0, True, None, None, "amount_in just-below min (invalid)"),
        (0, 0, True, None, None, "amount_in exactly at min boundary (invalid)"),
        (1, 0, False, 0, 0, "amount_in just-above min; output can be 0 under floor (valid)"),
        (1, 10_000, False, 0, 1, "fee_bps exactly at max: net_in=0 => output=0"),
        (1, -1, True, None, None, "fee_bps just-below min (invalid)"),
        (1, 10_001, True, None, None, "fee_bps just-above max (invalid)"),
        (1, 1, False, 0, 1, "fee_bps just-above 0 with ceil fee can consume amount_in"),
    ],
    ids=lambda x: str(x),
)
def test_compute_isolated_output_bva_amount_in_and_fee(
    amount_in: int,
    fee_bps: int,
    should_raise: bool,
    expected_out: int | None,
    expected_fee: int | None,
    reason: str,
) -> None:
    _ = reason
    if should_raise:
        with pytest.raises(ValueError):
            compute_isolated_output(1_000_000, 1_000_000, int(amount_in), int(fee_bps))
        return
    out, fee = compute_isolated_output(1_000_000, 1_000_000, int(amount_in), int(fee_bps))
    assert out == int(expected_out)
    assert fee == int(expected_fee)


@pytest.mark.parametrize(
    "pending,confidence_bps,should_raise,reason",
    [
        (-1, 9500, True, "pending just-below 0 (invalid)"),
        (0, 9500, False, "pending exactly at 0"),
        (1, 9500, False, "pending just-above 0"),
        (10, -1, True, "confidence just-below 0 (invalid)"),
        (10, 0, False, "confidence exactly at 0"),
        (10, 1, False, "confidence just-above 0"),
        (10, 9999, False, "confidence just-below 10_000"),
        (10, 10_000, False, "confidence exactly at 10_000"),
        (10, 10_001, True, "confidence just-above 10_000 (invalid)"),
    ],
    ids=lambda x: str(x),
)
def test_price_impact_preview_bva_pending_and_confidence_validation(
    pending: int, confidence_bps: int, should_raise: bool, reason: str
) -> None:
    _ = reason
    kwargs = dict(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
        pending_volume_same_direction=int(pending),
        confidence_bps=int(confidence_bps),
    )
    if should_raise:
        with pytest.raises(ValueError):
            price_impact_preview(**kwargs)
        return
    out = price_impact_preview(**kwargs)
    assert 0 <= out.confidence_bps <= 10_000
    assert out.pending_volume_same_direction == int(pending)


@pytest.mark.parametrize(
    "confidence_bps,expected_pending_conf,expected_out_conf,reason",
    [
        # Boundary mined near the historical regression witness (pending=80_000):
        # confidence_bps=9501 is the first value that pushes pending_volume_at_confidence
        # high enough to reduce amount_out_at_confidence by 1 under integer CPMM semantics.
        (9500, 76000, 1567, "just-below the output-step boundary"),
        (9501, 76008, 1566, "exactly at the boundary (first lower out_conf)"),
        (9502, 76016, 1566, "just-above the boundary"),
    ],
    ids=lambda x: str(x),
)
def test_price_impact_preview_bva_confidence_step_boundary(
    confidence_bps: int,
    expected_pending_conf: int,
    expected_out_conf: int,
    reason: str,
) -> None:
    _ = reason
    p = price_impact_preview(
        reserve_in=100_000,
        reserve_out=100_000,
        amount_in=5_000,
        fee_bps=30,
        pending_volume_same_direction=80_000,
        confidence_bps=int(confidence_bps),
    )
    assert p.pending_volume_at_confidence == int(expected_pending_conf)
    assert p.amount_out_at_confidence == int(expected_out_conf)
