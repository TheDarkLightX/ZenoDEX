from __future__ import annotations

import pytest

from src.core.slippage_advisor import slippage_advice_exact_in_cpmm


def test_slippage_advice_detects_mev_vs_revert_conflict_under_rounding() -> None:
    """Small-reserve regimes can have quantized min_out steps that flip MEV risk."""
    advice = slippage_advice_exact_in_cpmm(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        amount_in=50,
        pending_volume_same_direction=10,
        confidence_bps=9500,
        slippage_options_bps=[10, 50, 100, 300],
        max_attacker_amount_in=2000,
    )

    assert advice.best_amount_out == 47
    assert advice.amount_out_at_confidence == 46
    assert advice.required_slippage_bps == 213  # ceil((47-46)*10000/47)

    # Due to floor quantization, even 10 bps drops min_out by 1 token, which
    # is already enough to be revert-safe at the confidence bound.
    assert advice.recommended_slippage_bps_revert_safe == 10
    assert advice.recommended_slippage_bps == 10

    # But even the smallest discrete slippage (10 bps) drops min_out by 1 due to floor,
    # enabling a profitable sandwich under the bounded model.
    assert advice.recommended_slippage_bps_mev_safe is None
    assert advice.status == "mev_conflict"

    # At least one option should show positive profit.
    assert any(o.sandwich_max_profit > 0 for o in advice.options)


def test_slippage_advice_returns_no_revert_safe_option_if_all_min_out_too_high() -> None:
    advice = slippage_advice_exact_in_cpmm(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        amount_in=50,
        pending_volume_same_direction=400,
        confidence_bps=9500,
        slippage_options_bps=[10, 50, 100, 300],
        max_attacker_amount_in=2000,
    )
    assert advice.recommended_slippage_bps_revert_safe is None
    assert advice.recommended_slippage_bps is None
    assert advice.status == "no_revert_safe_option"


@pytest.mark.parametrize(
    "confidence_bps,expected_out_conf,expected_required_slip,reason",
    [
        # Boundary mined by tools/bva (label flip around confidence_bps=8000):
        # out_conf steps from 47 -> 46, which changes required_slippage_bps from 0 -> 213.
        (7999, 47, 0, "just-below the quantized output step boundary"),
        (8000, 46, 213, "exactly at the boundary (first value with lower out_conf)"),
        (8001, 46, 213, "just-above the boundary"),
    ],
    ids=lambda x: str(x),
)
def test_slippage_advice_bva_confidence_boundary(
    confidence_bps: int, expected_out_conf: int, expected_required_slip: int, reason: str
) -> None:
    # The `reason` is intentional: keep BVA cases explainable when failures occur.
    _ = reason
    advice = slippage_advice_exact_in_cpmm(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        amount_in=50,
        pending_volume_same_direction=10,
        confidence_bps=int(confidence_bps),
        slippage_options_bps=[10, 50, 100, 300],
        max_attacker_amount_in=2000,
    )
    assert advice.best_amount_out == 47
    assert advice.amount_out_at_confidence == int(expected_out_conf)
    assert advice.required_slippage_bps == int(expected_required_slip)


@pytest.mark.parametrize(
    "confidence_bps,should_raise,reason",
    [
        # BVA for confidence domain [0, 10_000]
        (-1, True, "just-below min (invalid)"),
        (0, False, "exactly at min"),
        (1, False, "just-above min"),
        (9999, False, "just-below max"),
        (10_000, False, "exactly at max"),
        (10_001, True, "just-above max (invalid)"),
        # Special type boundaries (bool is a common footgun in Python)
        (False, False, "bool is accepted by current implementation (subclass of int)"),
        (True, False, "bool is accepted by current implementation (subclass of int)"),
    ],
    ids=lambda x: str(x),
)
def test_slippage_advice_bva_confidence_input_validation(
    confidence_bps: int, should_raise: bool, reason: str
) -> None:
    _ = reason
    kwargs = dict(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        amount_in=50,
        pending_volume_same_direction=10,
        confidence_bps=confidence_bps,
        slippage_options_bps=[10, 50, 100, 300],
        max_attacker_amount_in=2000,
    )
    if should_raise:
        with pytest.raises(ValueError):
            slippage_advice_exact_in_cpmm(**kwargs)
    else:
        out = slippage_advice_exact_in_cpmm(**kwargs)
        assert 0 <= int(out.confidence_bps) <= 10_000


@pytest.mark.parametrize(
    "slippage_options,should_raise,expected_first,expected_last,reason",
    [
        (None, False, 10, 300, "special: None => defaults"),
        ([], True, None, None, "length boundary: empty list => no valid options"),
        ([10], False, 10, 10, "length boundary: single option"),
        ([10, 50], False, 10, 50, "length boundary: two options"),
        ([10, 10, 50, -1, 10_001], False, 10, 50, "duplicates + out-of-range are filtered deterministically"),
        ([True, False, 10], False, 10, 10, "bools are skipped (type boundary); ints remain"),
        ([None, -1, 10_001], True, None, None, "all invalid entries filtered => empty => error"),
        ([0], False, 0, 0, "boundary: 0 bps slippage is allowed"),
        ([10_000], False, 10_000, 10_000, "boundary: max slippage is allowed"),
    ],
    ids=lambda x: str(x),
)
def test_slippage_advice_bva_slippage_options_normalization(
    slippage_options: list[int] | None,
    should_raise: bool,
    expected_first: int | None,
    expected_last: int | None,
    reason: str,
) -> None:
    _ = reason
    kwargs = dict(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        amount_in=50,
        pending_volume_same_direction=10,
        confidence_bps=9500,
        slippage_options_bps=slippage_options,
        max_attacker_amount_in=2000,
    )
    if should_raise:
        with pytest.raises(ValueError):
            slippage_advice_exact_in_cpmm(**kwargs)
        return

    out = slippage_advice_exact_in_cpmm(**kwargs)
    assert out.options, "expected at least one option assessment"
    assert out.options[0].slippage_bps == int(expected_first)
    assert out.options[-1].slippage_bps == int(expected_last)


@pytest.mark.parametrize(
    "max_attacker_amount_in,should_raise,reason",
    [
        (-1, True, "just-below min (invalid)"),
        (0, False, "exactly at min"),
        (1, False, "just-above min"),
        (True, True, "special type boundary: bool is rejected explicitly"),
        ("2000", True, "out-of-domain type: str"),
    ],
    ids=lambda x: str(x),
)
def test_slippage_advice_bva_max_attacker_amount_in_validation(
    max_attacker_amount_in, should_raise: bool, reason: str
) -> None:
    _ = reason
    kwargs = dict(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        amount_in=50,
        pending_volume_same_direction=10,
        confidence_bps=9500,
        slippage_options_bps=[10, 50, 100, 300],
        max_attacker_amount_in=max_attacker_amount_in,
    )
    if should_raise:
        with pytest.raises((TypeError, ValueError)):
            slippage_advice_exact_in_cpmm(**kwargs)
        return
    out = slippage_advice_exact_in_cpmm(**kwargs)
    assert out.options
