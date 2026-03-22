from __future__ import annotations

import importlib
import random

import pytest


def _import_or_skip_if_top_level_missing(module_name: str):
    try:
        return importlib.import_module(module_name)
    except ModuleNotFoundError as exc:
        if exc.name == module_name:
            pytest.skip(f"{module_name} is not promoted on clean main", allow_module_level=True)
        raise


cpmm_u256_safety = _import_or_skip_if_top_level_missing("src.core.cpmm_u256_safety")
fixed_width = _import_or_skip_if_top_level_missing("src.core.fixed_width")

analyze_cpmm_exact_in_u256_overflows = cpmm_u256_safety.analyze_cpmm_exact_in_u256_overflows
fee_total_ceil_bigint = cpmm_u256_safety.fee_total_ceil_bigint
fee_total_ceil_decomposed = cpmm_u256_safety.fee_total_ceil_decomposed
mul_div_floor_gcd_reduced_u256 = cpmm_u256_safety.mul_div_floor_gcd_reduced_u256
U256_MAX = fixed_width.U256_MAX
will_mul_overflow = fixed_width.will_mul_overflow


def test_fee_total_decomposed_matches_bigint_reference_randomized() -> None:
    rng = random.Random(0)
    for _ in range(500):
        gross = rng.randrange(0, 10**18)
        fee_bps = rng.randrange(0, 10_001)
        assert fee_total_ceil_decomposed(gross, fee_bps) == fee_total_ceil_bigint(gross, fee_bps)


def test_fee_total_decomposed_avoids_u256_mul_overflow_on_extreme_witness() -> None:
    # Witness: naive (gross * fee_bps) overflows u256, but decomposed computation
    # uses smaller products and stays within range.
    gross = U256_MAX
    fee_bps = 10_000
    assert will_mul_overflow(256, gross, fee_bps) is True

    # Decomposed still matches the exact bigint value and should fit in u256.
    fee = fee_total_ceil_decomposed(gross, fee_bps)
    assert fee == gross
    assert 0 <= fee <= U256_MAX


def test_cpmm_exact_in_u256_overflow_report_bva() -> None:
    # BVA: inputs must be non-negative and fit u256.
    with pytest.raises(ValueError):
        analyze_cpmm_exact_in_u256_overflows(reserve_in=-1, reserve_out=1, amount_in=1, fee_bps=0)
    with pytest.raises(ValueError):
        analyze_cpmm_exact_in_u256_overflows(reserve_in=1, reserve_out=1, amount_in=-1, fee_bps=0)
    with pytest.raises(ValueError):
        analyze_cpmm_exact_in_u256_overflows(reserve_in=1, reserve_out=1, amount_in=1, fee_bps=10_001)

    r = analyze_cpmm_exact_in_u256_overflows(reserve_in=1, reserve_out=1, amount_in=1, fee_bps=0)
    assert r.fee_mul_overflow_naive is False
    assert r.fee_mul_overflow_decomposed is False
    assert r.denom_add_overflow is False
    assert r.numerator_mul_overflow is False


def test_cpmm_exact_in_u256_overflow_report_flags_mul_overflow() -> None:
    # BVA around the multiplication overflow boundary for reserve_out * net_in.
    #
    # Choose net_in=2^128, reserve_out=2^128: product = 2^256 => overflow.
    net_in = 1 << 128
    reserve_out = 1 << 128
    reserve_in = 1
    amount_in = net_in
    fee_bps = 0
    r = analyze_cpmm_exact_in_u256_overflows(
        reserve_in=reserve_in, reserve_out=reserve_out, amount_in=amount_in, fee_bps=fee_bps
    )
    assert r.net_in == net_in
    assert r.numerator_mul_overflow is True


def test_mul_div_floor_gcd_reduction_can_avoid_u256_mul_overflow() -> None:
    # Witness: naive a*b overflows u256, but gcd reduction cancels enough to compute exactly.
    #
    # Choose CPMM-style terms:
    #   a = reserve_out = 2^200
    #   b = net_in     = 2^100
    #   c = reserve_in + net_in = 2^101
    #
    # Then floor(a*b/c) = 2^199. Naive a*b is 2^300 (overflow), but gcd(b,c)=2^100
    # reduces it to floor(2^200 * 1 / 2) safely.
    a = 1 << 200
    b = 1 << 100
    c = 1 << 101
    assert will_mul_overflow(256, a, b) is True
    out = mul_div_floor_gcd_reduced_u256(a=a, b=b, c=c)
    assert out == 1 << 199


def test_fee_total_helpers_reject_invalid_inputs() -> None:
    with pytest.raises(ValueError, match="gross_in must be non-negative"):
        fee_total_ceil_bigint(-1, 1)
    with pytest.raises(ValueError, match="fee_bps out of range"):
        fee_total_ceil_bigint(1, 10_001)

    with pytest.raises(ValueError, match="gross_in must be non-negative"):
        fee_total_ceil_decomposed(-1, 1)
    with pytest.raises(ValueError, match="fee_bps out of range"):
        fee_total_ceil_decomposed(1, 10_001)


def test_mul_div_floor_gcd_reduction_rejects_invalid_inputs_and_reports_intractable_case() -> None:
    with pytest.raises(ValueError, match="a,b must be non-negative and c must be positive"):
        mul_div_floor_gcd_reduced_u256(a=-1, b=1, c=1)
    with pytest.raises(ValueError, match="inputs must fit in u256"):
        mul_div_floor_gcd_reduced_u256(a=U256_MAX + 1, b=1, c=1)

    assert mul_div_floor_gcd_reduced_u256(a=U256_MAX, b=2, c=1) is None


def test_cpmm_exact_in_u256_overflow_report_rejects_bad_types_and_u256_bounds() -> None:
    with pytest.raises(TypeError, match="reserve_in must be an int"):
        analyze_cpmm_exact_in_u256_overflows(reserve_in=1.5, reserve_out=1, amount_in=1, fee_bps=0)

    with pytest.raises(ValueError, match="inputs must fit in u256"):
        analyze_cpmm_exact_in_u256_overflows(reserve_in=U256_MAX + 1, reserve_out=1, amount_in=1, fee_bps=0)
