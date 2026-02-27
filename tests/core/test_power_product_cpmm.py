from __future__ import annotations

from fractions import Fraction

import pytest

from src.core.cpmm import swap_exact_in as cpmm_swap_exact_in
from src.core.cpmm import swap_exact_out as cpmm_swap_exact_out
from src.core.power_product_cpmm import (
    MAX_EXPONENT,
    _ceil_iroot,
    power_product_k,
    swap_exact_in_power_product,
    swap_exact_out_power_product,
)
from src.core.quadratic_cpmm import swap_exact_in_quadratic, swap_exact_out_quadratic


def test_power_product_exponent_bva_boundaries() -> None:
    # BVA: exponent just below/at/just above the valid range.
    with pytest.raises(ValueError):
        swap_exact_in_power_product(10, 10, 1, exp_in=0, exp_out=1)
    with pytest.raises(ValueError):
        swap_exact_in_power_product(10, 10, 1, exp_in=1, exp_out=0)
    with pytest.raises(ValueError):
        swap_exact_in_power_product(10, 10, 1, exp_in=-1, exp_out=1)
    with pytest.raises(TypeError):
        swap_exact_in_power_product(10, 10, 1, exp_in=True, exp_out=1)  # type: ignore[arg-type]

    # Use a trade size that yields positive output under conservative rounding.
    swap_exact_in_power_product(10, 10, 2, exp_in=1, exp_out=1)
    swap_exact_in_power_product(10, 10, 2, exp_in=2, exp_out=1)

    with pytest.raises(ValueError):
        swap_exact_in_power_product(10, 10, 1, exp_in=MAX_EXPONENT + 1, exp_out=1)


def test_power_product_fee_bva_boundaries() -> None:
    # This reference implementation is fee=0 only.
    swap_exact_in_power_product(10, 10, 2, exp_in=1, exp_out=1, fee_bps=0)
    with pytest.raises(ValueError):
        swap_exact_in_power_product(10, 10, 2, exp_in=1, exp_out=1, fee_bps=1)
    with pytest.raises(ValueError):
        swap_exact_out_power_product(10, 10, 1, exp_in=1, exp_out=1, fee_bps=1)


def test_power_product_reserve_amount_bva_boundaries() -> None:
    # BVA: reserves must be positive.
    with pytest.raises(ValueError):
        swap_exact_in_power_product(0, 10, 1, exp_in=1, exp_out=1)
    with pytest.raises(ValueError):
        swap_exact_in_power_product(10, 0, 1, exp_in=1, exp_out=1)
    with pytest.raises(ValueError):
        swap_exact_in_power_product(-1, 10, 1, exp_in=1, exp_out=1)

    # BVA: amount_in/out must be positive and cannot drain reserve_out.
    with pytest.raises(ValueError):
        swap_exact_in_power_product(10, 10, 0, exp_in=1, exp_out=1)
    with pytest.raises(ValueError):
        swap_exact_out_power_product(10, 10, 0, exp_in=1, exp_out=1)
    with pytest.raises(ValueError):
        swap_exact_out_power_product(10, 10, 10, exp_in=1, exp_out=1)


def test_power_product_matches_cpmm_fee0_for_exp_1_1() -> None:
    # exp_in=exp_out=1 => CPMM invariant K=x*y, with conservative rounding.
    out0, (x1_0, y1_0) = cpmm_swap_exact_in(2, 3, 2, 0)
    out1, (x1_1, y1_1) = swap_exact_in_power_product(2, 3, 2, exp_in=1, exp_out=1, fee_bps=0)
    assert (out1, (x1_1, y1_1)) == (out0, (x1_0, y1_0))

    dx0, (x2_0, y2_0) = cpmm_swap_exact_out(2, 3, 1, 0)
    dx1, (x2_1, y2_1) = swap_exact_out_power_product(2, 3, 1, exp_in=1, exp_out=1, fee_bps=0)
    assert (dx1, (x2_1, y2_1)) == (dx0, (x2_0, y2_0))


def test_power_product_matches_quadratic_for_exp_2_1() -> None:
    out0, (x1_0, y1_0) = swap_exact_in_quadratic(3, 10, 2, fee_bps=0)
    out1, (x1_1, y1_1) = swap_exact_in_power_product(3, 10, 2, exp_in=2, exp_out=1, fee_bps=0)
    assert (out1, (x1_1, y1_1)) == (out0, (x1_0, y1_0))

    dx0, (x2_0, y2_0) = swap_exact_out_quadratic(3, 10, 6, fee_bps=0)
    dx1, (x2_1, y2_1) = swap_exact_out_power_product(3, 10, 6, exp_in=2, exp_out=1, fee_bps=0)
    assert (dx1, (x2_1, y2_1)) == (dx0, (x2_0, y2_0))


def test_power_product_invariant_is_monotone_non_decreasing() -> None:
    # Check K' >= K across a few exponents and inputs.
    cases = [
        (1, 1, 5, 7, 3),
        (2, 1, 5, 7, 3),
        (1, 2, 5, 7, 3),
        (3, 2, 5, 7, 2),
    ]
    for exp_in, exp_out, x, y, dx in cases:
        k0 = power_product_k(x, y, exp_x=exp_in, exp_y=exp_out)
        out, (x1, y1) = swap_exact_in_power_product(x, y, dx, exp_in=exp_in, exp_out=exp_out, fee_bps=0)
        assert out > 0
        k1 = power_product_k(x1, y1, exp_x=exp_in, exp_y=exp_out)
        assert k1 >= k0


def test_ceil_iroot_minimality_bva() -> None:
    # BVA around perfect powers.
    assert _ceil_iroot(0, 3) == 0
    assert _ceil_iroot(1, 3) == 1
    assert _ceil_iroot(7, 3) == 2  # 1^3 < 7 <= 2^3
    assert _ceil_iroot(8, 3) == 2  # exact power
    assert _ceil_iroot(9, 3) == 3


def test_power_product_root_rounding_obligation_example() -> None:
    # Example where exp_out>1 triggers a real integer root.
    #
    # K = x * y^2, x=2, y=10, dx=1 => x1=3
    # need = ceil(2*100/3)=67, y1=ceil_sqrt(67)=9, out=1.
    out, (x1, y1) = swap_exact_in_power_product(2, 10, 1, exp_in=1, exp_out=2, fee_bps=0)
    assert (out, x1, y1) == (1, 3, 9)

    k0 = power_product_k(2, 10, exp_x=1, exp_y=2)
    need = (k0 + pow(x1, 1) - 1) // pow(x1, 1)
    assert pow(y1, 2) >= need
    assert pow(y1 - 1, 2) < need
