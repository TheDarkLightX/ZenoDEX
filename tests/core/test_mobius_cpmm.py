from __future__ import annotations

from fractions import Fraction

import pytest

from src.core.mobius_cpmm import Mobius, cpmm_pool_mobius, cpmm_two_hop_collapsed_floor_fee0


def _cpmm_exact_in_floor(*, x: int, y: int, dx: int) -> int:
    # fee=0 exact-in semantics: floor(y*dx/(dx+x))
    if x <= 0 or y <= 0 or dx <= 0:
        raise ValueError("x,y,dx must be positive")
    return (y * dx) // (dx + x)


def test_matrix_associativity_strong_claim_falsified_regression() -> None:
    # Minimal counterexample (from ESSO/Z3 witness in temp_algo_lab evidence pack).
    x1, y1, x2, y2, dx = 2, 3, 3, 3, 2
    out1 = _cpmm_exact_in_floor(x=x1, y=y1, dx=dx)
    out2 = _cpmm_exact_in_floor(x=x2, y=y2, dx=out1)
    collapsed = cpmm_two_hop_collapsed_floor_fee0(x1=x1, y1=y1, x2=x2, y2=y2, dx=dx)

    assert out2 == 0
    assert collapsed == 1
    assert out2 != collapsed


def test_two_hop_upper_bound_bva_fee0() -> None:
    # Boundary Value Analysis (BVA): include "just below/at/just above" around a chosen cap.
    # Domain minimum is 1, and 0 is out-of-domain (we keep it separate from this lemma test).
    vals = [1, 2, 3, 10, 11, 12, 13]

    # For all positive values, sequential floor-per-hop output should be <= collapsed floor.
    for x1 in vals:
        for y1 in vals:
            for x2 in vals:
                for y2 in vals:
                    for dx in vals:
                        out1 = _cpmm_exact_in_floor(x=x1, y=y1, dx=dx)
                        out2 = _cpmm_exact_in_floor(x=x2, y=y2, dx=out1) if out1 > 0 else 0
                        collapsed = cpmm_two_hop_collapsed_floor_fee0(
                            x1=x1, y1=y1, x2=x2, y2=y2, dx=dx
                        )
                        assert out2 <= collapsed


def test_mobius_composition_matches_closed_form_fee0() -> None:
    x1, y1, x2, y2, dx = 7, 11, 13, 5, 19

    m1 = cpmm_pool_mobius(reserve_in=x1, reserve_out=y1)
    m2 = cpmm_pool_mobius(reserve_in=x2, reserve_out=y2)
    route = m2 @ m1

    out_frac = route.eval_fraction(Fraction(dx, 1))
    collapsed = cpmm_two_hop_collapsed_floor_fee0(x1=x1, y1=y1, x2=x2, y2=y2, dx=dx)

    assert out_frac == Fraction(y1 * y2 * dx, ((y1 + x2) * dx) + (x1 * x2))
    assert route.eval_floor_int(dx) == collapsed


def test_cpmm_pool_mobius_rejects_bad_inputs() -> None:
    with pytest.raises(ValueError):
        cpmm_pool_mobius(reserve_in=-1, reserve_out=10)
    with pytest.raises(ValueError):
        cpmm_pool_mobius(reserve_in=10, reserve_out=-1)
    with pytest.raises(ValueError):
        cpmm_pool_mobius(reserve_in=10, reserve_out=10, fee_mul_num=0, fee_mul_den=1)
    with pytest.raises(ValueError):
        cpmm_pool_mobius(reserve_in=10, reserve_out=10, fee_mul_num=1, fee_mul_den=0)


def test_mobius_eval_floor_int_rejects_non_int() -> None:
    m = Mobius(a=1, b=0, c=1, d=1)
    with pytest.raises(TypeError):
        m.eval_floor_int(1.5)  # type: ignore[arg-type]


def test_mobius_eval_rejects_zero_denominator() -> None:
    m = Mobius(a=1, b=0, c=0, d=0)
    with pytest.raises(ZeroDivisionError, match="Mobius denominator is zero"):
        m.eval_fraction(Fraction(3, 1))
    with pytest.raises(ZeroDivisionError, match="Mobius denominator is zero"):
        m.eval_floor_int(3)


def test_cpmm_pool_mobius_and_two_hop_reject_non_int_and_non_positive_inputs() -> None:
    with pytest.raises(TypeError, match="reserve_in must be an int"):
        cpmm_pool_mobius(reserve_in=1.5, reserve_out=10)  # type: ignore[arg-type]

    with pytest.raises(TypeError, match="dx must be an int"):
        cpmm_two_hop_collapsed_floor_fee0(x1=1, y1=1, x2=1, y2=1, dx=1.5)  # type: ignore[arg-type]

    with pytest.raises(ValueError, match="x1,y1,x2,y2,dx must be positive"):
        cpmm_two_hop_collapsed_floor_fee0(x1=1, y1=1, x2=1, y2=1, dx=0)
