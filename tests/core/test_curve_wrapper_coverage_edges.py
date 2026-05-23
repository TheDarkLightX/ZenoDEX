from __future__ import annotations

from types import SimpleNamespace

import pytest

import src.core.cubic_sum_amm as cubic_sum_module
import src.core.quartic_blend_amm as quartic_module
import src.core.quintic_blend_amm as quintic_module
import src.core.sum_boost_amm as sum_boost_module


EXACT_IN_CASES = [
    (
        cubic_sum_module,
        cubic_sum_module.swap_exact_in_cubic_sum,
        {"p": 0},
        "p and q must be positive",
    ),
    (
        quartic_module,
        quartic_module.swap_exact_in_quartic_blend,
        {"c_num": -1},
        "c_num must be non-negative, c_den must be positive",
    ),
    (
        quintic_module,
        quintic_module.swap_exact_in_quintic_blend,
        {"c_num": -1},
        "c_num must be non-negative, c_den must be positive",
    ),
    (
        sum_boost_module,
        sum_boost_module.swap_exact_in_sum_boost,
        {"mu_num": -1},
        "mu_num must be non-negative, mu_den must be positive",
    ),
]

EXACT_OUT_CASES = [
    (
        cubic_sum_module,
        cubic_sum_module.swap_exact_out_cubic_sum,
        {"p": 0},
        "p and q must be positive",
    ),
    (
        quartic_module,
        quartic_module.swap_exact_out_quartic_blend,
        {"c_num": -1},
        "c_num must be non-negative, c_den must be positive",
    ),
    (
        quintic_module,
        quintic_module.swap_exact_out_quintic_blend,
        {"c_num": -1},
        "c_num must be non-negative, c_den must be positive",
    ),
    (
        sum_boost_module,
        sum_boost_module.swap_exact_out_sum_boost,
        {"mu_num": -1},
        "mu_num must be non-negative, mu_den must be positive",
    ),
]


@pytest.mark.parametrize(("module", "swap_exact_in", "bad_curve_kwargs", "curve_error"), EXACT_IN_CASES)
def test_curve_wrappers_exact_in_fail_closed_validation_and_invariant(
    monkeypatch: pytest.MonkeyPatch,
    module,
    swap_exact_in,
    bad_curve_kwargs: dict[str, int],
    curve_error: str,
) -> None:
    with pytest.raises(ValueError, match="Reserves must be non-negative"):
        swap_exact_in(-1, 10, 1)
    with pytest.raises(ValueError, match="amount_in must be positive"):
        swap_exact_in(10, 10, 0)
    with pytest.raises(ValueError, match=curve_error):
        swap_exact_in(10, 10, 1, **bad_curve_kwargs)
    with pytest.raises(ValueError, match="fee_bps must be in"):
        swap_exact_in(10, 10, 1, fee_bps=10_001)

    monkeypatch.setattr(
        module,
        "_kernel_swap_exact_in_v1",
        lambda **_kwargs: SimpleNamespace(
            k_before=5,
            k_after=4,
            amount_out=1,
            new_reserve_in=11,
            new_reserve_out=9,
        ),
    )
    with pytest.raises(ValueError, match="Invariant violation"):
        swap_exact_in(10, 10, 1)


@pytest.mark.parametrize(("module", "swap_exact_out", "bad_curve_kwargs", "curve_error"), EXACT_OUT_CASES)
def test_curve_wrappers_exact_out_fail_closed_validation_and_invariant(
    monkeypatch: pytest.MonkeyPatch,
    module,
    swap_exact_out,
    bad_curve_kwargs: dict[str, int],
    curve_error: str,
) -> None:
    with pytest.raises(ValueError, match="Reserves must be non-negative"):
        swap_exact_out(-1, 10, 1)
    with pytest.raises(ValueError, match="amount_out must be positive"):
        swap_exact_out(10, 10, 0)
    with pytest.raises(ValueError, match="cannot drain full reserve_out"):
        swap_exact_out(10, 10, 10)
    with pytest.raises(ValueError, match=curve_error):
        swap_exact_out(10, 10, 1, **bad_curve_kwargs)
    with pytest.raises(ValueError, match="fee_bps must be in"):
        swap_exact_out(10, 10, 1, fee_bps=10_001)

    monkeypatch.setattr(
        module,
        "_kernel_swap_exact_out_v1",
        lambda **_kwargs: SimpleNamespace(
            k_before=5,
            k_after=4,
            amount_in=1,
            new_reserve_in=11,
            new_reserve_out=9,
        ),
    )
    with pytest.raises(ValueError, match="Invariant violation"):
        swap_exact_out(10, 10, 1)
