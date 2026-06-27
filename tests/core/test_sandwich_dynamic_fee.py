from __future__ import annotations

import pytest

from src.core.dynamic_fee_policy import StressFeePolicy, fee_bps_from_stress_policy
from src.core.sandwich_risk import (
    max_sandwich_profit_exact_in_cpmm_bounded,
    max_sandwich_profit_exact_in_cpmm_bounded_dynamic_fee,
    sandwich_profit_exact_in_cpmm,
    sandwich_profit_exact_in_cpmm_dynamic_fee,
)


def test_stress_fee_policy_bva_boundaries() -> None:
    # BVA: fee bounds and slope.
    StressFeePolicy(base_fee_bps=0, slope_bps=0)
    StressFeePolicy(base_fee_bps=30, slope_bps=0, min_fee_bps=0, max_fee_bps=100)
    with pytest.raises(ValueError):
        StressFeePolicy(base_fee_bps=-1, slope_bps=0)
    with pytest.raises(ValueError):
        StressFeePolicy(base_fee_bps=0, slope_bps=-1)
    with pytest.raises(ValueError):
        StressFeePolicy(base_fee_bps=0, slope_bps=0, min_fee_bps=200, max_fee_bps=100)

    # BVA: reserve/amount for fee computation.
    p = StressFeePolicy(base_fee_bps=30, slope_bps=600, max_fee_bps=300)
    with pytest.raises(ValueError):
        fee_bps_from_stress_policy(p, reserve_in=0, amount_in=1)
    with pytest.raises(ValueError):
        fee_bps_from_stress_policy(p, reserve_in=10, amount_in=-1)

    # Stress just below/at/above 100% (clamps at 10_000 bps).
    assert fee_bps_from_stress_policy(p, reserve_in=100, amount_in=0) == 30
    assert fee_bps_from_stress_policy(p, reserve_in=100, amount_in=100) <= 300
    assert fee_bps_from_stress_policy(p, reserve_in=100, amount_in=101) <= 300


def test_dynamic_fee_can_reduce_max_sandwich_profit_on_witness() -> None:
    # Witness-style comparison: a stress-increasing fee schedule should not increase
    # the best attacker profit in a bounded scan, and typically reduces it.
    x = 100_000
    y = 100_000
    base_fee = 30

    victim_amount_in = 20_000
    victim_min_out = 1  # loose; we focus on attacker-profit suppression, not UX tightness here

    static = max_sandwich_profit_exact_in_cpmm_bounded(
        reserve_in=x,
        reserve_out=y,
        fee_bps=base_fee,
        victim_amount_in=victim_amount_in,
        victim_min_out=victim_min_out,
        max_attacker_amount_in=500,
    )

    policy = StressFeePolicy(base_fee_bps=base_fee, slope_bps=600, min_fee_bps=base_fee, max_fee_bps=300)

    def fee_fn(res_in: int, _res_out: int, amt_in: int) -> int:
        return fee_bps_from_stress_policy(policy, reserve_in=res_in, amount_in=amt_in)

    dyn = max_sandwich_profit_exact_in_cpmm_bounded_dynamic_fee(
        reserve_in=x,
        reserve_out=y,
        fee_bps_fn=fee_fn,
        victim_amount_in=victim_amount_in,
        victim_min_out=victim_min_out,
        max_attacker_amount_in=500,
    )

    assert dyn.status == "inconclusive"  # no analytic cutoff for dynamic fees yet
    assert dyn.max_profit <= static.max_profit


def test_dynamic_fee_baseline_domain_error_is_inconclusive_not_victim_reverts() -> None:
    def bad_fee(_res_in: int, _res_out: int, _amount_in: int) -> int:
        raise ValueError("fee policy unavailable")

    dyn = max_sandwich_profit_exact_in_cpmm_bounded_dynamic_fee(
        reserve_in=100_000,
        reserve_out=100_000,
        fee_bps_fn=bad_fee,
        victim_amount_in=20_000,
        victim_min_out=1,
        max_attacker_amount_in=500,
    )

    assert dyn.status == "inconclusive"
    assert dyn.max_profit == 0
    assert dyn.scanned_max_attacker_amount_in == 500


def test_static_swap_internal_errors_are_not_suppressed(monkeypatch: pytest.MonkeyPatch) -> None:
    from src.core import sandwich_risk

    def broken_swap(*_args: object, **_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise RuntimeError("unexpected swap bug")

    monkeypatch.setattr(sandwich_risk, "swap_exact_in", broken_swap)

    with pytest.raises(RuntimeError, match="unexpected swap bug"):
        sandwich_profit_exact_in_cpmm(
            reserve_in=1000,
            reserve_out=1000,
            fee_bps=0,
            victim_amount_in=50,
            victim_min_out=1,
            attacker_amount_in=1,
        )


def test_dynamic_fee_internal_errors_are_not_suppressed() -> None:
    def broken_fee(_res_in: int, _res_out: int, _amount_in: int) -> int:
        raise RuntimeError("unexpected fee bug")

    with pytest.raises(RuntimeError, match="unexpected fee bug"):
        sandwich_profit_exact_in_cpmm_dynamic_fee(
            reserve_in=1000,
            reserve_out=1000,
            fee_bps_fn=broken_fee,
            victim_amount_in=50,
            victim_min_out=1,
            attacker_amount_in=1,
        )

    with pytest.raises(RuntimeError, match="unexpected fee bug"):
        max_sandwich_profit_exact_in_cpmm_bounded_dynamic_fee(
            reserve_in=1000,
            reserve_out=1000,
            fee_bps_fn=broken_fee,
            victim_amount_in=50,
            victim_min_out=1,
            max_attacker_amount_in=5,
        )
