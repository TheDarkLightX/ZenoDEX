"""Tests for the application economic-security bound.

Run: PYTHONPATH=. pytest experiments/economic_security_bound_v1/test_economic_security_bound.py
"""

from __future__ import annotations

import pytest

from economic_security_bound import (
    BPS,
    AttackModel,
    deters_for_all_alpha,
    fee_deterrence_efficiency_bps,
    fee_paid,
    min_non_recapturable_to_deter,
    non_recapturable_fee_cost,
    recaptured_fee,
)


def test_fee_deterrence_efficiency_decreases_with_alpha():
    assert fee_deterrence_efficiency_bps(0) == BPS        # alpha=0   -> 100% deters
    assert fee_deterrence_efficiency_bps(5000) == 5000    # alpha=50% -> 50%
    assert fee_deterrence_efficiency_bps(9000) == 1000    # alpha=90% -> 10%
    assert fee_deterrence_efficiency_bps(BPS) == 0        # alpha=100% -> 0% (full recapture)


def test_recapture_complementation_is_exact():
    # recaptured + non_recapturable == fee exactly, for every alpha (integer split).
    for fee in (0, 1, 999, 1000, 123_456):
        for a in (0, 1, 3333, 5000, 9999, BPS):
            assert recaptured_fee(fee, a) + non_recapturable_fee_cost(fee, a) == fee


def test_whale_recaptures_fee_so_high_fee_still_fails():
    # COUNTEREXAMPLE to "a big fee deters": nominal fee 1000 > V 500 looks safe, but
    # a whale (alpha=90%) recaptures 900, leaving only 100 of real deterrence -> the
    # attack is profitable despite the fee being twice V.
    m = AttackModel(v_attack=500, fee_notional=1_000_000, fee_bps=10, alpha_bps=9000, gas=0, collateral=0)
    assert m.fee() == 1000 and m.fee() > m.v_attack          # nominal fee exceeds V
    assert non_recapturable_fee_cost(m.fee(), 9000) == 100   # but only 100 actually deters
    assert m.is_profitable() and m.net_profit() == 400


def test_robust_theorem_exactly_characterizes_bruteforce_over_alpha():
    # The closed-form bound deters_for_all_alpha(V, gas, collat) == "not profitable
    # at ANY alpha" (the brute force includes alpha=10000 where the fee deters 0).
    for v in (0, 1, 1000, 50_000):
        for gas in (0, 500, 50_000):
            for collat in (0, 700):
                closed = deters_for_all_alpha(v, gas, collat)
                brute = all(
                    not AttackModel(
                        v_attack=v, fee_notional=10_000_000, fee_bps=30,
                        alpha_bps=a, gas=gas, collateral=collat,
                    ).is_profitable()
                    for a in range(0, BPS + 1)  # EVERY alpha in [0, 10000], exhaustive
                )
                assert closed == brute, (v, gas, collat)


def test_min_non_recapturable_is_full_V_for_a_whale():
    # alpha=100%: fee deters nothing, so non-recapturable cost must cover all of V.
    assert min_non_recapturable_to_deter(50_000, fee_amount=9_999, alpha_bps=BPS) == 50_000
    # alpha=0: the full fee counts toward deterrence.
    assert min_non_recapturable_to_deter(50_000, fee_amount=9_999, alpha_bps=0) == 50_000 - 9_999


def test_zenodex_30bps_concrete_number():
    # ZenoDEX swap fee = 30 bps. A whale LP (alpha=90%) routes a 1_000_000 base-unit
    # manipulation: nominal fee = 3000, but effective deterrence is only 10% = 300.
    fee = fee_paid(1_000_000, 30)
    assert fee == 3000
    assert non_recapturable_fee_cost(fee, 9000) == 300  # 30bps * (1 - 0.9) = 3bps effective
    whale = AttackModel(v_attack=1000, fee_notional=1_000_000, fee_bps=30, alpha_bps=9000, gas=0, collateral=0)
    assert whale.is_profitable()  # V=1000 > 300 effective fee -> pays off
    # Robust fix: size non-recapturable cost (gas + locked collateral) >= V; then it
    # deters for ANY LP share, including a 100%-pool whale.
    assert deters_for_all_alpha(1000, gas=600, collateral=400)
    assert not AttackModel(
        v_attack=1000, fee_notional=1_000_000, fee_bps=30, alpha_bps=BPS, gas=600, collateral=400
    ).is_profitable()


def test_inputs_fail_closed():
    with pytest.raises(ValueError):
        fee_deterrence_efficiency_bps(BPS + 1)
    with pytest.raises(ValueError):
        AttackModel(v_attack=-1, fee_notional=0, fee_bps=0, alpha_bps=0, gas=0, collateral=0)
    with pytest.raises(TypeError):
        recaptured_fee(1.5, 0)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        AttackModel(v_attack=True, fee_notional=0, fee_bps=0, alpha_bps=0, gas=0, collateral=0)
