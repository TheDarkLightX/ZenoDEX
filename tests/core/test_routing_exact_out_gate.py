from __future__ import annotations

import random

from src.core.routing import (
    ExactOutTwoHopGateConfig,
    decide_exact_out_two_hop_gate,
    should_consider_exact_out_two_hop,
)
from src.kernels.python.cpmm_swap_v8 import swap_exact_out


def test_exact_out_two_hop_gate_basic_policies() -> None:
    # stress = 0.8, pressure = 2.75
    common = {
        "amount_out": 80,
        "direct_reserve_out": 100,
        "direct_amount_in": 220,
    }

    d_stress = decide_exact_out_two_hop_gate(
        **common,
        config=ExactOutTwoHopGateConfig(policy="stress", stress_threshold_bps=6000),
    )
    assert d_stress.consider_two_hop is True
    assert d_stress.stress_bps >= 8000

    d_pressure = decide_exact_out_two_hop_gate(
        **common,
        config=ExactOutTwoHopGateConfig(policy="pressure", pressure_threshold_e4=30_000),
    )
    assert d_pressure.consider_two_hop is False

    d_combo = decide_exact_out_two_hop_gate(
        **common,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure",
            stress_threshold_bps=9000,
            pressure_threshold_e4=20_000,
        ),
    )
    assert d_combo.consider_two_hop is True
    d_adaptive = decide_exact_out_two_hop_gate(
        **common,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure_adaptive",
            stress_threshold_bps=9000,
            pressure_threshold_e4=20_000,
            pressure_slope_e4=12_000,
        ),
    )
    assert d_adaptive.consider_two_hop is True
    d_piecewise = decide_exact_out_two_hop_gate(
        **common,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure_piecewise",
            stress_threshold_bps=9000,
            piecewise_stress_cutoff_bps=1500,
            piecewise_pressure_mid_e4=20_000,
            piecewise_pressure_low_e4=22_000,
        ),
    )
    assert d_piecewise.consider_two_hop is True
    d_piecewise_fee = decide_exact_out_two_hop_gate(
        **common,
        direct_fee_bps=10,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure_piecewise_fee",
            stress_threshold_bps=9000,
            fee_piecewise_stress_cutoff_bps=1200,
            fee_piecewise_pressure_mid_e4=20_000,
            fee_piecewise_pressure_low_e4=22_000,
            fee_piecewise_fee_slope_e4=120_000,
        ),
    )
    assert d_piecewise_fee.consider_two_hop is True
    d_tripiece = decide_exact_out_two_hop_gate(
        **common,
        direct_fee_bps=10,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure_tripiece",
            stress_threshold_bps=9000,
            tripiece_stress_lower_cutoff_bps=1400,
            tripiece_stress_upper_cutoff_bps=2000,
            tripiece_pressure_mid_band_e4=20_000,
            tripiece_pressure_upper_band_e4=19_000,
            tripiece_pressure_low_base_e4=22_000,
            tripiece_fee_slope_e4=160_000,
        ),
    )
    assert d_tripiece.consider_two_hop is True
    assert should_consider_exact_out_two_hop(
        **common,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure",
            stress_threshold_bps=9000,
            pressure_threshold_e4=20_000,
        ),
    )

    # Low-stress regime: adaptive gate should be stricter than plain OR.
    low_stress = {
        "amount_out": 20,  # stress = 0.2
        "direct_reserve_out": 100,
        "direct_amount_in": 35,  # pressure = 1.75
    }
    assert should_consider_exact_out_two_hop(
        **low_stress,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure",
            stress_threshold_bps=4000,
            pressure_threshold_e4=16_000,
        ),
    )
    assert not should_consider_exact_out_two_hop(
        **low_stress,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure_adaptive",
            stress_threshold_bps=4000,
            pressure_threshold_e4=16_000,
            pressure_slope_e4=12_000,
        ),
    )
    assert should_consider_exact_out_two_hop(
        **low_stress,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure_piecewise",
            stress_threshold_bps=4000,
            piecewise_stress_cutoff_bps=1500,
            piecewise_pressure_mid_e4=15_000,
            piecewise_pressure_low_e4=22_000,
        ),
    )
    assert should_consider_exact_out_two_hop(
        **low_stress,
        direct_fee_bps=40,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure_piecewise_fee",
            stress_threshold_bps=4000,
            fee_piecewise_stress_cutoff_bps=1200,
            fee_piecewise_pressure_mid_e4=15_000,
            fee_piecewise_pressure_low_e4=23_000,
            fee_piecewise_fee_slope_e4=120_000,
        ),
    )

    very_low_stress = {
        "amount_out": 4,  # stress = 0.04
        "direct_reserve_out": 100,
        "direct_amount_in": 7,  # pressure = 1.75
    }
    assert not should_consider_exact_out_two_hop(
        **very_low_stress,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure_piecewise",
            stress_threshold_bps=4000,
            piecewise_stress_cutoff_bps=1500,
            piecewise_pressure_mid_e4=15_000,
            piecewise_pressure_low_e4=22_000,
        ),
    )
    assert not should_consider_exact_out_two_hop(
        **very_low_stress,
        direct_fee_bps=20,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure_tripiece",
            stress_threshold_bps=4000,
            tripiece_stress_lower_cutoff_bps=1400,
            tripiece_stress_upper_cutoff_bps=2000,
            tripiece_pressure_mid_band_e4=16_000,
            tripiece_pressure_upper_band_e4=14_500,
            tripiece_pressure_low_base_e4=23_000,
            tripiece_fee_slope_e4=160_000,
        ),
    )

    # In deep low-stress band, fee-aware gate raises pressure threshold with direct fee.
    fee_sensitive = {
        "amount_out": 10,  # stress = 0.05 with reserve_out=200
        "direct_reserve_out": 200,
        "direct_amount_in": 23,  # pressure = 2.3
    }
    assert should_consider_exact_out_two_hop(
        **fee_sensitive,
        direct_fee_bps=0,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure_piecewise_fee",
            stress_threshold_bps=4000,
            fee_piecewise_stress_cutoff_bps=1200,
            fee_piecewise_pressure_mid_e4=15_000,
            fee_piecewise_pressure_low_e4=23_000,
            fee_piecewise_fee_slope_e4=120_000,
        ),
    )
    assert not should_consider_exact_out_two_hop(
        **fee_sensitive,
        direct_fee_bps=50,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure_piecewise_fee",
            stress_threshold_bps=4000,
            fee_piecewise_stress_cutoff_bps=1200,
            fee_piecewise_pressure_mid_e4=15_000,
            fee_piecewise_pressure_low_e4=23_000,
            fee_piecewise_fee_slope_e4=120_000,
        ),
    )


def test_exact_out_two_hop_gate_rejects_bad_inputs() -> None:
    try:
        decide_exact_out_two_hop_gate(
            amount_out=0,
            direct_reserve_out=100,
            direct_amount_in=10,
        )
    except ValueError as exc:
        assert "amount_out must be positive" in str(exc)
    else:
        assert False, "expected ValueError for non-positive amount_out"

    try:
        decide_exact_out_two_hop_gate(
            amount_out=10,
            direct_reserve_out=100,
            direct_amount_in=20,
            config=ExactOutTwoHopGateConfig(policy="unknown"),
        )
    except ValueError as exc:
        assert "unsupported exact-out gate policy" in str(exc)
    else:
        assert False, "expected ValueError for unknown policy"

    try:
        decide_exact_out_two_hop_gate(
            amount_out=10,
            direct_reserve_out=100,
            direct_amount_in=20,
            direct_fee_bps=-1,
        )
    except ValueError as exc:
        assert "direct_fee_bps must be non-negative" in str(exc)
    else:
        assert False, "expected ValueError for negative direct_fee_bps"


def test_interpretable_gate_tradeoff_on_holdout_distribution() -> None:
    rng = random.Random(20260221)
    n = 1800

    feasible = 0
    total_improvement = 0
    stress_calls = 0
    combo_calls = 0
    adaptive_calls = 0
    piecewise_calls = 0
    fee_piecewise_calls = 0
    tripiece_calls = 0
    stress_capture = 0
    combo_capture = 0
    adaptive_capture = 0
    piecewise_capture = 0
    fee_piecewise_capture = 0
    tripiece_capture = 0

    stress_cfg = ExactOutTwoHopGateConfig(policy="stress", stress_threshold_bps=4000)
    combo_cfg = ExactOutTwoHopGateConfig(
        policy="stress_or_pressure",
        stress_threshold_bps=4000,
        pressure_threshold_e4=16_000,
    )
    adaptive_cfg = ExactOutTwoHopGateConfig(
        policy="stress_or_pressure_adaptive",
        stress_threshold_bps=4000,
        pressure_threshold_e4=16_000,
        pressure_slope_e4=12_000,
    )
    piecewise_cfg = ExactOutTwoHopGateConfig(
        policy="stress_or_pressure_piecewise",
        stress_threshold_bps=4000,
        piecewise_stress_cutoff_bps=1500,
        piecewise_pressure_mid_e4=15_000,
        piecewise_pressure_low_e4=22_000,
    )
    fee_piecewise_cfg = ExactOutTwoHopGateConfig(
        policy="stress_or_pressure_piecewise_fee",
        stress_threshold_bps=4000,
        fee_piecewise_stress_cutoff_bps=1200,
        fee_piecewise_pressure_mid_e4=15_000,
        fee_piecewise_pressure_low_e4=23_000,
        fee_piecewise_fee_slope_e4=120_000,
    )
    tripiece_cfg = ExactOutTwoHopGateConfig(
        policy="stress_or_pressure_tripiece",
        stress_threshold_bps=4000,
        tripiece_stress_lower_cutoff_bps=1400,
        tripiece_stress_upper_cutoff_bps=2000,
        tripiece_pressure_mid_band_e4=16_000,
        tripiece_pressure_upper_band_e4=14_500,
        tripiece_pressure_low_base_e4=23_000,
        tripiece_fee_slope_e4=160_000,
    )

    for _ in range(n):
        x_ab = rng.randint(40, 400)
        y_ab = rng.randint(40, 400)
        fee_ab = rng.randint(0, 50)
        x_ac = rng.randint(40, 400)
        y_ac = rng.randint(40, 400)
        fee_ac = rng.randint(0, 50)
        x_cb = rng.randint(40, 400)
        y_cb = rng.randint(40, 400)
        fee_cb = rng.randint(0, 50)
        max_out = min(y_ab - 1, y_cb - 1, 120)
        if max_out < 1:
            continue
        amount_out = rng.randint(1, max_out)

        try:
            direct_in = swap_exact_out(
                reserve_in=x_ab,
                reserve_out=y_ab,
                amount_out=amount_out,
                fee_bps=fee_ab,
            ).amount_in
            mid_in = swap_exact_out(
                reserve_in=x_cb,
                reserve_out=y_cb,
                amount_out=amount_out,
                fee_bps=fee_cb,
            ).amount_in
            two_hop_in = swap_exact_out(
                reserve_in=x_ac,
                reserve_out=y_ac,
                amount_out=mid_in,
                fee_bps=fee_ac,
            ).amount_in
        except Exception:
            continue

        feasible += 1
        win = int(two_hop_in) < int(direct_in)
        improvement = int(direct_in - two_hop_in) if win else 0
        total_improvement += improvement

        use_stress = should_consider_exact_out_two_hop(
            amount_out=amount_out,
            direct_reserve_out=y_ab,
            direct_amount_in=int(direct_in),
            config=stress_cfg,
        )
        use_combo = should_consider_exact_out_two_hop(
            amount_out=amount_out,
            direct_reserve_out=y_ab,
            direct_amount_in=int(direct_in),
            config=combo_cfg,
        )
        use_adaptive = should_consider_exact_out_two_hop(
            amount_out=amount_out,
            direct_reserve_out=y_ab,
            direct_amount_in=int(direct_in),
            config=adaptive_cfg,
        )
        use_piecewise = should_consider_exact_out_two_hop(
            amount_out=amount_out,
            direct_reserve_out=y_ab,
            direct_amount_in=int(direct_in),
            config=piecewise_cfg,
        )
        use_fee_piecewise = should_consider_exact_out_two_hop(
            amount_out=amount_out,
            direct_reserve_out=y_ab,
            direct_amount_in=int(direct_in),
            direct_fee_bps=fee_ab,
            config=fee_piecewise_cfg,
        )
        use_tripiece = should_consider_exact_out_two_hop(
            amount_out=amount_out,
            direct_reserve_out=y_ab,
            direct_amount_in=int(direct_in),
            direct_fee_bps=fee_ab,
            config=tripiece_cfg,
        )
        stress_calls += 3 if use_stress else 1
        combo_calls += 3 if use_combo else 1
        adaptive_calls += 3 if use_adaptive else 1
        piecewise_calls += 3 if use_piecewise else 1
        fee_piecewise_calls += 3 if use_fee_piecewise else 1
        tripiece_calls += 3 if use_tripiece else 1

        if win and use_stress:
            stress_capture += improvement
        if win and use_combo:
            combo_capture += improvement
        if win and use_adaptive:
            adaptive_capture += improvement
        if win and use_piecewise:
            piecewise_capture += improvement
        if win and use_fee_piecewise:
            fee_piecewise_capture += improvement
        if win and use_tripiece:
            tripiece_capture += improvement

    assert feasible > 0
    assert total_improvement > 0

    stress_capture_rate = stress_capture / total_improvement
    combo_capture_rate = combo_capture / total_improvement
    adaptive_capture_rate = adaptive_capture / total_improvement
    piecewise_capture_rate = piecewise_capture / total_improvement
    fee_piecewise_capture_rate = fee_piecewise_capture / total_improvement
    tripiece_capture_rate = tripiece_capture / total_improvement
    combo_avg_calls = combo_calls / feasible
    adaptive_avg_calls = adaptive_calls / feasible
    piecewise_avg_calls = piecewise_calls / feasible
    fee_piecewise_avg_calls = fee_piecewise_calls / feasible
    tripiece_avg_calls = tripiece_calls / feasible

    # Combo trigger should capture at least as much value as stress-only.
    assert combo_capture_rate >= stress_capture_rate
    # and it should remain cheaper than always running 2-hop checks (3 calls).
    assert combo_avg_calls < 3.0
    # Empirical floor from held-out sweeps: interpretable triggers capture most value.
    assert combo_capture_rate > 0.9
    # Adaptive gate preserves high capture while reducing compute vs plain OR.
    assert adaptive_capture_rate >= 0.96
    assert adaptive_capture_rate >= stress_capture_rate
    assert adaptive_avg_calls <= combo_avg_calls
    # Piecewise gate keeps near-combo capture and trims calls in low-stress tails.
    assert piecewise_capture_rate >= 0.97
    assert piecewise_capture_rate >= adaptive_capture_rate
    assert piecewise_avg_calls <= combo_avg_calls
    # Fee-aware piecewise gate should remain near-combo quality and below combo compute.
    assert fee_piecewise_capture_rate >= 0.97
    assert fee_piecewise_capture_rate >= combo_capture_rate - 0.02
    assert fee_piecewise_avg_calls <= combo_avg_calls
    # Tri-piece policy should improve over piecewise-v2 reference point in this holdout.
    assert tripiece_capture_rate >= piecewise_capture_rate
    assert tripiece_avg_calls <= piecewise_avg_calls
