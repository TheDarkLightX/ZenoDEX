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
        config=ExactOutTwoHopGateConfig(policy="stress", stress_threshold=0.6),
    )
    assert d_stress.consider_two_hop is True
    assert d_stress.stress >= 0.8

    d_pressure = decide_exact_out_two_hop_gate(
        **common,
        config=ExactOutTwoHopGateConfig(policy="pressure", pressure_threshold=3.0),
    )
    assert d_pressure.consider_two_hop is False

    d_combo = decide_exact_out_two_hop_gate(
        **common,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure",
            stress_threshold=0.9,
            pressure_threshold=2.0,
        ),
    )
    assert d_combo.consider_two_hop is True
    assert should_consider_exact_out_two_hop(
        **common,
        config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure",
            stress_threshold=0.9,
            pressure_threshold=2.0,
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


def test_interpretable_gate_tradeoff_on_holdout_distribution() -> None:
    rng = random.Random(20260221)
    n = 1800

    feasible = 0
    total_improvement = 0
    stress_calls = 0
    combo_calls = 0
    stress_capture = 0
    combo_capture = 0

    stress_cfg = ExactOutTwoHopGateConfig(policy="stress", stress_threshold=0.4)
    combo_cfg = ExactOutTwoHopGateConfig(
        policy="stress_or_pressure",
        stress_threshold=0.4,
        pressure_threshold=1.6,
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
        stress_calls += 3 if use_stress else 1
        combo_calls += 3 if use_combo else 1

        if win and use_stress:
            stress_capture += improvement
        if win and use_combo:
            combo_capture += improvement

    assert feasible > 0
    assert total_improvement > 0

    stress_capture_rate = stress_capture / total_improvement
    combo_capture_rate = combo_capture / total_improvement
    stress_avg_calls = stress_calls / feasible
    combo_avg_calls = combo_calls / feasible

    # Combo trigger should capture at least as much value as stress-only.
    assert combo_capture_rate >= stress_capture_rate
    # and it should remain cheaper than always running 2-hop checks (3 calls).
    assert combo_avg_calls < 3.0
    # Empirical floor from held-out sweeps: interpretable triggers capture most value.
    assert combo_capture_rate > 0.9

