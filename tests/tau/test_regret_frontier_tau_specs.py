from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


ROOT = Path(__file__).resolve().parents[2]


def test_perp_liquidation_oracle_sanity_guard_v1_trace() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    spec_path = ROOT / "src/tau_specs/recommended/perp_liquidation_oracle_sanity_guard_v1.tau"
    assert spec_path.exists(), f"missing spec: {spec_path}"

    steps = [
        # liquidation requested + under maintenance + healthy oracle + proof/binding => accept
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1},
        # liquidation requested + stale oracle => reject
        {"i1": 1, "i2": 1, "i3": 1, "i4": 0, "i5": 1, "i6": 1, "i7": 1, "i8": 1},
        # no liquidation requested => safe path (still proof-gated)
        {"i1": 0, "i2": 0, "i3": 0, "i4": 0, "i5": 0, "i6": 0, "i7": 1, "i8": 1},
    ]

    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=steps, timeout_s=60.0)
    expected_o4 = [1, 0, 1]
    for idx, exp in enumerate(expected_o4):
        assert outputs.get(idx, {}).get("o4") == exp, f"step {idx}: o4 expected {exp}, got {outputs.get(idx, {}).get('o4')}"


def test_perp_market_param_velocity_guard_v1_trace() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    spec_path = ROOT / "src/tau_specs/recommended/perp_market_param_velocity_guard_v1.tau"
    assert spec_path.exists(), f"missing spec: {spec_path}"

    steps = [
        # open positions + sensitive param + small allowed increase
        {"i1": 1, "i2": 1, "i3": 100, "i4": 105, "i5": 10, "i6": 1, "i7": 0, "i8": 1, "i9": 1},
        # open positions + increase disallowed
        {"i1": 1, "i2": 1, "i3": 100, "i4": 105, "i5": 10, "i6": 0, "i7": 1, "i8": 1, "i9": 1},
        # open positions + delta too large
        {"i1": 1, "i2": 1, "i3": 100, "i4": 130, "i5": 10, "i6": 1, "i7": 1, "i8": 1, "i9": 1},
        # no open positions + large direction changes allowed if bounded by delta
        {"i1": 0, "i2": 1, "i3": 200, "i4": 150, "i5": 60, "i6": 0, "i7": 0, "i8": 1, "i9": 1},
    ]

    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=steps, timeout_s=60.0)
    expected_o4 = [1, 0, 0, 1]
    for idx, exp in enumerate(expected_o4):
        assert outputs.get(idx, {}).get("o4") == exp, f"step {idx}: o4 expected {exp}, got {outputs.get(idx, {}).get('o4')}"


def test_swap_execution_regret_guard_v1_trace() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    spec_path = ROOT / "src/tau_specs/recommended/swap_execution_regret_guard_v1.tau"
    assert spec_path.exists(), f"missing spec: {spec_path}"

    base = {
        "i1": 1,   # regret_within_limit_ok
        "i2": 1,   # impact_within_limit_ok
        "i3": 1,   # quote_age_within_limit_ok
        "i4": 1,   # hop_count_within_limit_ok
        "i5": 1,   # route_cert_ok
        "i6": 1,   # oracle_fresh_ok
        "i7": 1,   # not_expired_ok
        "i8": 1,   # require_route_cert
        "i9": 1,   # require_oracle_fresh
        "i10": 1,  # require_not_expired
        "i11": 1,  # proof_ok
        "i12": 1,  # binding_ok
    }

    steps = [
        dict(base),
        dict(base, i1=0),             # ProofUX regret check failed -> reject
        dict(base, i3=0),             # quote age check failed -> reject
        dict(base, i5=0),             # missing route cert while required -> reject
        dict(base, i5=0, i8=0),       # route cert not required -> accept
    ]

    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=steps, timeout_s=60.0)
    expected_o4 = [1, 0, 0, 0, 1]
    for idx, exp in enumerate(expected_o4):
        assert outputs.get(idx, {}).get("o4") == exp, f"step {idx}: o4 expected {exp}, got {outputs.get(idx, {}).get('o4')}"
