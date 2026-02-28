from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


ROOT = Path(__file__).resolve().parents[2]


def test_resource_budget_guard_v1_trace() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    spec_path = ROOT / "src/tau_specs/recommended/resource_budget_guard_v1.tau"
    assert spec_path.exists(), f"missing spec: {spec_path}"

    steps = [
        # healthy path + proof/binding => accept
        {
            "i1": 1,
            "i2": 1,
            "i3": 1,
            "i4": 1,
            "i5": 1,
            "i6": 1,
            "i7": 1,
            "i8": 1,
            "i9": 1,
            "i10": 1,
            "i11": 1,
            "i12": 1,
        },
        # core limits failed => reject
        {
            "i1": 0,
            "i2": 1,
            "i3": 1,
            "i4": 1,
            "i5": 1,
            "i6": 1,
            "i7": 1,
            "i8": 1,
            "i9": 1,
            "i10": 1,
            "i11": 1,
            "i12": 1,
        },
        # cache/telemetry optional in degraded mode => accept
        {
            "i1": 1,
            "i2": 0,
            "i3": 1,
            "i4": 1,
            "i5": 1,
            "i6": 1,
            "i7": 1,
            "i8": 0,
            "i9": 0,
            "i10": 0,
            "i11": 1,
            "i12": 1,
        },
        # backpressure clear failed => reject
        {
            "i1": 1,
            "i2": 1,
            "i3": 0,
            "i4": 1,
            "i5": 1,
            "i6": 1,
            "i7": 1,
            "i8": 1,
            "i9": 1,
            "i10": 1,
            "i11": 1,
            "i12": 1,
        },
    ]

    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=steps, timeout_s=60.0)
    expected_o3 = [1, 0, 1, 0]
    for idx, exp in enumerate(expected_o3):
        assert outputs.get(idx, {}).get("o3") == exp, f"step {idx}: o3 expected {exp}, got {outputs.get(idx, {}).get('o3')}"


def test_resource_artifact_binding_guard_v1_trace() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    spec_path = ROOT / "src/tau_specs/recommended/resource_artifact_binding_guard_v1.tau"
    assert spec_path.exists(), f"missing spec: {spec_path}"

    steps = [
        # fully bound + proof/binding => accept
        {
            "i1": 1,
            "i2": 1,
            "i3": 1,
            "i4": 1,
            "i5": 1,
            "i6": 1,
            "i7": 1,
            "i8": 1,
            "i9": 1,
            "i10": 1,
            "i11": 1,
            "i12": 1,
        },
        # hash binding failed => reject
        {
            "i1": 0,
            "i2": 1,
            "i3": 1,
            "i4": 1,
            "i5": 1,
            "i6": 1,
            "i7": 1,
            "i8": 1,
            "i9": 1,
            "i10": 1,
            "i11": 1,
            "i12": 1,
        },
        # replay+attachments optional when not required => accept
        {
            "i1": 1,
            "i2": 0,
            "i3": 1,
            "i4": 0,
            "i5": 1,
            "i6": 1,
            "i7": 0,
            "i8": 0,
            "i9": 1,
            "i10": 1,
            "i11": 1,
            "i12": 1,
        },
        # signer required but not present => reject
        {
            "i1": 1,
            "i2": 1,
            "i3": 0,
            "i4": 1,
            "i5": 1,
            "i6": 1,
            "i7": 1,
            "i8": 1,
            "i9": 1,
            "i10": 1,
            "i11": 1,
            "i12": 1,
        },
    ]

    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=steps, timeout_s=60.0)
    expected_o5 = [1, 0, 1, 0]
    for idx, exp in enumerate(expected_o5):
        assert outputs.get(idx, {}).get("o5") == exp, f"step {idx}: o5 expected {exp}, got {outputs.get(idx, {}).get('o5')}"


def test_resource_load_shedding_regret_guard_v1_trace() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    spec_path = ROOT / "src/tau_specs/recommended/resource_load_shedding_regret_guard_v1.tau"
    assert spec_path.exists(), f"missing spec: {spec_path}"

    steps = [
        # normal mode happy path
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 0, "i9": 0, "i10": 1, "i11": 1, "i12": 1},
        # normal mode with bad user safety => reject
        {"i1": 1, "i2": 1, "i3": 0, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 0, "i9": 0, "i10": 1, "i11": 1, "i12": 1},
        # load shedding path with override and non-strict regret => accept
        {"i1": 0, "i2": 1, "i3": 0, "i4": 0, "i5": 0, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 0, "i11": 1, "i12": 1},
        # load shedding strict mode requires user safety => reject here
        {"i1": 0, "i2": 1, "i3": 0, "i4": 0, "i5": 0, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1, "i12": 1},
    ]

    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=steps, timeout_s=60.0)
    expected_o6 = [1, 0, 1, 0]
    for idx, exp in enumerate(expected_o6):
        assert outputs.get(idx, {}).get("o6") == exp, f"step {idx}: o6 expected {exp}, got {outputs.get(idx, {}).get('o6')}"
