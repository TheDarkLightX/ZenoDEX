from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


ROOT = Path(__file__).resolve().parents[2]
SPEC_PATH = ROOT / "src" / "tau_specs" / "recommended" / "settlement_witness_lifecycle_v1.tau"


def test_settlement_witness_lifecycle_trace() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    assert SPEC_PATH.exists(), f"missing spec: {SPEC_PATH}"

    steps = [
        {
            "i1": 1,
            "i2": 1,
            "i3": 1,
            "i4": 1,
            "i5": 1,
            "i6": 0,
            "i7": 0,
        },
        {
            "i1": 0,
            "i2": 0,
            "i3": 1,
            "i4": 0,
            "i5": 0,
            "i6": 1,
            "i7": 1,
        },
        {
            "i1": 1,
            "i2": 1,
            "i3": 1,
            "i4": 1,
            "i5": 0,
            "i6": 1,
            "i7": 0,
        },
    ]
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=steps,
        timeout_s=60.0,
    )

    expected = [
        {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1},
        {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1},
        {"o1": 1, "o2": 1, "o3": 1, "o4": 0, "o5": 1, "o6": 0},
    ]
    for idx, expected_outputs in enumerate(expected):
        for output_name, expected_value in expected_outputs.items():
            actual_value = outputs.get(idx, {}).get(output_name)
            assert actual_value == expected_value, (
                f"settlement_witness_lifecycle_v1.tau step {idx}: "
                f"expected {output_name}={expected_value}, got {actual_value}"
            )
