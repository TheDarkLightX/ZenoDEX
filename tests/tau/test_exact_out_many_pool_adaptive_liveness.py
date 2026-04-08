from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


ROOT = Path(__file__).resolve().parents[2]
SPEC_PATH = ROOT / "src" / "tau_specs" / "recommended" / "optimizer_audited_bounds_liveness_v2.tau"


def test_exact_out_many_pool_adaptive_liveness_trace() -> None:
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
            "i6": 1,
            "i7": 1,
            "i8": 0,
            "i9": 0,
            "i10": 1,
            "i11": 1,
            "i12": 0,
            "i13": 1,
            "i14": 0,
        },
        {
            "i1": 1,
            "i2": 1,
            "i3": 1,
            "i4": 1,
            "i5": 1,
            "i6": 1,
            "i7": 0,
            "i8": 1,
            "i9": 1,
            "i10": 0,
            "i11": 0,
            "i12": 1,
            "i13": 0,
            "i14": 1,
        },
        {
            "i1": 1,
            "i2": 1,
            "i3": 1,
            "i4": 1,
            "i5": 1,
            "i6": 1,
            "i7": 0,
            "i8": 1,
            "i9": 1,
            "i10": 1,
            "i11": 0,
            "i12": 1,
            "i13": 0,
            "i14": 1,
        },
    ]
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=steps,
        timeout_s=60.0,
    )

    expected = [
        {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1, "o7": 1},
        {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1, "o7": 1},
        {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 0, "o7": 0},
    ]
    for idx, expected_outputs in enumerate(expected):
        for output_name, expected_value in expected_outputs.items():
            actual_value = outputs.get(idx, {}).get(output_name)
            assert actual_value == expected_value, (
                f"optimizer_audited_bounds_liveness_v2.tau step {idx}: "
                f"expected {output_name}={expected_value}, got {actual_value}"
            )
