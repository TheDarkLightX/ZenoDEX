from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps

ROOT = Path(__file__).resolve().parents[2]
UNSIGNED_SPEC = ROOT / "src" / "tau_specs" / "perceptron_2input_single_output_v1.tau"
SIGNED_OFFSET_SPEC = ROOT / "src" / "tau_specs" / "perceptron_2input_signed_offset_v1.tau"


def test_tau_unsigned_perceptron_two_input_experiment() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=UNSIGNED_SPEC,
        steps=[
            {"i1": 2, "i2": 3, "i3": 4, "i4": 5, "i5": 1, "i6": 20, "i7": 1},
            {"i1": 2, "i2": 1, "i3": 1, "i4": 2, "i5": 0, "i6": 10, "i7": 0},
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o1"] == 1
    assert outputs[1]["o1"] == 1


def test_tau_signed_offset_perceptron_two_input_experiment() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SIGNED_OFFSET_SPEC,
        steps=[
            {"i1": 129, "i2": 130, "i3": 131, "i4": 132, "i5": 128, "i6": 127, "i7": 1},
            {"i1": 125, "i2": 124, "i3": 131, "i4": 132, "i5": 127, "i6": 127, "i7": 0},
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o1"] == 1
    assert outputs[1]["o1"] == 1
