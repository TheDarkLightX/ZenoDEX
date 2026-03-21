from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps

ROOT = Path(__file__).resolve().parents[2]
UNSIGNED_SPEC = ROOT / "src" / "tau_specs" / "perceptron_2input_single_output_v1.tau"
SIGNED_OFFSET_SPEC = ROOT / "src" / "tau_specs" / "perceptron_2input_signed_offset_v1.tau"
MARGIN_SPEC = ROOT / "src" / "tau_specs" / "perceptron_2input_margin_v2.tau"
THREE_INPUT_SPEC = ROOT / "src" / "tau_specs" / "perceptron_3input_single_output_v3.tau"


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


def test_tau_margin_gated_perceptron_two_input_experiment() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=MARGIN_SPEC,
        steps=[
            {"i1": 2, "i2": 3, "i3": 4, "i4": 5, "i5": 1, "i6": 20, "i7": 1, "i8": 4},
            {"i1": 2, "i2": 1, "i3": 1, "i4": 2, "i5": 0, "i6": 10, "i7": 0, "i8": 5},
            {"i1": 2, "i2": 3, "i3": 4, "i4": 5, "i5": 1, "i6": 20, "i7": 1, "i8": 5},
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o1"] == 1
    assert outputs[1]["o1"] == 1
    assert outputs[2]["o1"] == 0


def test_tau_three_input_perceptron_experiment() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=THREE_INPUT_SPEC,
        steps=[
            {"i1": 2, "i2": 3, "i3": 1, "i4": 4, "i5": 5, "i6": 6, "i7": 1, "i8": 20, "i9": 1},
            {"i1": 2, "i2": 1, "i3": 1, "i4": 1, "i5": 2, "i6": 1, "i7": 0, "i8": 10, "i9": 0},
            {"i1": 1, "i2": 1, "i3": 1, "i4": 2, "i5": 2, "i6": 2, "i7": 1, "i8": 7, "i9": 1},
        ],
        timeout_s=60.0,
    )

    steps = [
        {"i1": 2, "i2": 3, "i3": 1, "i4": 4, "i5": 5, "i6": 6, "i7": 1, "i8": 20, "i9": 1},
        {"i1": 2, "i2": 1, "i3": 1, "i4": 1, "i5": 2, "i6": 1, "i7": 0, "i8": 10, "i9": 0},
        {"i1": 1, "i2": 1, "i3": 1, "i4": 2, "i5": 2, "i6": 2, "i7": 1, "i8": 7, "i9": 1},
    ]
    for idx, step in enumerate(steps):
        activation = (step["i1"] * step["i4"]) + (step["i2"] * step["i5"]) + (step["i3"] * step["i6"]) + step["i7"]
        expected = 1 if ((activation >= step["i8"] and step["i9"] == 1) or (activation < step["i8"] and step["i9"] == 0)) else 0
        assert outputs[idx]["o1"] == expected
