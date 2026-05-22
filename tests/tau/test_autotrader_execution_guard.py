from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps

SPEC_PATH = Path("src/tau_specs/recommended/autotrader_execution_guard_v1.tau")


def test_autotrader_execution_guard_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=[
            {"i1": 10, "i2": 1, "i3": 100, "i4": 1, "i5": 5, "i6": 4, "i7": 2, "i8": 2, "i9": 3},
            {"i1": 0, "i2": 1, "i3": 100, "i4": 0, "i5": 0, "i6": 4, "i7": 0, "i8": 1, "i9": 3},
            {"i1": 10, "i2": 1, "i3": 100, "i4": 1, "i5": 9, "i6": 4, "i7": 0, "i8": 1, "i9": 3},
            {"i1": 10, "i2": 1, "i3": 100, "i4": 0, "i5": 0, "i6": 4, "i7": 0, "i8": 4, "i9": 3},
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o1"] == 1
    assert outputs[1]["o1"] == 0
    assert outputs[2]["o1"] == 0
    assert outputs[3]["o1"] == 0
