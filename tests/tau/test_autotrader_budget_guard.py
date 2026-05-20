from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps

SPEC_PATH = Path("src/tau_specs/recommended/autotrader_budget_guard_v1.tau")


def test_autotrader_budget_guard_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=[
            {"i1": 100, "i2": 50, "i3": 100, "i4": 500, "i5": 150, "i6": 0},
            {"i1": 100, "i2": 150, "i3": 100, "i4": 500, "i5": 250, "i6": 0},
            {"i1": 100, "i2": 50, "i3": 100, "i4": 500, "i5": 150, "i6": 1},
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o1"] == 1
    assert outputs[1]["o1"] == 0
    assert outputs[2]["o1"] == 0
