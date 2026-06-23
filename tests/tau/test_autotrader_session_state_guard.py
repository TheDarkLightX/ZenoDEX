from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps

SPEC_PATH = Path("src/tau_specs/recommended/autotrader_session_state_guard_v1.tau")


def test_autotrader_session_state_guard_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=[
            {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 0, "i6": 5, "i7": 0},
            {"i1": 0, "i2": 1, "i3": 1, "i4": 1, "i5": 0, "i6": 5, "i7": 0},
            {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 5, "i7": 5},
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o6"] == 1
    assert outputs[1]["o6"] == 0
    assert outputs[2]["o6"] == 0
