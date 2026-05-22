from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps_spec_mode

SPEC_PATH = Path("src/tau_specs/recommended/autotrader_nonce_guard_v1.tau")


def test_autotrader_nonce_guard_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps_spec_mode(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=[
            {"i1": 9, "i2": 8, "i3": 9},
            {"i1": 11, "i2": 8, "i3": 9},
            {"i1": 9, "i2": 8, "i3": 10},
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o4"] == 1
    assert outputs[1]["o4"] == 0
    assert outputs[2]["o4"] == 0
