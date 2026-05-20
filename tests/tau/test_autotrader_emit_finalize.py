from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps_spec_mode

SPEC_PATH = Path("src/tau_specs/recommended/autotrader_emit_finalize_v1.tau")


def test_autotrader_emit_finalize_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps_spec_mode(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=[
            {"i1": 1, "i2": 1, "i3": 1},
            {"i1": 1, "i2": 1, "i3": 0},
            {"i1": 0, "i2": 0, "i3": 0},
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o1"] == 1
    assert outputs[1]["o1"] == 0
    assert outputs[2]["o1"] == 1
