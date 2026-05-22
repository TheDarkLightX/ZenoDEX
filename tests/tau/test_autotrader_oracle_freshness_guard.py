from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps

SPEC_PATH = Path("src/tau_specs/recommended/autotrader_oracle_freshness_guard_v1.tau")


def test_autotrader_oracle_freshness_guard_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=[
            {"i1": 10, "i2": 8, "i3": 3},
            {"i1": 10, "i2": 6, "i3": 3},
            {"i1": 10, "i2": 11, "i3": 3},
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o1"] == 1
    assert outputs[1]["o1"] == 0
    assert outputs[2]["o1"] == 0
