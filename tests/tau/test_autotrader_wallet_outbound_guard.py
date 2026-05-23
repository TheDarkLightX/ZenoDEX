from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps

SPEC_PATH = Path("src/tau_specs/recommended/autotrader_wallet_outbound_guard_v1.tau")


def test_autotrader_wallet_outbound_guard_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=[
            {"i1": 50, "i2": 100, "i3": 7, "i4": 7, "i5": 1, "i6": 1, "i7": 1, "i8": 1},
            {"i1": 150, "i2": 100, "i3": 7, "i4": 7, "i5": 1, "i6": 1, "i7": 1, "i8": 1},
            {"i1": 150, "i2": 100, "i3": 8, "i4": 7, "i5": 0, "i6": 0, "i7": 0, "i8": 1},
            {"i1": 150, "i2": 100, "i3": 7, "i4": 7, "i5": 1, "i6": 1, "i7": 1, "i8": 0},
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o5"] == 1
    assert outputs[1]["o5"] == 0
    assert outputs[2]["o5"] == 1
    assert outputs[3]["o5"] == 1
