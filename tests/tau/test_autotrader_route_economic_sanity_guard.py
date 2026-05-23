from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps_spec_mode

SPEC_PATH = Path("src/tau_specs/recommended/autotrader_route_economic_sanity_guard_v1.tau")


def test_autotrader_route_economic_sanity_guard_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps_spec_mode(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=[
            {
                "i1": 1,
                "i2": 1,
                "i3": 1,
                "i4": 1,
                "i5": 1,
                "i6": 1,
                "i7": 0,
                "i8": 2500,
                "i9": 2000,
                "i10": 800,
                "i11": 10000,
                "i12": 9000,
                "i13": 5000,
            },
            {
                "i1": 1,
                "i2": 1,
                "i3": 1,
                "i4": 1,
                "i5": 0,
                "i6": 1,
                "i7": 1,
                "i8": 2500,
                "i9": 2000,
                "i10": 800,
                "i11": 10000,
                "i12": 9000,
                "i13": 5000,
            },
            {
                "i1": 1,
                "i2": 1,
                "i3": 1,
                "i4": 1,
                "i5": 1,
                "i6": 1,
                "i7": 0,
                "i8": 10000,
                "i9": 2000,
                "i10": 800,
                "i11": 10000,
                "i12": 9000,
                "i13": 5000,
            },
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o5"] == 1
    assert outputs[1]["o1"] == 0
    assert outputs[1]["o5"] == 0
    assert outputs[2]["o2"] == 1
    assert outputs[2]["o5"] == 0
