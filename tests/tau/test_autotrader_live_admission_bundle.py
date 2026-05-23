from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps_spec_mode

SPEC_PATH = Path("src/tau_specs/recommended/autotrader_live_admission_bundle_v1.tau")


def test_autotrader_live_admission_bundle_traces() -> None:
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
                "i7": 1,
                "i8": 1,
                "i9": 1,
                "i10": 1,
                "i11": 1,
            },
            {
                "i1": 1,
                "i2": 1,
                "i3": 0,
                "i4": 1,
                "i5": 1,
                "i6": 1,
                "i7": 1,
                "i8": 1,
                "i9": 1,
                "i10": 1,
                "i11": 1,
            },
            {
                "i1": 0,
                "i2": 1,
                "i3": 1,
                "i4": 1,
                "i5": 1,
                "i6": 1,
                "i7": 1,
                "i8": 1,
                "i9": 1,
                "i10": 1,
                "i11": 1,
            },
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o12"] == 1
    assert outputs[1]["o12"] == 0
    assert outputs[2]["o12"] == 0
