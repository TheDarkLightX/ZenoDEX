from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps

SPEC_PATH = Path("src/tau_specs/recommended/autotrader_system_compose_v1.tau")


def test_autotrader_system_compose_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=[
            {
                "i1": 0,
                "i2": 0,
                "i3": 0,
                "i4": 0,
                "i5": 0,
                "i6": 0,
                "i7": 0,
                "i8": 0,
                "i9": 0,
                "i10": 0,
                "i11": 0,
                "i12": 0,
                "i13": 0,
                "i14": 0,
                "i15": 0,
                "i16": 0,
                "i17": 0,
                "i18": 0,
                "i19": 0,
            },
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
                "i12": 1,
                "i13": 1,
                "i14": 1,
                "i15": 1,
                "i16": 1,
                "i17": 1,
                "i18": 1,
                "i19": 1,
            },
            {
                "i1": 1,
                "i2": 1,
                "i3": 1,
                "i4": 1,
                "i5": 1,
                "i6": 1,
                "i7": 1,
                "i8": 0,
                "i9": 1,
                "i10": 1,
                "i11": 1,
                "i12": 1,
                "i13": 1,
                "i14": 1,
                "i15": 1,
                "i16": 1,
                "i17": 1,
                "i18": 1,
                "i19": 1,
            },
        ],
        timeout_s=60.0,
    )

    assert outputs[0]["o3"] == 1
    assert outputs[1]["o3"] == 1
    assert outputs[2]["o3"] == 0
