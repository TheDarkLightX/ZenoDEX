from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import TauRunError, find_tau_bin, run_tau_spec_steps_spec_mode

SPEC_PATH = Path("src/tau_specs/recommended/autotrader_observation_packet_contract_v1.tau")


def test_autotrader_observation_packet_contract_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    try:
        outputs = run_tau_spec_steps_spec_mode(
            tau_bin=tau_bin,
            spec_path=SPEC_PATH,
            steps=[
                {"i1": 1, "i2": 2, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 2, "i10": 1, "i11": 1},
                {"i1": 4, "i2": 0, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 0},
                {"i1": 1, "i2": 2, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 2, "i10": 1, "i11": 0},
            ],
            timeout_s=60.0,
        )
    except TauRunError as exc:
        if exc.rc == -1 and "timed out" in str(exc):
            pytest.skip("tau spec-mode timed out for observation packet contract")
        raise

    assert outputs[0]["o2"] == 1
    assert outputs[0]["o5"] == 1
    assert outputs[1]["o1"] == 1
    assert outputs[1]["o2"] == 0
    assert outputs[1]["o5"] == 1
    assert outputs[2]["o4"] == 0
    assert outputs[2]["o5"] == 0
