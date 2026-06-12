from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


ROOT = Path(__file__).resolve().parents[2]
SPEC_PATH = ROOT / "src" / "tau_specs" / "recommended" / "settlement_v1_proof_gate.tau"


def test_settlement_v1_proof_gate_trace() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    assert SPEC_PATH.exists(), f"missing spec: {SPEC_PATH}"

    common = {
        "i5": 10,
        "i6": 11,
        "i7": 12,
        "i8": 1,
        "i9": 1,
        "i10": 1,
        "i11": 1,
        "i12": 1,
    }
    steps = [
        {"i1": 1, "i2": 2, "i3": 3, "i4": 4, **common},
        {"i1": 1, "i2": 1, "i3": 3, "i4": 4, **common},
        {"i1": 1, "i2": 2, "i3": 2, "i4": 4, **common},
        {"i1": 1, "i2": 2, "i3": 3, "i4": 3, **common},
        {"i1": 4, "i2": 3, "i3": 2, "i4": 1, **common},
    ]
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=steps,
        timeout_s=60.0,
    )

    expected = [1, 0, 0, 0, 0]
    for idx, expected_o1 in enumerate(expected):
        actual_o1 = outputs.get(idx, {}).get("o1")
        assert actual_o1 == expected_o1, (
            f"settlement_v1_proof_gate.tau step {idx}: expected o1={expected_o1}, got {actual_o1}"
        )
        assert outputs.get(idx, {}).get("o7") == expected_o1
