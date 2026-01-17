# [TESTER] v1

from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


SPEC_PATH = Path(__file__).resolve().parents[2] / "src" / "tau_specs" / "proof_mining_reward_32_v1.tau"


def test_proof_mining_reward_gate_traces() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    steps = [
        # Accept: epoch 0, reward == base.
        {"i1": 1000, "i2": 0, "i3": 1000, "i4": 5000, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1},
        # Reject: wrong reward for epoch 1 (expected 500).
        {"i1": 1000, "i2": 1, "i3": 1000, "i4": 5000, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1},
        # Reject: one failed flag.
        {"i1": 1000, "i2": 0, "i3": 1000, "i4": 5000, "i5": 1, "i6": 1, "i7": 0, "i8": 1, "i9": 1},
        # Reject: pool too small.
        {"i1": 1000, "i2": 0, "i3": 1000, "i4": 999, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1},
        # Accept: clamp-to-1 for small base at epoch 7.
        {"i1": 1, "i2": 7, "i3": 1, "i4": 10, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1},
        # Reject: epoch out of range.
        {"i1": 1000, "i2": 8, "i3": 1, "i4": 10_000, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1},
    ]

    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=SPEC_PATH, steps=steps, timeout_s=120.0)

    assert outputs[0]["o4"] == 1
    assert outputs[1]["o4"] != 1
    assert outputs[2]["o4"] != 1
    assert outputs[3]["o4"] != 1
    assert outputs[4]["o4"] == 1
    assert outputs[5]["o4"] != 1
