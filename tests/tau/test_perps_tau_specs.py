from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps

ROOT = Path(__file__).resolve().parents[2]


def test_perp_bounty_shock_guard_v1_trace() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    spec_path = ROOT / "src/tau_specs/recommended/perp_bounty_shock_guard_v1.tau"
    assert spec_path.exists(), f"missing spec: {spec_path}"

    steps = [
        # Open positions + penalty increase => reject.
        {"i1": 1, "i2": 50, "i3": 60, "i4": 100_000_000, "i5": 100_000_000},
        # Open positions + bounty threshold decrease => reject.
        {"i1": 1, "i2": 50, "i3": 40, "i4": 100_000_000, "i5": 50_000_000},
        # Open positions + hardening direction => accept.
        {"i1": 1, "i2": 50, "i3": 40, "i4": 100_000_000, "i5": 120_000_000},
        # No open positions => allow (guard inactive).
        {"i1": 0, "i2": 50, "i3": 80, "i4": 100_000_000, "i5": 10_000_000},
        # Open positions + both shocks => reject.
        {"i1": 1, "i2": 50, "i3": 80, "i4": 100_000_000, "i5": 10_000_000},
    ]

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=spec_path,
        steps=steps,
        timeout_s=60.0,
    )

    expected = [
        {"o1": 1, "o2": 0, "o3": 1, "o4": 0},
        {"o1": 0, "o2": 1, "o3": 1, "o4": 0},
        {"o1": 0, "o2": 0, "o3": 0, "o4": 1},
        {"o1": 0, "o2": 0, "o3": 0, "o4": 1},
        {"o1": 1, "o2": 1, "o3": 1, "o4": 0},
    ]

    for idx, exp in enumerate(expected):
        got = outputs.get(idx, {})
        for name, exp_val in exp.items():
            assert got.get(name) == exp_val, f"step {idx}: {name} expected {exp_val}, got {got.get(name)}"


def test_perp_tau_ingress_schema_guard_v1_trace() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    spec_path = ROOT / "src/tau_specs/recommended/perp_tau_ingress_schema_guard_v1.tau"
    assert spec_path.exists(), f"missing spec: {spec_path}"

    steps = [
        # Signed ingress with canonical module, market, version, fields, and host projection.
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 0, "i9": 1, "i10": 0, "i11": 1},
        # Oracle ingress is accepted through the mutually exclusive oracle auth path.
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 0, "i8": 1, "i9": 0, "i10": 1, "i11": 1},
        # Unknown or non-one-hot action selection rejects the final schema guard.
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 0, "i6": 0, "i7": 1, "i8": 0, "i9": 1, "i10": 0, "i11": 1},
        # Selecting both auth modes is fail-closed even when both credentials are otherwise valid.
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
        # Host projection mismatch rejects the precondition bundle and final schema guard.
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 0, "i9": 1, "i10": 0, "i11": 0},
    ]

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=spec_path,
        steps=steps,
        timeout_s=60.0,
    )

    expected = [
        {"o1": 1, "o2": 1, "o3": 1, "o4": 1},
        {"o1": 1, "o2": 1, "o3": 1, "o4": 1},
        {"o1": 0, "o2": 1, "o3": 1, "o4": 0},
        {"o1": 1, "o2": 0, "o3": 1, "o4": 0},
        {"o1": 1, "o2": 1, "o3": 0, "o4": 0},
    ]

    for idx, exp in enumerate(expected):
        got = outputs.get(idx, {})
        for name, exp_val in exp.items():
            assert got.get(name) == exp_val, f"step {idx}: {name} expected {exp_val}, got {got.get(name)}"
