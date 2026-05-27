from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


ROOT = Path(__file__).resolve().parents[2]
SPEC_ROOT = ROOT / "src" / "tau_specs" / "recommended"
DIGEST_A = 1234567890123456789012345678901234567890
DIGEST_B = DIGEST_A + 1
TAU_PROFILES = ("runtime", "latest")


def _tau_bin(profile: str) -> str | None:
    return find_tau_bin(ROOT, profile=profile)


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_commit_reveal_binding_guard_v1_trace(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "commit_reveal_binding_guard_v1.tau",
        [
            {"i1": DIGEST_A, "i2": DIGEST_A, "i3": 1, "i4": 1, "i5": 1, "i6": 1},
            {"i1": DIGEST_A, "i2": DIGEST_B, "i3": 1, "i4": 1, "i5": 1, "i6": 1},
            {"i1": DIGEST_A, "i2": DIGEST_A, "i3": 0, "i4": 1, "i5": 1, "i6": 1},
            {"i1": DIGEST_A, "i2": DIGEST_A, "i3": 1, "i4": 0, "i5": 1, "i6": 1},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o5"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o5"] == 0
    assert outputs[2]["o2"] == 0 and outputs[2]["o5"] == 0
    assert outputs[3]["o3"] == 0 and outputs[3]["o5"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_idempotency_window_guard_v1_trace(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "idempotency_window_guard_v1.tau",
        [
            {"i1": DIGEST_A, "i2": DIGEST_A, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1},
            {"i1": DIGEST_A, "i2": DIGEST_B, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1},
            {"i1": DIGEST_A, "i2": DIGEST_B, "i3": 0, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1},
            {"i1": DIGEST_A, "i2": DIGEST_A, "i3": 1, "i4": 1, "i5": 1, "i6": 0, "i7": 1, "i8": 1},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o5"] == 1
    assert outputs[1]["o3"] == 0 and outputs[1]["o5"] == 0
    assert outputs[2]["o4"] == 1 and outputs[2]["o5"] == 1
    assert outputs[3]["o4"] == 0 and outputs[3]["o5"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_isolated_margin_no_cascade_guard_v1_trace(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "isolated_margin_no_cascade_guard_v1.tau",
        [
            {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1},
            {"i1": 1, "i2": 0, "i3": 1, "i4": 1, "i5": 1},
            {"i1": 1, "i2": 1, "i3": 0, "i4": 1, "i5": 1},
            {"i1": 0, "i2": 1, "i3": 1, "i4": 1, "i5": 1},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o2"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o2"] == 0
    assert outputs[2]["o1"] == 0 and outputs[2]["o2"] == 0
    assert outputs[3]["o1"] == 0 and outputs[3]["o2"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_routing_decision_tree_guard_v1_trace(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "routing_decision_tree_guard_v1.tau",
        [
            {"i1": 100, "i2": 120, "i3": 0, "i4": 10, "i5": 1, "i6": 1, "i7": 1},
            {"i1": 120, "i2": 100, "i3": 20, "i4": 10, "i5": 2, "i6": 1, "i7": 1},
            {"i1": 120, "i2": 100, "i3": 5, "i4": 10, "i5": 1, "i6": 1, "i7": 1},
            {"i1": 120, "i2": 100, "i3": 20, "i4": 10, "i5": 1, "i6": 1, "i7": 1},
        ],
        timeout_s=90.0,
    )

    assert [outputs[idx]["o3"] for idx in range(4)] == [1, 1, 1, 0]


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_slippage_floor_invariant_guard_v1_trace(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "slippage_floor_invariant_guard_v1.tau",
        [
            {"i1": 1000, "i2": 1000, "i3": 1001, "i4": 1, "i5": 1},
            {"i1": 1000, "i2": 999, "i3": 1001, "i4": 1, "i5": 1},
            {"i1": 1000, "i2": 1000, "i3": 999, "i4": 1, "i5": 1},
        ],
        timeout_s=90.0,
    )

    assert [outputs[idx]["o4"] for idx in range(3)] == [1, 0, 0]
