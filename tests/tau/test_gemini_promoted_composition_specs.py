from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


ROOT = Path(__file__).resolve().parents[2]
SPEC_ROOT = ROOT / "src" / "tau_specs" / "recommended"
TAU_PROFILES = ("runtime", "latest")


def _tau_bin(profile: str) -> str | None:
    return find_tau_bin(ROOT, profile=profile)


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_cross_module_conservation_consistency_v1_blocks_omitted_or_spoofed_witnesses(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1}
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "cross_module_conservation_consistency_v1.tau",
        [
            good,
            {**good, "i4": 0},
            {**good, "i6": 0},
            {**good, "i7": 0},
            {**good, "i8": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o4"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o2"] == 0 and outputs[1]["o4"] == 0
    assert outputs[2]["o1"] == 1 and outputs[2]["o4"] == 0
    assert outputs[3]["o1"] == 1 and outputs[3]["o2"] == 0 and outputs[3]["o4"] == 0
    assert outputs[4]["o3"] == 1 and outputs[4]["o4"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_atomic_batch_commit_guard_v1_requires_abort_containment_on_partial_failure(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    commit = {f"i{idx}": 1 for idx in range(1, 13)}
    partial_abort = {**commit, "i4": 0, "i7": 0, "i8": 1, "i9": 1, "i10": 1}
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "atomic_batch_commit_guard_v1.tau",
        [
            commit,
            partial_abort,
            {**commit, "i4": 0, "i7": 1, "i8": 1, "i9": 1, "i10": 1},
            {**partial_abort, "i9": 0},
            {**commit, "i11": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o5"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o2"] == 1 and outputs[1]["o3"] == 1 and outputs[1]["o5"] == 1
    assert outputs[2]["o2"] == 0 and outputs[2]["o5"] == 0
    assert outputs[3]["o3"] == 0 and outputs[3]["o5"] == 0
    assert outputs[4]["o4"] == 1 and outputs[4]["o5"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_dispute_window_finality_guard_v1_rejects_unbounded_or_challenged_finality(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = {f"i{idx}": 1 for idx in range(1, 11)}
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "dispute_window_finality_guard_v1.tau",
        [
            good,
            {**good, "i2": 0},
            {**good, "i3": 0},
            {**good, "i4": 0},
            {**good, "i8": 0},
            {**good, "i9": 0},
            {**good, "i1": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o5"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o5"] == 0
    assert outputs[2]["o2"] == 0 and outputs[2]["o5"] == 0
    assert outputs[3]["o3"] == 0 and outputs[3]["o5"] == 0
    assert outputs[4]["o3"] == 0 and outputs[4]["o5"] == 0
    assert outputs[5]["o4"] == 1 and outputs[5]["o5"] == 0
    assert outputs[6]["o4"] == 0 and outputs[6]["o5"] == 0
