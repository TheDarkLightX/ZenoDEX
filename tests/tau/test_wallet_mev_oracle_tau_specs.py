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
def test_wallet_recovery_envelope_guard_v1_blocks_recovery_disaster_states(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = {
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
    }
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "wallet_recovery_envelope_guard_v1.tau",
        [
            good,
            {**good, "i2": 0},
            {**good, "i3": 0},
            {**good, "i5": 0},
            {**good, "i8": 0},
            {**good, "i9": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o2"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o2"] == 0
    assert outputs[2]["o1"] == 0 and outputs[2]["o2"] == 0
    assert outputs[3]["o1"] == 0 and outputs[3]["o2"] == 0
    assert outputs[4]["o1"] == 0 and outputs[4]["o2"] == 0
    assert outputs[5]["o1"] == 1 and outputs[5]["o2"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_key_rotation_admission_guard_v1_preserves_live_paths(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = {f"i{idx}": 1 for idx in range(1, 13)}
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "key_rotation_admission_guard_v1.tau",
        [
            good,
            {**good, "i4": 0},
            {**good, "i7": 0},
            {**good, "i9": 0},
            {**good, "i10": 0},
            {**good, "i1": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o2"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o2"] == 0
    assert outputs[2]["o1"] == 0 and outputs[2]["o2"] == 0
    assert outputs[3]["o1"] == 0 and outputs[3]["o2"] == 0
    assert outputs[4]["o1"] == 0 and outputs[4]["o2"] == 0
    assert outputs[5]["o1"] == 0 and outputs[5]["o2"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_sss_recovery_share_quorum_guard_v1_rejects_bad_share_sets(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = {
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
    }
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "sss_recovery_share_quorum_guard_v1.tau",
        [
            good,
            {**good, "i2": 0},
            {**good, "i7": 0},
            {**good, "i3": 0},
            {**good, "i6": 0},
            {**good, "i9": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o2"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o2"] == 0
    assert outputs[2]["o1"] == 0 and outputs[2]["o2"] == 0
    assert outputs[3]["o1"] == 0 and outputs[3]["o2"] == 0
    assert outputs[4]["o1"] == 0 and outputs[4]["o2"] == 0
    assert outputs[5]["o1"] == 1 and outputs[5]["o2"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_mev_batch_atomic_replay_guard_v1_blocks_ordering_and_atomicity_failures(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = {f"i{idx}": 1 for idx in range(1, 12)}
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "mev_batch_atomic_replay_guard_v1.tau",
        [
            good,
            {**good, "i3": 0},
            {**good, "i4": 0},
            {**good, "i5": 0},
            {**good, "i7": 0},
            {**good, "i9": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o2"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o2"] == 0
    assert outputs[2]["o1"] == 0 and outputs[2]["o2"] == 0
    assert outputs[3]["o1"] == 0 and outputs[3]["o2"] == 0
    assert outputs[4]["o1"] == 0 and outputs[4]["o2"] == 0
    assert outputs[5]["o1"] == 0 and outputs[5]["o2"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_oracle_epoch_equivocation_guard_v1_blocks_epoch_and_equivocation_faults(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = {f"i{idx}": 1 for idx in range(1, 12)}
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "oracle_epoch_equivocation_guard_v1.tau",
        [
            good,
            {**good, "i3": 0},
            {**good, "i5": 0},
            {**good, "i6": 0},
            {**good, "i8": 0},
            {**good, "i10": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o2"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o2"] == 0
    assert outputs[2]["o1"] == 0 and outputs[2]["o2"] == 0
    assert outputs[3]["o1"] == 0 and outputs[3]["o2"] == 0
    assert outputs[4]["o1"] == 0 and outputs[4]["o2"] == 0
    assert outputs[5]["o1"] == 1 and outputs[5]["o2"] == 0
