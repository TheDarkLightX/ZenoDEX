from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


ROOT = Path(__file__).resolve().parents[2]
SPEC_ROOT = ROOT / "src" / "tau_specs" / "recommended"
TAU_PROFILES = ("runtime", "latest")


def _tau_bin(profile: str) -> str | None:
    return find_tau_bin(ROOT, profile=profile)


def _ones(first: int, last: int) -> dict[str, int]:
    return {f"i{idx}": 1 for idx in range(first, last + 1)}


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_secure_signer_operation_admission_v1_blocks_unsafe_key_ops(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = _ones(1, 13)
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "secure_signer_operation_admission_v1.tau",
        [
            good,
            {**good, "i2": 0},
            {**good, "i5": 0},
            {**good, "i9": 0},
            {**good, "i6": 0},
            {**good, "i12": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o6"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o6"] == 0
    assert outputs[2]["o2"] == 0 and outputs[2]["o6"] == 0
    assert outputs[3]["o4"] == 0 and outputs[3]["o6"] == 0
    assert outputs[4]["o3"] == 0 and outputs[4]["o6"] == 0
    assert outputs[5]["o5"] == 1 and outputs[5]["o6"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_runtime_action_capability_envelope_v1_rejects_mixed_or_overbroad_actions(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = _ones(1, 13)
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "runtime_action_capability_envelope_v1.tau",
        [
            good,
            {**good, "i2": 0},
            {**good, "i5": 0},
            {**good, "i8": 0},
            {**good, "i10": 0},
            {**good, "i12": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o6"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o6"] == 0
    assert outputs[2]["o2"] == 0 and outputs[2]["o6"] == 0
    assert outputs[3]["o3"] == 0 and outputs[3]["o6"] == 0
    assert outputs[4]["o4"] == 0 and outputs[4]["o6"] == 0
    assert outputs[5]["o5"] == 1 and outputs[5]["o6"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_incident_latch_reset_quorum_guard_v1_requires_full_reset_evidence(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    clear = _ones(1, 10)
    clear.update({"i1": 0, "i2": 0, "i3": 0})
    fault = {**clear, "i2": 1}
    previous_latched = {**clear, "i1": 1}
    reset = {**previous_latched, "i3": 1}
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "incident_latch_reset_quorum_guard_v1.tau",
        [
            clear,
            fault,
            previous_latched,
            reset,
            {**reset, "i4": 0},
            {**reset, "i9": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o2"] == 0 and outputs[0]["o3"] == 1
    assert outputs[1]["o2"] == 1 and outputs[1]["o3"] == 0
    assert outputs[2]["o2"] == 1 and outputs[2]["o3"] == 0
    assert outputs[3]["o1"] == 1 and outputs[3]["o2"] == 0 and outputs[3]["o3"] == 1
    assert outputs[4]["o1"] == 0 and outputs[4]["o2"] == 1
    assert outputs[5]["o1"] == 0 and outputs[5]["o2"] == 1


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_tau_policy_shadow_migration_gate_v1_requires_equivalence_and_fallback(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = _ones(1, 12)
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "tau_policy_shadow_migration_gate_v1.tau",
        [
            good,
            {**good, "i3": 0},
            {**good, "i5": 0},
            {**good, "i7": 0},
            {**good, "i10": 0},
            {**good, "i11": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o6"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o6"] == 0
    assert outputs[2]["o3"] == 0 and outputs[2]["o6"] == 0
    assert outputs[3]["o2"] == 0 and outputs[3]["o6"] == 0
    assert outputs[4]["o4"] == 0 and outputs[4]["o6"] == 0
    assert outputs[5]["o5"] == 1 and outputs[5]["o6"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_disaster_axis_safe_noop_guard_v1_contains_known_bad_axes(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = _ones(1, 12)
    good.update({"i2": 0, "i3": 0, "i4": 0, "i5": 0, "i6": 0, "i7": 0, "i8": 0, "i9": 0, "i10": 0})
    replay_axis = {**good, "i4": 1}
    safe_noop = {**replay_axis, "i8": 1, "i9": 1, "i10": 1}
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "disaster_axis_safe_noop_guard_v1.tau",
        [
            good,
            replay_axis,
            safe_noop,
            {**good, "i11": 0},
            {**safe_noop, "i9": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o1"] == 1 and outputs[0]["o3"] == 1 and outputs[0]["o4"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o2"] == 0 and outputs[1]["o4"] == 0
    assert outputs[2]["o1"] == 0 and outputs[2]["o2"] == 1 and outputs[2]["o3"] == 0 and outputs[2]["o4"] == 1
    assert outputs[3]["o3"] == 0 and outputs[3]["o4"] == 1
    assert outputs[4]["o2"] == 0 and outputs[4]["o4"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_payout_template_age_replay_envelope_v1_requires_real_timestamp_and_replay_clear(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = _ones(1, 11)
    good.update({"i3": 0})
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "payout_template_age_replay_envelope_v1.tau",
        [
            good,
            {**good, "i2": 0},
            {**good, "i3": 1},
            {**good, "i4": 0},
            {**good, "i6": 0},
            {**good, "i8": 0},
            {**good, "i10": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o6"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o6"] == 0
    assert outputs[2]["o1"] == 0 and outputs[2]["o6"] == 0
    assert outputs[3]["o2"] == 0 and outputs[3]["o6"] == 0
    assert outputs[4]["o3"] == 0 and outputs[4]["o6"] == 0
    assert outputs[5]["o4"] == 0 and outputs[5]["o6"] == 0
    assert outputs[6]["o5"] == 1 and outputs[6]["o6"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_public_testnet_node_admission_guard_v1_rejects_wrong_chain_or_demo_posture(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = _ones(1, 13)
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "public_testnet_node_admission_guard_v1.tau",
        [
            good,
            {**good, "i2": 0},
            {**good, "i7": 0},
            {**good, "i8": 0},
            {**good, "i11": 0},
            {**good, "i12": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o7"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o7"] == 0
    assert outputs[2]["o3"] == 0 and outputs[2]["o7"] == 0
    assert outputs[3]["o4"] == 0 and outputs[3]["o7"] == 0
    assert outputs[4]["o5"] == 0 and outputs[4]["o7"] == 0
    assert outputs[5]["o6"] == 1 and outputs[5]["o7"] == 0


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_release_artifact_manifest_binding_guard_v1_requires_hashes_ci_and_posture(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    good = _ones(1, 14)
    outputs = run_tau_spec_steps(
        tau_bin,
        SPEC_ROOT / "release_artifact_manifest_binding_guard_v1.tau",
        [
            good,
            {**good, "i3": 0},
            {**good, "i7": 0},
            {**good, "i10": 0},
            {**good, "i12": 0},
            {**good, "i13": 0},
        ],
        timeout_s=90.0,
    )

    assert outputs[0]["o5"] == 1
    assert outputs[1]["o1"] == 0 and outputs[1]["o5"] == 0
    assert outputs[2]["o2"] == 0 and outputs[2]["o5"] == 0
    assert outputs[3]["o3"] == 0 and outputs[3]["o5"] == 0
    assert outputs[4]["o3"] == 0 and outputs[4]["o5"] == 0
    assert outputs[5]["o4"] == 1 and outputs[5]["o5"] == 0
