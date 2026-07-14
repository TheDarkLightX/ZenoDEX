"""Adversarial evidence for the authority-false Spot V7 Firecracker join."""

from __future__ import annotations

import json
from dataclasses import dataclass, replace
from typing import Any

import pytest

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_firecracker_authority import (
    _bind_governed_firecracker_spot_v7_settlement_v1,
)
from src.integration._zrpf_spot_v7_firecracker_execution_binding import (
    SPOT_V7_FIRECRACKER_STATIC_BINDING_BLOCKER_V1,
    SpotV7FirecrackerExecutionBindingRejectV1,
    _AuthorityFalseSpotV7FirecrackerExecutionBindingV1,
    _derive_authority_false_spot_v7_execution_record_v1,
    _ObservedSpotV7FirecrackerArtifactSetV1,
    _ProposedSpotV7FirecrackerExecutionPolicyV1,
    _verify_authority_false_spot_v7_firecracker_execution_binding_v1,
)
from tests.integration.test_zrpf_spot_v7_atomic_settlement_store import (
    _bound_committed_output,
)
from tools import zrpf_v3_firecracker_output_protocol as protocol

_AUTHORITY_NONCLAIMS = {
    "chroot_base_live_verified": False,
    "cgroup_limits_live_verified": False,
    "cgroup_membership_live_verified": False,
    "descriptor_bound_exec_handoff_verified": False,
    "external_watchdog_live_verified": False,
    "firecracker_jailer_live_verified": False,
    "io_backing_device_binding_live_verified": False,
    "network_namespace_exclusive_live_verified": False,
    "network_namespace_live_verified": False,
    "production_authority": False,
    "root_owned_launcher_live_verified": False,
    "sandbox_escape_resistance": False,
    "settlement_authority": False,
}


def _digest(seed: int) -> str:
    return f"{seed:064x}"


def _canonical(document: object) -> bytes:
    return (
        json.dumps(document, ensure_ascii=True, separators=(",", ":"), sort_keys=True)
        + "\n"
    ).encode("ascii")


def _launch_document(*, cgroup_relative_path: str) -> dict[str, Any]:
    return {
        "authority": dict(_AUTHORITY_NONCLAIMS),
        "cgroup_relative_path": cgroup_relative_path,
        "control_facts": {
            "cgroup_descendant_set_verified": True,
            "executable_bytes_reverified_after_spawn": True,
            "network_namespace_membership_verified": True,
        },
        "jailer_pid": 42,
        "observed_process_count": 2,
        "schema": "zenodex/zrpf_firecracker_jailer_launch_observation/v1",
        "scope": "live_process_placement_control_only",
    }


def _finish_document() -> dict[str, Any]:
    return {
        "authority": dict(_AUTHORITY_NONCLAIMS),
        "control_facts": {
            "cgroup_populated_zero_verified": True,
            "cgroup_removed_after_kill": True,
            "network_namespace_path_identity_preserved": True,
            "process_exit_observed": True,
        },
        "exit_code": 0,
        "schema": "zenodex/zrpf_firecracker_jailer_finish_observation/v1",
        "scope": "live_process_exit_and_cgroup_teardown_control_only",
    }


@dataclass(slots=True)
class _Fixture:
    policy: _ProposedSpotV7FirecrackerExecutionPolicyV1
    observed_artifacts: _ObservedSpotV7FirecrackerArtifactSetV1
    request_bytes: bytes
    output_device_bytes: bytes
    candidate: _SpotV7SettlementCandidateInputV1
    launch_observation_bytes: bytes
    finish_observation_bytes: bytes


def _fixture() -> _Fixture:
    bound, _, _ = _bound_committed_output()
    candidate = bound.candidate
    runtime_manifest = _canonical(
        {
            "profile": "spot_v7_candidate_runtime",
            "schema": "zenodex/test_runtime_manifest/v1",
        }
    )
    cgroup_relative_path = "zenodex01/zrpf0001/run00001"
    policy = _ProposedSpotV7FirecrackerExecutionPolicyV1(
        exact_runtime_manifest_bytes=runtime_manifest,
        run_nonce_256=bytes([0x41]) * 32,
        input_drive_sha256=bytes.fromhex(_digest(0x42)),
        replay_intent_sha256=bytes.fromhex(_digest(0x43)),
        artifact_set_id=_digest(0x44),
        firecracker_sha256=_digest(0x45),
        jailer_sha256=_digest(0x46),
        guest_kernel_sha256=_digest(0x47),
        rootfs_sha256=_digest(0x48),
        input_image_sha256=_digest(0x49),
        guest_init_sha256=_digest(0x4A),
        cgroup_relative_path=cgroup_relative_path,
    )
    artifacts = _ObservedSpotV7FirecrackerArtifactSetV1(
        runtime_manifest_sha256=policy.runtime_manifest_sha256,
        artifact_set_id=policy.artifact_set_id,
        firecracker_sha256=policy.firecracker_sha256,
        jailer_sha256=policy.jailer_sha256,
        guest_kernel_sha256=policy.guest_kernel_sha256,
        rootfs_sha256=policy.rootfs_sha256,
        input_image_sha256=policy.input_image_sha256,
        guest_init_sha256=policy.guest_init_sha256,
    )
    request = protocol.FirecrackerRequestV1.validated(
        run_nonce_256=policy.run_nonce_256,
        runtime_manifest_sha256=bytes.fromhex(policy.runtime_manifest_sha256),
        input_drive_sha256=policy.input_drive_sha256,
        replay_intent_sha256=policy.replay_intent_sha256,
    )
    output_device = protocol.build_committed_output(
        request,
        observed_input_drive_sha256=request.input_drive_sha256,
        payload=candidate.exact_firecracker_output_bytes,
    )
    launch_bytes = _canonical(
        _launch_document(cgroup_relative_path=cgroup_relative_path)
    )
    finish_bytes = _canonical(_finish_document())
    record = _derive_authority_false_spot_v7_execution_record_v1(
        policy=policy,
        observed_artifacts=artifacts,
        request_bytes=request.encode(),
        output_device_bytes=output_device,
        candidate=candidate,
        launch_observation_bytes=launch_bytes,
        finish_observation_bytes=finish_bytes,
    )
    candidate = replace(candidate, exact_firecracker_execution_record_bytes=record)
    return _Fixture(
        policy=policy,
        observed_artifacts=artifacts,
        request_bytes=request.encode(),
        output_device_bytes=output_device,
        candidate=candidate,
        launch_observation_bytes=launch_bytes,
        finish_observation_bytes=finish_bytes,
    )


def _verify(values: _Fixture) -> _AuthorityFalseSpotV7FirecrackerExecutionBindingV1:
    return _verify_authority_false_spot_v7_firecracker_execution_binding_v1(
        policy=values.policy,
        observed_artifacts=values.observed_artifacts,
        request_bytes=values.request_bytes,
        output_device_bytes=values.output_device_bytes,
        candidate=values.candidate,
        launch_observation_bytes=values.launch_observation_bytes,
        finish_observation_bytes=values.finish_observation_bytes,
    )


def test_exact_static_join_remains_authority_false_and_cannot_enter_binder() -> None:
    values = _fixture()

    assessment = _verify(values)

    assert assessment.static_binding_verified is True
    assert assessment.governed_execution_result_verified is False
    assert assessment.firecracker_execution_verified is False
    assert assessment.settlement_authority is False
    assert assessment.production_authority is False
    assert assessment.authority_blocker == (
        SPOT_V7_FIRECRACKER_STATIC_BINDING_BLOCKER_V1
    )
    assert assessment.execution_record_bytes == (
        values.candidate.exact_firecracker_execution_record_bytes
    )
    with pytest.raises(TypeError, match="governed jailed Firecracker execution"):
        _bind_governed_firecracker_spot_v7_settlement_v1(
            runtime_execution=assessment,
        )


@pytest.mark.parametrize(
    ("mutation", "expected_code"),
    (
        ("nonce", "request_nonce_binding"),
        ("runtime_manifest", "request_runtime_manifest_binding"),
        ("input", "request_input_binding"),
        ("intent", "request_intent_binding"),
        ("artifact", "artifact_binding"),
        ("launch_cgroup", "lifecycle_launch_binding"),
        ("finish_teardown", "lifecycle_finish_binding"),
        ("output_commit", "output_output_commit"),
        ("execution_record", "execution_record_binding"),
    ),
)
def test_each_static_join_boundary_rejects_exact_mutation(
    mutation: str,
    expected_code: str,
) -> None:
    values = _fixture()
    policy = values.policy
    artifacts = values.observed_artifacts
    if mutation == "nonce":
        values.policy = replace(policy, run_nonce_256=bytes([0x99]) * 32)
    elif mutation == "runtime_manifest":
        changed_policy = replace(
            policy,
            exact_runtime_manifest_bytes=policy.exact_runtime_manifest_bytes + b" ",
        )
        values.policy = changed_policy
        values.observed_artifacts = replace(
            artifacts,
            runtime_manifest_sha256=changed_policy.runtime_manifest_sha256,
        )
    elif mutation == "input":
        values.policy = replace(
            policy,
            input_drive_sha256=bytes.fromhex(_digest(0x99)),
        )
    elif mutation == "intent":
        values.policy = replace(
            policy,
            replay_intent_sha256=bytes.fromhex(_digest(0x99)),
        )
    elif mutation == "artifact":
        values.observed_artifacts = replace(
            artifacts,
            guest_init_sha256=_digest(0x99),
        )
    elif mutation == "launch_cgroup":
        values.launch_observation_bytes = _canonical(
            _launch_document(cgroup_relative_path="zenodex01/zrpf0001/other0001")
        )
    elif mutation == "finish_teardown":
        document = _finish_document()
        document["control_facts"]["cgroup_populated_zero_verified"] = False
        values.finish_observation_bytes = _canonical(document)
    elif mutation == "output_commit":
        raw = bytearray(values.output_device_bytes)
        raw[-1] ^= 1
        values.output_device_bytes = bytes(raw)
    else:
        candidate = values.candidate
        values.candidate = replace(
            candidate,
            exact_firecracker_execution_record_bytes=(
                candidate.exact_firecracker_execution_record_bytes + b"x"
            ),
        )

    with pytest.raises(SpotV7FirecrackerExecutionBindingRejectV1) as captured:
        _verify(values)

    assert captured.value.code == expected_code


def test_request_profile_mutation_rejects_before_output_authority() -> None:
    values = _fixture()
    request_bytes = bytearray(values.request_bytes)
    request_bytes[48] ^= 1
    values.request_bytes = bytes(request_bytes)

    with pytest.raises(SpotV7FirecrackerExecutionBindingRejectV1) as captured:
        _verify(values)

    assert captured.value.code == "output_request_profile"


def test_lifecycle_documents_are_exact_canonical_data_not_attestation() -> None:
    values = _fixture()
    launch = json.loads(values.launch_observation_bytes)
    values.launch_observation_bytes = json.dumps(launch, indent=2).encode("ascii")

    with pytest.raises(SpotV7FirecrackerExecutionBindingRejectV1) as captured:
        _verify(values)

    assert captured.value.code == "lifecycle_launch_noncanonical"


def test_authority_claim_inside_runner_document_rejects() -> None:
    values = _fixture()
    launch = json.loads(values.launch_observation_bytes)
    launch["authority"]["settlement_authority"] = True
    values.launch_observation_bytes = _canonical(launch)

    with pytest.raises(SpotV7FirecrackerExecutionBindingRejectV1) as captured:
        _verify(values)

    assert captured.value.code == "lifecycle_launch_authority"
