from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from tests.test_zrpf_v3_firecracker_runtime_manifest import (
    build_manifest_document,
    parse_manifest,
)
from tools import zrpf_v3_firecracker_artifact_set as artifact_set
from tools import zrpf_v3_firecracker_candidate_plan as candidate_plan
from tools import zrpf_v3_firecracker_runtime_manifest as runtime


def build_intent_document() -> dict[str, Any]:
    return {
        "expected_output_payload_sha256": _hash(b"accepted-transcript"),
        "expected_output_payload_size_bytes": len(b"accepted-transcript"),
        "input_bundle_root": _hash(b"input-bundle"),
        "input_drive_sha256": _hash(b"input-image"),
        "input_size_bytes": len(b"input-image"),
        "schema": candidate_plan.INTENT_SCHEMA,
    }


def parse_intent(
    document: dict[str, Any] | None = None,
) -> candidate_plan.ValidatedReplayIntentV1:
    selected = build_intent_document() if document is None else document
    return candidate_plan.parse_replay_intent_bytes(runtime.canonical_document_bytes(selected))


def test_candidate_plan_is_deterministic_path_free_and_non_executable() -> None:
    manifest = parse_manifest(build_manifest_document())
    intent = parse_intent()

    first = candidate_plan.compile_candidate_plan(manifest, intent)
    second = candidate_plan.compile_candidate_plan(manifest, intent)
    document = first.to_document()

    assert first.candidate_plan_id == second.candidate_plan_id
    assert first.canonical_bytes() == second.canonical_bytes()
    assert document["status"] == "candidate_compiled_non_executable"
    assert document["artifact_bytes_status"] == "not_supplied"
    assert "artifact_bytes_not_locally_bound" in document["execution_blockers"]
    assert all(value is False for value in document["authority"].values())
    serialized = first.canonical_bytes().decode("ascii")
    assert "/home/" not in serialized
    assert (
        document["microvm_configuration_template"]["boot-source"]["kernel_image_path"] == "/kernel"
    )
    assert [
        drive["path_on_host"] for drive in document["microvm_configuration_template"]["drives"]
    ] == ["/rootfs", "/input", "/output"]
    assert "run_nonce_256" in document["root_owned_allocations"]
    document["authority"]["root_launcher_ready"] = True
    assert first.to_document()["authority"]["root_launcher_ready"] is False
    with pytest.raises(TypeError):
        candidate_plan.CompiledCandidateLaunchPlanV1()


def test_locally_bound_artifacts_change_status_without_readiness(
    tmp_path: Path,
) -> None:
    kernel = b"kernel"
    rootfs = b"rootfs"
    manifest = parse_manifest(build_manifest_document(kernel, rootfs))
    (tmp_path / manifest.guest_kernel.artifact.artifact_name).write_bytes(kernel)
    (tmp_path / manifest.input_image.artifact.artifact_name).write_bytes(b"input-image")
    (tmp_path / manifest.rootfs.artifact.artifact_name).write_bytes(rootfs)
    bound = artifact_set.verify_artifact_set(tmp_path, manifest)

    document = candidate_plan.compile_candidate_plan(
        manifest,
        parse_intent(),
        locally_bound_artifacts=bound,
    ).to_document()

    assert document["artifact_bytes_status"] == "exact_match"
    assert "artifact_bytes_not_locally_bound" not in document["execution_blockers"]
    assert "root_owned_launcher_pending" in document["execution_blockers"]
    assert document["authority"]["root_launcher_ready"] is False


def test_intent_rejects_noncanonical_unknown_integer_and_digest_drift() -> None:
    document = build_intent_document()
    with pytest.raises(candidate_plan.CandidatePlanError) as noncanonical:
        candidate_plan.parse_replay_intent_bytes(json.dumps(document).encode("ascii"))
    assert noncanonical.value.code == "candidate_intent_noncanonical"

    unknown = copy.deepcopy(document)
    unknown["path"] = "/attacker"
    with pytest.raises(candidate_plan.CandidatePlanError) as unknown_field:
        candidate_plan.parse_replay_intent_bytes(runtime.canonical_document_bytes(unknown))
    assert unknown_field.value.code == "candidate_intent_fields_mismatch"

    integer = copy.deepcopy(document)
    integer["expected_output_payload_size_bytes"] = True
    with pytest.raises(candidate_plan.CandidatePlanError) as integer_error:
        candidate_plan.parse_replay_intent_bytes(runtime.canonical_document_bytes(integer))
    assert integer_error.value.code == "candidate_intent_output_payload_size_invalid"

    digest = copy.deepcopy(document)
    digest["expected_output_payload_sha256"] = "0" * 64
    with pytest.raises(candidate_plan.CandidatePlanError) as digest_error:
        candidate_plan.parse_replay_intent_bytes(runtime.canonical_document_bytes(digest))
    assert digest_error.value.code == "candidate_intent_digest_invalid"


def test_candidate_plan_rechecks_locally_bound_identity() -> None:
    manifest = parse_manifest(build_manifest_document())
    forged = artifact_set.LocallyBoundRuntimeArtifactSetV1._from_verified(
        artifact_set_id=manifest.artifact_set_id,
        guest_kernel=artifact_set.BoundArtifactIdentityV1(
            "guest_kernel",
            "ab" * 32,
            manifest.guest_kernel.artifact.size_bytes,
        ),
        input_image=artifact_set.BoundArtifactIdentityV1(
            "input_image",
            manifest.input_image.artifact.sha256,
            manifest.input_image.artifact.size_bytes,
        ),
        rootfs=artifact_set.BoundArtifactIdentityV1(
            "rootfs",
            manifest.rootfs.artifact.sha256,
            manifest.rootfs.artifact.size_bytes,
        ),
    )

    with pytest.raises(candidate_plan.CandidatePlanError) as mismatch:
        candidate_plan.compile_candidate_plan(
            manifest,
            parse_intent(),
            locally_bound_artifacts=forged,
        )
    assert mismatch.value.code == "candidate_plan_artifact_binding_mismatch"


def test_intent_change_changes_plan_id() -> None:
    manifest = parse_manifest(build_manifest_document())
    first = candidate_plan.compile_candidate_plan(manifest, parse_intent())
    changed_document = build_intent_document()
    changed_document["expected_output_payload_sha256"] = _hash(b"different-payload")
    second = candidate_plan.compile_candidate_plan(
        manifest,
        parse_intent(changed_document),
    )

    assert first.candidate_plan_id != second.candidate_plan_id


def test_intent_cannot_rebind_the_pinned_input_image() -> None:
    manifest = parse_manifest(build_manifest_document())
    changed_document = build_intent_document()
    changed_document["input_drive_sha256"] = _hash(b"different-input")

    with pytest.raises(candidate_plan.CandidatePlanError) as mismatch:
        candidate_plan.compile_candidate_plan(
            manifest,
            parse_intent(changed_document),
        )

    assert mismatch.value.code == "candidate_plan_input_binding_mismatch"


def test_binary_request_binds_manifest_input_and_exact_intent() -> None:
    manifest = parse_manifest(build_manifest_document())
    intent = parse_intent()
    plan = candidate_plan.compile_candidate_plan(manifest, intent)

    request = candidate_plan.compile_binary_request(
        plan,
        run_nonce_256=bytes([9]) * 32,
    )

    assert request.runtime_manifest_sha256 == bytes.fromhex(manifest.canonical_sha256)
    assert request.input_drive_sha256 == bytes.fromhex(intent.input_drive_sha256)
    assert request.replay_intent_sha256 == bytes.fromhex(intent.intent_sha256)
    assert candidate_plan.protocol.decode_request(request.encode()) == request


def _hash(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()
