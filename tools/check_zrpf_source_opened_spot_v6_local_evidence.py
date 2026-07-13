#!/usr/bin/env python3
"""Fail-closed checker for one bounded source-opened Spot V6 proof chain.

The evidence binds one source proof through V6 leaf, L1, L2, settlement, exact
seal mutation, and the external verifier output. Static validation never grants
ledger, release, settlement, privacy, or production authority.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import sys
from datetime import date
from pathlib import Path
from typing import Any, NoReturn

if __package__:
    from tools import check_zrpf_source_opened_spot_v6_build_record as build_checker
else:
    sys.path.insert(0, Path(__file__).resolve().parents[1].as_posix())
    from tools import check_zrpf_source_opened_spot_v6_build_record as build_checker

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EVIDENCE = (
    REPO_ROOT / "docs/research/ZRPF_SOURCE_OPENED_SPOT_V6_LOCAL_EVIDENCE_20260712.json"
)
EVIDENCE_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_local_evidence/v2"
REPORT_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_local_evidence_check/v2"
MAX_EVIDENCE_BYTES = 512 * 1024
SUCCINCT_PROFILE_ID = "risc0_succinct_poseidon2_resolve_3_0_5_v1"
MUTATION_ERROR_CODE = "source_opened_spot_settlement_v6_receipt_rejected"

ARTIFACT_SPECS = (
    ("source_request", "source_request.json", "canonical_json"),
    ("source_proof", "source_proof.json", "canonical_json"),
    ("adapter_receipt", "adapter_receipt.json", "canonical_receipt_json"),
    ("leaf_source_envelope", "leaf_source_envelope.bin", "binary"),
    ("leaf_receipt", "leaf_receipt.json", "canonical_receipt_json"),
    ("leaf_mutation_receipt", "leaf_mutation_receipt.json", "canonical_receipt_json"),
    ("l1_receipt", "l1_receipt.json", "canonical_receipt_json"),
    ("l1_mutation_receipt", "l1_mutation_receipt.json", "canonical_receipt_json"),
    ("l2_receipt", "l2_receipt.json", "canonical_receipt_json"),
    ("l2_mutation_receipt", "l2_mutation_receipt.json", "canonical_receipt_json"),
    ("settlement_receipt", "settlement_receipt.json", "canonical_receipt_json"),
    (
        "settlement_mutation_receipt",
        "settlement_mutation_receipt.json",
        "canonical_receipt_json",
    ),
    (
        "settlement_admission_journal",
        "settlement_admission_journal.bin",
        "binary",
    ),
    ("settlement_guest_input", "settlement_guest_input.bin", "binary"),
    ("settlement_replay", "settlement_replay.bin", "binary"),
    ("settlement_da_certificate", "settlement_da_certificate.bin", "binary"),
    ("leaf_program_binary", "spot_value_leaf_v6.bin", "risc0_program_binary"),
    (
        "level_one_program_binary",
        "spot_value_aggregate_l1_v6.bin",
        "risc0_program_binary",
    ),
    (
        "level_two_program_binary",
        "spot_value_aggregate_l2_v6.bin",
        "risc0_program_binary",
    ),
    (
        "settlement_program_binary",
        "source_opened_spot_settlement_v6.bin",
        "risc0_program_binary",
    ),
    (
        "external_verifier_output",
        "external_verifier_output.json",
        "canonical_json",
    ),
    ("chain_verifier_output", "chain_verifier_output.json", "canonical_json"),
)

EXECUTED_COMMAND_FIELDS = {
    "all_positive_commands_exit_zero",
    "chain_verifier_ambient_dev_executed",
    "chain_verifier_normal_executed",
    "external_positive_verifier_executed",
    "external_mutation_verifier_executed",
    "leaf_proving_executed",
    "level_one_proving_executed",
    "level_two_proving_executed",
    "mutation_command_rejected_nonzero",
    "settlement_proving_executed",
    "source_opening_executed",
}
TRUE_CLAIMS = {
    "all_retained_layer_seal_mutations_rejected",
    "current_v6_dependency_chain_verified",
    "exact_settlement_seal_mutation_rejected",
    "fake_receipt_rejected_with_dev_mode_disabled",
    "four_stage_succinct_receipts_generated",
    "normal_and_ambient_dev_chain_outputs_identical",
    "source_opened_singleton_spot_execution_verified",
    "source_to_settlement_artifact_hash_chain_bound",
}
FALSE_CLAIMS = {
    "arbitrary_depth_recursion_verified",
    "cross_host_reproducible_build",
    "durable_atomic_admission_verified",
    "end_user_signature_scheme_verified",
    "general_recursive_semantics_verified",
    "maximum_fanout_verified",
    "privacy_verified",
    "proof_byte_determinism_verified",
    "release_authority",
    "settlement_authority",
    "tau_finality_verified",
    "production_authority",
}


class EvidenceError(ValueError):
    """Stable fail-closed V6 local-evidence rejection."""


def _reject_float(_value: str) -> NoReturn:
    raise EvidenceError("floating-point JSON numbers are forbidden")


def _object_no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise EvidenceError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def canonical_bytes(document: Any) -> bytes:
    return (json.dumps(document, indent=2, sort_keys=False) + "\n").encode("utf-8")


def load_evidence(path: Path) -> tuple[dict[str, Any], bytes]:
    raw = path.read_bytes()
    if not raw or len(raw) > MAX_EVIDENCE_BYTES:
        raise EvidenceError("evidence record byte length is unsupported")
    try:
        document = json.loads(
            raw,
            object_pairs_hook=_object_no_duplicates,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, EvidenceError) as exc:
        raise EvidenceError(f"evidence JSON rejected: {exc}") from exc
    if type(document) is not dict:
        raise EvidenceError("evidence root must be an object")
    if canonical_bytes(document) != raw:
        raise EvidenceError("evidence bytes are noncanonical")
    return document, raw


def validate_evidence(
    document: dict[str, Any],
    raw: bytes,
    *,
    artifact_directory: Path | None = None,
    build_record_path: Path | None = None,
    r0vm_path: Path | None = None,
    expected_evidence_sha256: str | None = None,
) -> dict[str, Any]:
    record = _exact_object(
        document,
        {
            "schema",
            "recorded_at",
            "build_record_sha256",
            "images",
            "artifacts",
            "stages",
            "executed_commands",
            "claims",
        },
        "evidence",
    )
    _require_equal(record["schema"], EVIDENCE_SCHEMA, "evidence.schema")
    _require_date(record["recorded_at"], "evidence.recorded_at")
    _require_hash(record["build_record_sha256"], "evidence.build_record_sha256")
    evidence_sha256 = hashlib.sha256(raw).hexdigest()
    anchor_checked = expected_evidence_sha256 is not None
    if expected_evidence_sha256 is not None:
        _require_hash(expected_evidence_sha256, "expected_evidence_sha256")
        if evidence_sha256 != expected_evidence_sha256:
            raise EvidenceError("evidence SHA-256 differs from supplied anchor")

    _validate_images(record["images"])
    artifacts = _validate_artifacts(record["artifacts"])
    _validate_stages(record["stages"], artifacts)
    _require_true_fields(
        record["executed_commands"],
        EXECUTED_COMMAND_FIELDS,
        "evidence.executed_commands",
    )
    _validate_claims(record["claims"])

    build_record_rechecked = False
    program_image_ids_recomputed = 0
    program_artifact_bindings_checked = 0
    if build_record_path is not None:
        build_document, build_raw = build_checker.load_record(build_record_path)
        if hashlib.sha256(build_raw).hexdigest() != record["build_record_sha256"]:
            raise EvidenceError("build record SHA-256 binding mismatch")
        build_report = build_checker.validate_record(
            build_document,
            build_raw,
            artifact_directory=artifact_directory,
            r0vm_path=r0vm_path,
            expected_record_sha256=record["build_record_sha256"],
        )
        build_record_rechecked = True
        program_image_ids_recomputed = build_report["program_image_ids_recomputed"]
        if artifact_directory is not None:
            program_artifact_bindings_checked = _validate_program_artifact_bindings(
                build_document["programs"],
                record["images"],
                artifacts,
                program_image_ids_recomputed=program_image_ids_recomputed,
            )

    artifacts_checked = 0
    mutation_relations_checked = 0
    verifier_transcripts_checked = 0
    if artifact_directory is not None:
        (
            artifacts_checked,
            mutation_relations_checked,
            verifier_transcripts_checked,
        ) = _validate_external_artifacts(artifact_directory, artifacts)
    scoped_local_claim_allowed = (
        anchor_checked
        and build_record_rechecked
        and program_image_ids_recomputed == len(build_checker.PROGRAM_SPECS)
        and program_artifact_bindings_checked == len(build_checker.PROGRAM_SPECS)
        and artifacts_checked == len(ARTIFACT_SPECS)
        and mutation_relations_checked == 4
        and verifier_transcripts_checked == 2
    )
    return {
        "ok": True,
        "schema": REPORT_SCHEMA,
        "evidence_sha256": evidence_sha256,
        "governed_anchor_checked": anchor_checked,
        "build_record_rechecked": build_record_rechecked,
        "program_image_ids_recomputed": program_image_ids_recomputed,
        "program_artifact_bindings_checked": program_artifact_bindings_checked,
        "external_artifact_files_checked": artifacts_checked,
        "exact_mutation_relations_checked": mutation_relations_checked,
        "verifier_transcripts_checked": verifier_transcripts_checked,
        "scoped_local_replay_claim_allowed": scoped_local_claim_allowed,
        "source_image_id": build_checker.SOURCE_SPOT_IMAGE_ID,
        "leaf_image_id": build_checker.LEAF_IMAGE_ID,
        "level_one_image_id": build_checker.L1_IMAGE_ID,
        "level_two_image_id": build_checker.L2_IMAGE_ID,
        "settlement_image_id": build_checker.SETTLEMENT_IMAGE_ID,
        "dependency_chain_verified": True,
        "mutation_rejected": mutation_relations_checked == 4,
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
    }


def _validate_images(value: Any) -> None:
    images = _exact_object(
        value,
        {
            "source_spot_v1",
            "adapter_v3",
            "spot_value_leaf_v6",
            "spot_value_aggregate_l1_v6",
            "spot_value_aggregate_l2_v6",
            "source_opened_spot_settlement_v6",
        },
        "evidence.images",
    )
    expected = {
        "source_spot_v1": build_checker.SOURCE_SPOT_IMAGE_ID,
        "adapter_v3": build_checker.ADAPTER_IMAGE_ID,
        "spot_value_leaf_v6": build_checker.LEAF_IMAGE_ID,
        "spot_value_aggregate_l1_v6": build_checker.L1_IMAGE_ID,
        "spot_value_aggregate_l2_v6": build_checker.L2_IMAGE_ID,
        "source_opened_spot_settlement_v6": build_checker.SETTLEMENT_IMAGE_ID,
    }
    for field, image_id in expected.items():
        _require_equal(images[field], image_id, f"images.{field}")


def _validate_artifacts(value: Any) -> dict[str, dict[str, Any]]:
    if type(value) is not list or len(value) != len(ARTIFACT_SPECS):
        raise EvidenceError("evidence.artifacts must contain the ordered artifact inventory")
    result: dict[str, dict[str, Any]] = {}
    for index, (row, spec) in enumerate(zip(value, ARTIFACT_SPECS, strict=True)):
        artifact_id, path, kind = spec
        artifact = _exact_object(
            row,
            {"id", "path", "kind", "size_bytes", "sha256"},
            f"evidence.artifacts[{index}]",
        )
        for field, expected in (("id", artifact_id), ("path", path), ("kind", kind)):
            _require_equal(artifact[field], expected, f"artifacts[{index}].{field}")
        _require_positive_int(artifact["size_bytes"], f"artifacts[{index}].size_bytes")
        if artifact["size_bytes"] > build_checker.MAX_ARTIFACT_BYTES:
            raise EvidenceError(f"artifacts[{index}].size_bytes exceeds bound")
        _require_hash(artifact["sha256"], f"artifacts[{index}].sha256")
        if artifact["sha256"] == "0" * 64:
            raise EvidenceError(f"artifacts[{index}].sha256 is zero")
        result[artifact_id] = artifact
    return result


def _validate_program_artifact_bindings(
    programs: Any,
    images: dict[str, Any],
    artifacts: dict[str, dict[str, Any]],
    *,
    program_image_ids_recomputed: int,
) -> int:
    if program_image_ids_recomputed != len(build_checker.PROGRAM_SPECS):
        raise EvidenceError("build record did not recompute all V6 program image IDs")
    evidence_programs_by_path = {
        path: artifacts[artifact_id]
        for artifact_id, path, kind in ARTIFACT_SPECS
        if kind == "risc0_program_binary"
    }
    expected_paths = {spec[2] for spec in build_checker.PROGRAM_SPECS}
    if set(evidence_programs_by_path) != expected_paths:
        raise EvidenceError("evidence program artifact path set differs from build record")
    checked = 0
    for program, spec in zip(programs, build_checker.PROGRAM_SPECS, strict=True):
        stage, _package, expected_path, _image_id, _child_stage, _child_image = spec
        artifact = evidence_programs_by_path[expected_path]
        if program["stage"] != stage or program["artifact_file"] != artifact["path"]:
            raise EvidenceError(
                f"program artifact path mapping differs between evidence and build record: {stage}"
            )
        if program["program_binary_bytes"] != artifact["size_bytes"]:
            raise EvidenceError(
                f"program artifact byte size differs between evidence and build record: {stage}"
            )
        if program["program_binary_sha256"] != artifact["sha256"]:
            raise EvidenceError(
                f"program artifact SHA-256 differs between evidence and build record: {stage}"
            )
        if program["image_id_hex"] != images[stage]:
            raise EvidenceError(
                f"program image ID differs between evidence and build record: {stage}"
            )
        checked += 1
    return checked


def _validate_stages(value: Any, artifacts: dict[str, dict[str, Any]]) -> None:
    stages = _exact_object(
        value,
        {
            "source_opening",
            "adapter",
            "leaf",
            "level_one",
            "level_two",
            "settlement",
            "external_verifier",
        },
        "evidence.stages",
    )
    _validate_source_stage(stages["source_opening"], artifacts)
    _validate_adapter_stage(stages["adapter"], artifacts)
    _validate_leaf_stage(stages["leaf"], artifacts)
    _validate_aggregate_stage(
        stages["level_one"],
        "level_one",
        build_checker.L1_IMAGE_ID,
        artifacts["leaf_receipt"]["sha256"],
        artifacts["l1_receipt"]["sha256"],
        artifacts["l1_mutation_receipt"]["sha256"],
    )
    _validate_aggregate_stage(
        stages["level_two"],
        "level_two",
        build_checker.L2_IMAGE_ID,
        artifacts["l1_receipt"]["sha256"],
        artifacts["l2_receipt"]["sha256"],
        artifacts["l2_mutation_receipt"]["sha256"],
    )
    _validate_settlement_stage(stages["settlement"], artifacts)
    _validate_external_verifier_stage(stages["external_verifier"], artifacts)


def _validate_source_stage(value: Any, artifacts: dict[str, dict[str, Any]]) -> None:
    stage = _exact_object(
        value,
        {
            "ok",
            "source_image_id",
            "source_program_sha256",
            "source_cli_sha256",
            "generator_sha256",
            "r0vm_sha256",
            "request_sha256",
            "proof_sha256",
            "receipt_kind",
        },
        "stages.source_opening",
    )
    _require_exact_bool(stage["ok"], "source_opening.ok", expected=True)
    _require_equal(
        stage["source_image_id"],
        build_checker.SOURCE_SPOT_IMAGE_ID,
        "source_opening.source_image_id",
    )
    for field in (
        "source_program_sha256",
        "source_cli_sha256",
        "generator_sha256",
        "r0vm_sha256",
    ):
        _require_hash(stage[field], f"source_opening.{field}")
    _require_hash_equal(
        stage["request_sha256"],
        artifacts["source_request"]["sha256"],
        "source request",
    )
    _require_hash_equal(
        stage["proof_sha256"],
        artifacts["source_proof"]["sha256"],
        "source proof",
    )
    _require_equal(stage["receipt_kind"], "succinct", "source_opening.receipt_kind")


def _validate_adapter_stage(value: Any, artifacts: dict[str, dict[str, Any]]) -> None:
    stage = _exact_object(
        value,
        {"image_id", "receipt_sha256", "receipt_kind", "verified"},
        "stages.adapter",
    )
    _require_equal(stage["image_id"], build_checker.ADAPTER_IMAGE_ID, "adapter.image_id")
    _require_hash_equal(
        stage["receipt_sha256"],
        artifacts["adapter_receipt"]["sha256"],
        "adapter receipt",
    )
    _require_equal(stage["receipt_kind"], "succinct", "adapter.receipt_kind")
    _require_exact_bool(stage["verified"], "adapter.verified", expected=True)


def _validate_leaf_stage(value: Any, artifacts: dict[str, dict[str, Any]]) -> None:
    stage = _exact_object(
        value,
        {
            "ok",
            "image_id",
            "receipt_sha256",
            "mutation_receipt_sha256",
            "mutation_rejected",
            "receipt_profile_id",
            "source_proof_sha256",
            "adapter_receipt_sha256",
            "source_envelope_sha256",
            "verified_program_manifest_root",
            "action_nullifier_root",
            "statement_hash",
        },
        "stages.leaf",
    )
    _require_exact_bool(stage["ok"], "leaf.ok", expected=True)
    _require_exact_bool(stage["mutation_rejected"], "leaf.mutation_rejected", expected=True)
    _require_equal(stage["image_id"], build_checker.LEAF_IMAGE_ID, "leaf.image_id")
    for field in ("verified_program_manifest_root", "action_nullifier_root", "statement_hash"):
        _require_nonzero_hash(stage[field], f"leaf.{field}")
    _require_equal(stage["receipt_profile_id"], SUCCINCT_PROFILE_ID, "leaf.receipt_profile_id")
    for field, artifact_id, label in (
        ("receipt_sha256", "leaf_receipt", "leaf receipt"),
        ("mutation_receipt_sha256", "leaf_mutation_receipt", "leaf mutation receipt"),
        ("source_proof_sha256", "source_proof", "leaf source proof"),
        ("adapter_receipt_sha256", "adapter_receipt", "leaf adapter receipt"),
        ("source_envelope_sha256", "leaf_source_envelope", "leaf source envelope"),
    ):
        _require_hash_equal(stage[field], artifacts[artifact_id]["sha256"], label)


def _validate_aggregate_stage(
    value: Any,
    label: str,
    expected_image: str,
    expected_child_receipt: str,
    expected_receipt: str,
    expected_mutation_receipt: str,
) -> None:
    stage = _exact_object(
        value,
        {
            "ok",
            "image_id",
            "child_receipt_sha256",
            "receipt_sha256",
            "mutation_receipt_sha256",
            "mutation_rejected",
            "verified_child_count",
        },
        f"stages.{label}",
    )
    _require_exact_bool(stage["ok"], f"{label}.ok", expected=True)
    _require_exact_bool(stage["mutation_rejected"], f"{label}.mutation_rejected", expected=True)
    _require_equal(stage["image_id"], expected_image, f"{label}.image_id")
    _require_hash_equal(
        stage["child_receipt_sha256"],
        expected_child_receipt,
        f"{label} child receipt",
    )
    _require_hash_equal(stage["receipt_sha256"], expected_receipt, f"{label} receipt")
    _require_hash_equal(
        stage["mutation_receipt_sha256"],
        expected_mutation_receipt,
        f"{label} mutation receipt",
    )
    if type(stage["verified_child_count"]) is not int or stage["verified_child_count"] != 1:
        raise EvidenceError(f"{label}.verified_child_count must be exactly 1")


def _validate_settlement_stage(value: Any, artifacts: dict[str, dict[str, Any]]) -> None:
    stage = _exact_object(
        value,
        {
            "ok",
            "image_id",
            "l2_receipt_sha256",
            "source_envelope_sha256",
            "receipt_sha256",
            "mutation_receipt_sha256",
            "mutation_rejected",
            "admission_journal_sha256",
            "guest_input_sha256",
            "replay_sha256",
            "data_availability_certificate_sha256",
            "settlement_claim_binding",
            "settlement_program_manifest_root",
            "settlement_program_id",
            "succinct_receipt_profile_id",
            "action_count",
            "consumed_object_count",
        },
        "stages.settlement",
    )
    _require_exact_bool(stage["ok"], "settlement.ok", expected=True)
    _require_exact_bool(stage["mutation_rejected"], "settlement.mutation_rejected", expected=True)
    _require_equal(stage["image_id"], build_checker.SETTLEMENT_IMAGE_ID, "settlement.image_id")
    _require_equal(
        stage["settlement_program_id"],
        build_checker.SETTLEMENT_IMAGE_ID,
        "settlement.settlement_program_id",
    )
    _require_equal(
        stage["succinct_receipt_profile_id"],
        SUCCINCT_PROFILE_ID,
        "settlement.succinct_receipt_profile_id",
    )
    for field in ("settlement_claim_binding", "settlement_program_manifest_root"):
        _require_nonzero_hash(stage[field], f"settlement.{field}")
    for field in ("action_count", "consumed_object_count"):
        if type(stage[field]) is not int or stage[field] != 1:
            raise EvidenceError(f"settlement.{field} must be exactly 1")
    for field, artifact_id, label in (
        ("l2_receipt_sha256", "l2_receipt", "settlement L2 receipt"),
        ("source_envelope_sha256", "leaf_source_envelope", "settlement source envelope"),
        ("receipt_sha256", "settlement_receipt", "settlement receipt"),
        ("mutation_receipt_sha256", "settlement_mutation_receipt", "settlement mutation receipt"),
        ("admission_journal_sha256", "settlement_admission_journal", "settlement journal"),
        ("guest_input_sha256", "settlement_guest_input", "settlement guest input"),
        ("replay_sha256", "settlement_replay", "settlement replay"),
        (
            "data_availability_certificate_sha256",
            "settlement_da_certificate",
            "settlement DA certificate",
        ),
    ):
        _require_hash_equal(stage[field], artifacts[artifact_id]["sha256"], label)


def _validate_external_verifier_stage(
    value: Any,
    artifacts: dict[str, dict[str, Any]],
) -> None:
    stage = _exact_object(
        value,
        {
            "positive_receipt_sha256",
            "positive_guest_input_sha256",
            "positive_output_sha256",
            "chain_output_sha256",
            "ambient_dev_chain_output_sha256",
            "normal_dev_outputs_equal",
            "fake_receipt_rejected",
            "positive_receipts_verified",
            "exact_seal_mutations_rejected",
            "mutation_receipt_sha256",
            "mutation_rejected",
            "mutation_error_code",
        },
        "stages.external_verifier",
    )
    _require_exact_bool(
        stage["mutation_rejected"],
        "external_verifier.mutation_rejected",
        expected=True,
    )
    _require_exact_bool(
        stage["normal_dev_outputs_equal"],
        "external_verifier.normal_dev_outputs_equal",
        expected=True,
    )
    _require_exact_bool(
        stage["fake_receipt_rejected"],
        "external_verifier.fake_receipt_rejected",
        expected=True,
    )
    for field in ("positive_receipts_verified", "exact_seal_mutations_rejected"):
        if type(stage[field]) is not int or stage[field] != 4:
            raise EvidenceError(f"external_verifier.{field} must be exactly 4")
    _require_equal(
        stage["mutation_error_code"],
        MUTATION_ERROR_CODE,
        "external_verifier.mutation_error_code",
    )
    for field, artifact_id, label in (
        ("positive_receipt_sha256", "settlement_receipt", "external positive receipt"),
        ("positive_guest_input_sha256", "settlement_guest_input", "external positive guest input"),
        ("positive_output_sha256", "external_verifier_output", "external verifier output"),
        ("chain_output_sha256", "chain_verifier_output", "chain verifier output"),
        (
            "ambient_dev_chain_output_sha256",
            "chain_verifier_output",
            "ambient-dev chain verifier output",
        ),
        ("mutation_receipt_sha256", "settlement_mutation_receipt", "external mutation receipt"),
    ):
        _require_hash_equal(stage[field], artifacts[artifact_id]["sha256"], label)


def _validate_claims(value: Any) -> None:
    claims = _exact_object(value, TRUE_CLAIMS | FALSE_CLAIMS, "evidence.claims")
    for field in TRUE_CLAIMS:
        _require_exact_bool(claims[field], f"claims.{field}", expected=True)
    for field in FALSE_CLAIMS:
        _require_exact_bool(claims[field], f"claims.{field}", expected=False)


def _validate_external_artifacts(
    directory: Path,
    artifacts: dict[str, dict[str, Any]],
) -> tuple[int, int, int]:
    root = directory.resolve(strict=True)
    if not root.is_dir():
        raise EvidenceError("artifact directory is not a directory")
    checked = 0
    for artifact_id, path, kind in ARTIFACT_SPECS:
        artifact = artifacts[artifact_id]
        try:
            candidate = build_checker._resolve_artifact(root, path)
            if kind == "risc0_program_binary":
                descriptor, size, digest = build_checker._open_stable_program_binary(candidate)
                os.close(descriptor)
            else:
                size, digest = build_checker._stable_file_facts(candidate)
        except build_checker.BuildRecordError as exc:
            raise EvidenceError(str(exc)) from exc
        if size != artifact["size_bytes"] or digest != artifact["sha256"]:
            raise EvidenceError(f"external artifact identity mismatch: {artifact_id}")
        checked += 1
    for source_id, mutation_id in (
        ("leaf_receipt", "leaf_mutation_receipt"),
        ("l1_receipt", "l1_mutation_receipt"),
        ("l2_receipt", "l2_mutation_receipt"),
        ("settlement_receipt", "settlement_mutation_receipt"),
    ):
        _validate_exact_succinct_seal_mutation(
            _read_bound_artifact(root, artifacts[source_id]),
            _read_bound_artifact(root, artifacts[mutation_id]),
        )
    _validate_external_verifier_output(
        _read_bound_artifact(root, artifacts["external_verifier_output"]),
        artifacts,
    )
    _validate_chain_verifier_output(
        _read_bound_artifact(root, artifacts["chain_verifier_output"]),
        artifacts,
    )
    return checked, 4, 2


def _read_bound_artifact(root: Path, artifact: dict[str, Any]) -> bytes:
    try:
        path = build_checker._resolve_artifact(root, artifact["path"])
        raw = path.read_bytes()
    except (OSError, build_checker.BuildRecordError) as exc:
        raise EvidenceError("bound artifact read failed") from exc
    if len(raw) != artifact["size_bytes"] or hashlib.sha256(raw).hexdigest() != artifact["sha256"]:
        raise EvidenceError("bound artifact changed between identity and relation checks")
    return raw


def _validate_exact_succinct_seal_mutation(source_raw: bytes, mutation_raw: bytes) -> None:
    source = _load_canonical_compact_json(source_raw, "source receipt")
    mutation = _load_canonical_compact_json(mutation_raw, "mutation receipt")
    if type(source) is not dict or type(mutation) is not dict:
        raise EvidenceError("receipt mutation relation requires JSON objects")
    restored = copy.deepcopy(mutation)
    source_seal = _succinct_seal(source, "source receipt")
    restored_seal = _succinct_seal(restored, "mutation receipt")
    if len(source_seal) <= 1 or len(restored_seal) != len(source_seal):
        raise EvidenceError("Succinct mutation seal length mismatch")
    if type(source_seal[1]) is not int or type(restored_seal[1]) is not int:
        raise EvidenceError("Succinct mutation word must be an integer")
    if source_seal[1] ^ restored_seal[1] != 1:
        raise EvidenceError("Succinct mutation must XOR seal word 1 by exactly one")
    restored_seal[1] = source_seal[1]
    if restored != source:
        raise EvidenceError("Succinct mutation changes data outside seal word 1")


def _succinct_seal(receipt: dict[str, Any], label: str) -> list[Any]:
    if set(receipt) != {"inner", "journal", "metadata"}:
        raise EvidenceError(f"{label} outer field set mismatch")
    inner = receipt.get("inner")
    if type(inner) is not dict or set(inner) != {"Succinct"}:
        raise EvidenceError(f"{label} is not structurally Succinct")
    succinct = inner.get("Succinct")
    if type(succinct) is not dict:
        raise EvidenceError(f"{label} Succinct body is malformed")
    seal = succinct.get("seal")
    if type(seal) is not list or not seal:
        raise EvidenceError(f"{label} Succinct seal is malformed")
    return seal


def _load_canonical_compact_json(raw: bytes, label: str) -> Any:
    try:
        value = json.loads(
            raw,
            object_pairs_hook=_object_no_duplicates,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, EvidenceError) as exc:
        raise EvidenceError(f"{label} JSON rejected: {exc}") from exc
    canonical = json.dumps(
        value,
        ensure_ascii=False,
        separators=(",", ":"),
    ).encode("utf-8")
    if canonical != raw:
        raise EvidenceError(f"{label} JSON is noncanonical")
    return value


def _load_canonical_json_line(raw: bytes, label: str) -> dict[str, Any]:
    if not raw.endswith(b"\n") or raw.endswith(b"\n\n"):
        raise EvidenceError(f"{label} must be one newline-terminated JSON object")
    value = _load_canonical_compact_json(raw[:-1], label)
    if type(value) is not dict:
        raise EvidenceError(f"{label} must be a JSON object")
    return value


def _validate_external_verifier_output(
    raw: bytes,
    artifacts: dict[str, dict[str, Any]],
) -> None:
    value = _load_canonical_json_line(raw, "external verifier output")
    if value.get("ok") is not True or value.get("schema") != (
        "zenodex.source_opened_spot_settlement_verifier_v6.response.v1"
    ):
        raise EvidenceError("external verifier output status mismatch")
    admission = value.get("verified_settlement_admission")
    if type(admission) is not dict:
        raise EvidenceError("external verifier admission projection is unavailable")
    for field, artifact_id in (
        ("receipt_sha256", "settlement_receipt"),
        ("guest_input_sha256", "settlement_guest_input"),
        ("admission_journal_sha256", "settlement_admission_journal"),
    ):
        if admission.get(field) != artifacts[artifact_id]["sha256"]:
            raise EvidenceError(f"external verifier {field} binding mismatch")


def _validate_chain_verifier_output(
    raw: bytes,
    artifacts: dict[str, dict[str, Any]],
) -> None:
    value = _exact_object(
        _load_canonical_json_line(raw, "chain verifier output"),
        {
            "ok",
            "schema",
            "positive_receipts_verified",
            "exact_seal_mutations_rejected",
            "fake_receipt_rejected",
            "receipt_profile_id",
            "leaf_receipt_sha256",
            "level_one_receipt_sha256",
            "level_two_receipt_sha256",
            "settlement_receipt_sha256",
            "settlement_claim_binding",
            "settlement_admission_journal_sha256",
            "release_authority",
            "settlement_authority",
            "production_authority",
        },
        "chain verifier output",
    )
    if value["ok"] is not True or value["schema"] != (
        "zenodex.source_opened_spot_v6_chain_verifier.response.v1"
    ):
        raise EvidenceError("chain verifier output status mismatch")
    for field in ("positive_receipts_verified", "exact_seal_mutations_rejected"):
        if type(value[field]) is not int or value[field] != 4:
            raise EvidenceError(f"chain verifier {field} mismatch")
    if value["fake_receipt_rejected"] is not True:
        raise EvidenceError("chain verifier fake receipt rejection is absent")
    if value["receipt_profile_id"] != SUCCINCT_PROFILE_ID:
        raise EvidenceError("chain verifier receipt profile mismatch")
    for field in ("release_authority", "settlement_authority", "production_authority"):
        if value[field] is not False:
            raise EvidenceError(f"chain verifier {field} must remain false")
    for field, artifact_id in (
        ("leaf_receipt_sha256", "leaf_receipt"),
        ("level_one_receipt_sha256", "l1_receipt"),
        ("level_two_receipt_sha256", "l2_receipt"),
        ("settlement_receipt_sha256", "settlement_receipt"),
        ("settlement_admission_journal_sha256", "settlement_admission_journal"),
    ):
        if value[field] != artifacts[artifact_id]["sha256"]:
            raise EvidenceError(f"chain verifier {field} binding mismatch")
    _require_nonzero_hash(value["settlement_claim_binding"], "chain settlement claim binding")


def _exact_object(value: Any, fields: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise EvidenceError(f"{label} must be an object")
    observed = set(value)
    if observed != fields:
        raise EvidenceError(
            f"{label} field set mismatch: missing={sorted(fields - observed)}, "
            f"unknown={sorted(observed - fields)}"
        )
    return value


def _require_true_fields(value: Any, fields: set[str], label: str) -> None:
    obj = _exact_object(value, fields, label)
    for field in fields:
        _require_exact_bool(obj[field], f"{label}.{field}", expected=True)


def _require_exact_bool(value: Any, label: str, *, expected: bool) -> None:
    if type(value) is not bool or value is not expected:
        raise EvidenceError(f"{label} must be exactly {expected}")


def _require_positive_int(value: Any, label: str) -> None:
    if type(value) is not int or value <= 0:
        raise EvidenceError(f"{label} must be a positive integer")


def _require_equal(value: Any, expected: str, label: str) -> None:
    if type(value) is not str or value != expected:
        raise EvidenceError(f"{label} mismatch")


def _require_hash(value: Any, label: str) -> None:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise EvidenceError(f"{label} must be 64 lowercase hexadecimal characters")


def _require_nonzero_hash(value: Any, label: str) -> None:
    _require_hash(value, label)
    if value == "0" * 64:
        raise EvidenceError(f"{label} must be nonzero")


def _require_hash_equal(value: Any, expected: str, label: str) -> None:
    _require_hash(value, label)
    if value != expected:
        raise EvidenceError(f"{label} SHA-256 mismatch")


def _require_date(value: Any, label: str) -> None:
    if type(value) is not str:
        raise EvidenceError(f"{label} must be an ISO date")
    try:
        parsed = date.fromisoformat(value)
    except ValueError as exc:
        raise EvidenceError(f"{label} must be an ISO date") from exc
    if parsed.isoformat() != value:
        raise EvidenceError(f"{label} must be a canonical ISO date")


def check_evidence(
    path: Path = DEFAULT_EVIDENCE,
    *,
    artifact_directory: Path | None = None,
    build_record_path: Path | None = None,
    r0vm_path: Path | None = None,
    expected_evidence_sha256: str | None = None,
    require_scoped_claim: bool = False,
) -> dict[str, Any]:
    try:
        document, raw = load_evidence(path)
        report = validate_evidence(
            document,
            raw,
            artifact_directory=artifact_directory,
            build_record_path=build_record_path,
            r0vm_path=r0vm_path,
            expected_evidence_sha256=expected_evidence_sha256,
        )
        if require_scoped_claim and not report["scoped_local_replay_claim_allowed"]:
            raise EvidenceError("scoped local replay claim is not established")
        return report
    except (OSError, EvidenceError, build_checker.BuildRecordError) as exc:
        return {
            "ok": False,
            "schema": REPORT_SCHEMA,
            "errors": [str(exc)],
            "governed_anchor_checked": False,
            "build_record_rechecked": False,
            "program_image_ids_recomputed": 0,
            "program_artifact_bindings_checked": 0,
            "external_artifact_files_checked": 0,
            "exact_mutation_relations_checked": 0,
            "verifier_transcripts_checked": 0,
            "scoped_local_replay_claim_allowed": False,
            "release_authority": False,
            "settlement_authority": False,
            "production_authority": False,
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence", type=Path, default=DEFAULT_EVIDENCE)
    parser.add_argument("--artifact-directory", type=Path)
    parser.add_argument("--build-record", type=Path)
    parser.add_argument("--r0vm", type=Path)
    parser.add_argument("--expected-evidence-sha256")
    parser.add_argument("--require-scoped-claim", action="store_true")
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args()
    report = check_evidence(
        arguments.evidence,
        artifact_directory=arguments.artifact_directory,
        build_record_path=arguments.build_record,
        r0vm_path=arguments.r0vm,
        expected_evidence_sha256=arguments.expected_evidence_sha256,
        require_scoped_claim=arguments.require_scoped_claim,
    )
    if arguments.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print("accepted" if report["ok"] else "rejected")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
