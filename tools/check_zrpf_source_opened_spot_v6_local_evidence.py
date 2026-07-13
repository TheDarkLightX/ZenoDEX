#!/usr/bin/env python3
"""Fail-closed checker for one bounded source-opened Spot V6 proof chain.

The evidence binds one source proof through V6 leaf, L1, L2, settlement, exact
seal mutation, and the external verifier output. Static validation never grants
ledger, release, settlement, privacy, or production authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
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
    REPO_ROOT
    / "docs/research/ZRPF_SOURCE_OPENED_SPOT_V6_LOCAL_EVIDENCE_20260712.json"
)
EVIDENCE_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_local_evidence/v1"
REPORT_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_local_evidence_check/v1"
MAX_EVIDENCE_BYTES = 512 * 1024
SUCCINCT_PROFILE_ID = "risc0_succinct_poseidon2_resolve_3_0_5_v1"
MUTATION_ERROR_CODE = "source_opened_spot_settlement_v6_receipt_rejected"

ARTIFACT_SPECS = (
    ("source_request", "source_request.json", "canonical_json"),
    ("source_proof", "source_proof.json", "canonical_json"),
    ("adapter_receipt", "adapter_receipt.json", "canonical_receipt_json"),
    ("leaf_source_envelope", "leaf_source_envelope.bin", "binary"),
    ("leaf_receipt", "leaf_receipt.json", "canonical_receipt_json"),
    ("l1_receipt", "l1_receipt.json", "canonical_receipt_json"),
    ("l2_receipt", "l2_receipt.json", "canonical_receipt_json"),
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
    (
        "external_verifier_output",
        "external_verifier_output.json",
        "canonical_json",
    ),
)

EXECUTED_COMMAND_FIELDS = {
    "all_positive_commands_exit_zero",
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
    "current_v6_dependency_chain_verified",
    "exact_settlement_seal_mutation_rejected",
    "four_stage_succinct_receipts_generated",
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
    if build_record_path is not None:
        build_document, build_raw = build_checker.load_record(build_record_path)
        if hashlib.sha256(build_raw).hexdigest() != record["build_record_sha256"]:
            raise EvidenceError("build record SHA-256 binding mismatch")
        build_checker.validate_record(build_document, build_raw)
        build_record_rechecked = True

    artifacts_checked = 0
    if artifact_directory is not None:
        artifacts_checked = _validate_external_artifacts(artifact_directory, artifacts)
    return {
        "ok": True,
        "schema": REPORT_SCHEMA,
        "evidence_sha256": evidence_sha256,
        "governed_anchor_checked": anchor_checked,
        "build_record_rechecked": build_record_rechecked,
        "external_artifact_files_checked": artifacts_checked,
        "source_image_id": build_checker.SOURCE_SPOT_IMAGE_ID,
        "leaf_image_id": build_checker.LEAF_IMAGE_ID,
        "level_one_image_id": build_checker.L1_IMAGE_ID,
        "level_two_image_id": build_checker.L2_IMAGE_ID,
        "settlement_image_id": build_checker.SETTLEMENT_IMAGE_ID,
        "dependency_chain_verified": True,
        "mutation_rejected": True,
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
    )
    _validate_aggregate_stage(
        stages["level_two"],
        "level_two",
        build_checker.L2_IMAGE_ID,
        artifacts["l1_receipt"]["sha256"],
        artifacts["l2_receipt"]["sha256"],
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
    _require_equal(stage["image_id"], build_checker.LEAF_IMAGE_ID, "leaf.image_id")
    for field in ("verified_program_manifest_root", "action_nullifier_root", "statement_hash"):
        _require_nonzero_hash(stage[field], f"leaf.{field}")
    _require_equal(stage["receipt_profile_id"], SUCCINCT_PROFILE_ID, "leaf.receipt_profile_id")
    for field, artifact_id, label in (
        ("receipt_sha256", "leaf_receipt", "leaf receipt"),
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
) -> None:
    stage = _exact_object(
        value,
        {"ok", "image_id", "child_receipt_sha256", "receipt_sha256", "verified_child_count"},
        f"stages.{label}",
    )
    _require_exact_bool(stage["ok"], f"{label}.ok", expected=True)
    _require_equal(stage["image_id"], expected_image, f"{label}.image_id")
    _require_hash_equal(
        stage["child_receipt_sha256"],
        expected_child_receipt,
        f"{label} child receipt",
    )
    _require_hash_equal(stage["receipt_sha256"], expected_receipt, f"{label} receipt")
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
    _require_equal(
        stage["mutation_error_code"],
        MUTATION_ERROR_CODE,
        "external_verifier.mutation_error_code",
    )
    for field, artifact_id, label in (
        ("positive_receipt_sha256", "settlement_receipt", "external positive receipt"),
        ("positive_guest_input_sha256", "settlement_guest_input", "external positive guest input"),
        ("positive_output_sha256", "external_verifier_output", "external verifier output"),
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
) -> int:
    root = directory.resolve(strict=True)
    if not root.is_dir():
        raise EvidenceError("artifact directory is not a directory")
    checked = 0
    for artifact_id, path, _kind in ARTIFACT_SPECS:
        artifact = artifacts[artifact_id]
        try:
            candidate = build_checker._resolve_artifact(root, path)
            size, digest = build_checker._stable_file_facts(candidate)
        except build_checker.BuildRecordError as exc:
            raise EvidenceError(str(exc)) from exc
        if size != artifact["size_bytes"] or digest != artifact["sha256"]:
            raise EvidenceError(f"external artifact identity mismatch: {artifact_id}")
        checked += 1
    return checked


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
    expected_evidence_sha256: str | None = None,
) -> dict[str, Any]:
    try:
        document, raw = load_evidence(path)
        return validate_evidence(
            document,
            raw,
            artifact_directory=artifact_directory,
            build_record_path=build_record_path,
            expected_evidence_sha256=expected_evidence_sha256,
        )
    except (OSError, EvidenceError, build_checker.BuildRecordError) as exc:
        return {
            "ok": False,
            "schema": REPORT_SCHEMA,
            "errors": [str(exc)],
            "governed_anchor_checked": False,
            "build_record_rechecked": False,
            "external_artifact_files_checked": 0,
            "release_authority": False,
            "settlement_authority": False,
            "production_authority": False,
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence", type=Path, default=DEFAULT_EVIDENCE)
    parser.add_argument("--artifact-directory", type=Path)
    parser.add_argument("--build-record", type=Path)
    parser.add_argument("--expected-evidence-sha256")
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args()
    report = check_evidence(
        arguments.evidence,
        artifact_directory=arguments.artifact_directory,
        build_record_path=arguments.build_record,
        expected_evidence_sha256=arguments.expected_evidence_sha256,
    )
    if arguments.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print("accepted" if report["ok"] else "rejected")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
