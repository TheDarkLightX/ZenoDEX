#!/usr/bin/env python3
"""Build one deterministic, fail-closed Spot V6 candidate evidence bundle.

Every input path is explicit. Inputs are snapshotted through bounded regular
file descriptors before any output is created. The resulting evidence is
validated for internal consistency by the V2 checker, including fresh image-ID
recomputation through the pinned r0vm. A digest computed during generation is
never treated as an independently governed anchor. This builder cannot enable
scoped replay, ledger, release, settlement, privacy, general-scaling, or
production authority.

The supplied proof and replay reports propose execution history. This builder
does not execute either sealed verifier, so its successful result remains a
candidate pending a separately governed digest and live replay gate. Bundle and
evidence publication use two atomic renames and are not one atomic transaction.
Scoped validation remains a separate checker operation that requires both a
pre-existing governed digest and an explicit request to require the scoped
claim.
"""

from __future__ import annotations

import argparse
import ctypes
import errno
import hashlib
import json
import os
import stat
import sys
from dataclasses import dataclass
from datetime import date
from pathlib import Path
from typing import Any, Mapping, NoReturn, Sequence

if __package__:
    from tools import check_zrpf_source_opened_spot_v6_build_record as build_checker
    from tools import check_zrpf_source_opened_spot_v6_local_evidence as evidence_checker
else:
    sys.path.insert(0, Path(__file__).resolve().parents[1].as_posix())
    from tools import check_zrpf_source_opened_spot_v6_build_record as build_checker
    from tools import check_zrpf_source_opened_spot_v6_local_evidence as evidence_checker

MAX_REPORT_BYTES = 2 * 1024 * 1024
MAX_TOTAL_ARTIFACT_BYTES = 256 * 1024 * 1024
MAX_TOTAL_REPORT_BYTES = 8 * 1024 * 1024
READ_CHUNK_BYTES = 1024 * 1024

EXPECTED_EVIDENCE_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_local_evidence/v2"
EXPECTED_BUILD_RECORD_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_build_record/v2"
EXPECTED_ARTIFACT_SPECS = (
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
    ("settlement_admission_journal", "settlement_admission_journal.bin", "binary"),
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
    ("external_verifier_output", "external_verifier_output.json", "canonical_json"),
    ("chain_verifier_output", "chain_verifier_output.json", "canonical_json"),
)
EXPECTED_EXECUTED_COMMAND_FIELDS = {
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
EXPECTED_TRUE_CLAIMS = {
    "all_retained_layer_seal_mutations_rejected",
    "current_v6_dependency_chain_verified",
    "exact_settlement_seal_mutation_rejected",
    "fake_receipt_rejected_with_dev_mode_disabled",
    "four_stage_succinct_receipts_generated",
    "normal_and_ambient_dev_chain_outputs_identical",
    "source_opened_singleton_spot_execution_verified",
    "source_to_settlement_artifact_hash_chain_bound",
}
EXPECTED_FALSE_CLAIMS = {
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

REPORT_IDS = (
    "source_opening",
    "leaf",
    "level_one",
    "level_two",
    "settlement",
    "retained_replay",
)

SOURCE_OPENING_NONCLAIMS = (
    "this run supplies one retained source receipt and no aggregate authority",
    "source proving alone grants no settlement, ledger, release, or production authority",
)
LEAF_NONCLAIMS = (
    "the V6 receipt alone grants no ledger, settlement, release, or production authority",
    "this report proves one bounded singleton Spot transition and no maximum-fanout throughput claim",
)
SETTLEMENT_NONCLAIMS = (
    "the accepted source receipt does not establish an end-user signature scheme",
    "this local receipt grants no release, governance, Tau-finality, or production authority",
)


class EvidenceBuildError(ValueError):
    """Stable fail-closed evidence-builder rejection."""


@dataclass(frozen=True)
class BuildResult:
    evidence_path: Path
    bundle_directory: Path
    evidence_sha256: str
    build_record_sha256: str
    artifact_count: int
    candidate_bundle_built: bool = True
    scoped_local_replay_claim_allowed: bool = False
    bundle_and_evidence_publication_atomic: bool = False
    release_authority: bool = False
    settlement_authority: bool = False
    production_authority: bool = False


@dataclass(frozen=True)
class _InputSnapshot:
    artifact_raw: dict[str, bytes]
    report_raw: dict[str, bytes]
    build_raw: bytes
    build_document: dict[str, Any]
    build_record_sha256: str


@dataclass(frozen=True)
class _AggregateReportSpec:
    label: str
    schema: str
    status: str
    image_id: str
    child_artifact: str
    receipt_artifact: str


L1_REPORT_SPEC = _AggregateReportSpec(
    label="level_one",
    schema="zenodex/zrpf_source_opened_spot_value_aggregate_l1_v6_proof_report/v1",
    status="source_opened_spot_value_aggregate_l1_v6_succinct_receipt_verified",
    image_id=build_checker.L1_IMAGE_ID,
    child_artifact="leaf_receipt",
    receipt_artifact="l1_receipt",
)
L2_REPORT_SPEC = _AggregateReportSpec(
    label="level_two",
    schema="zenodex/zrpf_source_opened_spot_value_aggregate_l2_v6_proof_report/v1",
    status="source_opened_spot_value_aggregate_l2_v6_succinct_receipt_verified",
    image_id=build_checker.L2_IMAGE_ID,
    child_artifact="l1_receipt",
    receipt_artifact="l2_receipt",
)


def build_evidence(
    *,
    recorded_at: str,
    artifact_paths: Mapping[str, Path],
    report_paths: Mapping[str, Path],
    build_record_path: Path,
    r0vm_path: Path,
    bundle_directory: Path,
    evidence_path: Path,
) -> BuildResult:
    """Build and self-check one exact singleton Spot V6 candidate bundle.

    All arguments are explicit and deterministic. ``recorded_at`` is supplied
    by the caller; no wall clock, network, environment, or implicit artifact
    discovery participates in the evidence bytes.
    """

    _require_checker_contract()
    _require_canonical_date(recorded_at)
    expected_artifact_ids = {
        artifact_id for artifact_id, _path, _kind in EXPECTED_ARTIFACT_SPECS
    }
    _require_exact_path_inventory(artifact_paths, expected_artifact_ids, "artifact")
    _require_exact_path_inventory(report_paths, set(REPORT_IDS), "report")
    bundle = _new_output_path(bundle_directory, "bundle directory")
    evidence_output = _new_output_path(evidence_path, "evidence path")
    if _path_is_within(evidence_output, bundle):
        raise EvidenceBuildError("evidence path must be outside the exact artifact bundle")
    snapshot = _snapshot_inputs(
        artifact_paths,
        report_paths,
        build_record_path,
        r0vm_path,
    )
    document, evidence_raw, evidence_sha256 = _compose_evidence(
        recorded_at,
        snapshot,
    )
    staged_bundle = _new_output_path(
        bundle.with_name(f".{bundle.name}.candidate-staging"),
        "staged bundle directory",
    )
    staged_evidence = _new_output_path(
        evidence_output.with_name(f".{evidence_output.name}.candidate-staging"),
        "staged evidence path",
    )
    try:
        _write_bundle(staged_bundle, snapshot.artifact_raw)
        _self_check_candidate(
            document=document,
            evidence_raw=evidence_raw,
            bundle=staged_bundle,
            build_record_path=build_record_path,
            r0vm_path=r0vm_path,
        )
        _write_new(staged_evidence, evidence_raw)
        _fsync_directory(staged_evidence.parent)
        _publish_candidate(
            staged_bundle,
            staged_evidence,
            bundle,
            evidence_output,
        )
    except BaseException:
        _cleanup_candidate_staging(staged_bundle, staged_evidence)
        raise
    return BuildResult(
        evidence_path=evidence_output,
        bundle_directory=bundle,
        evidence_sha256=evidence_sha256,
        build_record_sha256=snapshot.build_record_sha256,
        artifact_count=len(snapshot.artifact_raw),
    )


def _snapshot_inputs(
    artifact_paths: Mapping[str, Path],
    report_paths: Mapping[str, Path],
    build_record_path: Path,
    r0vm_path: Path,
) -> _InputSnapshot:
    artifact_raw = _snapshot_artifacts(artifact_paths)
    report_raw = _snapshot_reports(report_paths)
    build_raw = _read_stable_bytes(
        build_record_path,
        maximum_bytes=build_checker.MAX_RECORD_BYTES,
        label="build record",
    )
    build_document = _load_pretty_canonical_object(build_raw, "build record")
    try:
        build_checker.validate_record(build_document, build_raw)
    except build_checker.BuildRecordError as exc:
        raise EvidenceBuildError(f"build record rejected: {exc}") from exc
    _validate_build_program_bindings(build_document, artifact_raw)
    r0vm_raw = _read_stable_bytes(
        r0vm_path,
        maximum_bytes=build_checker.MAX_R0VM_BYTES,
        label="r0vm",
    )
    _require_equal(
        _sha256(r0vm_raw),
        build_checker._tool_sha256(build_document["toolchain"]["r0vm"], "r0vm"),
        "r0vm SHA-256",
    )
    return _InputSnapshot(
        artifact_raw=artifact_raw,
        report_raw=report_raw,
        build_raw=build_raw,
        build_document=build_document,
        build_record_sha256=_sha256(build_raw),
    )


def _snapshot_artifacts(artifact_paths: Mapping[str, Path]) -> dict[str, bytes]:
    result: dict[str, bytes] = {}
    total_bytes = 0
    for artifact_id, _canonical_path, kind in EXPECTED_ARTIFACT_SPECS:
        raw = _read_stable_bytes(
            artifact_paths[artifact_id],
            maximum_bytes=build_checker.MAX_ARTIFACT_BYTES,
            label=f"artifact {artifact_id}",
        )
        total_bytes += len(raw)
        if total_bytes > MAX_TOTAL_ARTIFACT_BYTES:
            raise EvidenceBuildError("total artifact input exceeds governed bound")
        _validate_artifact_bytes(artifact_id, kind, raw)
        result[artifact_id] = raw
    return result


def _snapshot_reports(report_paths: Mapping[str, Path]) -> dict[str, bytes]:
    result: dict[str, bytes] = {}
    total_bytes = 0
    for report_id in REPORT_IDS:
        raw = _read_stable_bytes(
            report_paths[report_id],
            maximum_bytes=MAX_REPORT_BYTES,
            label=f"report {report_id}",
        )
        total_bytes += len(raw)
        if total_bytes > MAX_TOTAL_REPORT_BYTES:
            raise EvidenceBuildError("total report input exceeds governed bound")
        result[report_id] = raw
    return result


def _compose_evidence(
    recorded_at: str,
    snapshot: _InputSnapshot,
) -> tuple[dict[str, Any], bytes, str]:
    artifacts = _artifact_rows(snapshot.artifact_raw)
    facts = {row["id"]: row for row in artifacts}
    reports = {
        report_id: _load_canonical_json_line(raw, f"{report_id} report")
        for report_id, raw in snapshot.report_raw.items()
    }
    _require_equal(
        reports["source_opening"].get("r0vm_sha256"),
        build_checker._tool_sha256(snapshot.build_document["toolchain"]["r0vm"], "r0vm"),
        "source/build r0vm SHA-256",
    )
    _validate_relations(snapshot.artifact_raw, facts)
    document = {
        "schema": EXPECTED_EVIDENCE_SCHEMA,
        "recorded_at": recorded_at,
        "build_record_sha256": snapshot.build_record_sha256,
        "images": _image_inventory(),
        "artifacts": artifacts,
        "stages": _derive_stages(reports, facts, snapshot.artifact_raw),
        "executed_commands": {
            field: True for field in sorted(EXPECTED_EXECUTED_COMMAND_FIELDS)
        },
        "claims": {
            **{field: True for field in sorted(EXPECTED_TRUE_CLAIMS)},
            **{field: False for field in sorted(EXPECTED_FALSE_CLAIMS)},
        },
    }
    raw = evidence_checker.canonical_bytes(document)
    if len(raw) > evidence_checker.MAX_EVIDENCE_BYTES:
        raise EvidenceBuildError("generated evidence exceeds checker byte bound")
    return document, raw, _sha256(raw)


def _image_inventory() -> dict[str, str]:
    return {
        "source_spot_v1": build_checker.SOURCE_SPOT_IMAGE_ID,
        "adapter_v3": build_checker.ADAPTER_IMAGE_ID,
        "spot_value_leaf_v6": build_checker.LEAF_IMAGE_ID,
        "spot_value_aggregate_l1_v6": build_checker.L1_IMAGE_ID,
        "spot_value_aggregate_l2_v6": build_checker.L2_IMAGE_ID,
        "source_opened_spot_settlement_v6": build_checker.SETTLEMENT_IMAGE_ID,
    }


def _write_bundle(bundle: Path, artifact_raw: Mapping[str, bytes]) -> None:
    bundle.mkdir(mode=0o700, parents=False, exist_ok=False)
    for artifact_id, canonical_path, _kind in EXPECTED_ARTIFACT_SPECS:
        _write_new(bundle / canonical_path, artifact_raw[artifact_id])
    _fsync_directory(bundle)
    _require_exact_output_inventory(bundle)


def _self_check_candidate(
    *,
    document: dict[str, Any],
    evidence_raw: bytes,
    bundle: Path,
    build_record_path: Path,
    r0vm_path: Path,
) -> None:
    try:
        report = evidence_checker.validate_evidence(
            document,
            evidence_raw,
            artifact_directory=bundle,
            build_record_path=build_record_path,
            r0vm_path=r0vm_path,
        )
    except (
        OSError,
        evidence_checker.EvidenceError,
        build_checker.BuildRecordError,
    ) as exc:
        raise EvidenceBuildError(f"generated evidence self-check rejected: {exc}") from exc
    required_counts = {
        "program_image_ids_recomputed": len(build_checker.PROGRAM_SPECS),
        "external_artifact_files_checked": len(EXPECTED_ARTIFACT_SPECS),
        "exact_mutation_relations_checked": 4,
        "verifier_transcripts_checked": 2,
    }
    if report["build_record_rechecked"] is not True:
        raise EvidenceBuildError("candidate build record was not rechecked")
    for field, expected in required_counts.items():
        if report[field] != expected:
            raise EvidenceBuildError(f"candidate self-check {field} mismatch")
    if report["governed_anchor_checked"] is not False:
        raise EvidenceBuildError("candidate self-check manufactured a governed anchor")
    if report["scoped_local_replay_claim_allowed"] is not False:
        raise EvidenceBuildError("candidate self-check promoted the scoped replay claim")
    for field in ("release_authority", "settlement_authority", "production_authority"):
        if report[field] is not False:
            raise EvidenceBuildError(f"generated evidence unexpectedly promoted {field}")


def _publish_candidate(
    staged_bundle: Path,
    staged_evidence: Path,
    bundle: Path,
    evidence: Path,
) -> None:
    if bundle.exists() or bundle.is_symlink() or evidence.exists() or evidence.is_symlink():
        raise EvidenceBuildError("candidate output appeared before atomic publication")
    bundle_published = False
    evidence_published = False
    try:
        _rename_no_replace(staged_bundle, bundle)
        bundle_published = True
        _rename_no_replace(staged_evidence, evidence)
        evidence_published = True
        _fsync_directory(bundle.parent)
        if evidence.parent != bundle.parent:
            _fsync_directory(evidence.parent)
    except OSError as exc:
        rollback_failed = False
        if evidence_published:
            try:
                _rename_no_replace(evidence, staged_evidence)
            except OSError:
                rollback_failed = True
        if bundle_published:
            try:
                _rename_no_replace(bundle, staged_bundle)
            except OSError:
                rollback_failed = True
        if rollback_failed:
            raise EvidenceBuildError("candidate publication and rollback failed") from exc
        raise EvidenceBuildError("candidate publication failed and was rolled back") from exc


def _rename_no_replace(source: Path, destination: Path) -> None:
    """Atomically rename one staged output without replacing any destination."""

    libc = ctypes.CDLL(None, use_errno=True)
    renameat2: Any = getattr(libc, "renameat2", None)
    if renameat2 is None:
        raise OSError(errno.ENOSYS, "renameat2 is required for no-replace publication")
    renameat2.argtypes = (
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_uint,
    )
    renameat2.restype = ctypes.c_int
    ctypes.set_errno(0)
    result = renameat2(
        -100,  # AT_FDCWD
        os.fsencode(source),
        -100,
        os.fsencode(destination),
        1,  # RENAME_NOREPLACE
    )
    if result == 0:
        return
    error_number = ctypes.get_errno()
    if error_number == 0:
        error_number = errno.EIO
    raise OSError(
        error_number,
        os.strerror(error_number),
        os.fspath(destination),
    )


def _cleanup_candidate_staging(staged_bundle: Path, staged_evidence: Path) -> None:
    if staged_evidence.exists() and not staged_evidence.is_symlink():
        try:
            staged_evidence.unlink()
        except OSError:
            pass
    if not staged_bundle.exists() or staged_bundle.is_symlink():
        return
    for _artifact_id, path, _kind in EXPECTED_ARTIFACT_SPECS:
        candidate = staged_bundle / path
        if candidate.exists() and not candidate.is_symlink():
            try:
                candidate.unlink()
            except OSError:
                pass
    try:
        staged_bundle.rmdir()
    except OSError:
        pass


def _require_checker_contract() -> None:
    if evidence_checker.EVIDENCE_SCHEMA != EXPECTED_EVIDENCE_SCHEMA:
        raise EvidenceBuildError("V2 evidence checker schema changed")
    if build_checker.RECORD_SCHEMA != EXPECTED_BUILD_RECORD_SCHEMA:
        raise EvidenceBuildError("V2 build-record checker schema changed")
    if evidence_checker.ARTIFACT_SPECS != EXPECTED_ARTIFACT_SPECS:
        raise EvidenceBuildError("V2 evidence artifact contract changed")
    if evidence_checker.EXECUTED_COMMAND_FIELDS != EXPECTED_EXECUTED_COMMAND_FIELDS:
        raise EvidenceBuildError("V2 executed-command contract changed")
    if evidence_checker.TRUE_CLAIMS != EXPECTED_TRUE_CLAIMS:
        raise EvidenceBuildError("V2 positive-claim contract changed")
    if evidence_checker.FALSE_CLAIMS != EXPECTED_FALSE_CLAIMS:
        raise EvidenceBuildError("V2 nonclaim contract changed")


def _artifact_rows(raw_by_id: Mapping[str, bytes]) -> list[dict[str, Any]]:
    return [
        {
            "id": artifact_id,
            "path": path,
            "kind": kind,
            "size_bytes": len(raw_by_id[artifact_id]),
            "sha256": _sha256(raw_by_id[artifact_id]),
        }
        for artifact_id, path, kind in evidence_checker.ARTIFACT_SPECS
    ]


def _derive_stages(
    reports: Mapping[str, dict[str, Any]],
    facts: Mapping[str, dict[str, Any]],
    artifact_raw: Mapping[str, bytes],
) -> dict[str, Any]:
    source = _validate_source_report(reports["source_opening"], facts)
    leaf = _validate_leaf_report(reports["leaf"], facts)
    level_one = _validate_aggregate_report(reports["level_one"], L1_REPORT_SPEC, facts)
    level_two = _validate_aggregate_report(reports["level_two"], L2_REPORT_SPEC, facts)
    settlement = _validate_settlement_report(reports["settlement"], facts)
    replay = _validate_replay_report(reports["retained_replay"], facts)
    chain = _load_canonical_json_line(
        artifact_raw["chain_verifier_output"],
        "chain verifier output",
    )
    _require_equal(
        chain.get("settlement_claim_binding"),
        settlement["settlement_claim_binding"],
        "chain/settlement claim binding",
    )
    return {
        "source_opening": source,
        "adapter": {
            "image_id": build_checker.ADAPTER_IMAGE_ID,
            "receipt_sha256": facts["adapter_receipt"]["sha256"],
            "receipt_kind": "succinct",
            "verified": True,
        },
        "leaf": _leaf_stage(leaf, facts),
        "level_one": {
            **level_one,
            "mutation_receipt_sha256": facts["l1_mutation_receipt"]["sha256"],
            "mutation_rejected": True,
        },
        "level_two": {
            **level_two,
            "mutation_receipt_sha256": facts["l2_mutation_receipt"]["sha256"],
            "mutation_rejected": True,
        },
        "settlement": settlement,
        "external_verifier": _external_verifier_stage(replay, facts),
    }


def _leaf_stage(
    leaf: Mapping[str, str], facts: Mapping[str, dict[str, Any]]
) -> dict[str, Any]:
    return {
        "ok": True,
        "image_id": build_checker.LEAF_IMAGE_ID,
        "receipt_sha256": facts["leaf_receipt"]["sha256"],
        "mutation_receipt_sha256": facts["leaf_mutation_receipt"]["sha256"],
        "mutation_rejected": True,
        "receipt_profile_id": evidence_checker.SUCCINCT_PROFILE_ID,
        "source_proof_sha256": facts["source_proof"]["sha256"],
        "adapter_receipt_sha256": facts["adapter_receipt"]["sha256"],
        "source_envelope_sha256": facts["leaf_source_envelope"]["sha256"],
        "verified_program_manifest_root": leaf["verified_program_manifest_root"],
        "action_nullifier_root": leaf["action_nullifier_root"],
        "statement_hash": leaf["statement_hash"],
    }


def _external_verifier_stage(
    replay: Mapping[str, Any], facts: Mapping[str, dict[str, Any]]
) -> dict[str, Any]:
    return {
        "positive_receipt_sha256": facts["settlement_receipt"]["sha256"],
        "positive_guest_input_sha256": facts["settlement_guest_input"]["sha256"],
        "positive_output_sha256": facts["external_verifier_output"]["sha256"],
        "chain_output_sha256": facts["chain_verifier_output"]["sha256"],
        "ambient_dev_chain_output_sha256": replay["ambient_dev_chain_output_sha256"],
        "normal_dev_outputs_equal": True,
        "fake_receipt_rejected": True,
        "positive_receipts_verified": 4,
        "exact_seal_mutations_rejected": 4,
        "mutation_receipt_sha256": facts["settlement_mutation_receipt"]["sha256"],
        "mutation_rejected": True,
        "mutation_error_code": evidence_checker.MUTATION_ERROR_CODE,
    }


def _validate_source_report(
    value: dict[str, Any], facts: Mapping[str, dict[str, Any]]
) -> dict[str, Any]:
    report = _exact_object(
        value,
        {
            "schema",
            "ok",
            "source_image_id",
            "source_program_sha256",
            "source_cli_sha256",
            "generator_sha256",
            "r0vm_sha256",
            "request_bytes",
            "request_sha256",
            "proof_bytes",
            "proof_sha256",
            "receipt_kind",
            "nonclaims",
        },
        "source opening report",
    )
    _require_equal(report["schema"], "zenodex/zrpf_spot_source_opening_run/v1", "source schema")
    _require_true(report["ok"], "source ok")
    _require_equal(report["source_image_id"], build_checker.SOURCE_SPOT_IMAGE_ID, "source image ID")
    for field in ("source_program_sha256", "source_cli_sha256", "generator_sha256", "r0vm_sha256"):
        _require_nonzero_hash(report[field], f"source {field}")
    _require_size_hash(report, "request", facts["source_request"], "source request")
    _require_size_hash(report, "proof", facts["source_proof"], "source proof")
    _require_equal(report["receipt_kind"], "succinct", "source receipt kind")
    _require_exact_sequence(report["nonclaims"], SOURCE_OPENING_NONCLAIMS, "source nonclaims")
    return {
        "ok": True,
        "source_image_id": build_checker.SOURCE_SPOT_IMAGE_ID,
        "source_program_sha256": report["source_program_sha256"],
        "source_cli_sha256": report["source_cli_sha256"],
        "generator_sha256": report["generator_sha256"],
        "r0vm_sha256": report["r0vm_sha256"],
        "request_sha256": facts["source_request"]["sha256"],
        "proof_sha256": facts["source_proof"]["sha256"],
        "receipt_kind": "succinct",
    }


def _validate_leaf_report(
    value: dict[str, Any], facts: Mapping[str, dict[str, Any]]
) -> dict[str, str]:
    report = _exact_object(
        value,
        {
            "action_nullifier_root",
            "adapter_receipt_sha256",
            "candidate_accepted",
            "guest_program_binary_bytes",
            "guest_program_binary_sha256",
            "ok",
            "receipt_bytes",
            "receipt_profile_id",
            "receipt_sha256",
            "source_envelope_bytes",
            "source_envelope_sha256",
            "schema",
            "source_proof_sha256",
            "statement_hash",
            "status",
            "v6_image_id",
            "verified_program_manifest_root",
            "nonclaims",
        },
        "leaf report",
    )
    _require_equal(report["schema"], "zenodex/zrpf_source_opened_spot_value_leaf_v6_proof_report/v2", "leaf schema")
    _require_equal(report["status"], "source_opened_spot_value_leaf_v6_succinct_receipt_verified", "leaf status")
    _require_true(report["ok"], "leaf ok")
    _require_true(report["candidate_accepted"], "leaf candidate_accepted")
    _require_equal(report["v6_image_id"], build_checker.LEAF_IMAGE_ID, "leaf image ID")
    _require_equal(report["receipt_profile_id"], evidence_checker.SUCCINCT_PROFILE_ID, "leaf receipt profile")
    _require_size_hash(report, "receipt", facts["leaf_receipt"], "leaf receipt")
    _require_size_hash(report, "source_envelope", facts["leaf_source_envelope"], "leaf source envelope")
    _require_equal(report["source_proof_sha256"], facts["source_proof"]["sha256"], "leaf source proof SHA-256")
    _require_equal(report["adapter_receipt_sha256"], facts["adapter_receipt"]["sha256"], "leaf adapter receipt SHA-256")
    _require_equal(report["guest_program_binary_bytes"], facts["leaf_program_binary"]["size_bytes"], "leaf program byte length")
    _require_equal(report["guest_program_binary_sha256"], facts["leaf_program_binary"]["sha256"], "leaf program SHA-256")
    for field in ("verified_program_manifest_root", "action_nullifier_root", "statement_hash"):
        _require_nonzero_hash(report[field], f"leaf {field}")
    _require_exact_sequence(report["nonclaims"], LEAF_NONCLAIMS, "leaf nonclaims")
    return {
        "verified_program_manifest_root": report["verified_program_manifest_root"],
        "action_nullifier_root": report["action_nullifier_root"],
        "statement_hash": report["statement_hash"],
    }


def _validate_aggregate_report(
    value: dict[str, Any],
    spec: _AggregateReportSpec,
    facts: Mapping[str, dict[str, Any]],
) -> dict[str, Any]:
    report = _exact_object(
        value,
        {"child_receipt_sha256", "image_id", "ok", "receipt_bytes", "receipt_sha256", "schema", "status", "verified_child_count"},
        f"{spec.label} report",
    )
    _require_equal(report["schema"], spec.schema, f"{spec.label} schema")
    _require_equal(report["status"], spec.status, f"{spec.label} status")
    _require_true(report["ok"], f"{spec.label} ok")
    _require_equal(report["image_id"], spec.image_id, f"{spec.label} image ID")
    _require_equal(
        report["verified_child_count"], 1, f"{spec.label} verified child count"
    )
    _require_equal(
        report["child_receipt_sha256"],
        facts[spec.child_artifact]["sha256"],
        f"{spec.label} child receipt SHA-256",
    )
    _require_size_hash(
        report,
        "receipt",
        facts[spec.receipt_artifact],
        f"{spec.label} receipt",
    )
    return {
        "ok": True,
        "image_id": spec.image_id,
        "child_receipt_sha256": facts[spec.child_artifact]["sha256"],
        "receipt_sha256": facts[spec.receipt_artifact]["sha256"],
        "verified_child_count": 1,
    }


def _validate_settlement_report(
    value: dict[str, Any], facts: Mapping[str, dict[str, Any]]
) -> dict[str, Any]:
    report = _exact_object(
        value,
        {
            "action_count", "admission_journal_bytes", "admission_journal_sha256",
            "consumed_object_count", "data_availability_certificate_bytes",
            "data_availability_certificate_sha256", "image_id", "l2_receipt_sha256",
            "mutation_receipt_sha256", "mutation_rejected", "ok", "receipt_bytes",
            "receipt_sha256", "replay_bytes", "replay_sha256", "schema",
            "source_envelope_sha256", "status", "settlement_claim_binding",
            "settlement_program_manifest_root", "settlement_program_id",
            "succinct_receipt_profile_id", "guest_input_bytes", "guest_input_sha256",
            "nonclaims",
        },
        "settlement report",
    )
    _require_equal(report["schema"], "zenodex/zrpf_source_opened_spot_settlement_v6_proof_report/v1", "settlement schema")
    _require_equal(report["status"], "source_opened_spot_settlement_v6_succinct_receipt_verified", "settlement status")
    _require_true(report["ok"], "settlement ok")
    _require_true(report["mutation_rejected"], "settlement mutation_rejected")
    _require_equal(report["image_id"], build_checker.SETTLEMENT_IMAGE_ID, "settlement image ID")
    _require_equal(report["settlement_program_id"], build_checker.SETTLEMENT_IMAGE_ID, "settlement program ID")
    _require_equal(report["succinct_receipt_profile_id"], evidence_checker.SUCCINCT_PROFILE_ID, "settlement receipt profile")
    for field in ("action_count", "consumed_object_count"):
        _require_equal(report[field], 1, f"settlement {field}")
    _require_equal(report["l2_receipt_sha256"], facts["l2_receipt"]["sha256"], "settlement L2 receipt SHA-256")
    _require_equal(report["source_envelope_sha256"], facts["leaf_source_envelope"]["sha256"], "settlement source envelope SHA-256")
    _require_size_hash(report, "receipt", facts["settlement_receipt"], "settlement receipt")
    _require_equal(report["mutation_receipt_sha256"], facts["settlement_mutation_receipt"]["sha256"], "settlement mutation receipt SHA-256")
    _require_size_hash(report, "admission_journal", facts["settlement_admission_journal"], "settlement admission journal")
    _require_size_hash(report, "guest_input", facts["settlement_guest_input"], "settlement guest input")
    _require_size_hash(report, "replay", facts["settlement_replay"], "settlement replay")
    _require_equal(report["data_availability_certificate_bytes"], facts["settlement_da_certificate"]["size_bytes"], "settlement DA certificate byte length")
    _require_equal(report["data_availability_certificate_sha256"], facts["settlement_da_certificate"]["sha256"], "settlement DA certificate SHA-256")
    for field in ("settlement_claim_binding", "settlement_program_manifest_root"):
        _require_nonzero_hash(report[field], f"settlement {field}")
    _require_exact_sequence(report["nonclaims"], SETTLEMENT_NONCLAIMS, "settlement nonclaims")
    return {
        "ok": True,
        "image_id": build_checker.SETTLEMENT_IMAGE_ID,
        "l2_receipt_sha256": facts["l2_receipt"]["sha256"],
        "source_envelope_sha256": facts["leaf_source_envelope"]["sha256"],
        "receipt_sha256": facts["settlement_receipt"]["sha256"],
        "mutation_receipt_sha256": facts["settlement_mutation_receipt"]["sha256"],
        "mutation_rejected": True,
        "admission_journal_sha256": facts["settlement_admission_journal"]["sha256"],
        "guest_input_sha256": facts["settlement_guest_input"]["sha256"],
        "replay_sha256": facts["settlement_replay"]["sha256"],
        "data_availability_certificate_sha256": facts["settlement_da_certificate"]["sha256"],
        "settlement_claim_binding": report["settlement_claim_binding"],
        "settlement_program_manifest_root": report["settlement_program_manifest_root"],
        "settlement_program_id": build_checker.SETTLEMENT_IMAGE_ID,
        "succinct_receipt_profile_id": evidence_checker.SUCCINCT_PROFILE_ID,
        "action_count": 1,
        "consumed_object_count": 1,
    }


def _validate_replay_report(
    value: dict[str, Any], facts: Mapping[str, dict[str, Any]]
) -> dict[str, Any]:
    report = _exact_object(
        value,
        {
            "ambient_dev_chain_output_sha256", "chain_verifier_sha256",
            "exact_seal_mutations_rejected", "fake_receipt_rejected",
            "normal_chain_output_sha256", "normal_dev_outputs_equal", "ok",
            "positive_receipts_verified", "production_authority", "release_authority",
            "schema", "settlement_authority", "settlement_mutation_error_code",
            "settlement_verifier_sha256", "settlement_verifier_output_sha256",
        },
        "retained replay report",
    )
    _require_equal(report["schema"], "zenodex/zrpf_source_opened_spot_v6_retained_replay/v1", "replay schema")
    _require_true(report["ok"], "replay ok")
    _require_true(report["normal_dev_outputs_equal"], "replay normal_dev_outputs_equal")
    _require_true(report["fake_receipt_rejected"], "replay fake_receipt_rejected")
    for field in ("positive_receipts_verified", "exact_seal_mutations_rejected"):
        _require_equal(report[field], 4, f"replay {field}")
    for field in ("release_authority", "settlement_authority", "production_authority"):
        _require_false(report[field], f"replay {field}")
    _require_equal(report["settlement_mutation_error_code"], evidence_checker.MUTATION_ERROR_CODE, "replay mutation error code")
    _require_equal(report["normal_chain_output_sha256"], facts["chain_verifier_output"]["sha256"], "replay normal chain output SHA-256")
    _require_equal(report["ambient_dev_chain_output_sha256"], facts["chain_verifier_output"]["sha256"], "replay ambient-dev chain output SHA-256")
    _require_equal(report["settlement_verifier_output_sha256"], facts["external_verifier_output"]["sha256"], "replay settlement verifier output SHA-256")
    for field in ("chain_verifier_sha256", "settlement_verifier_sha256"):
        _require_nonzero_hash(report[field], f"replay {field}")
    return report


def _validate_relations(
    artifact_raw: Mapping[str, bytes], facts: Mapping[str, dict[str, Any]]
) -> None:
    try:
        for positive, mutation in (
            ("leaf_receipt", "leaf_mutation_receipt"),
            ("l1_receipt", "l1_mutation_receipt"),
            ("l2_receipt", "l2_mutation_receipt"),
            ("settlement_receipt", "settlement_mutation_receipt"),
        ):
            evidence_checker._validate_exact_succinct_seal_mutation(
                artifact_raw[positive], artifact_raw[mutation]
            )
        evidence_checker._validate_external_verifier_output(
            artifact_raw["external_verifier_output"], dict(facts)
        )
        evidence_checker._validate_chain_verifier_output(
            artifact_raw["chain_verifier_output"], dict(facts)
        )
    except evidence_checker.EvidenceError as exc:
        raise EvidenceBuildError(f"artifact relation rejected: {exc}") from exc


def _validate_build_program_bindings(
    record: dict[str, Any], artifact_raw: Mapping[str, bytes]
) -> None:
    artifact_by_stage = {
        stage: artifact_id
        for (stage, _package, _path, _image, _child, _child_image), (
            artifact_id,
            _artifact_path,
            _kind,
        ) in zip(build_checker.PROGRAM_SPECS, evidence_checker.ARTIFACT_SPECS[16:20], strict=True)
    }
    programs = record.get("programs")
    if type(programs) is not list or len(programs) != len(artifact_by_stage):
        raise EvidenceBuildError("build record program inventory mismatch")
    for row in programs:
        if type(row) is not dict or row.get("stage") not in artifact_by_stage:
            raise EvidenceBuildError("build record program stage mismatch")
        raw = artifact_raw[artifact_by_stage[row["stage"]]]
        _require_equal(row.get("program_binary_bytes"), len(raw), "build program byte length")
        _require_equal(row.get("program_binary_sha256"), _sha256(raw), "build program SHA-256")


def _validate_artifact_bytes(artifact_id: str, kind: str, raw: bytes) -> None:
    if kind == "canonical_json":
        _load_canonical_json_line(raw, f"artifact {artifact_id}")
        return
    if kind == "canonical_receipt_json":
        value = _load_canonical_compact_json(raw, f"artifact {artifact_id}")
        if type(value) is not dict:
            raise EvidenceBuildError(f"artifact {artifact_id} receipt must be an object")
        try:
            evidence_checker._succinct_seal(value, f"artifact {artifact_id}")
        except evidence_checker.EvidenceError as exc:
            raise EvidenceBuildError(str(exc)) from exc
        return
    if kind == "risc0_program_binary":
        if len(raw) < 8 or raw[:4] != b"R0BF":
            raise EvidenceBuildError(f"artifact {artifact_id} is not a stable RISC0 program binary")
        return
    if kind != "binary":
        raise EvidenceBuildError(f"artifact {artifact_id} has unknown kind")


def _load_pretty_canonical_object(raw: bytes, label: str) -> dict[str, Any]:
    value = _load_json(raw, label)
    if type(value) is not dict:
        raise EvidenceBuildError(f"{label} must be a JSON object")
    if build_checker.canonical_bytes(value) != raw:
        raise EvidenceBuildError(f"{label} JSON is noncanonical")
    return value


def _load_canonical_json_line(raw: bytes, label: str) -> dict[str, Any]:
    if not raw.endswith(b"\n") or raw.endswith(b"\n\n"):
        raise EvidenceBuildError(f"{label} must be one newline-terminated JSON object")
    value = _load_canonical_compact_json(raw[:-1], label)
    if type(value) is not dict:
        raise EvidenceBuildError(f"{label} must be a JSON object")
    return value


def _load_canonical_compact_json(raw: bytes, label: str) -> Any:
    value = _load_json(raw, label)
    canonical = json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode()
    if canonical != raw:
        raise EvidenceBuildError(f"{label} JSON is noncanonical")
    return value


def _load_json(raw: bytes, label: str) -> Any:
    try:
        return json.loads(
            raw,
            object_pairs_hook=_object_no_duplicates,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, EvidenceBuildError) as exc:
        raise EvidenceBuildError(f"{label} JSON rejected: {exc}") from exc


def _object_no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise EvidenceBuildError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_float(_value: str) -> NoReturn:
    raise EvidenceBuildError("floating-point JSON numbers are forbidden")


def _read_stable_bytes(path: Path, *, maximum_bytes: int, label: str) -> bytes:
    candidate = Path(os.path.abspath(os.fspath(path)))
    _reject_symlink_components(candidate, label)
    try:
        path_before = os.lstat(candidate)
    except OSError as exc:
        raise EvidenceBuildError(f"{label} is unavailable") from exc
    if not stat.S_ISREG(path_before.st_mode):
        raise EvidenceBuildError(f"{label} must be a regular file")
    if path_before.st_size <= 0 or path_before.st_size > maximum_bytes:
        raise EvidenceBuildError(f"{label} byte length is unsupported")
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise EvidenceBuildError("O_NOFOLLOW is required for stable evidence reads")
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NONBLOCK | nofollow
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise EvidenceBuildError(f"{label} stable open failed") from exc
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or _stat_identity(before) != _stat_identity(path_before):
            raise EvidenceBuildError(f"{label} changed before stable read")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, min(READ_CHUNK_BYTES, maximum_bytes + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
            if total > maximum_bytes:
                raise EvidenceBuildError(f"{label} exceeds governed byte bound")
        after = os.fstat(descriptor)
        try:
            path_after = os.lstat(candidate)
        except OSError as exc:
            raise EvidenceBuildError(f"{label} disappeared during stable read") from exc
        if _stat_identity(after) != _stat_identity(before) or _stat_identity(path_after) != _stat_identity(before):
            raise EvidenceBuildError(f"{label} changed during stable read")
        raw = b"".join(chunks)
        if len(raw) != before.st_size:
            raise EvidenceBuildError(f"{label} changed during stable read")
        return raw
    finally:
        os.close(descriptor)


def _stat_identity(value: os.stat_result) -> tuple[int, ...]:
    return (
        value.st_dev,
        value.st_ino,
        value.st_mode,
        value.st_nlink,
        value.st_uid,
        value.st_gid,
        value.st_size,
        value.st_mtime_ns,
        value.st_ctime_ns,
    )


def _reject_symlink_components(path: Path, label: str) -> None:
    current = Path(path.anchor)
    for part in path.parts[1:]:
        current /= part
        try:
            metadata = os.lstat(current)
        except OSError as exc:
            raise EvidenceBuildError(f"{label} path component is unavailable") from exc
        if stat.S_ISLNK(metadata.st_mode):
            raise EvidenceBuildError(f"{label} symlink path component rejected")


def _new_output_path(path: Path, label: str) -> Path:
    candidate = Path(os.path.abspath(os.fspath(path)))
    if candidate.exists() or candidate.is_symlink():
        raise EvidenceBuildError(f"{label} already exists")
    parent = candidate.parent
    _reject_symlink_components(parent, f"{label} parent")
    if not parent.is_dir():
        raise EvidenceBuildError(f"{label} parent is not a directory")
    return candidate


def _path_is_within(candidate: Path, root: Path) -> bool:
    try:
        candidate.relative_to(root)
    except ValueError:
        return False
    return True


def _write_new(path: Path, raw: bytes) -> None:
    descriptor = os.open(
        path,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC,
        0o600,
    )
    try:
        offset = 0
        while offset < len(raw):
            written = os.write(descriptor, raw[offset:])
            if written <= 0:
                raise EvidenceBuildError("output write made no progress")
            offset += written
        os.fsync(descriptor)
    except OSError as exc:
        raise EvidenceBuildError(f"output write failed: {path.name}") from exc
    finally:
        os.close(descriptor)


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _require_exact_output_inventory(bundle: Path) -> None:
    expected = {path for _artifact_id, path, _kind in evidence_checker.ARTIFACT_SPECS}
    observed: set[str] = set()
    for candidate in bundle.iterdir():
        if candidate.is_symlink() or not candidate.is_file():
            raise EvidenceBuildError("generated bundle contains a non-regular artifact")
        observed.add(candidate.name)
    if observed != expected:
        raise EvidenceBuildError("generated bundle inventory mismatch")


def _require_exact_path_inventory(
    value: Mapping[str, Path], expected: set[str], label: str
) -> None:
    observed = set(value)
    if observed != expected:
        raise EvidenceBuildError(
            f"{label} path inventory mismatch: missing={sorted(expected - observed)}, "
            f"unknown={sorted(observed - expected)}"
        )
    for key, path in value.items():
        if not isinstance(path, Path):
            raise EvidenceBuildError(f"{label} path {key} must be a pathlib.Path")


def _exact_object(value: Any, fields: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise EvidenceBuildError(f"{label} must be an object")
    observed = set(value)
    if observed != fields:
        raise EvidenceBuildError(
            f"{label} field set mismatch: missing={sorted(fields - observed)}, "
            f"unknown={sorted(observed - fields)}"
        )
    return value


def _require_true(value: Any, label: str) -> None:
    if type(value) is not bool or value is not True:
        raise EvidenceBuildError(f"{label} must be exactly True")


def _require_false(value: Any, label: str) -> None:
    if type(value) is not bool or value is not False:
        raise EvidenceBuildError(f"{label} must be exactly False")


def _require_equal(value: Any, expected: Any, label: str) -> None:
    if type(value) is not type(expected) or value != expected:
        raise EvidenceBuildError(f"{label} mismatch")


def _require_nonzero_hash(value: Any, label: str) -> None:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
        or value == "0" * 64
    ):
        raise EvidenceBuildError(f"{label} must be a nonzero lowercase SHA-256 value")


def _require_size_hash(
    report: Mapping[str, Any], prefix: str, fact: Mapping[str, Any], label: str
) -> None:
    _require_equal(report[f"{prefix}_bytes"], fact["size_bytes"], f"{label} byte length")
    _require_equal(report[f"{prefix}_sha256"], fact["sha256"], f"{label} SHA-256")


def _require_exact_sequence(value: Any, expected: Sequence[str], label: str) -> None:
    if type(value) is not list or value != list(expected):
        raise EvidenceBuildError(f"{label} mismatch")


def _require_canonical_date(value: str) -> None:
    if type(value) is not str:
        raise EvidenceBuildError("recorded_at must be an ISO date")
    try:
        parsed = date.fromisoformat(value)
    except ValueError as exc:
        raise EvidenceBuildError("recorded_at must be an ISO date") from exc
    if parsed.isoformat() != value:
        raise EvidenceBuildError("recorded_at must be a canonical ISO date")


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _parse_bindings(values: Sequence[str], expected: set[str], label: str) -> dict[str, Path]:
    result: dict[str, Path] = {}
    for value in values:
        key, separator, raw_path = value.partition("=")
        if not separator or not key or not raw_path:
            raise EvidenceBuildError(f"{label} binding must be ID=PATH")
        if key in result:
            raise EvidenceBuildError(f"duplicate {label} binding: {key}")
        result[key] = Path(raw_path)
    _require_exact_path_inventory(result, expected, label)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--recorded-at", required=True)
    parser.add_argument("--artifact", action="append", default=[], metavar="ID=PATH")
    parser.add_argument("--report", action="append", default=[], metavar="ID=PATH")
    parser.add_argument("--build-record", type=Path, required=True)
    parser.add_argument("--r0vm", type=Path, required=True)
    parser.add_argument("--bundle-directory", type=Path, required=True)
    parser.add_argument("--evidence-out", type=Path, required=True)
    arguments = parser.parse_args()
    try:
        artifact_ids = {
            artifact_id
            for artifact_id, _path, _kind in evidence_checker.ARTIFACT_SPECS
        }
        result = build_evidence(
            recorded_at=arguments.recorded_at,
            artifact_paths=_parse_bindings(arguments.artifact, artifact_ids, "artifact"),
            report_paths=_parse_bindings(arguments.report, set(REPORT_IDS), "report"),
            build_record_path=arguments.build_record,
            r0vm_path=arguments.r0vm,
            bundle_directory=arguments.bundle_directory,
            evidence_path=arguments.evidence_out,
        )
    except (OSError, EvidenceBuildError) as exc:
        print(
            json.dumps(
                {
                    "ok": False,
                    "schema": "zenodex/zrpf_source_opened_spot_v6_local_evidence_build/v1",
                    "error": str(exc),
                    "release_authority": False,
                    "settlement_authority": False,
                    "production_authority": False,
                },
                sort_keys=True,
                separators=(",", ":"),
            )
        )
        return 1
    print(
        json.dumps(
            {
                "artifact_count": result.artifact_count,
                "build_record_sha256": result.build_record_sha256,
                "bundle_and_evidence_publication_atomic": False,
                "candidate_bundle_built": result.candidate_bundle_built,
                "evidence_sha256": result.evidence_sha256,
                "ok": True,
                "production_authority": False,
                "release_authority": False,
                "schema": "zenodex/zrpf_source_opened_spot_v6_local_evidence_build/v1",
                "scoped_local_replay_claim_allowed": result.scoped_local_replay_claim_allowed,
                "settlement_authority": False,
            },
            sort_keys=True,
            separators=(",", ":"),
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
