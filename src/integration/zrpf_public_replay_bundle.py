"""Build, check, and execute the bounded ZRPF V3 public replay bundle."""

from __future__ import annotations

import hashlib
import json
import os
import re
import resource
import shutil
import stat
import subprocess
import tempfile
from datetime import date
from pathlib import Path, PurePosixPath
from typing import Any, cast

from tools.zrpf_v3_source_closure import SOURCE_ROWS as FROZEN_SOURCE_ROWS

BUNDLE_SCHEMA = "zenodex/zrpf_v3_public_replay_bundle/v1"
REFERENCE_SCHEMA = "zenodex/zrpf_v3_public_replay_reference/v1"
REPORT_SCHEMA = "zenodex/zrpf_v3_public_replay_check/v1"
SOURCE_CLOSURE_SCHEMA = "zenodex/zrpf_v3_frozen_source_closure/v1"
MAX_JSON_BYTES = 16 * 1024 * 1024
MAX_ARTIFACT_BYTES = 32 * 1024 * 1024
MAX_TRANSCRIPT_BYTES = 128 * 1024
HEX_DIGEST = re.compile(r"[0-9a-f]{64}")
GIT_OBJECT_ID = re.compile(r"(?:[0-9a-f]{40}|[0-9a-f]{64})")
EMPTY_SHA256 = hashlib.sha256(b"").hexdigest()
# This value is updated only after the generated reference has been reviewed.
EXPECTED_REFERENCE_FILE_SHA256 = "521fb021c75c5ad7d4826cbfc35ff1301040abe46c1926624f7f57e5cc88af21"
EXPECTED_VERIFIER_SHA256 = "c196c56e8e61cc757142e8199aeb6f27a31c071f7fe20c0e54825b527d63c1bc"
SOURCE_CLOSURE_DEFINITION = (
    "sha256 of sorted role, path, sha256, and size records with NUL field "
    "separators and LF record separators"
)

DEFAULT_BUNDLE_RELATIVE = "evidence/zrpf-v3-structural-public-replay-v1"
DEFAULT_REFERENCE_RELATIVE = "config/proof_profiles/zrpf_v3_public_replay_reference_v1.json"

CLAIMS = {
    "fresh_proof_artifacts_from_source_frozen_run": False,
    "proof_generation_provenance_machine_verified": False,
    "verifier_build_provenance_machine_verified": False,
    "guest_elf_image_ids_recomputed_by_public_checker": False,
    "source_proofs_bound_to_leaf_journals_by_public_checker": False,
    "toolchain_lock_semantically_validated_by_public_checker": False,
    "public_artifact_replay": True,
    "typed_succinct_seal_mutation_rejection": True,
    "four_leaf_two_level_structural_tree": True,
    "reproducible_build": False,
    "cross_host_reproducibility": False,
    "release_backed": False,
    "full_zenodex_semantic_composition": False,
    "data_availability_or_carry_semantics": False,
    "asset_conservation_or_value_flow": False,
    "ledger_or_settlement_admission_authority": False,
    "production_authority": False,
    "zero_knowledge_or_witness_privacy": False,
}

NON_CLAIMS = [
    "no_reproducible_build_claim",
    "no_cross_host_reproducibility_claim",
    "no_authenticated_runtime_rootfs_claim",
    "no_release_authority_claim",
    "no_full_zenodex_semantic_composition_claim",
    "no_data_availability_or_carry_semantics_claim",
    "no_asset_conservation_or_value_flow_claim",
    "no_zenoledger_or_settlement_admission_claim",
    "no_production_authority_claim",
    "no_zero_knowledge_or_witness_privacy_claim",
    "no_receipt_byte_determinism_claim",
]

VERIFIER_NONCLAIMS = [
    "structural roots bind child commitments without proving their application semantics",
    "temporary compiler-visible paths are not release identities",
    "no settlement, ledger admission, data availability, conservation, or production authority",
]

FIXED_INPUTS: tuple[tuple[str, str], ...] = (
    ("v1-spot.proof.json", "inputs/v1-spot.proof.json"),
    ("v1-spot-0002.proof.json", "inputs/v1-spot-0002.proof.json"),
    ("v1-spot-0002-distinct.proof.json", "inputs/v1-spot-0002-distinct.proof.json"),
    ("v1-spot-0002-fee.proof.json", "inputs/v1-spot-0002-fee.proof.json"),
)

FIXED_RECEIPTS: tuple[tuple[str, str], ...] = (
    ("adapter-leaf-0.receipt.json", "receipts/adapter-leaf-0.receipt.json"),
    ("adapter-leaf-1.receipt.json", "receipts/adapter-leaf-1.receipt.json"),
    ("adapter-leaf-2.receipt.json", "receipts/adapter-leaf-2.receipt.json"),
    ("adapter-leaf-3.receipt.json", "receipts/adapter-leaf-3.receipt.json"),
    (
        "structural-tree/structural-l1-left.receipt.json",
        "receipts/structural-l1-left.receipt.json",
    ),
    (
        "structural-tree/structural-l1-right.receipt.json",
        "receipts/structural-l1-right.receipt.json",
    ),
    (
        "structural-tree/structural-l2-root.receipt.json",
        "receipts/structural-l2-root.receipt.json",
    ),
    (
        "structural-tree/structural-l2-root.seal-word-1-xor-lsb.receipt.json",
        "receipts/structural-l2-root.seal-word-1-xor-lsb.receipt.json",
    ),
)

REPLAY_RECEIPTS = [
    "receipts/adapter-leaf-0.receipt.json",
    "receipts/adapter-leaf-1.receipt.json",
    "receipts/adapter-leaf-2.receipt.json",
    "receipts/adapter-leaf-3.receipt.json",
    "receipts/structural-l1-left.receipt.json",
    "receipts/structural-l1-right.receipt.json",
    "receipts/structural-l2-root.receipt.json",
]
MUTATED_RECEIPT = "receipts/structural-l2-root.seal-word-1-xor-lsb.receipt.json"
VERIFIER = "bin/verify_structural_tree"
POSITIVE_TRANSCRIPT = "transcripts/positive-replay.jsonl"
MUTATION_TRANSCRIPT = "transcripts/seal-mutation-reject.jsonl"
PROOF_SOURCE_CLOSURE = "source/proof-generation-source-closure.json"
VERIFIER_SOURCE_CLOSURE = "source/verifier-build-source-closure.json"

EXPECTED_ARTIFACT_POLICY = {
    VERIFIER: ("verifier_binary", True, True),
    "programs/v1-leaf-adapter.bin": ("guest_elf_context", False, False),
    "programs/structural-l1.bin": ("guest_elf_context", False, False),
    "programs/structural-l2.bin": ("guest_elf_context", False, False),
    **{relative: ("source_proof_context", False, False) for _, relative in FIXED_INPUTS},
    **{relative: ("receipt", False, True) for _, relative in FIXED_RECEIPTS},
    PROOF_SOURCE_CLOSURE: ("proof_source_closure_context", False, False),
    VERIFIER_SOURCE_CLOSURE: ("verifier_source_closure_context", False, False),
    "toolchain/risc0_recursive_toolchain_lock.json": (
        "toolchain_lock_context",
        False,
        False,
    ),
    POSITIVE_TRANSCRIPT: ("positive_transcript", False, True),
    MUTATION_TRANSCRIPT: ("mutation_transcript", False, True),
}
EXPECTED_BUNDLE_DIRECTORIES = frozenset(
    {
        "bin",
        "inputs",
        "programs",
        "receipts",
        "source",
        "toolchain",
        "transcripts",
    }
)


class PublicReplayError(ValueError):
    """Raised when build or replay data violates the bounded public contract."""


def build_bundle(
    *,
    repository_root: Path,
    verifier_binary_path: Path,
    proof_source_closure_path: Path,
    verifier_source_closure_path: Path,
    proof_target_root: Path,
    verifier_target_root: Path,
    evidence_root: Path,
    source_proof_root: Path,
    output_directory: Path,
    reference_output: Path,
    evidence_date: str,
) -> dict[str, Any]:
    root = repository_root.resolve(strict=True)
    output_directory = _resolve_new_path(output_directory, "bundle output")
    reference_output = _resolve_new_path(reference_output, "reference output")
    if output_directory != root / DEFAULT_BUNDLE_RELATIVE:
        raise PublicReplayError("bundle output must use the governed repository path")
    if reference_output != root / DEFAULT_REFERENCE_RELATIVE:
        raise PublicReplayError("reference output must use the governed repository path")
    if output_directory.exists() or output_directory.is_symlink():
        raise PublicReplayError("bundle output directory must be absent")
    if not _is_iso_date(evidence_date):
        raise PublicReplayError("evidence date must use YYYY-MM-DD")
    output_directory.mkdir(mode=0o755)

    copied: list[str] = []
    try:
        verifier_raw = _read_regular(
            verifier_binary_path,
            MAX_ARTIFACT_BYTES,
            "reviewed verifier binary",
        )
        if sha256_hex(verifier_raw) != EXPECTED_VERIFIER_SHA256:
            raise PublicReplayError("verifier input does not match the reviewed trust anchor")
        _write_relative_create_new(output_directory, VERIFIER, verifier_raw, 0o755)
        copied.append(VERIFIER)
        program_sources = (
            (
                verifier_target_root
                / "riscv-guest/zenodex-zrpf-risc0-methods/zenodex-zrpf-risc0-v1-leaf-adapter/riscv32im-risc0-zkvm-elf/release/zenodex-zrpf-risc0-v1-leaf-adapter.bin",
                "programs/v1-leaf-adapter.bin",
            ),
            (
                verifier_target_root
                / "riscv-guest/zenodex-zrpf-risc0-methods/zenodex-zrpf-risc0-structural-aggregate-l1/riscv32im-risc0-zkvm-elf/release/zenodex-zrpf-risc0-structural-aggregate-l1.bin",
                "programs/structural-l1.bin",
            ),
            (
                verifier_target_root
                / "riscv-guest/zenodex-zrpf-risc0-methods/zenodex-zrpf-risc0-structural-aggregate-l2/riscv32im-risc0-zkvm-elf/release/zenodex-zrpf-risc0-structural-aggregate-l2.bin",
                "programs/structural-l2.bin",
            ),
        )
        for source, relative in program_sources:
            _copy_artifact(source, output_directory, relative, executable=False)
            copied.append(relative)
        for source_name, relative in FIXED_INPUTS:
            _copy_artifact(
                source_proof_root / source_name,
                output_directory,
                relative,
                executable=False,
            )
            copied.append(relative)
        for source_name, relative in FIXED_RECEIPTS:
            _copy_artifact(
                evidence_root / source_name,
                output_directory,
                relative,
                executable=False,
            )
            copied.append(relative)
        for source_path, relative in (
            (proof_source_closure_path, PROOF_SOURCE_CLOSURE),
            (verifier_source_closure_path, VERIFIER_SOURCE_CLOSURE),
        ):
            _copy_artifact(
                source_path,
                output_directory,
                relative,
                executable=False,
            )
            copied.append(relative)
        toolchain_relative = "toolchain/risc0_recursive_toolchain_lock.json"
        _copy_artifact(
            root / "config/proof_profiles/risc0_recursive_toolchain_lock.json",
            output_directory,
            toolchain_relative,
            executable=False,
        )
        copied.append(toolchain_relative)

        positive = _run_bundle_verifier(output_directory, mutation=False)
        mutation = _run_bundle_verifier(output_directory, mutation=True)
        _validate_positive_transcript(positive)
        _validate_mutation_transcript(mutation)
        _write_relative_create_new(output_directory, POSITIVE_TRANSCRIPT, positive, 0o644)
        copied.append(POSITIVE_TRANSCRIPT)
        _write_relative_create_new(output_directory, MUTATION_TRANSCRIPT, mutation, 0o644)
        copied.append(MUTATION_TRANSCRIPT)

        proof_source_closure = _load_canonical_json(
            (output_directory / PROOF_SOURCE_CLOSURE).read_bytes(),
            MAX_JSON_BYTES,
            "proof source closure",
        )
        verifier_source_closure = _load_canonical_json(
            (output_directory / VERIFIER_SOURCE_CLOSURE).read_bytes(),
            MAX_JSON_BYTES,
            "verifier source closure",
        )
        _validate_source_closure(proof_source_closure)
        _validate_source_closure(verifier_source_closure)
        positive_document = _load_json_line(positive, "positive transcript")
        mutation_document = _load_json_line(mutation, "mutation transcript")
        artifacts = [_artifact_row(output_directory, relative) for relative in sorted(copied)]
        manifest = {
            "artifacts": artifacts,
            "proof_generation_record": {
                "authority": "publisher_record_only",
                "checker_rebuilds_guests": False,
                "checker_regenerates_proofs": False,
                "guest_programs_rebuilt_recorded": True,
                "proof_generation_completed_recorded": True,
                "source_closure_file_count": proof_source_closure["file_count"],
                "source_closure_observed_before_and_after_recorded": True,
                "source_closure_sha256": proof_source_closure["sha256"],
                "source_git_commit": proof_source_closure["git_commit"],
                "tree_prover_binary": _external_artifact_fact(
                    proof_target_root / "release/prove_structural_tree"
                ),
                "v1_adapter_harness_binary": _external_artifact_fact(
                    proof_target_root / "release/zenodex-zrpf-risc0-harness"
                ),
            },
            "claims": CLAIMS,
            "evidence_date": evidence_date,
            "non_claims": NON_CLAIMS,
            "replay": {
                "mutation": {
                    "expected_exit_code": 0,
                    "expected_stderr_sha256": EMPTY_SHA256,
                    "status": mutation_document["status"],
                    "transcript_path": MUTATION_TRANSCRIPT,
                },
                "positive": {
                    "expected_exit_code": 0,
                    "expected_stderr_sha256": EMPTY_SHA256,
                    "status": positive_document["status"],
                    "transcript_path": POSITIVE_TRANSCRIPT,
                },
                "verifier_path": VERIFIER,
            },
            "sanitization": {
                "embedded_absolute_compiler_paths_present": True,
                "publisher_private_name_review_recorded": True,
                "public_checker_validates_artifact_bytes_for_private_names": False,
                "source_path_remapping_complete": False,
            },
            "schema": BUNDLE_SCHEMA,
            "scope": "four_leaf_two_level_zrpf_v3_structural_tree",
            "status": "source_frozen_public_artifact_replay",
            "tree": {
                "adapter_image_id": positive_document["adapter_image_id"],
                "level_one_image_id": positive_document["level_one_image_id"],
                "level_two_image_id": positive_document["level_two_image_id"],
                "root": positive_document["root"],
                "seal_mutation": mutation_document["mutation"],
            },
            "verifier_build_record": {
                "authority": "publisher_record_only",
                "checker_rebuilds_verifier": False,
                "source_closure_file_count": verifier_source_closure["file_count"],
                "source_closure_observed_before_and_after_recorded": True,
                "source_closure_sha256": verifier_source_closure["sha256"],
                "source_git_commit": verifier_source_closure["git_commit"],
            },
            "version": 1,
        }
        manifest_raw = canonical_json_bytes(manifest)
        _write_relative_create_new(output_directory, "manifest.json", manifest_raw, 0o644)
        manifest_sha256 = sha256_hex(manifest_raw)
        reference = {
            "bundle_directory": DEFAULT_BUNDLE_RELATIVE,
            "manifest_sha256": manifest_sha256,
            "production_claim_allowed": False,
            "schema": REFERENCE_SCHEMA,
            "scoped_public_replay_claim_allowed": True,
            "proof_generation_source_closure_sha256": proof_source_closure["sha256"],
            "status": "source_frozen_public_artifact_replay",
            "verifier_sha256": _artifact_by_path(artifacts, VERIFIER)["sha256"],
            "verifier_build_source_closure_sha256": verifier_source_closure["sha256"],
            "version": 1,
        }
        _sync_directory(output_directory)
        _write_external_create_new(reference_output, canonical_json_bytes(reference), 0o644)
        return {
            "artifact_count": len(artifacts),
            "bundle_directory": DEFAULT_BUNDLE_RELATIVE,
            "manifest_sha256": manifest_sha256,
            "ok": True,
            "reference_sha256": sha256_hex(canonical_json_bytes(reference)),
            "schema": BUNDLE_SCHEMA,
            "status": "public_replay_bundle_built",
        }
    except Exception:
        shutil.rmtree(output_directory, ignore_errors=True)
        raise


def check_bundle(
    *,
    bundle_directory: Path,
    reference_path: Path,
    execute: bool,
) -> dict[str, Any]:
    errors: list[str] = []
    checked_artifacts = 0
    snapshot: tempfile.TemporaryDirectory[str] | None = None
    try:
        if type(execute) is not bool:
            raise PublicReplayError("execute flag must be boolean")
        reference_raw, reference_mode = _read_regular_with_mode(
            reference_path,
            MAX_JSON_BYTES,
            "reference",
        )
        if reference_mode & 0o777 != 0o644:
            raise PublicReplayError("reference mode mismatch")
        if sha256_hex(reference_raw) != EXPECTED_REFERENCE_FILE_SHA256:
            raise PublicReplayError("reference does not match the reviewed trust anchor")
        reference = _load_canonical_json(reference_raw, MAX_JSON_BYTES, "reference")
        _require_exact_fields(
            reference,
            {
                "bundle_directory",
                "manifest_sha256",
                "production_claim_allowed",
                "proof_generation_source_closure_sha256",
                "schema",
                "scoped_public_replay_claim_allowed",
                "status",
                "verifier_sha256",
                "verifier_build_source_closure_sha256",
                "version",
            },
            "reference",
        )
        if (
            reference.get("schema") != REFERENCE_SCHEMA
            or type(reference.get("version")) is not int
            or reference.get("version") != 1
        ):
            raise PublicReplayError("reference schema or version mismatch")
        if reference.get("bundle_directory") != DEFAULT_BUNDLE_RELATIVE:
            raise PublicReplayError("reference bundle directory mismatch")
        if (
            reference.get("production_claim_allowed") is not False
            or reference.get("scoped_public_replay_claim_allowed") is not True
        ):
            raise PublicReplayError("reference overstates release authority")
        for field in (
            "manifest_sha256",
            "proof_generation_source_closure_sha256",
            "verifier_build_source_closure_sha256",
            "verifier_sha256",
        ):
            if not _is_digest(reference.get(field)):
                raise PublicReplayError(f"reference {field} is invalid")
        if reference.get("status") != "source_frozen_public_artifact_replay":
            raise PublicReplayError("reference status mismatch")

        manifest_path = bundle_directory / "manifest.json"
        manifest_raw, manifest_mode = _read_regular_with_mode(
            manifest_path,
            MAX_JSON_BYTES,
            "manifest",
        )
        if manifest_mode & 0o777 != 0o644:
            raise PublicReplayError("manifest mode mismatch")
        if sha256_hex(manifest_raw) != reference.get("manifest_sha256"):
            raise PublicReplayError("manifest SHA-256 differs from external reference")
        manifest = _load_canonical_json(manifest_raw, MAX_JSON_BYTES, "manifest")
        _validate_manifest_shape(manifest)
        _require_exact_bool_map(manifest.get("claims"), CLAIMS, "claims")
        if manifest.get("non_claims") != NON_CLAIMS:
            raise PublicReplayError("claim boundary mismatch")
        _validate_no_absolute_strings(manifest)
        artifacts = manifest["artifacts"]
        for row in artifacts:
            _validate_artifact_row(row)
        expected_paths = [row["path"] for row in artifacts]
        if expected_paths != sorted(expected_paths) or len(expected_paths) != len(
            set(expected_paths)
        ):
            raise PublicReplayError("artifact paths must be sorted and unique")
        actual_paths = _bundle_inventory(bundle_directory)
        if actual_paths != sorted(["manifest.json", *expected_paths]):
            raise PublicReplayError("bundle inventory mismatch")
        actual_policy = {
            row["path"]: (row["role"], row["executable"], row["replay_authority"])
            for row in artifacts
        }
        if actual_policy != EXPECTED_ARTIFACT_POLICY:
            raise PublicReplayError("artifact path, role, or authority contract mismatch")
        snapshot = tempfile.TemporaryDirectory(prefix="zenodex-zrpf-static-snapshot-")
        bundle_directory = _stage_bundle_snapshot(
            source=bundle_directory,
            destination=Path(snapshot.name),
            manifest_raw=manifest_raw,
            artifacts=artifacts,
        )
        manifest_path = bundle_directory / "manifest.json"
        actual_paths = _bundle_inventory(bundle_directory)
        _validate_artifact_files(bundle_directory, artifacts)
        checked_artifacts = len(artifacts)
        if _artifact_by_path(artifacts, VERIFIER)["sha256"] != reference.get("verifier_sha256"):
            raise PublicReplayError("verifier SHA-256 differs from external reference")
        if reference.get("verifier_sha256") != EXPECTED_VERIFIER_SHA256:
            raise PublicReplayError("verifier does not match the reviewed trust anchor")

        for relative, reference_field, record_field, label in (
            (
                PROOF_SOURCE_CLOSURE,
                "proof_generation_source_closure_sha256",
                "proof_generation_record",
                "proof source closure",
            ),
            (
                VERIFIER_SOURCE_CLOSURE,
                "verifier_build_source_closure_sha256",
                "verifier_build_record",
                "verifier source closure",
            ),
        ):
            source_raw = _read_regular(
                bundle_directory / relative,
                MAX_JSON_BYTES,
                label,
            )
            source = _load_canonical_json(source_raw, MAX_JSON_BYTES, label)
            _validate_source_closure(source)
            if source.get("sha256") != reference.get(reference_field):
                raise PublicReplayError(f"{label} differs from external reference")
            record = manifest[record_field]
            if (
                record.get("source_closure_sha256") != source.get("sha256")
                or record.get("source_git_commit") != source.get("git_commit")
                or record.get("source_closure_file_count") != source.get("file_count")
            ):
                raise PublicReplayError(f"{label} differs from manifest build record")
        _validate_receipt_mutation_pair(bundle_directory)
        positive_raw = _read_regular(
            bundle_directory / POSITIVE_TRANSCRIPT,
            MAX_TRANSCRIPT_BYTES,
            "positive transcript",
        )
        mutation_raw = _read_regular(
            bundle_directory / MUTATION_TRANSCRIPT,
            MAX_TRANSCRIPT_BYTES,
            "mutation transcript",
        )
        _validate_positive_transcript(positive_raw)
        _validate_mutation_transcript(mutation_raw)
        positive_document = _load_json_line(positive_raw, "positive transcript")
        mutation_document = _load_json_line(mutation_raw, "mutation transcript")
        _validate_transcript_bindings(
            manifest,
            artifacts,
            positive_document,
            mutation_document,
        )
        if execute:
            _execute_and_compare(
                bundle_directory,
                artifacts,
                positive_raw,
                mutation_raw,
            )
        if _read_regular(manifest_path, MAX_JSON_BYTES, "manifest") != manifest_raw:
            raise PublicReplayError("manifest changed during validation")
        _validate_artifact_files(bundle_directory, artifacts)
        if _bundle_inventory(bundle_directory) != actual_paths:
            raise PublicReplayError("bundle inventory changed during validation")
    except (
        KeyError,
        OSError,
        PublicReplayError,
        subprocess.SubprocessError,
        TypeError,
        ValueError,
    ) as exc:
        errors.append(str(exc))
    finally:
        if snapshot is not None:
            snapshot.cleanup()
    execution_checked = execute is True and not errors
    return {
        "checked_artifacts": checked_artifacts,
        "errors": errors,
        "execution_checked": execution_checked,
        "ok": not errors,
        "production_claim_allowed": False,
        "scoped_public_replay_claim_allowed": execution_checked,
        "schema": REPORT_SCHEMA,
        "status": (
            "executed_replay_accepted"
            if execution_checked
            else "static_bundle_accepted"
            if not errors
            else "rejected"
        ),
    }


def canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def compact_json_bytes(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def sha256_hex(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _validate_artifact_files(bundle: Path, artifacts: list[dict[str, Any]]) -> None:
    for row in artifacts:
        path = bundle / row["path"]
        raw, mode = _read_regular_with_mode(
            path,
            MAX_ARTIFACT_BYTES,
            f"artifact {row['path']}",
        )
        if len(raw) != row["size_bytes"] or sha256_hex(raw) != row["sha256"]:
            raise PublicReplayError(f"artifact digest or size mismatch: {row['path']}")
        expected_mode = 0o755 if row["executable"] else 0o644
        if mode & 0o777 != expected_mode:
            raise PublicReplayError(f"artifact executable mode mismatch: {row['path']}")


def _stage_bundle_snapshot(
    *,
    source: Path,
    destination: Path,
    manifest_raw: bytes,
    artifacts: list[dict[str, Any]],
) -> Path:
    _write_external_create_new(destination / "manifest.json", manifest_raw, 0o644)
    for row in artifacts:
        raw, mode = _read_regular_with_mode(
            source / row["path"],
            MAX_ARTIFACT_BYTES,
            f"source artifact {row['path']}",
        )
        expected_mode = 0o755 if row["executable"] else 0o644
        if (
            len(raw) != row["size_bytes"]
            or sha256_hex(raw) != row["sha256"]
            or mode & 0o777 != expected_mode
        ):
            raise PublicReplayError(f"source artifact changed: {row['path']}")
        _write_relative_create_new(
            destination,
            row["path"],
            raw,
            expected_mode,
        )
    return destination


def _copy_artifact(source: Path, root: Path, relative: str, *, executable: bool) -> None:
    raw = _read_regular(source, MAX_ARTIFACT_BYTES, f"input {relative}")
    _write_relative_create_new(root, relative, raw, 0o755 if executable else 0o644)


def _write_relative_create_new(root: Path, relative: str, raw: bytes, mode: int) -> None:
    _require_safe_relative(relative)
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o755)
    _write_external_create_new(path, raw, mode)


def _write_external_create_new(path: Path, raw: bytes, mode: int) -> None:
    parent = path.parent.resolve(strict=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(parent / path.name, flags, mode)
    except OSError as exc:
        raise PublicReplayError(f"create-new output failed: {path.name}") from exc
    try:
        view = memoryview(raw)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise PublicReplayError("output write made no progress")
            view = view[written:]
        os.fchmod(descriptor, mode)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    _sync_directory(parent)


def _resolve_new_path(path: Path, label: str) -> Path:
    try:
        parent = path.parent.resolve(strict=True)
    except OSError as exc:
        raise PublicReplayError(f"{label} parent is unavailable") from exc
    return parent / path.name


def _sync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _read_regular(path: Path, maximum: int, label: str) -> bytes:
    raw, _ = _read_regular_with_mode(path, maximum, label)
    return raw


def _read_regular_with_mode(
    path: Path,
    maximum: int,
    label: str,
) -> tuple[bytes, int]:
    try:
        descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    except OSError as exc:
        raise PublicReplayError(f"{label} is unavailable") from exc
    try:
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_size <= 0
            or metadata.st_size > maximum
        ):
            raise PublicReplayError(f"{label} must be a bounded non-symlink regular file")
        chunks: list[bytes] = []
        remaining = metadata.st_size
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1024 * 1024))
            if not chunk:
                raise PublicReplayError(f"{label} changed while read")
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            raise PublicReplayError(f"{label} changed while read")
        after = os.fstat(descriptor)
        if (
            after.st_dev != metadata.st_dev
            or after.st_ino != metadata.st_ino
            or after.st_mode != metadata.st_mode
            or after.st_size != metadata.st_size
            or after.st_ctime_ns != metadata.st_ctime_ns
            or after.st_mtime_ns != metadata.st_mtime_ns
        ):
            raise PublicReplayError(f"{label} changed while read")
        return b"".join(chunks), metadata.st_mode
    finally:
        os.close(descriptor)


def _load_canonical_json(raw: bytes, maximum: int, label: str) -> dict[str, Any]:
    if not raw or len(raw) > maximum:
        raise PublicReplayError(f"{label} byte length unsupported")
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_unique_object,
            parse_constant=_reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise PublicReplayError(f"{label} JSON rejected: {exc}") from exc
    if not isinstance(value, dict) or canonical_json_bytes(value) != raw:
        raise PublicReplayError(f"{label} JSON is not an exact canonical object")
    return value


def _load_json_line(raw: bytes, label: str) -> dict[str, Any]:
    if not raw.endswith(b"\n") or raw.count(b"\n") != 1:
        raise PublicReplayError(f"{label} must be one canonical JSON line")
    return _load_canonical_json(raw[:-1], MAX_TRANSCRIPT_BYTES, label)


def _load_compact_json_object(raw: bytes, maximum: int, label: str) -> dict[str, Any]:
    if not raw or len(raw) > maximum:
        raise PublicReplayError(f"{label} byte length unsupported")
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_unique_object,
            parse_constant=_reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise PublicReplayError(f"{label} JSON rejected: {exc}") from exc
    if not isinstance(value, dict) or compact_json_bytes(value) != raw:
        raise PublicReplayError(f"{label} JSON is not an exact compact object")
    return value


def _run_bundle_verifier(bundle: Path, *, mutation: bool) -> bytes:
    args = [str(bundle / VERIFIER), *(str(bundle / path) for path in REPLAY_RECEIPTS)]
    if mutation:
        args.extend(["--expect-root-seal-reject", str(bundle / MUTATED_RECEIPT)])
    returncode, stdout, stderr = _run_bounded_process(args, bundle)
    if returncode != 0 or stderr:
        raise PublicReplayError("verifier failed while constructing replay transcript")
    return stdout


def _execute_and_compare(
    bundle: Path,
    artifacts: list[dict[str, Any]],
    positive_expected: bytes,
    mutation_expected: bytes,
) -> None:
    with tempfile.TemporaryDirectory(prefix="zenodex-zrpf-public-replay-") as temp:
        stage = Path(temp)
        staged: dict[str, Path] = {}
        for relative in [*REPLAY_RECEIPTS, MUTATED_RECEIPT]:
            raw = _read_bound_artifact(bundle, artifacts, relative)
            destination = stage / Path(relative).name
            _write_external_create_new(destination, raw, 0o600)
            staged[relative] = destination
        verifier = stage / "verify_structural_tree"
        _write_external_create_new(
            verifier,
            _read_bound_artifact(bundle, artifacts, VERIFIER),
            0o700,
        )
        base = [str(verifier), *(str(staged[path]) for path in REPLAY_RECEIPTS)]
        positive = _run_bounded_process(base, stage)
        mutation = _run_bounded_process(
            [*base, "--expect-root-seal-reject", str(staged[MUTATED_RECEIPT])],
            stage,
        )
    if positive[0] != 0 or positive[2] or positive[1] != positive_expected:
        raise PublicReplayError("live positive replay differs from pinned transcript")
    if mutation[0] != 0 or mutation[2] or mutation[1] != mutation_expected:
        raise PublicReplayError("live seal-mutation replay differs from pinned transcript")


def _read_bound_artifact(
    bundle: Path,
    artifacts: list[dict[str, Any]],
    relative: str,
) -> bytes:
    row = _artifact_by_path(artifacts, relative)
    raw = _read_regular(bundle / relative, MAX_ARTIFACT_BYTES, f"staged {relative}")
    if len(raw) != row["size_bytes"] or sha256_hex(raw) != row["sha256"]:
        raise PublicReplayError(f"artifact changed before native replay: {relative}")
    return raw


def _run_bounded_process(args: list[str], cwd: Path) -> tuple[int, bytes, bytes]:
    with tempfile.TemporaryFile() as stdout_file, tempfile.TemporaryFile() as stderr_file:
        try:
            process = subprocess.Popen(
                args,
                cwd=cwd,
                env=_clean_replay_environment(),
                preexec_fn=_apply_child_resource_limits,
                stdout=stdout_file,
                stderr=stderr_file,
                start_new_session=True,
            )
        except OSError as exc:
            raise PublicReplayError("native verifier process could not start") from exc
        try:
            returncode = process.wait(timeout=120)
        except subprocess.TimeoutExpired as exc:
            try:
                os.killpg(process.pid, 9)
            except ProcessLookupError:
                pass
            process.wait()
            raise PublicReplayError("native verifier process timed out") from exc
        stdout_file.seek(0, os.SEEK_END)
        stderr_file.seek(0, os.SEEK_END)
        stdout_size = stdout_file.tell()
        stderr_size = stderr_file.tell()
        if stdout_size > MAX_TRANSCRIPT_BYTES or stderr_size > MAX_TRANSCRIPT_BYTES:
            raise PublicReplayError("native verifier output exceeds byte cap")
        stdout_file.seek(0)
        stderr_file.seek(0)
        return returncode, stdout_file.read(), stderr_file.read()


def _apply_child_resource_limits() -> None:
    resource.setrlimit(
        resource.RLIMIT_FSIZE,
        (MAX_TRANSCRIPT_BYTES, MAX_TRANSCRIPT_BYTES),
    )
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def _clean_replay_environment() -> dict[str, str]:
    return {
        "HOME": "/nonexistent",
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "RUST_BACKTRACE": "0",
        "TZ": "UTC",
    }


def _artifact_row(root: Path, relative: str) -> dict[str, Any]:
    try:
        role, executable, replay_authority = EXPECTED_ARTIFACT_POLICY[relative]
    except KeyError as exc:
        raise PublicReplayError(f"unexpected artifact path: {relative}") from exc
    raw = _read_regular(root / relative, MAX_ARTIFACT_BYTES, f"artifact {relative}")
    return {
        "executable": executable,
        "path": relative,
        "replay_authority": replay_authority,
        "role": role,
        "sha256": sha256_hex(raw),
        "size_bytes": len(raw),
    }


def _external_artifact_fact(path: Path) -> dict[str, Any]:
    raw = _read_regular(path, MAX_ARTIFACT_BYTES, path.name)
    return {"sha256": sha256_hex(raw), "size_bytes": len(raw)}


def _artifact_by_path(artifacts: list[dict[str, Any]], path: str) -> dict[str, Any]:
    matches = [row for row in artifacts if row.get("path") == path]
    if len(matches) != 1:
        raise PublicReplayError(f"artifact path missing or duplicated: {path}")
    return matches[0]


def _validate_manifest_shape(manifest: dict[str, Any]) -> None:
    _require_exact_fields(
        manifest,
        {
            "artifacts",
            "claims",
            "evidence_date",
            "non_claims",
            "proof_generation_record",
            "replay",
            "sanitization",
            "schema",
            "scope",
            "status",
            "tree",
            "verifier_build_record",
            "version",
        },
        "manifest",
    )
    if (
        manifest.get("schema") != BUNDLE_SCHEMA
        or type(manifest.get("version")) is not int
        or manifest.get("version") != 1
    ):
        raise PublicReplayError("bundle manifest schema or version mismatch")
    if manifest.get("status") != "source_frozen_public_artifact_replay":
        raise PublicReplayError("bundle status mismatch")
    if manifest.get("scope") != "four_leaf_two_level_zrpf_v3_structural_tree":
        raise PublicReplayError("bundle scope mismatch")
    _require_exact_bool_map(
        manifest.get("sanitization"),
        {
            "embedded_absolute_compiler_paths_present": True,
            "publisher_private_name_review_recorded": True,
            "public_checker_validates_artifact_bytes_for_private_names": False,
            "source_path_remapping_complete": False,
        },
        "sanitization",
    )
    if not isinstance(manifest.get("artifacts"), list):
        raise PublicReplayError("manifest artifacts must be a list")
    evidence_date = manifest.get("evidence_date")
    if not _is_iso_date(evidence_date):
        raise PublicReplayError("manifest evidence date is invalid")
    _validate_proof_generation_record(manifest.get("proof_generation_record"))
    _validate_verifier_build_record(manifest.get("verifier_build_record"))
    _validate_replay_contract(manifest.get("replay"))
    _validate_tree_contract(manifest.get("tree"))


def _validate_proof_generation_record(value: Any) -> None:
    _require_exact_fields(
        value,
        {
            "authority",
            "checker_rebuilds_guests",
            "checker_regenerates_proofs",
            "guest_programs_rebuilt_recorded",
            "proof_generation_completed_recorded",
            "source_closure_file_count",
            "source_closure_observed_before_and_after_recorded",
            "source_closure_sha256",
            "source_git_commit",
            "tree_prover_binary",
            "v1_adapter_harness_binary",
        },
        "proof generation record",
    )
    value = cast(dict[str, Any], value)
    if value.get("authority") != "publisher_record_only":
        raise PublicReplayError("proof generation authority mismatch")
    if (
        value.get("checker_rebuilds_guests") is not False
        or value.get("checker_regenerates_proofs") is not False
        or value.get("guest_programs_rebuilt_recorded") is not True
        or value.get("proof_generation_completed_recorded") is not True
        or value.get("source_closure_observed_before_and_after_recorded") is not True
    ):
        raise PublicReplayError("proof generation record facts mismatch")
    if (
        type(value.get("source_closure_file_count")) is not int
        or value.get("source_closure_file_count") != 37
    ):
        raise PublicReplayError("proof generation source count mismatch")
    if not _is_digest(value.get("source_closure_sha256")) or not _is_git_object_id(
        value.get("source_git_commit")
    ):
        raise PublicReplayError("proof generation source identity is invalid")
    for field in ("tree_prover_binary", "v1_adapter_harness_binary"):
        fact = value.get(field)
        _require_exact_fields(fact, {"sha256", "size_bytes"}, field)
        fact = cast(dict[str, Any], fact)
        if not _is_digest(fact.get("sha256")) or type(fact.get("size_bytes")) is not int:
            raise PublicReplayError(f"{field} identity is invalid")
        if not 0 < fact["size_bytes"] <= MAX_ARTIFACT_BYTES:
            raise PublicReplayError(f"{field} size is invalid")


def _validate_verifier_build_record(value: Any) -> None:
    _require_exact_fields(
        value,
        {
            "authority",
            "checker_rebuilds_verifier",
            "source_closure_file_count",
            "source_closure_observed_before_and_after_recorded",
            "source_closure_sha256",
            "source_git_commit",
        },
        "verifier build record",
    )
    value = cast(dict[str, Any], value)
    if (
        value.get("authority") != "publisher_record_only"
        or value.get("checker_rebuilds_verifier") is not False
        or value.get("source_closure_observed_before_and_after_recorded") is not True
        or type(value.get("source_closure_file_count")) is not int
        or value.get("source_closure_file_count") != 37
        or not _is_digest(value.get("source_closure_sha256"))
        or not _is_git_object_id(value.get("source_git_commit"))
    ):
        raise PublicReplayError("verifier build record facts mismatch")


def _validate_replay_contract(value: Any) -> None:
    _require_exact_fields(value, {"mutation", "positive", "verifier_path"}, "replay")
    value = cast(dict[str, Any], value)
    if value.get("verifier_path") != VERIFIER:
        raise PublicReplayError("replay verifier path mismatch")
    expected = {
        "positive": (
            POSITIVE_TRANSCRIPT,
            "persisted_four_leaf_two_level_structural_tree_verified",
        ),
        "mutation": (
            MUTATION_TRANSCRIPT,
            "structural_l2_root_succinct_seal_mutation_rejected",
        ),
    }
    for field, (transcript_path, status) in expected.items():
        replay = value.get(field)
        _require_exact_fields(
            replay,
            {
                "expected_exit_code",
                "expected_stderr_sha256",
                "status",
                "transcript_path",
            },
            f"{field} replay",
        )
        replay = cast(dict[str, Any], replay)
        if (
            type(replay.get("expected_exit_code")) is not int
            or replay.get("expected_exit_code") != 0
            or replay.get("expected_stderr_sha256") != EMPTY_SHA256
            or replay.get("status") != status
            or replay.get("transcript_path") != transcript_path
        ):
            raise PublicReplayError(f"{field} replay contract mismatch")


def _validate_tree_contract(value: Any) -> None:
    _require_exact_fields(
        value,
        {
            "adapter_image_id",
            "level_one_image_id",
            "level_two_image_id",
            "root",
            "seal_mutation",
        },
        "tree",
    )
    value = cast(dict[str, Any], value)
    for field in ("adapter_image_id", "level_one_image_id", "level_two_image_id"):
        if not _is_digest(value.get(field)):
            raise PublicReplayError(f"tree {field} is invalid")
    _validate_root_facts(value.get("root"))
    _validate_mutation_facts(value.get("seal_mutation"))


def _validate_root_facts(value: Any) -> None:
    _validate_node_facts(
        value,
        immediate_child_count=2,
        leaf_count=4,
        node_level=2,
        operation_count=4,
        partition_start=0,
        partition_end_exclusive=4,
        subtree_node_count=7,
        label="root",
    )


def _validate_node_facts(
    value: Any,
    *,
    immediate_child_count: int,
    leaf_count: int,
    node_level: int,
    operation_count: int,
    partition_start: int,
    partition_end_exclusive: int,
    subtree_node_count: int,
    label: str,
) -> None:
    expected_fields = {
        "immediate_child_count",
        "journal_hash",
        "journal_sha256",
        "leaf_count",
        "node_level",
        "operation_count",
        "partition_end_exclusive",
        "partition_start",
        "receipt_bytes",
        "receipt_sha256",
        "subtree_node_count",
    }
    _require_exact_fields(value, expected_fields, f"{label} facts")
    value = cast(dict[str, Any], value)
    exact_numbers = {
        "immediate_child_count": immediate_child_count,
        "leaf_count": leaf_count,
        "node_level": node_level,
        "operation_count": operation_count,
        "partition_end_exclusive": partition_end_exclusive,
        "partition_start": partition_start,
        "subtree_node_count": subtree_node_count,
    }
    if any(
        type(value.get(field)) is not int or value.get(field) != expected
        for field, expected in exact_numbers.items()
    ):
        raise PublicReplayError(f"{label} structural facts mismatch")
    if (
        type(value.get("receipt_bytes")) is not int
        or not 0 < value["receipt_bytes"] <= MAX_ARTIFACT_BYTES
    ):
        raise PublicReplayError(f"{label} receipt byte count is invalid")
    for field in ("journal_hash", "journal_sha256", "receipt_sha256"):
        if not _is_digest(value.get(field)):
            raise PublicReplayError(f"{label} {field} is invalid")


def _validate_mutation_facts(value: Any) -> None:
    _require_exact_fields(
        value,
        {
            "kind",
            "seal_word_count",
            "seal_word_index",
            "seal_word_mutated",
            "seal_word_original",
            "xor_mask",
        },
        "seal mutation",
    )
    value = cast(dict[str, Any], value)
    if (
        value.get("kind") != "succinct_seal_word_xor_lsb_v1"
        or type(value.get("seal_word_index")) is not int
        or value.get("seal_word_index") != 1
        or type(value.get("xor_mask")) is not int
        or value.get("xor_mask") != 1
        or type(value.get("seal_word_count")) is not int
        or value["seal_word_count"] <= 1
        or type(value.get("seal_word_original")) is not int
        or value.get("seal_word_original") != 0
        or type(value.get("seal_word_mutated")) is not int
        or value.get("seal_word_mutated") != 1
    ):
        raise PublicReplayError("seal mutation facts mismatch")


def _validate_artifact_row(row: Any) -> None:
    _require_exact_fields(
        row,
        {
            "executable",
            "path",
            "replay_authority",
            "role",
            "sha256",
            "size_bytes",
        },
        "artifact",
    )
    if not isinstance(row, dict):
        raise PublicReplayError("artifact row must be an object")
    _require_safe_relative(row.get("path"))
    if not isinstance(row.get("role"), str) or not row["role"]:
        raise PublicReplayError("artifact role is invalid")
    if type(row.get("executable")) is not bool:
        raise PublicReplayError("artifact executable flag is invalid")
    if type(row.get("replay_authority")) is not bool:
        raise PublicReplayError("artifact replay-authority flag is invalid")
    if not _is_digest(row.get("sha256")):
        raise PublicReplayError("artifact SHA-256 is invalid")
    if type(row.get("size_bytes")) is not int or not 0 < row["size_bytes"] <= MAX_ARTIFACT_BYTES:
        raise PublicReplayError("artifact size is invalid")


def _validate_source_closure(document: dict[str, Any]) -> None:
    _require_exact_fields(
        document,
        {
            "definition",
            "file_count",
            "files",
            "git_commit",
            "schema",
            "sha256",
            "status",
            "worktree_clean",
        },
        "source closure",
    )
    if (
        document.get("schema") != SOURCE_CLOSURE_SCHEMA
        or document.get("worktree_clean") is not True
        or document.get("definition") != SOURCE_CLOSURE_DEFINITION
        or document.get("status") != "frozen_source_closure"
        or not _is_git_object_id(document.get("git_commit"))
        or not _is_digest(document.get("sha256"))
    ):
        raise PublicReplayError("source closure schema or cleanliness mismatch")
    files = document.get("files")
    if (
        not isinstance(files, list)
        or type(document.get("file_count")) is not int
        or document.get("file_count") != len(files)
        or len(files) != 37
    ):
        raise PublicReplayError("source closure file count mismatch")
    hasher = hashlib.sha256()
    paths: list[str] = []
    for row in files:
        _require_exact_fields(row, {"path", "role", "sha256", "size_bytes"}, "source row")
        if not isinstance(row, dict):
            raise PublicReplayError("source row must be an object")
        path = row.get("path")
        _require_safe_relative(path)
        path = cast(str, path)
        paths.append(path)
        role = row.get("role")
        digest = row.get("sha256")
        size = row.get("size_bytes")
        if not isinstance(role, str) or not role or not _is_digest(digest):
            raise PublicReplayError("source row role or digest is invalid")
        digest = cast(str, digest)
        if type(size) is not int or not 0 < size <= MAX_ARTIFACT_BYTES:
            raise PublicReplayError("source row size is invalid")
        hasher.update(role.encode("utf-8"))
        hasher.update(b"\0")
        hasher.update(path.encode("utf-8"))
        hasher.update(b"\0")
        hasher.update(digest.encode("ascii"))
        hasher.update(b"\0")
        hasher.update(str(size).encode("ascii"))
        hasher.update(b"\n")
    if paths != sorted(paths) or len(paths) != len(set(paths)):
        raise PublicReplayError("source closure paths are not sorted and unique")
    if [(row["role"], row["path"]) for row in files] != list(FROZEN_SOURCE_ROWS):
        raise PublicReplayError("source closure path and role inventory mismatch")
    if hasher.hexdigest() != document.get("sha256"):
        raise PublicReplayError("source closure root mismatch")


def _validate_positive_transcript(raw: bytes) -> None:
    value = _load_json_line(raw, "positive transcript")
    _require_exact_fields(
        value,
        {
            "adapter_image_id",
            "leaf_receipts",
            "level_one_image_id",
            "level_one_nodes",
            "level_two_image_id",
            "nonclaims",
            "ok",
            "root",
            "status",
        },
        "positive transcript",
    )
    if value.get("ok") is not True or value.get("status") != (
        "persisted_four_leaf_two_level_structural_tree_verified"
    ):
        raise PublicReplayError("positive transcript status mismatch")
    if value.get("nonclaims") != VERIFIER_NONCLAIMS:
        raise PublicReplayError("positive transcript nonclaims mismatch")
    for field in ("adapter_image_id", "level_one_image_id", "level_two_image_id"):
        if not _is_digest(value.get(field)):
            raise PublicReplayError(f"positive transcript {field} is invalid")
    leaves = value.get("leaf_receipts")
    if not isinstance(leaves, list) or len(leaves) != 4:
        raise PublicReplayError("positive transcript leaf count mismatch")
    for index, leaf in enumerate(leaves):
        _validate_node_facts(
            leaf,
            immediate_child_count=0,
            leaf_count=1,
            node_level=0,
            operation_count=1,
            partition_start=index,
            partition_end_exclusive=index + 1,
            subtree_node_count=1,
            label=f"leaf {index}",
        )
    level_one = value.get("level_one_nodes")
    if not isinstance(level_one, list) or len(level_one) != 2:
        raise PublicReplayError("positive transcript level-one count mismatch")
    for index, node in enumerate(level_one):
        _validate_node_facts(
            node,
            immediate_child_count=2,
            leaf_count=2,
            node_level=1,
            operation_count=2,
            partition_start=index * 2,
            partition_end_exclusive=(index + 1) * 2,
            subtree_node_count=3,
            label=f"level-one node {index}",
        )
    _validate_root_facts(value.get("root"))


def _validate_mutation_transcript(raw: bytes) -> None:
    value = _load_json_line(raw, "mutation transcript")
    _require_exact_fields(
        value,
        {
            "baseline_tree_verified",
            "candidate_accepted",
            "control_passed",
            "expected_image_id",
            "journal_protocol_hash",
            "journal_sha256",
            "mutated_receipt_sha256",
            "mutation",
            "reject",
            "schema",
            "source_receipt_sha256",
            "status",
        },
        "mutation transcript",
    )
    if (
        value.get("schema") != "zenodex/zrpf_v3_structural_root_seal_mutation_reject/v1"
        or value.get("baseline_tree_verified") is not True
        or value.get("candidate_accepted") is not False
        or value.get("control_passed") is not True
        or value.get("status") != "structural_l2_root_succinct_seal_mutation_rejected"
        or value.get("reject")
        != {
            "boundary": "VerifiedNodeReceiptV3::verify_exact_succinct_bytes",
            "code": "receipt_verification_failed",
        }
    ):
        raise PublicReplayError("mutation transcript typed rejection mismatch")
    mutation = value.get("mutation")
    _validate_mutation_facts(mutation)
    for field in (
        "expected_image_id",
        "journal_protocol_hash",
        "journal_sha256",
        "mutated_receipt_sha256",
        "source_receipt_sha256",
    ):
        if not _is_digest(value.get(field)):
            raise PublicReplayError(f"mutation transcript {field} is invalid")


def _validate_transcript_bindings(
    manifest: dict[str, Any],
    artifacts: list[dict[str, Any]],
    positive: dict[str, Any],
    mutation: dict[str, Any],
) -> None:
    tree = manifest["tree"]
    if tree["root"] != positive["root"] or tree["seal_mutation"] != mutation["mutation"]:
        raise PublicReplayError("manifest tree differs from verifier transcripts")
    for field in ("adapter_image_id", "level_one_image_id", "level_two_image_id"):
        if tree[field] != positive[field]:
            raise PublicReplayError(f"manifest {field} differs from positive replay")
    root = positive["root"]
    if (
        mutation["expected_image_id"] != positive["level_two_image_id"]
        or mutation["journal_protocol_hash"] != root["journal_hash"]
        or mutation["journal_sha256"] != root["journal_sha256"]
        or mutation["source_receipt_sha256"] != root["receipt_sha256"]
    ):
        raise PublicReplayError("mutation transcript differs from verified root")

    receipt_bindings = [
        *zip(REPLAY_RECEIPTS[:4], positive["leaf_receipts"], strict=True),
        *zip(REPLAY_RECEIPTS[4:6], positive["level_one_nodes"], strict=True),
        (REPLAY_RECEIPTS[6], root),
    ]
    for path, facts in receipt_bindings:
        artifact = _artifact_by_path(artifacts, path)
        if (
            artifact["sha256"] != facts["receipt_sha256"]
            or artifact["size_bytes"] != facts["receipt_bytes"]
        ):
            raise PublicReplayError(f"verified receipt facts differ from artifact: {path}")
    mutated_artifact = _artifact_by_path(artifacts, MUTATED_RECEIPT)
    if mutated_artifact["sha256"] != mutation["mutated_receipt_sha256"]:
        raise PublicReplayError("mutation transcript differs from mutated receipt artifact")


def _validate_receipt_mutation_pair(bundle: Path) -> None:
    source_raw = _read_regular(
        bundle / REPLAY_RECEIPTS[-1], MAX_ARTIFACT_BYTES, "source root receipt"
    )
    mutated_raw = _read_regular(
        bundle / MUTATED_RECEIPT, MAX_ARTIFACT_BYTES, "mutated root receipt"
    )
    source = _load_compact_json_object(source_raw, MAX_ARTIFACT_BYTES, "source root receipt")
    mutated = _load_compact_json_object(mutated_raw, MAX_ARTIFACT_BYTES, "mutated root receipt")
    source_seal = _receipt_seal(source)
    mutated_seal = _receipt_seal(mutated)
    if len(source_seal) != len(mutated_seal):
        raise PublicReplayError("mutated receipt changes the seal word count")
    differences = [
        index
        for index, (left, right) in enumerate(zip(source_seal, mutated_seal, strict=True))
        if left != right
    ]
    if differences != [1]:
        raise PublicReplayError("mutated receipt does not change exactly seal word 1")
    if source_seal[1] ^ mutated_seal[1] != 1:
        raise PublicReplayError("mutated receipt does not XOR the seal low bit")
    restored = json.loads(json.dumps(mutated))
    _receipt_seal(restored)[1] = source_seal[1]
    if compact_json_bytes(restored) != source_raw:
        raise PublicReplayError("mutated receipt changes data outside the seal word")


def _receipt_seal(receipt: dict[str, Any]) -> list[int]:
    if set(receipt) != {"inner", "journal", "metadata"}:
        raise PublicReplayError("receipt outer fields mismatch")
    inner = receipt.get("inner")
    if not isinstance(inner, dict) or set(inner) != {"Succinct"}:
        raise PublicReplayError("receipt inner variant is not exactly Succinct")
    succinct = inner.get("Succinct")
    expected_fields = {
        "claim",
        "control_id",
        "control_inclusion_proof",
        "hashfn",
        "seal",
        "verifier_parameters",
    }
    if not isinstance(succinct, dict) or set(succinct) != expected_fields:
        raise PublicReplayError("receipt Succinct fields mismatch")
    seal = succinct.get("seal") if isinstance(succinct, dict) else None
    if (
        not isinstance(seal, list)
        or not seal
        or any(type(word) is not int or word < 0 or word > 0xFFFF_FFFF for word in seal)
    ):
        raise PublicReplayError("receipt Succinct seal is malformed")
    return seal


def _bundle_inventory(root: Path) -> list[str]:
    if root.is_symlink() or not root.is_dir():
        raise PublicReplayError("bundle root must be a non-symlink directory")
    found: list[str] = []
    directories: set[str] = set()
    for path in root.rglob("*"):
        if path.is_symlink():
            raise PublicReplayError("bundle contains a symlink")
        if path.is_file():
            found.append(path.relative_to(root).as_posix())
        elif path.is_dir():
            directories.add(path.relative_to(root).as_posix())
        else:
            raise PublicReplayError("bundle contains an unsupported filesystem entry")
    if directories != EXPECTED_BUNDLE_DIRECTORIES:
        raise PublicReplayError("bundle directory inventory mismatch")
    return sorted(found)


def _validate_no_absolute_strings(value: Any) -> None:
    strings: list[str] = []
    if isinstance(value, str):
        strings.append(value)
    elif isinstance(value, dict):
        for key, child in value.items():
            strings.append(str(key))
            _validate_no_absolute_strings(child)
    elif isinstance(value, list):
        for child in value:
            _validate_no_absolute_strings(child)
    for string in strings:
        if string.startswith("/") or re.search(r"[A-Za-z]:[\\/]", string) or "file://" in string:
            raise PublicReplayError("manifest contains an absolute path")


def _require_exact_fields(value: Any, fields: set[str], label: str) -> None:
    if not isinstance(value, dict) or set(value) != fields:
        raise PublicReplayError(f"{label} fields mismatch")


def _require_exact_bool_map(
    value: Any,
    expected: dict[str, bool],
    label: str,
) -> None:
    _require_exact_fields(value, set(expected), label)
    value = cast(dict[str, Any], value)
    if any(
        type(value.get(field)) is not bool or value.get(field) is not expected_value
        for field, expected_value in expected.items()
    ):
        raise PublicReplayError(f"{label} values mismatch")


def _require_safe_relative(value: Any) -> None:
    if not isinstance(value, str) or not value or "\\" in value:
        raise PublicReplayError("artifact path is not a safe relative path")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or str(path) != value:
        raise PublicReplayError("artifact path is not a safe relative path")


def _is_digest(value: Any) -> bool:
    return isinstance(value, str) and HEX_DIGEST.fullmatch(value) is not None


def _is_git_object_id(value: Any) -> bool:
    return isinstance(value, str) and GIT_OBJECT_ID.fullmatch(value) is not None


def _is_iso_date(value: Any) -> bool:
    if not isinstance(value, str) or re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}", value) is None:
        return False
    try:
        return date.fromisoformat(value).isoformat() == value
    except ValueError:
        return False


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON number: {value}")
