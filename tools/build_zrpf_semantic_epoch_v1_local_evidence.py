#!/usr/bin/env python3
"""Build the governed Semantic Epoch V1 local evidence manifest."""

from __future__ import annotations

import argparse
import copy
import json
import os
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__:
    from tools import check_zrpf_semantic_epoch_v1_local_evidence as checker
    from tools import zrpf_semantic_epoch_v1_evidence_support as support
else:
    import check_zrpf_semantic_epoch_v1_local_evidence as checker  # type: ignore[no-redef]
    import zrpf_semantic_epoch_v1_evidence_support as support  # type: ignore[no-redef]


ARTIFACT_ROOT = "evidence/zrpf-semantic-epoch-v1-local-proof-v1"
DEFAULT_OUTPUT = support.DEFAULT_MANIFEST.relative_to(support.REPO_ROOT)

SEMANTIC_SOURCE_IDS = {
    "leaf-0": "077b98b101ccaaa26bc60c55f404eb45529cf8e33f881ee340c8931e9c66b0c0",
    "leaf-1": "ae75902cd62795c66472cd8f94a3b05d399950e073cc5123d66d1de338f20f09",
    "leaf-2-positive": "2e11e634189c385fd8541a07a8418e693134c9761c35a916bde5645fbbf07f43",
    "leaf-2-duplicate": "ae75902cd62795c66472cd8f94a3b05d399950e073cc5123d66d1de338f20f09",
}


class EvidenceBuildError(ValueError):
    """The governed bundle cannot produce an accepted manifest."""


@dataclass(frozen=True)
class ArtifactSpec:
    artifact_id: str
    kind: str
    path: str
    expected_sha256: str | None = None
    expected_size_bytes: int | None = None


ARTIFACT_SPECS = (
    ArtifactSpec(
        "duplicate-source-negative-report",
        "duplicate_source_report",
        "reports/duplicate-semantic-source.execution.json",
    ),
    ArtifactSpec(
        "final-independent-build-record",
        "final_build_record",
        "provenance/final-independent-build-record.json",
        "4d419b7874f17691414e1ef1b696c1ba6ea8f7c9386c1d89ce060d874a833e5e",
        3_060,
    ),
    ArtifactSpec("l1-left-receipt", "risc0_receipt", "receipts/l1-left.receipt.json"),
    ArtifactSpec("l1-left-report", "level_one_report", "reports/l1-left.prove.json"),
    ArtifactSpec(
        "l1-right-duplicate-receipt",
        "risc0_receipt",
        "receipts/l1-right-duplicate.receipt.json",
    ),
    ArtifactSpec(
        "l1-right-duplicate-report",
        "level_one_report",
        "reports/l1-right-duplicate.prove.json",
    ),
    ArtifactSpec(
        "l1-right-positive-receipt",
        "risc0_receipt",
        "receipts/l1-right-positive.receipt.json",
    ),
    ArtifactSpec(
        "l1-right-positive-report",
        "level_one_report",
        "reports/l1-right-positive.prove.json",
    ),
    ArtifactSpec(
        "leaf-0-adapter-receipt",
        "risc0_receipt",
        "receipts/adapter-ordinal-0.receipt.json",
    ),
    ArtifactSpec(
        "leaf-0-adapter-report",
        "adapter_report",
        "reports/adapter-ordinal-0.prove.json",
    ),
    ArtifactSpec(
        "leaf-1-adapter-receipt",
        "risc0_receipt",
        "receipts/adapter-ordinal-1.receipt.json",
    ),
    ArtifactSpec(
        "leaf-1-adapter-report",
        "adapter_report",
        "reports/adapter-ordinal-1.prove.json",
    ),
    ArtifactSpec(
        "leaf-2-duplicate-adapter-receipt",
        "risc0_receipt",
        "receipts/adapter-ordinal-2-duplicate.receipt.json",
    ),
    ArtifactSpec(
        "leaf-2-duplicate-adapter-report",
        "adapter_report",
        "reports/adapter-ordinal-2-duplicate.prove.json",
    ),
    ArtifactSpec(
        "leaf-2-positive-adapter-receipt",
        "risc0_receipt",
        "receipts/adapter-ordinal-2-fee.receipt.json",
    ),
    ArtifactSpec(
        "leaf-2-positive-adapter-report",
        "adapter_report",
        "reports/adapter-ordinal-2-fee.prove.json",
    ),
    ArtifactSpec(
        "semantic-positive-receipt",
        "risc0_receipt",
        "receipts/semantic-positive.receipt.json",
    ),
    ArtifactSpec(
        "semantic-positive-report",
        "semantic_report",
        "reports/semantic-positive.prove.json",
    ),
    ArtifactSpec(
        "semantic-positive-seal-mutation-receipt",
        "risc0_receipt",
        "receipts/semantic-positive.seal-word-1-xor-lsb.receipt.json",
    ),
    ArtifactSpec(
        "semantic-positive-seal-mutation-report",
        "semantic_seal_mutation_report",
        "reports/semantic-positive.seal-word-1-xor-lsb.verify.json",
    ),
    ArtifactSpec(
        "semantic-positive-verification-report",
        "semantic_verification_report",
        "reports/semantic-positive.verify.json",
    ),
    ArtifactSpec(
        "source-0-artifact",
        "source_proof_artifact",
        "source-inputs/source-ordinal-0.receipt.json",
    ),
    ArtifactSpec(
        "source-1-artifact",
        "source_proof_artifact",
        "source-inputs/source-ordinal-1.receipt.json",
    ),
    ArtifactSpec(
        "source-2-duplicate-artifact",
        "source_proof_artifact",
        "source-inputs/source-ordinal-2-duplicate.receipt.json",
    ),
    ArtifactSpec(
        "source-2-positive-artifact",
        "source_proof_artifact",
        "source-inputs/source-ordinal-2-fee.receipt.json",
    ),
    ArtifactSpec(
        "stage-d2-source-closure-record",
        "source_closure_record",
        "provenance/stage-d2-source-closure.json",
        "529f79d3667f6350e35d43278402b46a557cc8e9cd198ee4f38cd35703faf9dc",
        10_224,
    ),
    ArtifactSpec(
        "verifier-source-closure-record",
        "source_closure_record",
        "provenance/verifier-source-closure.json",
        "b6eb8f177fd3a510bc30d80117d5134087d31b22fe7561929d10ac5d05d2472b",
        10_415,
    ),
)


def _require_object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise EvidenceBuildError(f"{label} is not a JSON object")
    return value


def _artifact_material(
    artifact_root: Path,
    spec: ArtifactSpec,
) -> tuple[dict[str, Any], dict[str, Any]]:
    encoding = checker.EXPECTED_ENCODING_BY_KIND[spec.kind]
    raw = support.read_relative_regular_file(artifact_root, spec.path)
    try:
        document = _require_object(support.strict_json_loads(raw), f"artifact {spec.artifact_id}")
        canonical = support.canonical_artifact_bytes(document, encoding)
    except support.EvidenceInputError as exc:
        raise EvidenceBuildError(str(exc)) from exc
    if raw != canonical:
        raise EvidenceBuildError(f"artifact JSON bytes are not canonical: {spec.artifact_id}")
    journal_size: int | None = None
    journal_sha256: str | None = None
    if spec.kind == "risc0_receipt":
        try:
            journal_size, journal_sha256 = support.receipt_journal_facts(document)
        except support.EvidenceInputError as exc:
            raise EvidenceBuildError(str(exc)) from exc
    row = {
        "id": spec.artifact_id,
        "kind": spec.kind,
        "path": spec.path,
        "sha256": support.sha256_bytes(raw),
        "size_bytes": len(raw),
        "encoding": encoding,
        "journal_sha256": journal_sha256,
        "journal_size_bytes": journal_size,
    }
    if spec.expected_sha256 is not None and row["sha256"] != spec.expected_sha256:
        raise EvidenceBuildError(f"governed artifact SHA-256 mismatch: {spec.artifact_id}")
    if spec.expected_size_bytes is not None and row["size_bytes"] != spec.expected_size_bytes:
        raise EvidenceBuildError(f"governed artifact size mismatch: {spec.artifact_id}")
    return row, document


def _load_governed_bundle(
    repo_root: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]]]:
    try:
        artifact_root = support.resolve_relative_directory(repo_root, ARTIFACT_ROOT)
    except support.EvidenceInputError as exc:
        raise EvidenceBuildError(str(exc)) from exc
    actual, inventory_errors = support.artifact_inventory(artifact_root)
    if inventory_errors:
        raise EvidenceBuildError("; ".join(inventory_errors))
    expected = sorted(spec.path for spec in ARTIFACT_SPECS)
    if actual != expected:
        raise EvidenceBuildError("governed artifact inventory mismatch")

    rows: dict[str, dict[str, Any]] = {}
    documents: dict[str, dict[str, Any]] = {}
    for spec in ARTIFACT_SPECS:
        row, document = _artifact_material(artifact_root, spec)
        rows[spec.artifact_id] = row
        documents[spec.artifact_id] = document
    if list(rows) != sorted(rows) or len(rows) != 27:
        raise EvidenceBuildError("governed artifact IDs must be 27 unique sorted IDs")
    return rows, documents


def _leaf(
    leaf_id: str,
    ordinal: int,
    source_artifact_id: str,
    adapter_receipt_artifact_id: str,
    adapter_report_artifact_id: str,
    documents: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    report = documents[adapter_report_artifact_id]
    return {
        "id": leaf_id,
        "ordinal": ordinal,
        "semantic_source_id": SEMANTIC_SOURCE_IDS[leaf_id],
        "source_receipt_sha256": report.get("source_receipt_sha256"),
        "source_artifact_id": source_artifact_id,
        "adapter_receipt_artifact_id": adapter_receipt_artifact_id,
        "adapter_report_artifact_id": adapter_report_artifact_id,
    }


def _leaves(documents: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        _leaf(
            "leaf-0",
            0,
            "source-0-artifact",
            "leaf-0-adapter-receipt",
            "leaf-0-adapter-report",
            documents,
        ),
        _leaf(
            "leaf-1",
            1,
            "source-1-artifact",
            "leaf-1-adapter-receipt",
            "leaf-1-adapter-report",
            documents,
        ),
        _leaf(
            "leaf-2-positive",
            2,
            "source-2-positive-artifact",
            "leaf-2-positive-adapter-receipt",
            "leaf-2-positive-adapter-report",
            documents,
        ),
        _leaf(
            "leaf-2-duplicate",
            2,
            "source-2-duplicate-artifact",
            "leaf-2-duplicate-adapter-receipt",
            "leaf-2-duplicate-adapter-report",
            documents,
        ),
    ]


def _level_one_groups() -> list[dict[str, Any]]:
    return [
        {
            "id": "l1-left",
            "partition_start": 0,
            "partition_end_exclusive": 2,
            "child_leaf_ids": ["leaf-0", "leaf-1"],
            "receipt_artifact_id": "l1-left-receipt",
            "report_artifact_id": "l1-left-report",
        },
        {
            "id": "l1-right-positive",
            "partition_start": 2,
            "partition_end_exclusive": 3,
            "child_leaf_ids": ["leaf-2-positive"],
            "receipt_artifact_id": "l1-right-positive-receipt",
            "report_artifact_id": "l1-right-positive-report",
        },
        {
            "id": "l1-right-duplicate",
            "partition_start": 2,
            "partition_end_exclusive": 3,
            "child_leaf_ids": ["leaf-2-duplicate"],
            "receipt_artifact_id": "l1-right-duplicate-receipt",
            "report_artifact_id": "l1-right-duplicate-report",
        },
    ]


def _build_provenance(documents: dict[str, dict[str, Any]]) -> dict[str, Any]:
    closure = documents["stage-d2-source-closure-record"]
    verifier_closure = documents["verifier-source-closure-record"]
    final_build = documents["final-independent-build-record"]
    try:
        file_count, closure_sha256 = support.source_closure_facts(closure)
        verifier_file_count, verifier_closure_sha256 = support.source_closure_facts(
            verifier_closure
        )
        support.require_verifier_closure_extension(closure, verifier_closure)
    except support.EvidenceInputError as exc:
        raise EvidenceBuildError(str(exc)) from exc
    return {
        "cargo_lock_sha256": final_build.get("cargo_lock_sha256"),
        "complete_build_input_closure_verified": final_build.get(
            "complete_build_input_closure_verified"
        ),
        "container_image_id": final_build.get("container_image_id"),
        "cross_host_reproduced": final_build.get("cross_host_reproduced"),
        "final_clean_rebuild_guest_bytes_match": final_build.get(
            "same_host_clean_guest_rebuild_match"
        ),
        "path_independent_reproducibility": final_build.get("path_independent_reproducibility"),
        "risc0_zkvm_version": final_build.get("risc0_zkvm_version"),
        "source_closure_artifact_id": "stage-d2-source-closure-record",
        "source_closure_file_count": file_count,
        "source_closure_sha256": closure_sha256,
        "final_build_record_artifact_id": "final-independent-build-record",
        "toolchain_lock_sha256": final_build.get("toolchain_lock_sha256"),
        "verifier_source_closure_artifact_id": "verifier-source-closure-record",
        "verifier_source_closure_file_count": verifier_file_count,
        "verifier_source_closure_sha256": verifier_closure_sha256,
    }


def build_manifest_document(repo_root: Path = support.REPO_ROOT) -> dict[str, Any]:
    rows, documents = _load_governed_bundle(repo_root)
    semantic = documents["semantic-positive-report"]
    positive_epoch = {
        "leaf_ids": copy.deepcopy(checker.EXPECTED_POSITIVE_LEAVES),
        "l1_group_ids": copy.deepcopy(checker.EXPECTED_POSITIVE_GROUPS),
        "leaf_count": semantic.get("leaf_count"),
        "operation_count": semantic.get("operation_count"),
        "semantic_receipt_artifact_id": "semantic-positive-receipt",
        "semantic_report_artifact_id": "semantic-positive-report",
        "semantic_verification_report_artifact_id": "semantic-positive-verification-report",
        "semantic_seal_mutation_receipt_artifact_id": "semantic-positive-seal-mutation-receipt",
        "semantic_seal_mutation_report_artifact_id": "semantic-positive-seal-mutation-report",
        "semantic_epoch_root": semantic.get("semantic_epoch_root"),
        "proof_tree_root": semantic.get("proof_tree_root"),
        "proposal_hash": semantic.get("proposal_hash"),
        "program_manifest_root": semantic.get("program_manifest_root"),
    }
    return {
        **copy.deepcopy(checker.EXPECTED_HEADER),
        "artifact_root": ARTIFACT_ROOT,
        "build_provenance": _build_provenance(documents),
        "programs": copy.deepcopy(checker.EXPECTED_PROGRAMS),
        "artifacts": [rows[artifact_id] for artifact_id in sorted(rows)],
        "topology": {
            "leaves": _leaves(documents),
            "level_one_groups": _level_one_groups(),
            "positive_epoch": positive_epoch,
            "duplicate_source_control": {
                "leaf_ids": copy.deepcopy(checker.EXPECTED_NEGATIVE_LEAVES),
                "l1_group_ids": copy.deepcopy(checker.EXPECTED_NEGATIVE_GROUPS),
                "duplicated_leaf_ids": copy.deepcopy(checker.EXPECTED_DUPLICATED_LEAVES),
                "negative_report_artifact_id": "duplicate-source-negative-report",
                "semantic_receipt_artifact_id": None,
            },
        },
        "verifier_boundary": copy.deepcopy(checker.EXPECTED_VERIFIER_BOUNDARY),
        "claims": copy.deepcopy(checker.EXPECTED_CLAIMS),
        "non_claims": copy.deepcopy(checker.EXPECTED_NON_CLAIMS),
    }


def build_validated_manifest(
    repo_root: Path = support.REPO_ROOT,
) -> tuple[dict[str, Any], bytes, dict[str, Any]]:
    document = build_manifest_document(repo_root)
    raw = support.canonical_manifest_bytes(document)
    digest = support.sha256_bytes(raw)
    report = checker.validate_manifest(
        document,
        raw=raw,
        repo_root=repo_root,
        expected_manifest_sha256=digest,
    )
    if report.get("ok") is not True:
        errors = report.get("errors")
        raise EvidenceBuildError(f"constructed manifest rejected: {errors}")
    return document, raw, report


def _write_all(descriptor: int, raw: bytes) -> None:
    offset = 0
    while offset < len(raw):
        written = os.write(descriptor, raw[offset:])
        if written <= 0:
            raise EvidenceBuildError("manifest write made no progress")
        offset += written


def _write_new(path: Path, raw: bytes) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags, 0o644)
    except OSError as exc:
        raise EvidenceBuildError("manifest create_new failed") from exc
    try:
        _write_all(descriptor, raw)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _write_replacement(path: Path, raw: bytes) -> None:
    temporary = path.with_name(f".{path.name}.replace.tmp")
    if temporary.exists() or temporary.is_symlink():
        raise EvidenceBuildError("manifest replacement temporary path already exists")
    if path.exists() or path.is_symlink():
        metadata = path.lstat()
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
            raise EvidenceBuildError("manifest replacement target is not a regular file")
    _write_new(temporary, raw)
    try:
        os.replace(temporary, path)
    except OSError as exc:
        try:
            temporary.unlink()
        except OSError:
            pass
        raise EvidenceBuildError("manifest atomic replacement failed") from exc


def write_manifest(path: Path, raw: bytes, *, replace: bool) -> None:
    if not path.is_absolute():
        path = support.REPO_ROOT / path
    parent = path.parent
    if parent.is_symlink() or not parent.is_dir():
        raise EvidenceBuildError("manifest parent must be an existing non-symlink directory")
    if replace:
        _write_replacement(path, raw)
    else:
        _write_new(path, raw)
    try:
        loaded = support.load_manifest(path)
    except support.EvidenceInputError as exc:
        raise EvidenceBuildError(str(exc)) from exc
    if loaded.raw != raw:
        raise EvidenceBuildError("persisted manifest bytes differ from validated bytes")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=support.REPO_ROOT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--replace", action="store_true")
    args = parser.parse_args(argv)
    try:
        _, raw, validation = build_validated_manifest(args.repo_root)
        output = args.output
        if not output.is_absolute():
            output = args.repo_root / output
        write_manifest(output, raw, replace=args.replace)
    except EvidenceBuildError as exc:
        print(
            json.dumps(
                {"ok": False, "error": str(exc)},
                sort_keys=True,
                separators=(",", ":"),
            )
        )
        return 1
    try:
        manifest_path = output.relative_to(args.repo_root).as_posix()
    except ValueError:
        manifest_path = output.as_posix()
    print(
        json.dumps(
            {
                "artifact_count": 27,
                "manifest_path": manifest_path,
                "manifest_sha256": support.sha256_bytes(raw),
                "manifest_size_bytes": len(raw),
                "ok": True,
                "python_verifies_risc0_seals": False,
                "static_validation": validation,
            },
            sort_keys=True,
            separators=(",", ":"),
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
