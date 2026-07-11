from __future__ import annotations

import base64
import copy
import hashlib
from pathlib import Path
from typing import Any

import pytest

from tools import check_zrpf_semantic_epoch_v1_local_evidence as checker
from tools import zrpf_semantic_epoch_v1_evidence_support as support


def _digest(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def _write_json(path: Path, document: Any, encoding: str) -> bytes:
    raw = support.canonical_artifact_bytes(document, encoding)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return raw


def _receipt_document(label: str) -> dict[str, Any]:
    journal = list((f"journal:{label}").encode("ascii"))
    return {
        "inner": {"Succinct": {"seal": [1, 2, 3, len(label)]}},
        "journal": {"bytes": journal},
        "metadata": {"verifier_parameters": [7] * 8},
    }


def _artifact_row(
    artifact_root: Path,
    *,
    artifact_id: str,
    kind: str,
    relative: str,
    document: Any,
) -> dict[str, Any]:
    encoding = checker.EXPECTED_ENCODING_BY_KIND[kind]
    raw = _write_json(artifact_root / relative, document, encoding)
    journal_size: int | None = None
    journal_sha256: str | None = None
    if kind == "risc0_receipt":
        journal_size, journal_sha256 = support.receipt_journal_facts(document)
    return {
        "id": artifact_id,
        "kind": kind,
        "path": relative,
        "sha256": support.sha256_bytes(raw),
        "size_bytes": len(raw),
        "encoding": encoding,
        "journal_sha256": journal_sha256,
        "journal_size_bytes": journal_size,
    }


def _closure_document(rows: list[dict[str, Any]], commit: str) -> dict[str, Any]:
    ordered = sorted(rows, key=lambda row: row["path"])
    hasher = hashlib.sha256()
    for row in ordered:
        for value in (row["role"], row["path"], row["sha256"]):
            hasher.update(str(value).encode("ascii"))
            hasher.update(b"\0")
        hasher.update(str(row["size_bytes"]).encode("ascii"))
        hasher.update(b"\n")
    return {
        "definition": support.SOURCE_CLOSURE_DEFINITION,
        "file_count": len(ordered),
        "files": ordered,
        "git_commit": commit,
        "schema": "zenodex/zrpf_v3_frozen_source_closure/v1",
        "sha256": hasher.hexdigest(),
        "status": "frozen_source_closure",
        "worktree_clean": True,
    }


def _synthetic_evidence(tmp_path: Path) -> tuple[dict[str, Any], Path]:
    artifact_root = tmp_path / "evidence/bundle"
    artifacts: dict[str, dict[str, Any]] = {}

    leaf_specs = [
        ("leaf-0", 0, "source-0", "semantic-0"),
        ("leaf-1", 1, "source-1", "semantic-shared"),
        ("leaf-2-positive", 2, "source-2-positive", "semantic-2"),
        ("leaf-2-duplicate", 2, "source-2-duplicate", "semantic-shared"),
    ]
    leaves: list[dict[str, Any]] = []
    for leaf_id, ordinal, source_id, semantic_label in leaf_specs:
        source_artifact_id = f"{source_id}-artifact"
        embedded_source_receipt = support.canonical_artifact_bytes(
            _receipt_document(f"embedded:{source_id}"), "json_compact_insertion"
        )
        source_receipt_sha256 = support.sha256_bytes(embedded_source_receipt)
        source_document = {
            "meta": {
                "proof_profile": "recursive_spot_leaf_v1",
                "proof_type": support.SOURCE_PROOF_TYPE,
                "receipt_codec": "risc0_receipt_canonical_serde_json_depth128_v1",
                "receipt_hashfn": "poseidon2",
                "receipt_kind": "succinct",
            },
            "proof": base64.b64encode(embedded_source_receipt).decode("ascii"),
            "proof_type": support.SOURCE_PROOF_TYPE,
            "schema": "tau_state_proof",
            "schema_version": 1,
            "state_hash": _digest(f"state:{source_id}"),
        }
        artifacts[source_artifact_id] = _artifact_row(
            artifact_root,
            artifact_id=source_artifact_id,
            kind="source_proof_artifact",
            relative=f"source-inputs/{source_id}.json",
            document=source_document,
        )

        receipt_id = f"{leaf_id}-adapter-receipt"
        receipt_document = _receipt_document(receipt_id)
        artifacts[receipt_id] = _artifact_row(
            artifact_root,
            artifact_id=receipt_id,
            kind="risc0_receipt",
            relative=f"receipts/{receipt_id}.json",
            document=receipt_document,
        )
        report_id = f"{leaf_id}-adapter-report"
        report = {
            "adapter_image_id": checker._program_id("v1_leaf_adapter"),
            "adapter_program_bytes": checker.EXPECTED_PROGRAMS[0]["combined_elf_size_bytes"],
            "adapter_receipt_bytes": artifacts[receipt_id]["size_bytes"],
            "adapter_receipt_sha256": artifacts[receipt_id]["sha256"],
            "adapter_receipt_written": True,
            "assigned_leaf_ordinal": ordinal,
            "journal_hash": _digest(f"journal-hash:{leaf_id}"),
            "journal_sha256": artifacts[receipt_id]["journal_sha256"],
            "nonclaims": checker.ADAPTER_REPORT_NONCLAIMS,
            "ok": True,
            "source_receipt_sha256": source_receipt_sha256,
            "status": "temporary_path_spot_v1_adapter_receipt_verified",
        }
        artifacts[report_id] = _artifact_row(
            artifact_root,
            artifact_id=report_id,
            kind="adapter_report",
            relative=f"reports/{report_id}.json",
            document=report,
        )
        leaves.append(
            {
                "id": leaf_id,
                "ordinal": ordinal,
                "semantic_source_id": _digest(semantic_label),
                "source_receipt_sha256": source_receipt_sha256,
                "source_artifact_id": source_artifact_id,
                "adapter_receipt_artifact_id": receipt_id,
                "adapter_report_artifact_id": report_id,
            }
        )

    group_specs = [
        ("l1-left", 0, 2, ["leaf-0", "leaf-1"]),
        ("l1-right-positive", 2, 3, ["leaf-2-positive"]),
        ("l1-right-duplicate", 2, 3, ["leaf-2-duplicate"]),
    ]
    groups: list[dict[str, Any]] = []
    for group_id, start, end, children in group_specs:
        receipt_id = f"{group_id}-receipt"
        receipt_document = _receipt_document(receipt_id)
        artifacts[receipt_id] = _artifact_row(
            artifact_root,
            artifact_id=receipt_id,
            kind="risc0_receipt",
            relative=f"receipts/{receipt_id}.json",
            document=receipt_document,
        )
        report_id = f"{group_id}-report"
        report = {
            "adapter_image_id": checker._program_id("v1_leaf_adapter"),
            "child_count": len(children),
            "journal_hash": _digest(f"journal-hash:{group_id}"),
            "journal_sha256": artifacts[receipt_id]["journal_sha256"],
            "level_one_image_id": checker._program_id("structural_l1"),
            "nonclaims": checker.LEVEL_ONE_REPORT_NONCLAIMS,
            "ok": True,
            "receipt_bytes": artifacts[receipt_id]["size_bytes"],
            "receipt_sha256": artifacts[receipt_id]["sha256"],
            "receipt_written": True,
            "status": "bounded_structural_l1_succinct_receipt_verified",
        }
        artifacts[report_id] = _artifact_row(
            artifact_root,
            artifact_id=report_id,
            kind="level_one_report",
            relative=f"reports/{report_id}.json",
            document=report,
        )
        groups.append(
            {
                "id": group_id,
                "partition_start": start,
                "partition_end_exclusive": end,
                "child_leaf_ids": children,
                "receipt_artifact_id": receipt_id,
                "report_artifact_id": report_id,
            }
        )

    semantic_receipt_id = "semantic-positive-receipt"
    semantic_receipt = _receipt_document(semantic_receipt_id)
    artifacts[semantic_receipt_id] = _artifact_row(
        artifact_root,
        artifact_id=semantic_receipt_id,
        kind="risc0_receipt",
        relative=f"receipts/{semantic_receipt_id}.json",
        document=semantic_receipt,
    )
    semantic_report_id = "semantic-positive-report"
    semantic_facts: dict[str, Any] = {
        "semantic_epoch_root": _digest("semantic-epoch-root"),
        "proof_tree_root": _digest("proof-tree-root"),
        "proposal_hash": _digest("proposal-hash"),
        "program_manifest_root": _digest("program-manifest-root"),
    }
    semantic_report = {
        "adapter_image_id": checker._program_id("v1_leaf_adapter"),
        "leaf_count": 3,
        "level_one_group_count": 2,
        "level_one_image_id": checker._program_id("structural_l1"),
        "level_two_image_id": checker._program_id("structural_l2"),
        "nonclaims": checker.SEMANTIC_REPORT_NONCLAIMS,
        "ok": True,
        "operation_count": 3,
        "program_manifest_root": semantic_facts["program_manifest_root"],
        "proof_tree_root": semantic_facts["proof_tree_root"],
        "proposal_hash": semantic_facts["proposal_hash"],
        "receipt_bytes": artifacts[semantic_receipt_id]["size_bytes"],
        "receipt_sha256": artifacts[semantic_receipt_id]["sha256"],
        "receipt_written": True,
        "semantic_epoch_image_id": checker._program_id("semantic_epoch"),
        "semantic_epoch_root": semantic_facts["semantic_epoch_root"],
        "status": "bounded_v1_adapter_semantic_epoch_succinct_receipt_verified",
        "structural_level_two_journal_hash": semantic_facts["proof_tree_root"],
    }
    artifacts[semantic_report_id] = _artifact_row(
        artifact_root,
        artifact_id=semantic_report_id,
        kind="semantic_report",
        relative=f"reports/{semantic_report_id}.json",
        document=semantic_report,
    )

    def receipt_identity(artifact_id: str) -> dict[str, Any]:
        row = artifacts[artifact_id]
        return {
            "journal_sha256": row["journal_sha256"],
            "receipt_bytes": row["size_bytes"],
            "receipt_sha256": row["sha256"],
        }

    semantic_verification_report_id = "semantic-positive-verification-report"
    semantic_verification_report = {
        "adapter_image_id": checker._program_id("v1_leaf_adapter"),
        "adapter_receipts_sealed_verified": 3,
        "claim_binding": _digest("semantic-claim-binding"),
        "dependency_programs_governed": True,
        "exact_expected_proposal_verified": True,
        "groups": [
            {
                "adapter_receipts": [
                    receipt_identity("leaf-0-adapter-receipt"),
                    receipt_identity("leaf-1-adapter-receipt"),
                ],
                "level_one_receipt": receipt_identity("l1-left-receipt"),
            },
            {
                "adapter_receipts": [receipt_identity("leaf-2-positive-adapter-receipt")],
                "level_one_receipt": receipt_identity("l1-right-positive-receipt"),
            },
        ],
        "leaf_count": 3,
        "level_one_group_count": 2,
        "level_one_image_id": checker._program_id("structural_l1"),
        "level_one_receipts_sealed_verified": 2,
        "level_two_image_id": checker._program_id("structural_l2"),
        "methods_validated": True,
        "nonclaims": checker.PERSISTED_VERIFICATION_NONCLAIMS,
        "ok": True,
        "operation_count": 3,
        "program_manifest_root": semantic_facts["program_manifest_root"],
        "proof_tree_root": semantic_facts["proof_tree_root"],
        "proposal_hash": semantic_facts["proposal_hash"],
        "receipt_profile_id": checker.EXPECTED_VERIFIER_BOUNDARY["profile_id"],
        "schema": "zenodex/zrpf_semantic_epoch_persisted_verification/v1",
        "semantic_epoch_image_id": checker._program_id("semantic_epoch"),
        "semantic_epoch_root": semantic_facts["semantic_epoch_root"],
        "semantic_receipt": receipt_identity(semantic_receipt_id),
        "status": "persisted_bounded_v1_semantic_epoch_exact_receipt_verified",
        "structural_level_two_journal_hash": semantic_facts["proof_tree_root"],
    }
    artifacts[semantic_verification_report_id] = _artifact_row(
        artifact_root,
        artifact_id=semantic_verification_report_id,
        kind="semantic_verification_report",
        relative=f"reports/{semantic_verification_report_id}.json",
        document=semantic_verification_report,
    )

    mutation_receipt_id = "semantic-positive-seal-mutation-receipt"
    mutation_receipt = copy.deepcopy(semantic_receipt)
    mutation_receipt["inner"]["Succinct"]["seal"][1] ^= 1
    artifacts[mutation_receipt_id] = _artifact_row(
        artifact_root,
        artifact_id=mutation_receipt_id,
        kind="risc0_receipt",
        relative=f"receipts/{mutation_receipt_id}.json",
        document=mutation_receipt,
    )
    mutation_facts = support.exact_succinct_seal_word_one_xor_one(
        semantic_receipt, mutation_receipt
    )
    mutation_report_id = "semantic-positive-seal-mutation-report"
    mutation_report = {
        "adapter_receipts_sealed_verified": 3,
        "baseline_exact_expected_proposal_verified": True,
        "baseline_semantic_receipt_verified": True,
        "candidate_accepted": False,
        "candidate_create_new": True,
        "candidate_origin": "verifier_created_from_exact_baseline",
        "candidate_reopened_with_created_file_identity": True,
        "control_passed": True,
        "expected_image_id": checker._program_id("semantic_epoch"),
        "level_one_receipts_sealed_verified": 2,
        "mutated_receipt_sha256": artifacts[mutation_receipt_id]["sha256"],
        "mutation": {
            "journal_unchanged": True,
            "kind": "succinct_seal_word_1_xor_1_v1",
            "non_seal_receipt_bytes_unchanged": True,
            "seal_word_count": mutation_facts.word_count,
            "seal_word_index": mutation_facts.word_index,
            "seal_word_mutated": mutation_facts.mutated_word,
            "seal_word_original": mutation_facts.original_word,
            "xor_mask": 1,
        },
        "nonclaims": checker.SEAL_MUTATION_NONCLAIMS,
        "ok": True,
        "reject": {
            "boundary": "VerifiedSemanticEpochReceiptV1::verify_exact_succinct_bytes",
            "code": "receipt_verification_failed",
            "outer_code": "semantic_receipt_artifact_rejected",
            "variant": "ReceiptArtifact(ReceiptVerificationFailed)",
        },
        "schema": "zenodex/zrpf_semantic_epoch_succinct_seal_mutation_reject/v1",
        "semantic_epoch_root": semantic_facts["semantic_epoch_root"],
        "source_receipt_sha256": artifacts[semantic_receipt_id]["sha256"],
        "status": "persisted_semantic_epoch_succinct_seal_mutation_rejected",
    }
    artifacts[mutation_report_id] = _artifact_row(
        artifact_root,
        artifact_id=mutation_report_id,
        kind="semantic_seal_mutation_report",
        relative=f"reports/{mutation_report_id}.json",
        document=mutation_report,
    )

    negative_report_id = "duplicate-source-negative-report"
    negative_report = {
        "adapter_image_id": checker._program_id("v1_leaf_adapter"),
        "adapter_receipts_sealed_verified": 3,
        "authoritative_negative_evidence": False,
        "candidate_accepted": False,
        "cryptographic_reject_receipt_exists": False,
        "dynamic_loader_closure_verified": False,
        "executor_backend": "governed_ipc_r0vm_sealed_memfd",
        "executor_binary_sealed_memfd": True,
        "executor_binary_sha256": "36c016a5bb2ded5bd1f8f92cc487e6ffaeb1e95ec05850c983081a0f716b515b",
        "executor_environment_allowlist": ["RISC0_SERVER_PATH", "TMPDIR"],
        "executor_environment_exact": True,
        "guest_execution_attempted": True,
        "guest_execution_failed": True,
        "guest_execution_rejected": True,
        "guest_reject_boundary": "semantic_epoch_composition",
        "guest_reject_code": "duplicate_semantic_source",
        "host_mirror_reject": "duplicate_semantic_source",
        "level_one_assumptions_supplied": 2,
        "level_one_group_count": 2,
        "level_one_image_id": checker._program_id("structural_l1"),
        "level_one_receipts_sealed_verified": 2,
        "level_two_image_id": checker._program_id("structural_l2"),
        "methods_validated": True,
        "nonclaims": checker.NEGATIVE_REPORT_NONCLAIMS,
        "ok": True,
        "receipt_written": False,
        "same_uid_source_mutation_resistance": True,
        "semantic_epoch_image_id": checker._program_id("semantic_epoch"),
        "semantic_input_bytes": 256,
        "semantic_input_sha256": _digest("negative-semantic-input"),
        "semantic_receipt_created": False,
        "status": "bounded_v1_duplicate_semantic_source_guest_execution_rejected",
    }
    artifacts[negative_report_id] = _artifact_row(
        artifact_root,
        artifact_id=negative_report_id,
        kind="duplicate_source_report",
        relative=f"reports/{negative_report_id}.json",
        document=negative_report,
    )

    closure_row = {
        "path": "zk/zrpf_risc0/Cargo.toml",
        "role": "workspace_build",
        "sha256": _digest("synthetic-source-file"),
        "size_bytes": 123,
    }
    source_closure = _closure_document([closure_row], "11" * 20)
    closure_artifact_id = "stage-d2-source-closure-record"
    artifacts[closure_artifact_id] = _artifact_row(
        artifact_root,
        artifact_id=closure_artifact_id,
        kind="source_closure_record",
        relative="provenance/stage-d2-source-closure.json",
        document=source_closure,
    )
    verifier_source_closure = _closure_document(
        [closure_row, copy.deepcopy(support.VERIFIER_SOURCE_ROW)], "22" * 20
    )
    verifier_closure_artifact_id = "verifier-source-closure-record"
    artifacts[verifier_closure_artifact_id] = _artifact_row(
        artifact_root,
        artifact_id=verifier_closure_artifact_id,
        kind="source_closure_record",
        relative="provenance/verifier-source-closure.json",
        document=verifier_source_closure,
    )
    build_provenance = copy.deepcopy(checker.EXPECTED_BUILD_PROVENANCE)
    build_provenance["source_closure_file_count"] = 1
    build_provenance["source_closure_sha256"] = source_closure["sha256"]
    build_provenance["verifier_source_closure_file_count"] = 2
    build_provenance["verifier_source_closure_sha256"] = verifier_source_closure["sha256"]
    final_build_record = {
        "schema": "zenodex/zrpf_semantic_epoch_v1_final_build_record/v1",
        "status": "same_host_final_clean_guest_rebuild_matched",
        "source_closure_sha256": source_closure["sha256"],
        "source_closure_file_count": 1,
        "verifier_source_closure_sha256": verifier_source_closure["sha256"],
        "verifier_source_closure_file_count": 2,
        "cargo_lock_sha256": build_provenance["cargo_lock_sha256"],
        "toolchain_lock_sha256": build_provenance["toolchain_lock_sha256"],
        "container_image_id": build_provenance["container_image_id"],
        "risc0_zkvm_version": build_provenance["risc0_zkvm_version"],
        "network_disabled": True,
        "root_filesystem_read_only": True,
        "same_host_clean_guest_rebuild_match": True,
        "complete_build_input_closure_verified": False,
        "cross_host_reproduced": False,
        "path_independent_reproducibility": False,
        "proofs_regenerated_by_final_rebuild": False,
        "guest_programs": copy.deepcopy(checker.EXPECTED_PROGRAMS),
        "host_binaries": [
            {
                "role": role,
                "sha256": _digest(f"host-binary:{role}"),
                "size_bytes": index + 1_000,
            }
            for index, role in enumerate(checker.EXPECTED_HOST_BINARY_ROLES)
        ],
        "nonclaims": checker.FINAL_BUILD_NONCLAIMS,
    }
    final_build_artifact_id = "final-independent-build-record"
    artifacts[final_build_artifact_id] = _artifact_row(
        artifact_root,
        artifact_id=final_build_artifact_id,
        kind="final_build_record",
        relative="provenance/final-independent-build-record.json",
        document=final_build_record,
    )

    positive_epoch: dict[str, Any] = {
        "leaf_ids": checker.EXPECTED_POSITIVE_LEAVES,
        "l1_group_ids": checker.EXPECTED_POSITIVE_GROUPS,
        "leaf_count": 3,
        "operation_count": 3,
        "semantic_receipt_artifact_id": semantic_receipt_id,
        "semantic_report_artifact_id": semantic_report_id,
        "semantic_verification_report_artifact_id": semantic_verification_report_id,
        "semantic_seal_mutation_receipt_artifact_id": mutation_receipt_id,
        "semantic_seal_mutation_report_artifact_id": mutation_report_id,
    }
    positive_epoch.update(semantic_facts)
    manifest = {
        **checker.EXPECTED_HEADER,
        "artifact_root": "evidence/bundle",
        "build_provenance": build_provenance,
        "programs": copy.deepcopy(checker.EXPECTED_PROGRAMS),
        "artifacts": [artifacts[artifact_id] for artifact_id in sorted(artifacts)],
        "topology": {
            "leaves": leaves,
            "level_one_groups": groups,
            "positive_epoch": positive_epoch,
            "duplicate_source_control": {
                "leaf_ids": checker.EXPECTED_NEGATIVE_LEAVES,
                "l1_group_ids": checker.EXPECTED_NEGATIVE_GROUPS,
                "duplicated_leaf_ids": checker.EXPECTED_DUPLICATED_LEAVES,
                "negative_report_artifact_id": negative_report_id,
                "semantic_receipt_artifact_id": None,
            },
        },
        "verifier_boundary": copy.deepcopy(checker.EXPECTED_VERIFIER_BOUNDARY),
        "claims": copy.deepcopy(checker.EXPECTED_CLAIMS),
        "non_claims": copy.deepcopy(checker.EXPECTED_NON_CLAIMS),
    }
    return manifest, artifact_root


def _validate(document: dict[str, Any], repo_root: Path) -> dict[str, Any]:
    raw = support.canonical_manifest_bytes(document)
    return checker.validate_manifest(
        document,
        raw=raw,
        repo_root=repo_root,
        expected_manifest_sha256=support.sha256_bytes(raw),
    )


def _artifact_path(document: dict[str, Any], repo_root: Path, artifact_id: str) -> Path:
    row = next(row for row in document["artifacts"] if row["id"] == artifact_id)
    return repo_root / document["artifact_root"] / row["path"]


def _rewrite_artifact(
    document: dict[str, Any], repo_root: Path, artifact_id: str, artifact: Any
) -> None:
    row = next(row for row in document["artifacts"] if row["id"] == artifact_id)
    raw = support.canonical_artifact_bytes(artifact, row["encoding"])
    _artifact_path(document, repo_root, artifact_id).write_bytes(raw)
    row["sha256"] = support.sha256_bytes(raw)
    row["size_bytes"] = len(raw)
    if row["kind"] == "risc0_receipt":
        row["journal_size_bytes"], row["journal_sha256"] = support.receipt_journal_facts(artifact)


def test_synthetic_manifest_and_complete_artifact_inventory_pass(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)

    report = _validate(document, tmp_path)

    assert report["ok"] is True
    assert report["errors"] == []
    assert report["facts"]["artifact_files_checked"] == 27
    assert report["facts"]["python_verifies_risc0_seals"] is False


def test_default_checker_enforces_finalized_manifest_anchor(
    tmp_path: Path,
) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_bytes(support.canonical_manifest_bytes(document))

    report = checker.check_manifest(manifest_path, repo_root=tmp_path)

    assert report["ok"] is False
    assert "manifest SHA-256 differs from governed anchor" in report["errors"]


def test_default_checker_accepts_exact_governed_bundle() -> None:
    report = checker.check_manifest()

    assert report["ok"] is True
    assert report["errors"] == []
    assert report["facts"]["artifact_files_checked"] == 27
    assert report["facts"]["python_verifies_risc0_seals"] is False


@pytest.mark.parametrize(
    ("raw", "message"),
    [
        (b'{"nested":{"x":1,"x":2}}\n', "duplicate JSON key: x"),
        (b'{"value":NaN}\n', "non-finite JSON number: NaN"),
        (b'{"value":1.25}\n', "floating-point JSON number: 1.25"),
    ],
)
def test_manifest_loader_rejects_ambiguous_numbers_or_keys(
    tmp_path: Path, raw: bytes, message: str
) -> None:
    path = tmp_path / "manifest.json"
    path.write_bytes(raw)

    with pytest.raises(support.EvidenceInputError, match=message):
        support.load_manifest(path)


def test_manifest_loader_rejects_noncanonical_whitespace(tmp_path: Path) -> None:
    path = tmp_path / "manifest.json"
    path.write_bytes(b'{"a":1}\n')

    with pytest.raises(support.EvidenceInputError, match="manifest JSON bytes are not canonical"):
        support.load_manifest(path)


def test_unknown_claim_fails_closed(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    document["claims"]["invented_authority"] = False

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "claims has unknown fields: invented_authority" in report["errors"]
    assert "claims mismatch" not in report["errors"]


def test_integer_substitution_for_boolean_claim_fails_closed(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    document["claims"]["production_authority"] = 0

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "claims mismatch" in report["errors"]


def test_python_seal_or_production_claim_promotion_rejects(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    document["verifier_boundary"]["python_verifies_risc0_seals"] = True
    document["claims"]["python_verifies_risc0_seals"] = True
    document["claims"]["production_authority"] = True

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "verifier_boundary mismatch" in report["errors"]
    assert "claims mismatch" in report["errors"]
    assert report["facts"]["python_verifies_risc0_seals"] is False


def test_artifact_path_traversal_rejects(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    document["artifacts"][0]["path"] = "../escape.json"

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert any(error.startswith("artifact path is unsafe:") for error in report["errors"])


def test_artifact_symlink_rejects(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    artifact_id = document["artifacts"][0]["id"]
    path = _artifact_path(document, tmp_path, artifact_id)
    replacement = tmp_path / "replacement.json"
    replacement.write_bytes(path.read_bytes())
    path.unlink()
    path.symlink_to(replacement)

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert any("artifact inventory file rejected" in error for error in report["errors"])
    assert "artifact open or read failed" in report["errors"]


def test_extra_artifact_inventory_entry_rejects(tmp_path: Path) -> None:
    document, artifact_root = _synthetic_evidence(tmp_path)
    (artifact_root / "unlisted.json").write_bytes(b"{}")

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "artifact directory inventory differs from manifest" in report["errors"]


def test_source_closure_internal_hash_mutation_rejects(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    artifact_id = "stage-d2-source-closure-record"
    path = _artifact_path(document, tmp_path, artifact_id)
    closure = support.strict_json_loads(path.read_bytes())
    closure["files"][0]["size_bytes"] += 1
    _rewrite_artifact(document, tmp_path, artifact_id, closure)

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "source closure SHA-256 mismatch" in report["errors"]


def test_verifier_closure_cannot_rewrite_shared_guest_source_row(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    verifier_id = "verifier-source-closure-record"
    verifier_path = _artifact_path(document, tmp_path, verifier_id)
    verifier_closure = support.strict_json_loads(verifier_path.read_bytes())
    verifier_closure["files"][0]["sha256"] = _digest("rewritten-shared-source")
    verifier_closure = _closure_document(verifier_closure["files"], verifier_closure["git_commit"])
    _rewrite_artifact(document, tmp_path, verifier_id, verifier_closure)
    document["build_provenance"]["verifier_source_closure_sha256"] = verifier_closure["sha256"]

    build_id = "final-independent-build-record"
    build_path = _artifact_path(document, tmp_path, build_id)
    build_record = support.strict_json_loads(build_path.read_bytes())
    build_record["verifier_source_closure_sha256"] = verifier_closure["sha256"]
    _rewrite_artifact(document, tmp_path, build_id, build_record)

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "verifier source closure changes proof/guest source rows" in report["errors"]


def test_final_build_record_cannot_promote_cross_host_claim(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    artifact_id = "final-independent-build-record"
    path = _artifact_path(document, tmp_path, artifact_id)
    build_record = support.strict_json_loads(path.read_bytes())
    build_record["cross_host_reproduced"] = True
    _rewrite_artifact(document, tmp_path, artifact_id, build_record)

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "final build record binding mismatch: cross_host_reproduced" in report["errors"]


def test_artifact_hash_and_size_mutation_rejects(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    artifact_id = "leaf-0-adapter-receipt"
    path = _artifact_path(document, tmp_path, artifact_id)
    path.write_bytes(path.read_bytes() + b" ")

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert f"artifact size mismatch: {artifact_id}" in report["errors"]


def test_receipt_journal_substitution_rejects(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    row = next(row for row in document["artifacts"] if row["id"] == "leaf-0-adapter-receipt")
    row["journal_sha256"] = "00" * 32

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "receipt journal SHA-256 mismatch: leaf-0-adapter-receipt" in report["errors"]


def test_semantic_mutation_must_change_only_seal_word_one(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    mutation_id = "semantic-positive-seal-mutation-receipt"
    mutation_path = _artifact_path(document, tmp_path, mutation_id)
    mutation = support.strict_json_loads(mutation_path.read_bytes())
    mutation["metadata"]["extra"] = True
    _rewrite_artifact(document, tmp_path, mutation_id, mutation)

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "Succinct mutation changes non-seal receipt bytes" in report["errors"]


def test_persisted_verification_group_identity_substitution_rejects(
    tmp_path: Path,
) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    report_id = "semantic-positive-verification-report"
    report_path = _artifact_path(document, tmp_path, report_id)
    persisted = support.strict_json_loads(report_path.read_bytes())
    persisted["groups"][0]["adapter_receipts"].reverse()
    _rewrite_artifact(document, tmp_path, report_id, persisted)

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert any(error.endswith("adapter_receipts[0] binding mismatch") for error in report["errors"])


def test_seal_mutation_report_typed_reject_promotion_rejects(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    report_id = "semantic-positive-seal-mutation-report"
    report_path = _artifact_path(document, tmp_path, report_id)
    mutation_report = support.strict_json_loads(report_path.read_bytes())
    mutation_report["candidate_accepted"] = True
    mutation_report["reject"]["code"] = "accepted"
    _rewrite_artifact(document, tmp_path, report_id, mutation_report)

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "semantic seal-mutation report binding mismatch: candidate_accepted" in report["errors"]
    assert "semantic seal mutation typed reject mismatch" in report["errors"]


def test_positive_topology_group_swap_rejects(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    document["topology"]["positive_epoch"]["l1_group_ids"] = [
        "l1-right-positive",
        "l1-left",
    ]

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "positive epoch level-one group order mismatch" in report["errors"]
    assert "positive epoch group-to-leaf topology mismatch" in report["errors"]


def test_duplicate_control_requires_equal_semantic_source(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    document["topology"]["leaves"][3]["semantic_source_id"] = _digest("different")

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "duplicate-source control does not reuse one semantic source" in report["errors"]


def test_duplicate_control_cannot_claim_receipt(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    document["topology"]["duplicate_source_control"]["semantic_receipt_artifact_id"] = (
        "semantic-positive-receipt"
    )

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "duplicate-source control must not declare a semantic receipt" in report["errors"]


def test_adapter_report_receipt_binding_mutation_rejects(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    report_id = "leaf-0-adapter-report"
    report_path = _artifact_path(document, tmp_path, report_id)
    report_document = support.strict_json_loads(report_path.read_bytes())
    report_document["adapter_receipt_sha256"] = "00" * 32
    raw = support.canonical_artifact_bytes(report_document, "json_sorted_compact_newline")
    report_path.write_bytes(raw)
    row = next(row for row in document["artifacts"] if row["id"] == report_id)
    row["sha256"] = support.sha256_bytes(raw)
    row["size_bytes"] = len(raw)

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "adapter report binding mismatch: leaf-0:adapter_receipt_sha256" in report["errors"]


def test_source_artifact_embedded_receipt_binding_mutation_rejects(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    substituted_sha256 = "00" * 32
    document["topology"]["leaves"][0]["source_receipt_sha256"] = substituted_sha256
    report_id = "leaf-0-adapter-report"
    report_path = _artifact_path(document, tmp_path, report_id)
    report_document = support.strict_json_loads(report_path.read_bytes())
    report_document["source_receipt_sha256"] = substituted_sha256
    raw = support.canonical_artifact_bytes(report_document, "json_sorted_compact_newline")
    report_path.write_bytes(raw)
    row = next(row for row in document["artifacts"] if row["id"] == report_id)
    row["sha256"] = support.sha256_bytes(raw)
    row["size_bytes"] = len(raw)

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert "source proof receipt binding mismatch: leaf-0" in report["errors"]


def test_negative_report_must_preserve_non_authoritative_boundary(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    report_id = "duplicate-source-negative-report"
    report_path = _artifact_path(document, tmp_path, report_id)
    report_document = support.strict_json_loads(report_path.read_bytes())
    report_document["authoritative_negative_evidence"] = True
    report_document["cryptographic_reject_receipt_exists"] = True
    raw = support.canonical_artifact_bytes(report_document, "json_sorted_compact_newline")
    report_path.write_bytes(raw)
    row = next(row for row in document["artifacts"] if row["id"] == report_id)
    row["sha256"] = support.sha256_bytes(raw)
    row["size_bytes"] = len(raw)

    report = _validate(document, tmp_path)

    assert report["ok"] is False
    assert (
        "duplicate-source report binding mismatch: authoritative_negative_evidence"
        in report["errors"]
    )
    assert (
        "duplicate-source report binding mismatch: cryptographic_reject_receipt_exists"
        in report["errors"]
    )


def test_manifest_input_object_is_not_mutated(tmp_path: Path) -> None:
    document, _ = _synthetic_evidence(tmp_path)
    before = copy.deepcopy(document)

    _validate(document, tmp_path)

    assert document == before


def test_structure_preserving_malformed_frontier_rejects_without_exception(
    tmp_path: Path,
) -> None:
    seed, _ = _synthetic_evidence(tmp_path)

    def artifact_kind_list(document: dict[str, Any]) -> None:
        document["artifacts"][0]["kind"] = []

    def artifact_encoding_list(document: dict[str, Any]) -> None:
        document["artifacts"][0]["encoding"] = []

    def positive_leaf_ids_nested(document: dict[str, Any]) -> None:
        document["topology"]["positive_epoch"]["leaf_ids"] = [[]]

    def positive_group_ids_none(document: dict[str, Any]) -> None:
        document["topology"]["positive_epoch"]["l1_group_ids"] = None

    def negative_group_ids_none(document: dict[str, Any]) -> None:
        document["topology"]["duplicate_source_control"]["l1_group_ids"] = None

    def semantic_source_list(document: dict[str, Any]) -> None:
        document["topology"]["leaves"][3]["semantic_source_id"] = []

    def source_artifact_list(document: dict[str, Any]) -> None:
        document["topology"]["leaves"][3]["source_artifact_id"] = []

    def group_children_none(document: dict[str, Any]) -> None:
        document["topology"]["level_one_groups"][0]["child_leaf_ids"] = None

    def group_children_nested(document: dict[str, Any]) -> None:
        document["topology"]["level_one_groups"][0]["child_leaf_ids"] = [[]]

    mutations = [
        ("artifact_kind_list", artifact_kind_list),
        ("artifact_encoding_list", artifact_encoding_list),
        ("positive_leaf_ids_nested", positive_leaf_ids_nested),
        ("positive_group_ids_none", positive_group_ids_none),
        ("negative_group_ids_none", negative_group_ids_none),
        ("semantic_source_list", semantic_source_list),
        ("source_artifact_list", source_artifact_list),
        ("group_children_none", group_children_none),
        ("group_children_nested", group_children_nested),
    ]

    for name, mutate in mutations:
        document = copy.deepcopy(seed)
        mutate(document)
        report = _validate(document, tmp_path)
        assert report["ok"] is False, name
        assert report["errors"], name
