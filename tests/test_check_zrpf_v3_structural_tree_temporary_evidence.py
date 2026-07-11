from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from tools import check_zrpf_v3_structural_tree_temporary_evidence as checker
from tools import zrpf_v3_structural_tree_evidence_support as support


def _manifest() -> dict:
    document, errors = checker.load_manifest()
    assert errors == []
    assert isinstance(document, dict)
    return document


def test_retained_structural_evidence_rejects_hardened_verifier_source_drift() -> None:
    report = checker.validate_manifest(_manifest())

    assert report["ok"] is False
    assert set(report["errors"]) == {
        "source SHA-256 mismatch: zk/zrpf_risc0/Cargo.lock",
        "source SHA-256 mismatch: zk/zrpf_risc0/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_risc0/harness/src/bin/verify_structural_tree.rs",
        "source SHA-256 mismatch: zk/zrpf_risc0/verifier/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_risc0/verifier/src/lib.rs",
        "source SHA-256 mismatch: zk/state_proof_risc0/shared/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_protocol/protocol/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_risc0/aggregate_shared/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_risc0/shared/Cargo.toml",
    }
    assert report["facts"]["receipt_nodes_declared"] == 7
    assert report["facts"]["python_verifies_risc0_seal"] is False


def test_loader_rejects_duplicate_nested_key(tmp_path: Path) -> None:
    path = tmp_path / "manifest.json"
    path.write_text('{"nested":{"sha256":"a","sha256":"b"}}', encoding="utf-8")

    document, errors = checker.load_manifest(path)

    assert document is None
    assert errors == ["manifest JSON rejected: duplicate JSON key: sha256"]


def test_loader_rejects_non_finite_number(tmp_path: Path) -> None:
    path = tmp_path / "manifest.json"
    path.write_text('{"version":NaN}', encoding="utf-8")

    document, errors = checker.load_manifest(path)

    assert document is None
    assert errors == ["manifest JSON rejected: non-finite JSON number: NaN"]


def test_manifest_rejects_unknown_nested_authority_field() -> None:
    document = copy.deepcopy(_manifest())
    document["nodes"][6]["receipt"]["authoritative"] = True

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert "nodes[6].receipt has unknown fields: authoritative" in report["errors"]


def test_manifest_rejects_absolute_or_traversing_path() -> None:
    document = copy.deepcopy(_manifest())
    document["nodes"][0]["artifact_path"] = "/tmp/private.receipt.json"
    document["verification_sources"]["files"][0]["path"] = "../escape.rs"

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert any(error.startswith("absolute path detected at ") for error in report["errors"])
    assert any("path is not a safe relative path" in error for error in report["errors"])


def test_manifest_rejects_hashed_private_name_token(monkeypatch: pytest.MonkeyPatch) -> None:
    document = copy.deepcopy(_manifest())
    token = "confidentialfixture"
    monkeypatch.setattr(
        support,
        "PRIVATE_NAME_TOKEN_HASHES",
        {hashlib.sha256(token.encode("utf-8")).hexdigest()},
    )
    document["scope"] = token

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert "private project name token detected at manifest.scope" in report["errors"]


def test_manifest_rejects_wrong_program_image_word() -> None:
    document = copy.deepcopy(_manifest())
    document["programs"][1]["image_id_words"][0] ^= 1

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert "program image words do not encode image ID: structural_l1" in report["errors"]


def test_manifest_malformed_types_fail_closed_without_checker_exception() -> None:
    program_document = copy.deepcopy(_manifest())
    program_document["programs"][0]["role"] = []
    program_report = checker.validate_manifest(program_document)
    assert program_report["ok"] is False
    assert "program role must be a string" in program_report["errors"]

    node_document = copy.deepcopy(_manifest())
    node_document["nodes"][0]["id"] = []
    node_report = checker.validate_manifest(node_document)
    assert node_report["ok"] is False
    assert "node IDs must be strings" in node_report["errors"]

    child_document = copy.deepcopy(_manifest())
    child_document["nodes"][4]["child_ids"] = [[]]
    child_report = checker.validate_manifest(child_document)
    assert child_report["ok"] is False
    assert "tree child IDs must be strings: l1-left" in child_report["errors"]

    topology_document = copy.deepcopy(_manifest())
    topology_document["nodes"][6]["topology"]["leaf_count"] = "4"
    topology_report = checker.validate_manifest(topology_document)
    assert topology_report["ok"] is False
    assert "tree topology values must be integers: l2-root" in topology_report["errors"]


def test_manifest_rejects_partition_gap_and_count_drift() -> None:
    document = copy.deepcopy(_manifest())
    document["nodes"][5]["topology"]["partition_start"] = 3
    document["nodes"][6]["topology"]["leaf_count"] = 5

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert "tree child partitions are not dense: l2-root" in report["errors"]
    assert "tree leaf_count does not sum: l2-root" in report["errors"]


def test_manifest_rejects_parent_link_or_child_order_mutation() -> None:
    document = copy.deepcopy(_manifest())
    document["nodes"][4]["child_ids"] = ["leaf-1", "leaf-0"]

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert "node child_ids mismatch: l1-left" in report["errors"]
    assert "tree child partitions are not dense: l1-left" in report["errors"]


def test_manifest_rejects_python_seal_authority_or_release_promotion() -> None:
    document = copy.deepcopy(_manifest())
    document["receipt_verification"]["python_checker_verifies_seal"] = True
    document["claims"]["release_backed"] = True

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert "receipt-verification boundary facts mismatch" in report["errors"]
    assert "claim boundary mismatch" in report["errors"]


def test_manifest_rejects_false_proving_source_attestation() -> None:
    document = copy.deepcopy(_manifest())
    document["prover_execution"]["executed_harness_source_closure_attested"] = True
    document["prover_execution"]["current_source_matches_executed"] = True
    document["claims"]["proof_generation_source_closure_attested"] = True

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert "prover-execution provenance facts mismatch" in report["errors"]
    assert "claim boundary mismatch" in report["errors"]


def test_manifest_rejects_missing_negative_control() -> None:
    document = copy.deepcopy(_manifest())
    document["negative_controls"][0]["passed"] = False

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert "negative-control facts mismatch" in report["errors"]


def test_manifest_rejects_source_hash_drift() -> None:
    document = copy.deepcopy(_manifest())
    document["guest_build_sources"]["files"][0]["sha256"] = "00" * 32

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert any(error.startswith("source SHA-256 mismatch: ") for error in report["errors"])
    assert "source closure SHA-256 mismatch" in report["errors"]


def _synthetic_receipt(tmp_path: Path) -> tuple[Path, dict]:
    journal = b"bounded journal"
    document = {
        "inner": {"Succinct": {"seal": [1, 2, 3]}},
        "journal": {"bytes": list(journal)},
        "metadata": {"verifier_parameters": [1] * 8},
    }
    raw = json.dumps(document, separators=(",", ":")).encode("utf-8")
    path = tmp_path / "receipt.json"
    path.write_bytes(raw)
    node = {
        "artifact_path": "receipt.json",
        "receipt": {
            "kind": "succinct",
            "sha256": hashlib.sha256(raw).hexdigest(),
            "size_bytes": len(raw),
        },
        "journal": {
            "protocol_hash": "00" * 32,
            "sha256": hashlib.sha256(journal).hexdigest(),
            "size_bytes": len(journal),
        },
    }
    return path, node


def test_optional_receipt_check_binds_outer_and_journal_bytes(tmp_path: Path) -> None:
    path, node = _synthetic_receipt(tmp_path)

    assert support.verify_receipt_artifact(tmp_path, node) == []

    path.write_bytes(path.read_bytes() + b" ")
    errors = support.verify_receipt_artifact(tmp_path, node)
    assert errors == ["receipt artifact size mismatch: receipt.json", "receipt artifact SHA-256 mismatch: receipt.json"]


def test_optional_receipt_check_rejects_symlink(tmp_path: Path) -> None:
    path, node = _synthetic_receipt(tmp_path)
    link = tmp_path / "linked.json"
    link.symlink_to(path)
    node["artifact_path"] = "linked.json"

    assert support.verify_receipt_artifact(tmp_path, node) == [
        "receipt artifact path escapes its root or is not a regular file"
    ]


def test_optional_transcript_check_rejects_mutation(tmp_path: Path) -> None:
    transcript_path = tmp_path / "transcript.json"
    transcript_path.write_bytes(b'{"ok":true}\n')
    transcript = {
        "artifact_path": "transcript.json",
        "sha256": hashlib.sha256(transcript_path.read_bytes()).hexdigest(),
        "size_bytes": transcript_path.stat().st_size,
    }

    assert support.verify_transcript_artifact(tmp_path, transcript, "transcript") == []

    transcript_path.write_bytes(b'{"ok":false}\n')
    assert support.verify_transcript_artifact(tmp_path, transcript, "transcript") == [
        "transcript size mismatch",
        "transcript SHA-256 mismatch",
    ]
