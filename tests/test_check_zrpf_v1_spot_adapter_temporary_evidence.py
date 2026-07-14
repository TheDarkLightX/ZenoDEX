from __future__ import annotations

import copy
import hashlib
from pathlib import Path

from tools import check_zrpf_v1_spot_adapter_temporary_evidence as checker


def _manifest() -> dict:
    document, errors = checker.load_manifest()
    assert errors == []
    assert isinstance(document, dict)
    return document


def test_retained_adapter_evidence_rejects_hardened_verifier_source_drift() -> None:
    report = checker.validate_manifest(_manifest())

    assert report["ok"] is False
    assert set(report["errors"]) == {
        "source SHA-256 mismatch: config/proof_profiles/risc0_recursive_rebuild_reference.json",
        "source SHA-256 mismatch: config/proof_profiles/zrpf_v1_leaf_adapter_source_policy_v1.json",
        "source SHA-256 mismatch: zk/state_proof_risc0/shared/src/recursive.rs",
        "source SHA-256 mismatch: zk/state_proof_risc0/shared/src/lib.rs",
        "source SHA-256 mismatch: zk/state_proof_risc0/shared/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_protocol/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_protocol/protocol/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_protocol/protocol/src/lib.rs",
        "source SHA-256 mismatch: zk/zrpf_risc0/Cargo.lock",
        "source SHA-256 mismatch: zk/zrpf_risc0/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_risc0/harness/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_risc0/harness/src/main.rs",
        "source SHA-256 mismatch: zk/zrpf_risc0/methods/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_risc0/methods/build.rs",
        "source SHA-256 mismatch: zk/zrpf_risc0/shared/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_risc0/shared/src/lib.rs",
        "source SHA-256 mismatch: zk/zrpf_risc0/shared/src/v1_leaf_adapter.rs",
        "source SHA-256 mismatch: zk/zrpf_risc0/verifier/Cargo.toml",
        "source SHA-256 mismatch: zk/zrpf_risc0/verifier/src/lib.rs",
    }
    assert report["facts"]["evidence_ready"] is False
    assert report["facts"]["python_verifies_risc0_seal"] is False


def test_loader_rejects_duplicate_nested_fields(tmp_path: Path) -> None:
    manifest = tmp_path / "manifest.json"
    manifest.write_text(
        '{"schema":"a","nested":{"sha256":"a","sha256":"b"}}',
        encoding="utf-8",
    )

    document, errors = checker.load_manifest(manifest)

    assert document is None
    assert errors == ["manifest JSON rejected: duplicate JSON key: sha256"]


def test_loader_rejects_non_finite_json_number(tmp_path: Path) -> None:
    manifest = tmp_path / "manifest.json"
    manifest.write_text('{"version":NaN}', encoding="utf-8")

    document, errors = checker.load_manifest(manifest)

    assert document is None
    assert errors == ["manifest JSON rejected: non-finite JSON number: NaN"]


def test_manifest_rejects_unknown_nested_field() -> None:
    document = copy.deepcopy(_manifest())
    document["adapter"]["receipt"]["unreviewed_authority"] = True

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert "adapter.receipt has unknown fields: unreviewed_authority" in report["errors"]


def test_manifest_rejects_absolute_source_path() -> None:
    document = copy.deepcopy(_manifest())
    document["evidence_build_sources"]["files"][0]["path"] = "/tmp/private.rs"

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert any(error.startswith("absolute path detected at ") for error in report["errors"])
    assert any("path is not a safe relative path" in error for error in report["errors"])


def test_manifest_rejects_hashed_private_name_token(monkeypatch) -> None:
    document = copy.deepcopy(_manifest())
    synthetic_private_name = "confidentialfixture"
    private_hash = hashlib.sha256(synthetic_private_name.encode("utf-8")).hexdigest()
    monkeypatch.setattr(checker.support, "PRIVATE_NAME_TOKEN_HASHES", {private_hash})
    document["scope"] = synthetic_private_name

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert "private project name token detected at manifest.scope" in report["errors"]


def test_manifest_rejects_source_hash_drift() -> None:
    document = copy.deepcopy(_manifest())
    document["evidence_build_sources"]["files"][0]["sha256"] = "00" * 32

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert any(error.startswith("source SHA-256 mismatch: ") for error in report["errors"])


def test_manifest_rejects_python_seal_verification_overclaim() -> None:
    document = copy.deepcopy(_manifest())
    document["receipt_verification"]["python_checker_verifies_seal"] = True

    report = checker.validate_manifest(document)

    assert report["ok"] is False
    assert "Python checker must deny RISC0 seal verification" in report["errors"]


def test_final_source_closure_checks_relative_file_hash(tmp_path: Path) -> None:
    source = tmp_path / "src" / "guest.rs"
    source.parent.mkdir()
    source.write_bytes(b"fn main() {}\n")
    source_sha256 = hashlib.sha256(source.read_bytes()).hexdigest()
    record = f"adapter_guest\0src/guest.rs\0{source_sha256}\n".encode("utf-8")
    closure = {
        "scope": "test",
        "finalized": True,
        "definition": "test",
        "file_count": 1,
        "sha256": hashlib.sha256(record).hexdigest(),
        "files": [
            {
                "role": "adapter_guest",
                "path": "src/guest.rs",
                "sha256": source_sha256,
            }
        ],
    }
    errors: list[str] = []

    checked = checker._validate_source_closure(
        closure,
        tmp_path,
        errors,
        allow_pending=False,
    )

    assert checked == 1
    assert errors == []


def test_optional_artifact_check_is_hash_and_size_only(tmp_path: Path, monkeypatch) -> None:
    artifact = tmp_path / "adapter.receipt"
    artifact.write_bytes(b"opaque receipt bytes")
    monkeypatch.setitem(
        checker.EXPECTED_ARTIFACTS,
        "adapter_receipt",
        {
            "sha256": hashlib.sha256(artifact.read_bytes()).hexdigest(),
            "size_bytes": artifact.stat().st_size,
        },
    )

    assert checker.verify_optional_artifact(artifact, "adapter_receipt") == []

    artifact.write_bytes(b"mutated receipt bytes")
    assert checker.verify_optional_artifact(artifact, "adapter_receipt") == [
        "adapter_receipt size mismatch"
    ]


def test_final_optional_adapter_artifact_rejects_wrong_bytes(tmp_path: Path) -> None:
    artifact = tmp_path / "adapter.receipt"
    artifact.write_bytes(b"unreviewed")

    assert checker.verify_optional_artifact(artifact, "adapter_receipt") == [
        "adapter_receipt size mismatch"
    ]
