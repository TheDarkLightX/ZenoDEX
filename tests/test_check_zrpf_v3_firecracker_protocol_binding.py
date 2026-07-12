from __future__ import annotations

import json
from pathlib import Path

from tools import check_zrpf_v3_firecracker_protocol_binding as checker


def test_committed_profile_hash_is_bound_across_all_abi_mirrors() -> None:
    report = checker.build_report()

    assert report["ok"] is True
    assert report["errors"] == []
    assert len(set(report["observed_bindings"].values())) == 1
    assert {
        "direct_replay_checker",
        "direct_replay_evidence_governed_bindings",
        "direct_replay_evidence_request",
        "runtime_artifact_manifest",
    }.issubset(report["observed_bindings"])
    assert all(value is False for value in report["authority"].values())


def test_rust_constant_mutation_rejects(tmp_path: Path) -> None:
    raw = checker.RUST_PROTOCOL_PATH.read_bytes()
    first_byte = checker.protocol.CANDIDATE_PROFILE_CANONICAL_SHA256_V1[0]
    replacement = first_byte ^ 1
    changed = raw.replace(
        f"0x{first_byte:02x}".encode("ascii"),
        f"0x{replacement:02x}".encode("ascii"),
        1,
    )
    assert changed != raw
    rust_path = tmp_path / "firecracker_protocol.rs"
    rust_path.write_bytes(changed)

    report = checker.build_report(rust_protocol_path=rust_path)

    assert report["ok"] is False
    assert report["errors"] == ["profile_hash_binding_mismatch"]


def test_stale_runtime_manifest_profile_binding_rejects(tmp_path: Path) -> None:
    manifest = json.loads(checker.RUNTIME_MANIFEST_PATH.read_text(encoding="ascii"))
    manifest["firecracker_profile_canonical_sha256"] = "00" * 32
    path = tmp_path / "runtime-manifest.json"
    path.write_bytes(checker.runtime_manifest.canonical_document_bytes(manifest))

    report = checker.build_report(runtime_artifact_manifest_path=path)

    assert report["ok"] is False
    assert report["errors"] == ["profile_hash_binding_mismatch"]


def test_stale_direct_evidence_request_profile_binding_rejects(tmp_path: Path) -> None:
    evidence = json.loads(checker.DIRECT_REPLAY_EVIDENCE_PATH.read_text(encoding="ascii"))
    evidence["request"]["profile_sha256"] = "00" * 32
    path = tmp_path / "direct-evidence.json"
    path.write_bytes(checker.runtime_manifest.canonical_document_bytes(evidence))

    report = checker.build_report(direct_replay_evidence_path=path)

    assert report["ok"] is False
    assert report["errors"] == ["profile_hash_binding_mismatch"]
