"""Adversarial tests for the P4B4 direct-parity evidence checker."""

from __future__ import annotations

import json
from pathlib import Path
from typing import cast

from src.state.canonical import canonical_json_bytes, sha256_hex
from tools.build_fcis_m5_p4b4_parity import artifact_bytes_v1
from tools.check_fcis_m5_p4b4_parity import check_artifact_v1


def _write_artifact(path: Path, artifact: dict[str, object]) -> None:
    path.write_bytes(canonical_json_bytes(artifact) + b"\n")


def _decoded_artifact(repo_root: Path) -> dict[str, object]:
    decoded = json.loads(artifact_bytes_v1(repo_root))
    assert type(decoded) is dict
    return cast(dict[str, object], decoded)


def _rehash(artifact: dict[str, object]) -> None:
    artifact.pop("artifact_sha256", None)
    artifact["artifact_sha256"] = sha256_hex(canonical_json_bytes(artifact))


def test_current_artifact_semantically_rebuilds(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    artifact_path = tmp_path / "artifact.json"
    artifact_path.write_bytes(artifact_bytes_v1(repo_root))

    status, report = check_artifact_v1(repo_root, artifact_path)

    assert status == 0
    assert report["code"] == "artifact_valid"
    assert report["mount_authorized"] is False


def test_fabricated_all_refine_is_killed_after_outer_rehash(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    artifact = _decoded_artifact(repo_root)
    rows = cast(list[dict[str, object]], artifact["rows"])
    first = rows[0]
    legacy = cast(dict[str, object], first["legacy_result_projection"])
    legacy["kind"] = "REJECT"
    legacy["reason"] = "fabricated"
    first["status"] = "REFINE"
    first["first_mismatch_path"] = "REFINE"
    _rehash(artifact)
    artifact_path = tmp_path / "fabricated.json"
    _write_artifact(artifact_path, artifact)

    status, report = check_artifact_v1(repo_root, artifact_path)

    assert status == 1
    assert report["code"] == "semantic_rebuild_mismatch"


def test_stale_outer_hash_is_distinguished_from_semantic_fabrication(
    tmp_path: Path,
) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    artifact = _decoded_artifact(repo_root)
    artifact["verdict"] = "FABRICATED"
    artifact_path = tmp_path / "stale-hash.json"
    _write_artifact(artifact_path, artifact)

    status, report = check_artifact_v1(repo_root, artifact_path)

    assert status == 1
    assert report["code"] == "artifact_hash_mismatch"


def test_canonical_byte_drift_is_rejected_before_semantics(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    artifact_path = tmp_path / "noncanonical.json"
    artifact_path.write_bytes(artifact_bytes_v1(repo_root).replace(b"{", b"{ ", 1))

    status, report = check_artifact_v1(repo_root, artifact_path)

    assert status == 1
    assert report["code"] == "artifact_not_canonical"
