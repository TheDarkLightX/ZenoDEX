from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.m6_command_lane_registry_v1 import CAPABILITY_MANIFEST_SHA256_V1
from tools import build_m6_command_lane_registry_v1 as builder_module
from tools import check_m6_command_lane_registry_v1 as checker_module
from tools.build_m6_command_lane_registry_v1 import JSON_OUTPUT, REPO_ROOT, load_source_snapshot_v1
from tools.check_m6_command_lane_registry_v1 import check_m6_command_lane_registry_v1


def _artifact() -> dict[str, object]:
    return json.loads((REPO_ROOT / JSON_OUTPUT).read_text(encoding="utf-8"))


def _write(tmp_path: Path, value: object) -> Path:
    path = tmp_path / "registry.json"
    path.write_text(
        json.dumps(value, sort_keys=True, separators=(",", ":")),
        encoding="utf-8",
    )
    return path


def _write_pretty(tmp_path: Path, value: object) -> Path:
    path = tmp_path / "registry.json"
    path.write_text(json.dumps(value, sort_keys=True, indent=2), encoding="utf-8")
    return path


def test_bdd_given_generated_registry_when_checked_then_research_only_structural_map_passes() -> (
    None
):
    # Arrange / Act
    report = check_m6_command_lane_registry_v1()

    # Assert
    assert report["ok"] is True
    assert report["registered_command_mapping_complete"] is True
    assert report["whole_economy_command_vocabulary_complete"] is False
    assert report["requirements_target_coverage_complete"] is False
    assert report["semantic_launch_alignment_complete"] is False
    assert report["release_backed"] is False
    assert report["mounted"] is False
    assert report["value_movement_claim_allowed"] is False
    assert report["findings"] == []


def test_mutation_given_buy_and_burn_treasury_substitute_when_checked_then_exact_projection_rejects(
    tmp_path: Path,
) -> None:
    # Arrange
    mutated = _artifact()
    row = next(row for row in mutated["decisions"] if row["command"] == "protocol_buy_and_burn")
    row["target_kind"] = "LANE"
    row["target_id"] = "ZDEX_TOKENOMICS"

    # Act
    report = check_m6_command_lane_registry_v1(artifact_path=_write(tmp_path, mutated))

    # Assert
    assert report["ok"] is False
    assert report["findings"][0]["code"] == "ARTIFACT_BINDING_DRIFT"


def test_mutation_given_duplicate_command_when_checked_then_exact_projection_rejects(
    tmp_path: Path,
) -> None:
    # Arrange
    mutated = _artifact()
    mutated["decisions"].append(mutated["decisions"][0])

    # Act
    report = check_m6_command_lane_registry_v1(artifact_path=_write(tmp_path, mutated))

    # Assert
    assert report["ok"] is False
    assert report["findings"][0]["code"] == "ARTIFACT_BINDING_DRIFT"


def test_bva_given_noncanonical_whitespace_when_checked_then_checker_rejects(
    tmp_path: Path,
) -> None:
    # Arrange
    path = _write_pretty(tmp_path, _artifact())

    # Act
    report = check_m6_command_lane_registry_v1(artifact_path=path)

    # Assert
    assert report["ok"] is False
    assert report["findings"][0]["code"] == "NONCANONICAL_ARTIFACT"


def test_rejection_given_registry_artifact_is_missing_when_checked_then_fails_closed(
    tmp_path: Path,
) -> None:
    # Arrange
    missing = tmp_path / "missing-registry.json"

    # Act
    report = check_m6_command_lane_registry_v1(artifact_path=missing)

    # Assert
    assert report["ok"] is False
    assert report["registered_command_mapping_complete"] is False
    assert report["value_movement_claim_allowed"] is False


def test_mutation_given_capability_manifest_substitution_when_checked_then_source_binding_rejects(
    monkeypatch,
) -> None:
    # Arrange
    snapshot = load_source_snapshot_v1(REPO_ROOT)
    substituted = replace(snapshot, capability_manifest_sha256="0" * 64)
    monkeypatch.setattr(checker_module, "load_source_snapshot_v1", lambda _root: substituted)

    # Act
    report = checker_module.check_m6_command_lane_registry_v1()

    # Assert
    assert report["ok"] is False
    assert report["findings"][0]["code"] == "CAPABILITY_MANIFEST_SHA_DRIFT"
    assert CAPABILITY_MANIFEST_SHA256_V1 != "0" * 64


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("registry_root", "0" * 64),
        ("production_authority", "ACTIVE_NEW"),
    ],
)
def test_mutation_given_root_or_authority_drift_when_checked_then_exact_projection_rejects(
    tmp_path: Path,
    field: str,
    value: str,
) -> None:
    # Arrange
    mutated = _artifact()
    mutated[field] = value

    # Act
    report = check_m6_command_lane_registry_v1(artifact_path=_write(tmp_path, mutated))

    # Assert
    assert report["ok"] is False
    assert report["findings"][0]["code"] == "ARTIFACT_BINDING_DRIFT"


def test_mutation_given_safe_mount_worktree_blob_drift_when_snapshot_is_loaded_then_rejects(
    monkeypatch,
) -> None:
    # Arrange
    original_read = builder_module._read_bounded_regular_file_v1

    def substituted_read(path: Path, max_bytes: int, role: str) -> bytes:
        if role == "safe-mount source":
            return b"mutated source"
        return original_read(path, max_bytes, role)

    monkeypatch.setattr(builder_module, "_read_bounded_regular_file_v1", substituted_read)

    # Act
    with pytest.raises(builder_module.CommandLaneRegistryRejectV1) as raised:
        builder_module.load_source_snapshot_v1(REPO_ROOT)

    # Assert
    assert raised.value.code == "SAFE_MOUNT_WORKTREE_BLOB_DRIFT"


@pytest.mark.parametrize(
    ("role", "code"),
    [
        ("active plan registry", "ACTIVE_PLAN_REGISTRY_SHA_DRIFT"),
        ("plan admission receipt", "ADMISSION_RECEIPT_SHA_DRIFT"),
    ],
)
def test_mutation_given_plan_admission_source_substitution_when_loaded_then_rejects(
    monkeypatch,
    role: str,
    code: str,
) -> None:
    # Arrange
    original_read = builder_module._read_bounded_regular_file_v1

    def substituted_read(path: Path, max_bytes: int, actual_role: str) -> bytes:
        if actual_role == role:
            return b"{}"
        return original_read(path, max_bytes, actual_role)

    monkeypatch.setattr(builder_module, "_read_bounded_regular_file_v1", substituted_read)

    # Act
    with pytest.raises(builder_module.CommandLaneRegistryRejectV1) as raised:
        builder_module.load_source_snapshot_v1(REPO_ROOT)

    # Assert
    assert raised.value.code == code
