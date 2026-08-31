from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

import tools.check_global_settlement_abi_v2_o008_evidence as checker_module
from tools.check_global_settlement_abi_v2_o008_evidence import (
    MANIFEST_PATH,
    REPO_ROOT,
    check_evidence_manifest,
)


def _manifest() -> dict[str, object]:
    loaded = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    assert isinstance(loaded, dict)
    return loaded


def _write(tmp_path: Path, data: dict[str, object]) -> Path:
    path = tmp_path / "evidence.json"
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    return path


def _check(tmp_path: Path, data: dict[str, object]) -> dict[str, Any]:
    return check_evidence_manifest(_write(tmp_path, data), repo_root=REPO_ROOT)


def test_frozen_packet_validates_without_promotion_or_authority() -> None:
    report = check_evidence_manifest()
    assert report["ok"] is True, report["errors"]
    assert report["status"] == "BOUNDED_EVIDENCE_VALID_NO_PROMOTION"
    assert report["promotion_allowed"] is False
    assert report["authority"] == "NONE"
    assert report["whole_program_value_movement_gates_passed"] == 0
    current_source_drift = report["current_source_drift"]
    assert isinstance(current_source_drift, list)
    assert report["current_applicable"] is (len(current_source_drift) == 0)


@pytest.mark.parametrize(
    ("field", "mutant"),
    [("promotion_allowed", True), ("authority", "SETTLEMENT")],
)
def test_rejects_claim_elevation(
    tmp_path: Path, field: str, mutant: object
) -> None:
    data = _manifest()
    data[field] = mutant
    report = _check(tmp_path, data)
    assert report["ok"] is False
    assert report["promotion_allowed"] is False
    assert report["authority"] == "NONE"


def test_rejects_pinned_hash_drift(tmp_path: Path) -> None:
    data = _manifest()
    hashes = data["file_sha256"]
    assert isinstance(hashes, dict)
    hashes["src/core/global_settlement_primitives_v2.py"] = "0" * 64
    report = _check(tmp_path, data)
    assert report["ok"] is False
    assert any("hash registry" in error for error in report["errors"])


def test_rejects_projection_and_wire_order_mutants(tmp_path: Path) -> None:
    data = _manifest()
    registry = data["field_registry"]
    assert isinstance(registry, list)
    amount = next(row for row in registry if row["record"] == "EconomicAmountV2")
    amount["fields"][0], amount["fields"][1] = amount["fields"][1], amount["fields"][0]
    amount["canonical_key_order_if_encoded"] = list(
        reversed(amount["canonical_key_order_if_encoded"])
    )
    report = _check(tmp_path, data)
    assert report["ok"] is False
    assert any("projection/observable field order" in error for error in report["errors"])
    assert any("canonical wire key order" in error for error in report["errors"])


def test_rejects_lane_semantic_promotion(tmp_path: Path) -> None:
    data = _manifest()
    lanes = data["lane_conservation_status"]
    assert isinstance(lanes, list)
    lanes[1]["lane_semantic_status"] = "PROVED"
    lanes[1]["mounted"] = True
    report = _check(tmp_path, data)
    assert report["ok"] is False
    assert any("SPOT_LIQUIDITY semantic status" in error for error in report["errors"])
    assert any("SPOT_LIQUIDITY mounting claim" in error for error in report["errors"])


def test_rejects_enum_and_dependency_mutants(tmp_path: Path) -> None:
    data = _manifest()
    enums = data["enum_inventory"]
    dependencies = data["dependencies"]
    assert isinstance(enums, dict)
    assert isinstance(dependencies, dict)
    enums["LaneIdV2"] = list(reversed(enums["LaneIdV2"]))
    dependencies["O-006"] = "CLOSED"
    report = _check(tmp_path, data)
    assert report["ok"] is False
    assert any("enum inventory" in error for error in report["errors"])
    assert any("dependency status" in error for error in report["errors"])


@pytest.mark.parametrize(
    ("record_name", "field_name"),
    [
        ("AssetTransferPolicyV2", "asset_origin_root"),
        ("AssetTransferCommandV2", "asset_origin_root"),
        ("AssetOriginRegistrationCommandV2", "issue_policy_root"),
        ("GlobalEconomicStateEffectRefinementV2", "terminal_plan_root"),
        ("GlobalEconomicStateEffectRefinementV2", "oracle_plan_root"),
    ],
)
def test_rejects_exact_field_profile_mutants(
    tmp_path: Path, record_name: str, field_name: str
) -> None:
    data = _manifest()
    registry = data["field_registry"]
    assert isinstance(registry, list)
    record = next(row for row in registry if row["record"] == record_name)
    field = next(row for row in record["fields"] if row["name"] == field_name)
    field["profile"] = "root"
    report = _check(tmp_path, data)
    assert report["ok"] is False
    assert any(f"{record_name}.{field_name} field profile drift" in error for error in report["errors"])


def test_rejects_stale_source_anchor_and_blanket_collection_bound(
    tmp_path: Path,
) -> None:
    data = _manifest()
    registry = data["field_registry"]
    profiles = data["field_profiles"]
    assert isinstance(registry, list)
    assert isinstance(profiles, dict)
    fee_row = next(row for row in registry if row["record"] == "FeeConservationRowV2")
    fee_row["source"] = "src/core/global_settlement_effect_values_v2.py:112"
    profiles["ordered_records"]["width"] = "all collections are bounded"
    report = _check(tmp_path, data)
    assert report["ok"] is False
    assert any("FeeConservationRowV2.source" in error for error in report["errors"])
    assert any("ordered_records overstates cardinality" in error for error in report["errors"])


def test_cli_exit_codes_are_fail_closed(tmp_path: Path) -> None:
    checker = REPO_ROOT / "tools/check_global_settlement_abi_v2_o008_evidence.py"
    valid = subprocess.run(
        [sys.executable, str(checker)],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert valid.returncode == 0, valid.stdout + valid.stderr

    data = _manifest()
    data["authority"] = "PRODUCTION"
    invalid_path = _write(tmp_path, data)
    invalid = subprocess.run(
        [sys.executable, str(checker), str(invalid_path)],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert invalid.returncode == 1
    report = json.loads(invalid.stdout)
    assert report["ok"] is False
    assert report["authority"] == "NONE"


def test_current_source_drift_preserves_historical_validity(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    baseline = checker_module.check_evidence_manifest()["current_source_drift"]
    assert isinstance(baseline, list)
    original_sha256 = checker_module._sha256
    drifted = "src/core/global_settlement_primitives_v2.py"

    def current_sha256(path: Path) -> str:
        if path.as_posix().endswith(drifted):
            return "0" * 64
        return original_sha256(path)

    monkeypatch.setattr(checker_module, "_sha256", current_sha256)
    report = checker_module.check_evidence_manifest()
    assert report["ok"] is True, report["errors"]
    assert report["current_applicable"] is False
    assert report["current_source_drift"] == sorted({*baseline, drifted})


def test_frozen_subject_may_be_ancestor_of_head(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.invalid"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Evidence Test"], cwd=tmp_path, check=True)
    marker = tmp_path / "marker.txt"
    marker.write_text("subject\n", encoding="utf-8")
    subprocess.run(["git", "add", "marker.txt"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "subject"], cwd=tmp_path, check=True)
    subject = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=tmp_path, check=True, capture_output=True, text=True
    ).stdout.strip()
    marker.write_text("descendant\n", encoding="utf-8")
    subprocess.run(["git", "commit", "-qam", "descendant"], cwd=tmp_path, check=True)

    monkeypatch.setattr(checker_module, "SUBJECT_COMMIT", subject)
    errors: list[str] = []
    checker_module._validate_subject({"subject_commit": subject}, tmp_path, errors)
    assert errors == []
