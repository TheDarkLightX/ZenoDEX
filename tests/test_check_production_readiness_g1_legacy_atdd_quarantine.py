from __future__ import annotations

import json
from pathlib import Path

from tools.check_production_readiness_g1_legacy_atdd_quarantine import (
    DEFAULT_OUTPUT,
    build_document,
    check_artifact,
)


def test_historical_atdd_contract_is_explicitly_quarantined() -> None:
    report = check_artifact(DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["quarantined"] is True
    assert report["legacy_validation_ok"] is False
    assert report["validation_error_count"] == 23
    assert report["source_pin_mismatch_count"] == 22
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert report["production_authority"] == "NONE"


def test_quarantine_preserves_historical_catalogue_without_promotion() -> None:
    document = build_document()
    legacy_contract = document["legacy_contract"]
    quarantine = document["quarantine"]

    assert legacy_contract["base_commit"] == "12bde5263b8855e0ac76bd49b3de402e3e6f9b76"
    assert legacy_contract["base_commit_is_ancestor_of_current_head"] is True
    assert legacy_contract["base_commit_matches_current_head"] is False
    assert legacy_contract["workflow_count"] == 18
    assert legacy_contract["scenario_count"] == 81
    assert quarantine["usable_as_exact_subject_g1_evidence"] is False
    assert quarantine["production_authority"] == "NONE"


def test_quarantine_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["quarantine"]["quarantined"] = False
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_ready"] is False


def test_malformed_legacy_provenance_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["legacy_contract"] = "historical"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["validation_error_count"] == 0
    assert report["production_authority"] == "NONE"
