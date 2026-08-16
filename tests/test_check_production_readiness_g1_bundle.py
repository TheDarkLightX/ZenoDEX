from __future__ import annotations

import json
from pathlib import Path

from tools.check_production_readiness_g1_bundle import (
    DEFAULT_OUTPUT,
    build_document,
    check_artifact,
)


def test_cross_artifact_bundle_is_exact_and_research_only() -> None:
    report = check_artifact(DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert report["artifact_count"] == 7
    assert report["consistency_check_count"] == 7
    assert report["command_count"] == 33
    assert report["profile_decision_count"] == 9
    assert report["open_state_obligation_count"] == 6


def test_bundle_binds_the_registry_and_repair_overlay() -> None:
    document = build_document()

    assert document["source_subject"]["repair_relation"] == "ANCESTRY_ONLY_RESEARCH_OVERLAY"
    assert document["source_subject"]["semantic_equivalence"] == "NOT_PROVED"
    assert document["registry_binding"]["workflow_count"] == 33
    assert document["registry_binding"]["entrypoint_route_count"] == 33
    assert document["registry_binding"]["safe_hold_route_count"] == 33
    assert document["g1_exit_gate"]["production_authority"] == "NONE"
    assert document["g1_exit_gate"]["all_commands_unmounted"] is True


def test_bundle_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["registry_binding"]["command_count"] = 32
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["g1_complete"] is False
    assert report["production_ready"] is False


def test_bundle_cannot_promote_through_a_tampered_check_record(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["consistency_checks"][0]["status"] = "FAIL"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_ready"] is False
