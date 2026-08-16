from __future__ import annotations

import json
from pathlib import Path

from tools.check_production_readiness_g1_safe_hold import (
    DEFAULT_OUTPUT,
    build_document,
    check_artifact,
)


def test_safe_hold_is_exact_and_has_no_production_authority() -> None:
    report = check_artifact(DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert report["command_route_count"] == 33
    assert report["declared_production_writer_count"] == 0
    assert report["selected_profile_count"] == 0


def test_every_command_is_kept_unmounted_until_profile_closure() -> None:
    document = build_document()

    assert len(document["profile_decision_holds"]) == 9
    assert all(decision["status"] == "OPEN" for decision in document["profile_decision_holds"])
    assert all(decision["selected_profile"] is None for decision in document["profile_decision_holds"])
    assert len(document["command_routes"]) == 33
    assert all(
        route["safe_hold_status"] == "UNMOUNTED_RESEARCH_ONLY"
        and route["production_writer_declared"] is False
        for route in document["command_routes"]
    )


def test_safe_hold_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["command_routes"][0]["production_writer_declared"] = True
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_ready"] is False


def test_malformed_hold_policy_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["hold_policy"] = "selected"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_ready"] is False
    assert report["selected_profile_count"] == 0
