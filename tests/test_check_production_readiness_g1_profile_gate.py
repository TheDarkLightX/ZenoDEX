from __future__ import annotations

import json
from pathlib import Path

from tools.check_production_readiness_g1_profile_gate import (
    DEFAULT_OUTPUT,
    build_document,
    check_artifact,
)


def test_profile_gate_is_exact_and_non_authoritative() -> None:
    report = check_artifact(DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert report["decision_gate_count"] == 9
    assert report["closed_decision_count"] == 0
    assert report["selected_profile_count"] == 0
    assert report["production_authority_count"] == 0


def test_every_decision_requires_explicit_closure() -> None:
    document = build_document()

    assert len(document["decision_gates"]) == 9
    assert all(decision["status"] == "OPEN" for decision in document["decision_gates"])
    assert all(
        decision["selected_option_shape"] is None
        and decision["selected_profile"] is None
        and decision["production_authority"] == "NONE"
        for decision in document["decision_gates"]
    )
    assert document["selection_policy"]["exactly_one_option_shape_per_decision"] is True


def test_option_selection_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["decision_gates"][0]["selected_option_shape"] = "EXPLICIT_NAMED_PROFILE"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["g1_complete"] is False
    assert report["selected_profile_count"] == 1


def test_malformed_decision_gates_fail_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["decision_gates"] = "open"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["decision_gate_count"] == 0
    assert report["production_ready"] is False
