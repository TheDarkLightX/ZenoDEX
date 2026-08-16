from __future__ import annotations

import json
from pathlib import Path

from tools.check_production_readiness_g1_state_delta_gate import (
    DEFAULT_OUTPUT,
    build_document,
    check_artifact,
)


def test_state_delta_gate_is_exact_and_non_authoritative() -> None:
    report = check_artifact(DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert report["state_field_count"] == 14
    assert report["delta_class_count"] == 8
    assert report["open_obligation_count"] == 6
    assert report["production_authority"] == "NONE"


def test_declared_fields_and_delta_classes_keep_open_gap_status() -> None:
    document = build_document()
    state = document["state_projection"]
    algebra = document["value_delta_algebra"]

    assert state["closure_status"] == "GAP_FIELD_TYPES_ROOT_CODEC_AND_RECONCILIATION_UNSPECIFIED"
    assert state["obligation_status"] == "OPEN_GAP"
    assert state["field_count"] == state["field_contract_count"] == 14
    assert state["all_fields_have_terminal_paths"] is True
    assert algebra["closure_status"] == "GAP_EVENT_EQUATIONS_OWNERS_AND_RECONCILIATION_UNSPECIFIED"
    assert algebra["obligation_status"] == "OPEN_GAP"
    assert algebra["delta_class_count"] == algebra["class_contract_count"] == 8
    assert algebra["all_delta_classes_have_contracts"] is True


def test_closure_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["state_projection"]["obligation_status"] = "CLOSED"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["g1_complete"] is False
    assert report["production_ready"] is False


def test_malformed_state_projection_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["state_projection"] = "unknown"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["state_field_count"] == 0
    assert report["production_ready"] is False
