from __future__ import annotations

import ast
import json
from pathlib import Path

import pytest

from tools.check_production_readiness_g1_state_delta_gate import (
    DEFAULT_OUTPUT,
    REPO_ROOT,
    RUNTIME_SOURCE_PATH,
    _canonical_method_keys,
    _enum_values,
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
    assert report["runtime_state_field_count"] == 16
    assert report["runtime_effect_kind_count"] == 9


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


def test_runtime_shape_inventory_is_source_bound_without_closing_g1() -> None:
    runtime = build_document()["runtime_projection"]

    assert runtime["status"] == "SOURCE_SHAPE_INVENTORY_RESEARCH_ONLY"
    assert runtime["source_subject"] == "e8059cb5e27e80c2f8ba627501d6097f3c5e6b0c"
    assert runtime["state_type"]["declared_field_count"] == 16
    assert runtime["state_type"]["literal_projection_starts_with_schema"] is True
    assert runtime["state_type"]["declared_fields_match_literal_projection"] is True
    assert runtime["canonical_codec"]["delegate"] == "canonical_json_bytes"
    assert runtime["canonical_codec"]["delegate_path"] == "src/state/canonical.py"
    assert runtime["effect_kind_type"]["kind_count"] == 9
    assert runtime["canonical_codec"]["status"] == "PRESENT_SOURCE_SHAPE_ONLY"
    assert runtime["semantic_mapping_status"] == "GAP_ABSTRACT_14_FIELD_AND_8_DELTA_MAPPING_UNPROVED"
    assert runtime["production_authority"] == "NONE"


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


def test_runtime_projection_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["runtime_projection"]["semantic_mapping_status"] = "CLOSED"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["runtime_state_field_count"] == 16
    assert report["production_ready"] is False


def test_runtime_source_drift_fails_closed(monkeypatch: pytest.MonkeyPatch) -> None:
    original_read_bytes = Path.read_bytes
    runtime_path = REPO_ROOT / RUNTIME_SOURCE_PATH

    def read_bytes_with_drift(path: Path) -> bytes:
        value = original_read_bytes(path)
        if path == runtime_path:
            return value + b"\n# isolated drift\n"
        return value

    monkeypatch.setattr(Path, "read_bytes", read_bytes_with_drift)

    report = check_artifact(DEFAULT_OUTPUT)

    assert report["ok"] is False
    assert any("runtime source drift" in error for error in report["errors"])
    assert report["production_ready"] is False


def test_noncanonical_artifact_bytes_fail_closed(tmp_path: Path) -> None:
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(DEFAULT_OUTPUT.read_bytes() + b"\n")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert "artifact is not canonically encoded JSON" in report["errors"]


def test_runtime_shape_parsers_reject_nonliteral_and_non_enum_shapes() -> None:
    state = ast.parse(
        "class State:\n"
        "    def to_canonical(self):\n"
        "        mapping = {'x': 1}\n"
        "        return mapping\n"
    ).body[0]
    effect = ast.parse("class Effect:\n    VALUE = 'VALUE'\n").body[0]

    assert isinstance(state, ast.ClassDef)
    assert isinstance(effect, ast.ClassDef)
    with pytest.raises(ValueError, match="return one literal mapping"):
        _canonical_method_keys(state)
    with pytest.raises(ValueError, match="inherit Enum"):
        _enum_values(effect)
