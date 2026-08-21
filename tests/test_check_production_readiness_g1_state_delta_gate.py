from __future__ import annotations

import ast
import json
from pathlib import Path

import pytest

from tools.check_production_readiness_g1_state_delta_gate import (
    ABSTRACT_DELTA_CONTRACT_PROJECTION_SHA256,
    DEFAULT_OUTPUT,
    M6_DELTA_SOURCE_PATH,
    REPO_ROOT,
    RUNTIME_SOURCE_PATH,
    _canonical_method_keys,
    _encoded,
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
    assert report["delta_class_count"] == 11
    assert report["open_obligation_count"] == 6
    assert report["production_authority"] == "NONE"
    assert report["runtime_state_field_count"] == 16
    assert report["runtime_effect_kind_count"] == 9
    assert report["runtime_mapping_field_count"] == 14
    assert report["runtime_mapping_delta_class_count"] == 11
    assert report["unmapped_abstract_field_count"] == 2
    assert report["unmapped_runtime_effect_kind_count"] == 0
    assert report["m6_runtime_delta_class_count"] == 9
    assert report["m6_runtime_delta_surplus_count"] == 1
    assert report["m6_entry_field_count"] == 5
    assert report["m6_entry_missing_required_field_count"] == 29


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
    assert algebra["delta_class_count"] == algebra["class_contract_count"] == 11
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
    assert runtime["semantic_mapping_status"] == "GAP_ABSTRACT_14_FIELD_AND_11_DELTA_MAPPING_UNPROVED"
    assert runtime["production_authority"] == "NONE"

    mapping = build_document()["runtime_mapping_gap_ledger"]
    assert mapping["status"] == "GAP_STRUCTURAL_CANDIDATES_ONLY"
    assert mapping["abstract_field_count"] == 14
    assert mapping["abstract_delta_class_count"] == 11
    assert mapping["semantic_mapping_status"] == "GAP_ABSTRACT_14_FIELD_AND_11_DELTA_MAPPING_UNPROVED"
    assert set(mapping["unmapped_abstract_fields"]) == {"lp_state", "auctions"}
    assert mapping["runtime_effect_kinds_without_abstract_delta_candidate"] == []
    assert mapping["production_authority"] == "NONE"

    m6_surface = mapping["m6_value_delta_surface"]
    assert m6_surface["status"] == "M6_DELTA_SOURCE_SHAPE_RESEARCH_ONLY"
    assert m6_surface["source_subject"] == "e8059cb5e27e80c2f8ba627501d6097f3c5e6b0c"
    assert m6_surface["semantic_mapping_status"] == (
        "GAP_ENTRY_FIELDS_DO_NOT_CLOSE_ABSTRACT_DELTA_CONTRACTS"
    )
    assert m6_surface["production_authority"] == "NONE"
    assert m6_surface["abstract_contract_shape"]["projection_sha256"] == (
        ABSTRACT_DELTA_CONTRACT_PROJECTION_SHA256
    )
    assert m6_surface["abstract_contract_shape"]["projection_digest_status"] == (
        "EXACT_SUBJECT_HELPER_BASELINE_RESEARCH_ONLY"
    )
    assert m6_surface["delta_class_type"]["runtime_delta_class_count"] == 9
    assert m6_surface["delta_class_type"]["abstract_delta_classes_without_runtime_kind"] == [
        "reserve_transfer",
        "fee_allocation",
        "reward",
    ]
    assert m6_surface["delta_class_type"]["runtime_delta_classes_without_abstract_class"] == [
        "noop"
    ]
    assert m6_surface["delta_entry_type"]["declared_fields"] == [
        "delta_class",
        "owner",
        "asset",
        "custody",
        "delta_atoms",
    ]
    assert m6_surface["delta_entry_type"]["declared_fields_match_literal_projection"] is True
    assert "amount_atoms" in m6_surface["abstract_contract_shape"][
        "required_fields_missing_from_runtime_entry"
    ]


def test_closure_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["state_projection"]["obligation_status"] = "CLOSED"
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(_encoded(artifact))

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["g1_complete"] is False
    assert report["production_ready"] is False


def test_malformed_state_projection_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["state_projection"] = "unknown"
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(_encoded(artifact))

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["state_field_count"] == 0
    assert report["production_ready"] is False


def test_runtime_projection_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["runtime_projection"]["semantic_mapping_status"] = "CLOSED"
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(_encoded(artifact))

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["runtime_state_field_count"] == 16
    assert report["production_ready"] is False


def test_runtime_mapping_ledger_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["runtime_mapping_gap_ledger"]["semantic_mapping_status"] = "CLOSED"
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(_encoded(artifact))

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["runtime_mapping_field_count"] == 14
    assert report["production_ready"] is False


def test_m6_delta_surface_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["runtime_mapping_gap_ledger"]["m6_value_delta_surface"][
        "semantic_mapping_status"
    ] = "CLOSED"
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(_encoded(artifact))

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["m6_runtime_delta_class_count"] == 9
    assert report["m6_entry_missing_required_field_count"] == 29
    assert report["production_ready"] is False


def test_m6_abstract_contract_baseline_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["runtime_mapping_gap_ledger"]["m6_value_delta_surface"][
        "abstract_contract_shape"
    ]["projection_sha256"] = "0" * 64
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(_encoded(artifact))

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["m6_abstract_contract_projection_sha256"] == "0" * 64
    assert report["production_ready"] is False


def test_malformed_nested_m6_shape_returns_structured_failure(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["runtime_mapping_gap_ledger"]["m6_value_delta_surface"][
        "delta_class_type"
    ] = None
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(_encoded(artifact))

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["m6_runtime_delta_class_count"] == 0
    assert report["production_ready"] is False


def test_runtime_source_drift_fails_closed() -> None:
    runtime_path = REPO_ROOT / RUNTIME_SOURCE_PATH

    def read_bytes_with_drift(path: Path) -> bytes:
        value = path.read_bytes()
        if path == runtime_path:
            return value + b"\n# isolated drift\n"
        return value

    report = check_artifact(DEFAULT_OUTPUT, read_current=read_bytes_with_drift)

    assert report["ok"] is False
    assert any("runtime source drift" in error for error in report["errors"])
    assert report["production_ready"] is False


def test_m6_delta_source_drift_fails_closed() -> None:
    m6_path = REPO_ROOT / M6_DELTA_SOURCE_PATH

    def read_bytes_with_drift(path: Path) -> bytes:
        value = path.read_bytes()
        if path == m6_path:
            return value + b"\n# isolated M6 delta drift\n"
        return value

    report = check_artifact(DEFAULT_OUTPUT, read_current=read_bytes_with_drift)

    assert report["ok"] is False
    assert any(M6_DELTA_SOURCE_PATH in error for error in report["errors"])
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
        "        if self.dynamic:\n"
        "            return {'x': 1}\n"
        "        return {'x': 2}\n"
    ).body[0]
    effect = ast.parse("class Effect:\n    VALUE = 'VALUE'\n").body[0]

    assert isinstance(state, ast.ClassDef)
    assert isinstance(effect, ast.ClassDef)
    with pytest.raises(ValueError, match="one direct literal return"):
        _canonical_method_keys(state)
    with pytest.raises(ValueError, match="inherit Enum"):
        _enum_values(effect)
