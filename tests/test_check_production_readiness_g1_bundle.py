from __future__ import annotations

import json
from pathlib import Path

from tools.check_production_readiness_g1_bundle import (
    DEFAULT_OUTPUT,
    REPO_ROOT,
    _check_decision_and_state_bindings,
    _encoded,
    _generated_documents,
    build_document,
    check_artifact,
)


def test_cross_artifact_bundle_is_exact_and_research_only() -> None:
    report = check_artifact(DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert report["artifact_count"] == 7
    assert report["consistency_check_count"] == 9
    assert report["command_count"] == 33
    assert report["profile_decision_count"] == 9
    assert report["open_state_obligation_count"] == 6
    assert report["runtime_mapping_unmapped_field_count"] == 2
    assert report["runtime_mapping_unmapped_effect_kind_count"] == 3
    assert report["m6_runtime_delta_surplus_count"] == 1
    assert report["m6_entry_missing_required_field_count"] == 17


def test_bundle_binds_the_registry_and_repair_overlay() -> None:
    document = build_document()

    assert document["source_subject"]["repair_relation"] == "ANCESTRY_ONLY_RESEARCH_OVERLAY"
    assert document["source_subject"]["semantic_equivalence"] == "NOT_PROVED"
    assert document["registry_binding"]["workflow_count"] == 33
    assert document["registry_binding"]["entrypoint_route_count"] == 33
    assert document["registry_binding"]["safe_hold_route_count"] == 33
    assert document["g1_exit_gate"]["production_authority"] == "NONE"
    assert document["g1_exit_gate"]["all_commands_unmounted"] is True
    m6_surface = document["obligation_binding"]["m6_value_delta_surface"]
    assert m6_surface["status"] == "M6_DELTA_SOURCE_SHAPE_RESEARCH_ONLY"
    assert m6_surface["semantic_mapping_status"] == (
        "GAP_ENTRY_FIELDS_DO_NOT_CLOSE_ABSTRACT_DELTA_CONTRACTS"
    )
    assert m6_surface["runtime_delta_classes_without_abstract_class"] == ["noop"]
    assert m6_surface["abstract_contract_projection_digest_status"] == (
        "EXACT_SUBJECT_HELPER_BASELINE_RESEARCH_ONLY"
    )
    assert len(m6_surface["abstract_contract_projection_sha256"]) == 64
    assert m6_surface["entry_declared_field_count"] == 5
    assert m6_surface["entry_missing_required_field_count"] == 17


def test_bundle_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["registry_binding"]["command_count"] = 32
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(_encoded(artifact))

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert "bundle artifact differs from the exact-subject cross-artifact G1 bundle" in report["errors"]


def test_bundle_cannot_promote_through_a_tampered_check_record(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["consistency_checks"][0]["status"] = "FAIL"
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(_encoded(artifact))

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_ready"] is False
    assert "bundle artifact differs from the exact-subject cross-artifact G1 bundle" in report["errors"]


def test_bundle_binds_the_m6_delta_surface_gap(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["obligation_binding"]["m6_value_delta_surface"]["status"] = "CLOSED"
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(_encoded(artifact))

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_ready"] is False
    assert "bundle artifact differs from the exact-subject cross-artifact G1 bundle" in report["errors"]


def test_m6_binding_predicate_rejects_source_and_shape_mutations() -> None:
    source_tampered = _generated_documents(REPO_ROOT)
    source_tampered["state_delta"]["runtime_mapping_gap_ledger"][
        "m6_value_delta_surface"
    ]["source_pins"][0]["sha256"] = "0" * 64
    errors = _check_decision_and_state_bindings(source_tampered)
    assert any("runtime state/delta mapping" in error for error in errors)

    shape_tampered = _generated_documents(REPO_ROOT)
    shape_tampered["state_delta"]["runtime_mapping_gap_ledger"][
        "m6_value_delta_surface"
    ]["delta_entry_type"]["declared_fields"] = ["asset"]
    errors = _check_decision_and_state_bindings(shape_tampered)
    assert any("runtime state/delta mapping" in error for error in errors)


def test_malformed_nested_m6_bundle_shape_returns_structured_failure(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["obligation_binding"]["m6_value_delta_surface"] = None
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(_encoded(artifact))

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["m6_runtime_delta_surplus_count"] == 0
    assert report["production_ready"] is False


def test_bundle_rejects_noncanonical_artifact_bytes(tmp_path: Path) -> None:
    candidate = tmp_path / "candidate.json"
    candidate.write_bytes(DEFAULT_OUTPUT.read_bytes() + b"\n")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert "bundle artifact is not canonically encoded JSON" in report["errors"]
