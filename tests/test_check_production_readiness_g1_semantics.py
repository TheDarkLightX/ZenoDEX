from __future__ import annotations

import json
from pathlib import Path

from tools.check_production_readiness_g1_semantics import (
    DEFAULT_OUTPUT,
    EXPECTED_COMMANDS,
    EXPECTED_DISABLED,
    EXPECTED_EXCLUDED_COMMANDS,
    build_document,
    check_artifact,
)


def test_exact_subject_mapping_has_33_commands_and_8_disabled() -> None:
    report = check_artifact(DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert report["command_count"] == 33
    assert report["disabled_command_count"] == 8
    assert report["semantic_gap_count"] == 33
    assert report["executable_bdd_scenario_count"] == 0
    assert report["profile_decision_count"] == 9


def test_source_partition_is_exact() -> None:
    document = build_document()
    entries = document["command_registry"]

    assert {entry["id"] for entry in entries} == {command.value for command in EXPECTED_COMMANDS}
    assert {
        entry["id"]
        for entry in entries
        if entry["v1_profile"] == "M6_RESEARCH_DISABLED_COMMANDS_V1"
    } == {command.value for command in EXPECTED_DISABLED}


def test_emergency_shutdown_is_explicitly_excluded() -> None:
    document = build_document()
    exclusions = document["launch_profile_exclusions"]
    command_ids = {entry["id"] for entry in document["command_registry"]}

    assert exclusions["command_ids"] == list(EXPECTED_EXCLUDED_COMMANDS)
    assert exclusions["registry_absent"] is True
    assert command_ids.isdisjoint(EXPECTED_EXCLUDED_COMMANDS)
    assert exclusions["reentry_requires_new_profile_decision"] is True


def test_projection_and_delta_contracts_cover_declared_keys() -> None:
    document = build_document()
    projection = document["global_state_projection"]
    algebra = document["value_delta_algebra"]

    assert [field["name"] for field in projection["field_contracts"]] == projection["canonical_order"]
    assert [entry["class"] for entry in algebra["class_contracts"]] == algebra["delta_classes"]
    assert projection["closure_status"].startswith("GAP_")
    assert algebra["closure_status"].startswith("GAP_")


def test_frozen_dispatch_and_reject_guard_match_the_source_registry() -> None:
    observations = build_document()["source_observations"]

    assert observations["handler_binding_count"] == 33
    assert observations["handler_bindings_match_frozen_dispatch"] is True
    assert observations["disabled_guard_count"] == 8
    assert observations["disabled_guard_matches_source_registry"] is True


def test_each_command_exposes_semantic_and_bdd_gaps() -> None:
    entries = build_document()["command_registry"]
    required_for_all = {"happy", "rejection", "authorization", "recovery", "terminal"}

    assert len(entries) == 33
    for entry in entries:
        assert entry["semantic_status"] == "GAP_OPEN_PROFILE_DECISION"
        assert entry["user_story_status"] == "GAP_PRODUCT_STORY_NOT_FROZEN"
        assert entry["normative_spec_status"] == "GAP_PROFILE_NOT_SELECTED"
        assert entry["beneficial_owner"] is None
        assert entry["bdd_executable_scenarios"] == []
        assert required_for_all <= set(entry["bdd_required_scenario_classes"])

    sealed_bid_entries = [entry for entry in entries if entry["workflow_family"] == "sealed_bid"]
    assert len(sealed_bid_entries) == 10
    assert all("cancellation" in entry["bdd_required_scenario_classes"] for entry in sealed_bid_entries)


def test_missing_command_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["command_registry"].pop()
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert "exact-subject generated semantic mapping" in report["errors"][0]


def test_relabeling_disabled_oracle_command_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    for entry in artifact["command_registry"]:
        if entry["id"] == "oracle_submit":
            entry["production_enablement"] = "RESEARCH_ENABLED_PROFILE_REQUIRED"
            break
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False


def test_falsely_closing_an_unselected_normative_spec_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["command_registry"][0]["normative_spec_status"] = "SELECTED"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_ready"] is False


def test_profile_decisions_remain_explicitly_open() -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))

    decisions = artifact["profile_decisions"]
    assert len(decisions) == 9
    assert {decision["status"] for decision in decisions} == {"OPEN"}
    assert all(decision["selected_profile"] is None for decision in decisions)
    assert all(len(decision["required_outputs"]) >= 3 for decision in decisions)
    assert all(decision["question"] for decision in decisions)
    assert all(
        set(decision["allowed_option_shapes"])
        == {"EXPLICIT_NAMED_PROFILE", "VERSIONED_PROFILE_ALTERNATIVE", "EXCLUDE_UNTIL_CLOSED"}
        for decision in decisions
    )
    assert all(decision["affected_workflow_families"] for decision in decisions)
    assert artifact["g1_exit_gate"]["status"] == "BLOCKED_OPEN_PROFILE_DECISIONS"
    assert artifact["g1_exit_gate"]["closed_command_count"] == 0


def test_profile_selection_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["profile_decisions"][0]["selected_profile"] = "UNVERIFIED_PROFILE"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_ready"] is False


def test_profile_option_shape_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["profile_option_shapes"]["EXCLUDE_UNTIL_CLOSED"]["meaning"] = "enable now"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_ready"] is False


def test_profile_gate_completion_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["g1_exit_gate"]["complete"] = True
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_ready"] is False
