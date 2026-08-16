from __future__ import annotations

import json
from pathlib import Path

from tools.check_production_readiness_g1_semantics import (
    DEFAULT_OUTPUT,
    EXPECTED_COMMANDS,
    EXPECTED_DISABLED,
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


def test_profile_decisions_remain_explicitly_open() -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))

    decisions = artifact["profile_decisions"]
    assert len(decisions) == 9
    assert {decision["status"] for decision in decisions} == {"OPEN"}
    assert artifact["g1_exit_gate"]["status"] == "BLOCKED_OPEN_PROFILE_DECISIONS"
