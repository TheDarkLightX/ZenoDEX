from __future__ import annotations

import json
from pathlib import Path

from tools.check_production_readiness_g1_bdd import (
    DEFAULT_OUTPUT,
    build_document,
    check_artifact,
)


def test_bdd_contract_covers_all_33_commands() -> None:
    document = build_document()
    workflows = document["workflows"]
    report = check_artifact(DEFAULT_OUTPUT)

    assert len(workflows) == 33
    assert report["scenario_count"] == 267
    assert {workflow["command_id"] for workflow in workflows} == set(
        document["registry_binding"]["command_ids"]
    )
    assert all(
        workflow["production_mount"] == "UNMOUNTED_RESEARCH_ONLY"
        for workflow in workflows
    )
    assert all(
        scenario["evidence_status"] == "UNIMPLEMENTED_RESEARCH_SCENARIO"
        for workflow in workflows
        for scenario in workflow["scenarios"]
    )
    assert document["g1_exit_gate"]["complete"] is False


def test_family_specific_obligations_are_retained() -> None:
    document = build_document()
    workflows = {
        workflow["command_id"]: workflow for workflow in document["workflows"]
    }

    assert "accounting" in workflows["spot_swap"]["required_scenario_classes"]
    assert "freshness" in workflows["oracle_submit"]["required_scenario_classes"]
    assert "commit" in workflows["seller_auction_commit"]["required_scenario_classes"]
    assert "reveal" in workflows["private_swap_reveal"]["required_scenario_classes"]
    assert "outage" in workflows["tau_rejoin"]["required_scenario_classes"]
    assert "rejoin" in workflows["tau_rejoin"]["required_scenario_classes"]


def test_explicit_cancel_commands_have_cancellation_scenarios() -> None:
    document = build_document()
    workflows = {
        workflow["command_id"]: workflow for workflow in document["workflows"]
    }

    for command_id in (
        "seller_auction_cancel",
        "seller_auction_expire",
        "private_swap_cancel",
        "private_swap_expire",
    ):
        workflow = workflows[command_id]
        assert "cancellation" in workflow["required_scenario_classes"]
        assert any(
            scenario["class"] == "cancellation"
            for scenario in workflow["scenarios"]
        )


def test_missing_workflow_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["workflows"].pop()
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert "exact-subject generated BDD contract" in report["errors"][0]


def test_research_scenario_cannot_be_relabelled_as_evidence(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["workflows"][0]["scenarios"][0]["evidence_status"] = "PASS"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
