from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, Callable

import pytest

from tools.check_whole_program_plan_v2 import REPO_ROOT, check_whole_program_plan_v2

PLAN_PATH = REPO_ROOT / "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"


def _load_plan() -> dict[str, Any]:
    value = json.loads(PLAN_PATH.read_text(encoding="utf-8"))
    assert type(value) is dict
    return value


def _write_mutant(tmp_path: Path, plan: dict[str, Any]) -> Path:
    path = tmp_path / "mutant-plan.json"
    path.write_text(json.dumps(plan), encoding="utf-8")
    return path


def test_whole_program_plan_v2_binds_scope_without_granting_authority() -> None:
    report = check_whole_program_plan_v2()

    assert report == {
        "schema": "zenodex/whole-program-plan-check/v2",
        "ok": True,
        "production_authority": "NONE",
        "release_ready": False,
        "subject_tree_verified": True,
        "capability_count": 103,
        "value_movement_gate_count": 12,
        "closed_value_movement_gate_count": 0,
        "findings": [],
    }


@pytest.mark.parametrize(
    ("mutator", "expected_finding"),
    [
        (
            lambda plan: plan["authority"].update({"production_authority": "ACTIVE"}),
            "authority ceiling drift",
        ),
        (
            lambda plan: plan["selected_architecture"].update(
                {"settlement_abi": "GlobalSettlementABI V2"}
            ),
            "GlobalSettlementABI V1 selection drift",
        ),
        (
            lambda plan: plan["selected_architecture"]["closed_lane_registry"].pop(),
            "closed lane registry does not match the capability manifest",
        ),
        (
            lambda plan: plan["selected_architecture"][
                "initial_recursive_qualification"
            ].update({"commands_per_epoch_max": 1024}),
            "initial recursive qualification shape drift",
        ),
        (
            lambda plan: plan["value_movement_gates"].pop(),
            "value-movement gate set or order drift",
        ),
        (
            lambda plan: plan["unresolved_semantic_decisions"].pop(),
            "unresolved semantic-decision set or order drift",
        ),
        (
            lambda plan: plan["current_verdict"].update(
                {"closed_value_movement_gates": 1}
            ),
            "current plan must not claim a closed value-movement gate",
        ),
        (
            lambda plan: plan["subject"].update(
                {"implementation_base_tree": "0" * 40}
            ),
            "implementation base commit and tree do not match Git objects",
        ),
    ],
)
def test_whole_program_plan_v2_semantic_mutants_fail_closed(
    tmp_path: Path,
    mutator: Callable[[dict[str, Any]], object],
    expected_finding: str,
) -> None:
    plan = copy.deepcopy(_load_plan())
    mutator(plan)
    mutant_path = _write_mutant(tmp_path, plan)

    report = check_whole_program_plan_v2(plan_path=mutant_path)

    assert report["ok"] is False
    findings = report["findings"]
    assert type(findings) is list
    assert expected_finding in findings


def test_whole_program_plan_v2_normative_source_hash_mutant_fails_closed(
    tmp_path: Path,
) -> None:
    plan = _load_plan()
    plan["normative_inputs"][0]["sha256"] = "0" * 64
    mutant_path = _write_mutant(tmp_path, plan)

    report = check_whole_program_plan_v2(plan_path=mutant_path)

    assert report["ok"] is False
    findings = report["findings"]
    assert type(findings) is list
    assert (
        "normative input hash drift: "
        "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json"
    ) in findings


def test_whole_program_plan_v2_rejects_duplicate_json_keys(tmp_path: Path) -> None:
    mutant_path = tmp_path / "duplicate-key-plan.json"
    mutant_path.write_text(
        '{"schema":"zenodex/whole-program-plan/v2","schema":"forged"}',
        encoding="utf-8",
    )

    report = check_whole_program_plan_v2(plan_path=mutant_path)

    assert report["ok"] is False
    assert report["findings"] == [
        "plan inputs cannot be loaded: ValueError: duplicate JSON key: schema"
    ]
