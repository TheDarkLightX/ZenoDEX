from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, Callable

import pytest

from tools.check_whole_program_plan_v2 import (
    REPO_ROOT,
    _manifest_scope_counts,
    check_whole_program_plan_v2,
)

PLAN_PATH = REPO_ROOT / "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"


def _load_plan() -> dict[str, Any]:
    value = json.loads(PLAN_PATH.read_text(encoding="utf-8"))
    assert type(value) is dict
    return value


def _write_mutant(tmp_path: Path, plan: dict[str, Any]) -> Path:
    path = tmp_path / "mutant-plan.json"
    path.write_text(json.dumps(plan), encoding="utf-8")
    return path


def _obligation(plan: dict[str, Any], obligation_id: str) -> dict[str, Any]:
    matches = [
        row for row in plan["next_obligations"] if row["obligation_id"] == obligation_id
    ]
    assert len(matches) == 1
    return matches[0]


def test_whole_program_plan_v2_binds_scope_without_granting_authority() -> None:
    report = check_whole_program_plan_v2()

    assert report == {
        "schema": "zenodex/whole-program-plan-check/v2.1",
        "ok": True,
        "plan_status": "RESEARCH_ONLY_CANDIDATE_PENDING_ADMISSION",
        "production_authority": "NONE",
        "release_ready": False,
        "subject_tree_verified": True,
        "lane_count": 12,
        "capability_count": 103,
        "required_route_count": 4,
        "explicit_exclusion_count": 4,
        "minimum_release_evidence_cell_count": 967,
        "value_movement_gate_count": 12,
        "closed_value_movement_gate_count": 0,
        "findings": [],
    }


def test_malformed_exclusion_row_cannot_collapse_the_derived_denominator() -> None:
    manifest = json.loads(
        (REPO_ROOT / "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json").read_text(
            encoding="utf-8"
        )
    )
    manifest["explicit_exclusions"] = [7]
    findings: list[str] = []

    counts = _manifest_scope_counts(manifest, findings)

    assert counts == (12, 103, 4, 0, 963)
    assert "explicit exclusions must be nonempty and unique" in findings


@pytest.mark.parametrize(
    ("mutator", "expected_finding"),
    [
        (
            lambda plan: plan["authority"].update({"production_authority": "ACTIVE"}),
            "authority ceiling drift",
        ),
        (
            lambda plan: plan.update({"status": "RESEARCH_ONLY_ACTIVE_IMPLEMENTATION_PLAN"}),
            "plan must remain a candidate until external admission",
        ),
        (
            lambda plan: plan["admission_model"].update(
                {"llm_review": "AUTHORITATIVE_EVIDENCE"}
            ),
            "research-plan admission model drift",
        ),
        (
            lambda plan: plan["advisory_reviews"][0].update(
                {"authority": "EVIDENCE"}
            ),
            "advisory planning-review binding drift",
        ),
        (
            lambda plan: plan["normative_inputs"][0].update(
                {"role": "Closed and complete whole-program scope."}
            ),
            "normative input role or scope semantics drift",
        ),
        (
            lambda plan: plan["requirements_floor"].update({"manifest_complete": True}),
            "provisional requirements-floor semantics drift",
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
            lambda plan: plan["value_movement_gates"][0].update(
                {"title": "Complete writer and sink mediation"}
            ),
            "value-movement gate titles drift from the normative safety claim",
        ),
        (
            lambda plan: plan["unresolved_semantic_decisions"].pop(),
            "unresolved semantic-decision set or order drift",
        ),
        (
            lambda plan: plan["baseline_verdict"].update(
                {"closed_value_movement_gates": 1}
            ),
            "baseline verdict must not claim a closed value-movement gate",
        ),
        (
            lambda plan: _obligation(plan, "O-007A").update({"closes": ["VM-01"]}),
            "individual obligation claims aggregate VM closure: O-007A",
        ),
        (
            lambda plan: _obligation(plan, "O-003A").update(
                {"depends_on": ["O-010B"]}
            ),
            "invalid or forward obligation dependency: O-003A",
        ),
        (
            lambda plan: _obligation(plan, "O-004").update(
                {"closes": ["invented_gap"]}
            ),
            "unregistered gap target: O-004",
        ),
        (
            lambda plan: plan["gap_registry"][0].update(
                {"owner_obligation": "O-002"}
            ),
            "gap target owner mismatch: O-001",
        ),
        (
            lambda plan: plan["vm_gate_promotion"].update(
                {"individual_obligation_maximum": "CLOSES"}
            ),
            "aggregate VM-gate promotion rule drift",
        ),
        (
            lambda plan: plan["completeness_estimation_policy"].update(
                {"production_rule": "A high estimate closes VM-01."}
            ),
            "semantic completeness estimation policy drift",
        ),
        (
            lambda plan: plan["release_gate"]["required_capability_statuses"].remove(
                "PROVED"
            ),
            "whole-program release gate contract drift",
        ),
        (
            lambda plan: plan["upstream_dependencies"][0].update(
                {"observed_tree": "0" * 40}
            ),
            "current Tau dependency tree drift",
        ),
        (
            lambda plan: plan["upstream_dependencies"][0]["source_sha256"].update(
                {"server.py": "0" * 64}
            ),
            "current Tau source-hash set drift",
        ),
        (
            lambda plan: plan["upstream_dependencies"][1].update(
                {"observed_tree": "0" * 40}
            ),
            "current Tau Language dependency tree drift",
        ),
        (
            lambda plan: plan["upstream_dependencies"][0].update(
                {"integration_rule": "Tau authenticates ZenoDEX commands."}
            ),
            "current Tau authority-boundary wording drift",
        ),
        (
            lambda plan: plan["semantic_anchors"].update(
                {"tau_role": "Tau establishes final ZenoDEX ordering."}
            ),
            "current Tau semantic role drift",
        ),
        (
            lambda plan: plan["current_tau_integration_contract"].update(
                {"ingress": "A Tau signature becomes an EconomicCommandOccurrenceV1."}
            ),
            "current Tau ingress authentication boundary drift",
        ),
        (
            lambda plan: plan["current_tau_integration_contract"][
                "required_adapter_properties"
            ].remove(
                "classify pre-finality observations removed by reorganization as "
                "ORPHANED with no irreversible settlement"
            ),
            "current Tau reorganization semantics drift",
        ),
        (
            lambda plan: plan["subject"].update(
                {"implementation_base_tree": "0" * 40}
            ),
            "implementation base commit and tree do not match Git objects",
        ),
        (
            lambda plan: plan["requirements_floor"]["confirmed_findings"].pop(),
            "provisional requirements-floor semantics drift",
        ),
        (
            lambda plan: plan["historical_inputs"].pop(),
            "whole-program donor reconciliation set drift",
        ),
        (
            lambda plan: _obligation(plan, "O-010B").update(
                {"blocked_on_policy": ["UP-01"]}
            ),
            "buy-and-burn obligation policy blockers drift",
        ),
        (
            lambda plan: plan["baseline_verdict"].update(
                {"strict_release_closure": "0_PERCENT"}
            ),
            "manifest-derived release denominator or baseline telemetry drift",
        ),
        (
            lambda plan: plan["baseline_verdict"].update(
                {
                    "architecture_inventory": (
                        "12_LANES_103_CAPABILITIES_4_REQUIRED_ROUTES_3_EXCLUSIONS"
                    ),
                    "strict_release_closure": (
                        "0_OF_966_MANIFEST_DERIVED_MINIMUM_EVIDENCE_CELLS"
                    ),
                    "minimum_release_evidence_cell_count": 966,
                    "minimum_release_evidence_cell_formula": (
                        "103 capabilities * 9 required statuses + 4 routes * 9 "
                        "required statuses + 3 exclusion certificates"
                    ),
                    "explicit_exclusion_count": 3,
                    "unclosed_release_evidence_cell_count": 966,
                }
            ),
            "manifest-derived release denominator or baseline telemetry drift",
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
        '{"schema":"zenodex/whole-program-plan/v2.1","schema":"forged"}',
        encoding="utf-8",
    )

    report = check_whole_program_plan_v2(plan_path=mutant_path)

    assert report["ok"] is False
    assert report["findings"] == [
        "plan inputs cannot be loaded: ValueError: duplicate JSON key: schema"
    ]
