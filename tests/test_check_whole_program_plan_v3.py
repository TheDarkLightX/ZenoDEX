"""Scope/authority and dependency mutants for the research-only V3 checker.

Oracle: fixed user-supplied scope and dependency contracts plus immutable Git
blobs. These tests establish plan validation, never implementation completion.
"""

from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, Callable

import pytest

from tools import check_whole_program_plan_v3 as checker


def _plan() -> dict[str, Any]:
    return json.loads((checker.REPO_ROOT / checker.DEFAULT_PLAN).read_bytes())


def _check(tmp_path: Path, plan: dict[str, Any], **kwargs: Any) -> dict[str, Any]:
    path = tmp_path / "plan.json"
    path.write_text(json.dumps(plan), encoding="utf-8")
    return checker.check_whole_program_plan_v3(plan_path=path, **kwargs)


def test_real_pinned_plan_has_exact_floor_and_no_authority() -> None:
    report = checker.check_whole_program_plan_v3()
    assert report["ok"] is True, report
    assert report["eligible_next_starts"] == ["W00", "W01"]
    assert report["requirements_floor"] == [103, 12, 4, 4]
    assert report["production_authority"] == "NONE"
    assert report["release_ready"] is False
    assert report["closed_value_movement_gate_count"] == 0


@pytest.mark.parametrize(
    ("mutate", "code"),
    [
        (lambda p: p["authority"].update(production_authority="ACTIVE"), "AUTHORITY"),
        (lambda p: p["claim_ceiling"].update(formal_core_complete=True), "CLAIM_CEILING"),
        (lambda p: p["claim_ceiling"].update(closed_value_movement_gate_count=False), "CLAIM_CEILING"),
        (lambda p: p.update(unknown_field=False), "PLAN_FIELDS"),
        (lambda p: p["tasks"][3].update(unchecked_authority="ACTIVE"), "TASK_FIELDS"),
        (lambda p: p["tasks"][6]["closure_dependencies"].remove("W03"), "REQUIRED_DEPENDENCY"),
        (lambda p: p["tasks"][3]["start_after"].clear(), "REQUIRED_DEPENDENCY"),
        (lambda p: p["tasks"][0]["start_after"].append("W99"), "UNKNOWN_DEPENDENCY"),
        (lambda p: p["tasks"][0]["closure_dependencies"].append("W12"), "DEPENDENCY_CYCLE"),
        (lambda p: p["tasks"][1]["start_after"].append("W02"), "DEPENDENCY_CYCLE"),
        (lambda p: p["tasks"].pop(), "TASK_IDS"),
        (lambda p: p["tasks"][1].update(id="W00"), "TASK_IDS"),
        (lambda p: p["requirements_floor"]["lanes"][0]["capabilities"].pop(), "REQUIREMENTS_FLOOR"),
        (lambda p: p["requirements_floor"]["lanes"][0]["capabilities"].__setitem__(0, "invented_capability"), "REQUIREMENTS_FLOOR"),
        (lambda p: p["requirements_floor"]["explicit_exclusions"].pop(), "REQUIREMENTS_FLOOR"),
        (lambda p: p["requirements_floor"].update(capability_count=True), "REQUIREMENTS_FLOOR"),
        (lambda p: p["tasks"][8]["route_start_requirements"][0]["required_lane_lifecycle_contracts"].pop(), "ROUTE_CONTRACT"),
        (lambda p: p["normative_and_historical_inputs"][0].update(sha256="0" * 64), "SOURCE_PIN"),
        (lambda p: p["normative_and_historical_inputs"].pop(), "SOURCE_INPUTS"),
        (lambda p: p["integration_subject"].update(parent="0" * 40), "SUBJECT_BINDING"),
        (lambda p: p["initial_zrpf_limits"].update(epoch_commands_max=65), "ZRPF_LIMITS"),
        (lambda p: p["recovered_design_inputs"][0].update(sha256="0" * 64), "RECOVERED_INPUTS"),
    ],
)
def test_named_semantic_mutants_reject_before_advisory_readiness(
    tmp_path: Path, mutate: Callable[[dict[str, Any]], Any], code: str,
) -> None:
    plan = _plan()
    mutate(plan)
    report = _check(tmp_path, plan)
    assert report["ok"] is False
    assert report["findings"][0]["code"] == code, report
    assert report["eligible_next_starts"] == []
    assert report["production_authority"] == "NONE"
    assert report["closed_value_movement_gate_count"] == 0


def test_task_status_and_all_advisory_completions_cannot_promote(tmp_path: Path) -> None:
    plan = _plan()
    for task in plan["tasks"]:
        task["status"] = "COMPLETE"
    before = copy.deepcopy(plan)
    assert _check(tmp_path, plan)["eligible_next_starts"] == ["W00", "W01"]
    report = _check(tmp_path, plan, completed=tuple(f"W{i:02d}" for i in range(14)))
    assert report["ok"] is True, report
    assert report["eligible_next_starts"] == []
    assert report["release_ready"] is False
    assert report["production_authority"] == "NONE"
    assert report["closed_value_movement_gate_count"] == 0
    assert plan == before


@pytest.mark.parametrize("field", ["integration_subject", "normative_and_historical_inputs"])
def test_value_validator_also_rejects_source_schema_drift(field: str) -> None:
    plan = _plan()
    manifest = checker._source_manifest(checker.REPO_ROOT, plan)
    plan[field] = []
    with pytest.raises(checker.PlanReject):
        checker.validate_plan_v3(plan, manifest)


def test_route_start_remains_conditional_after_semantics_are_advisory_complete() -> None:
    report = checker.check_whole_program_plan_v3(completed=("W00", "W01", "W02"))
    assert report["ok"] is True, report
    assert "W08" not in report["eligible_next_starts"]
    routes = report["conditional_route_starts"]
    assert len(routes) == 4
    assert all(r["status"] == "CONTRACTS_NOT_VERIFIED" for r in routes)
    assert all(r["required_publication_contract"] == "W06" for r in routes)


@pytest.mark.parametrize("completed", [("W99",), ("W00", "W00"), (True,)])
def test_unknown_duplicate_and_non_string_advisory_inputs_reject(
    completed: tuple[object, ...],
) -> None:
    report = checker.check_whole_program_plan_v3(completed=completed)
    assert report["ok"] is False
    assert report["eligible_next_starts"] == []


@pytest.mark.parametrize("raw", [b"{", b"[]", b'{"schema":1,"schema":2}', b'{"x":NaN}', b'{"x":1.5}', b'\xff', b'{"x":' + b'[' * 1000 + b'0' + b']' * 1000 + b'}'])
def test_malformed_duplicate_nonfinite_and_deep_inputs_fail_closed(
    tmp_path: Path, raw: bytes,
) -> None:
    path = tmp_path / "malformed.json"
    path.write_bytes(raw)
    report = checker.check_whole_program_plan_v3(plan_path=path)
    assert report["ok"] is False
    assert report["production_authority"] == "NONE"


def test_missing_oversized_and_symlink_inputs_fail_closed(tmp_path: Path) -> None:
    path = tmp_path / "input.json"
    assert checker.check_whole_program_plan_v3(plan_path=path)["ok"] is False
    path.write_bytes(b" " * (checker.MAX_PLAN_BYTES + 1))
    assert checker.check_whole_program_plan_v3(plan_path=path)["ok"] is False
    path.unlink()
    path.symlink_to(checker.REPO_ROOT / checker.DEFAULT_PLAN)
    assert checker.check_whole_program_plan_v3(plan_path=path)["ok"] is False


def test_foreign_repository_cannot_claim_subject_ancestry(tmp_path: Path) -> None:
    report = checker.check_whole_program_plan_v3(
        root=tmp_path, plan_path=checker.REPO_ROOT / checker.DEFAULT_PLAN,
    )
    assert report["ok"] is False
    assert report["eligible_next_starts"] == []


def test_cli_failure_is_nonzero_and_advisory_success_never_promotes(
    tmp_path: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    assert checker.main(["--plan", str(tmp_path / "missing")]) == 1
    assert json.loads(capsys.readouterr().out)["ok"] is False
    assert checker.main(["--completed", "W00", "--json"]) == 0
    result = json.loads(capsys.readouterr().out)
    assert result["advisory_completed"] == ["W00"]
    assert result["production_authority"] == "NONE"
    assert result["release_ready"] is False
