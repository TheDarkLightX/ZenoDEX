#!/usr/bin/env python3
"""Validate a pinned research DAG; advisory completion never grants authority.

JSON stdout and exit 0 mean only scope, source and coordination checks passed.
Malformed inputs or drift return exit 1. No files, registry or task state change.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any, cast

try:
    from tools.build_m6_normative_requirements_v1 import (
        ShellRejectV1,
        _read_bounded_regular_file_v1,
        _run_git_v1,
    )
    from tools.m6_normative_requirements_v1 import (
        RequirementsRejectV1,
        canonical_json_bytes_v1,
        decode_json_object_v1,
    )
    from tools.o008_formal_cycle_admission_v1 import AdmissionRejectV1
    from tools.o008_formal_cycle_shell_v1 import GitReadPortV1, read_blob_v1
except ModuleNotFoundError:
    from build_m6_normative_requirements_v1 import (  # type: ignore[no-redef]
        ShellRejectV1,
        _read_bounded_regular_file_v1,
        _run_git_v1,
    )
    from m6_normative_requirements_v1 import (  # type: ignore[no-redef]
        RequirementsRejectV1,
        canonical_json_bytes_v1,
        decode_json_object_v1,
    )
    from o008_formal_cycle_shell_v1 import GitReadPortV1, read_blob_v1  # type: ignore[no-redef]

    from tools.o008_formal_cycle_admission_v1 import AdmissionRejectV1

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PLAN = Path("docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V3.json")
MAX_PLAN_BYTES = 131_072
BASE_COMMIT = "c6a9fd028ded9224427a645c1217d0ce576f78af"
BASE_SUBJECT = {
    "commit": BASE_COMMIT, "parent": "beb43baaef629276f3dae07e8e62ebc42cc3217a",
    "tree": "4610bff736c26e436c43adb66de05f0a24ae20c7",
}
MANIFEST = "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json"
MANIFEST_SHA256 = "34930be9d4d69c4c46c7c97f57fd492d4c95061f8960f936261a8a3415d5db95"
SOURCE_PATHS = {MANIFEST, *(
    "docs/research/" + name + ".json" for name in (
        "ZENODEX_M6_NORMATIVE_REQUIREMENTS_V1", "M6_O005_SEMANTIC_RESOLUTIONS_V1",
        "ZENODEX_WHOLE_PROGRAM_PLAN_V2", "ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1",
        "ZENODEX_O008_FORMAL_CYCLE_V1",
    )
)}
RECOVERED = {
    "zenodex-formal-core-plan-analysis-20260903.md":
        "f01730253a7d6570c43a629ce72cc025d6bb17fd0881a90e35e980eeae46616f",
    "zenodex-formal-core-plan-a-plus-20260903.md":
        "fd8c0fcabd2be7f4555c47a350162f3ab4c5b9794dac5c2a2f67b55128c74f65",
}
TASK_IDS = tuple(f"W{i:02d}" for i in range(14))
MIN_CLOSURE = (
    (), ("W00",), ("W01",), ("W00",), ("W02",), ("W04",),
    ("W02", "W03", "W04", "W05"), ("W02",), ("W06", "W07"),
    ("W02", "W06", "W07", "W08"), ("W03", "W08", "W09"),
    TASK_IDS[6:11], TASK_IDS[1:12], ("W12",),
)
MIN_START = (
    (), (), ("W00",), ("W00",), ("W00",), ("W00",), MIN_CLOSURE[6],
    ("W02",), ("W02",), ("W02",), MIN_CLOSURE[10], MIN_CLOSURE[11],
    MIN_CLOSURE[12], ("W06", "W07"),
)
ROUTES = {
    "fee_funded_zdex_purchase_and_burn": ["SPOT_LIQUIDITY", "ZDEX_TOKENOMICS"],
    "zusd_liquidation_settlement": ["ZUSD_MONETARY", "ORACLE_MARKET"],
    "perps_epoch_settlement": ["PERPS_MARKET", "ORACLE_MARKET"],
    "strategy_triggered_spot_swap": ["STRATEGY_ESCROW", "SPOT_LIQUIDITY"],
}
PLAN_FIELDS = "schema status authority integration_subject normative_and_historical_inputs requirements_floor initial_zrpf_limits milestones tasks outcome_classes policy_resolution historical_findings claim_ceiling nonclaims recovered_design_inputs coordination_rule"
TASK_FIELDS = "id title closure_dependencies start_after status source_commit owned_paths invariant acceptance_evidence reviewer remaining_nonclaims"
CEILING = {"formal_core_complete": False, "whole_value_movement_safe": False,
           "production_promotion": False, "whole_product_complete": False,
           "closed_value_movement_gate_count": 0}


class PlanReject(ValueError):
    def __init__(self, code: str, detail: str) -> None:
        super().__init__(detail)
        self.code, self.detail = code, detail


def _require(condition: bool, code: str, detail: str) -> None:
    if not condition:
        raise PlanReject(code, detail)


def _object(value: object, fields: str, code: str) -> dict[str, Any]:
    _require(type(value) is dict and set(value) == set(fields.split()), code, "closed field set required")
    return cast(dict[str, Any], value)


def _text(value: object, code: str) -> None:
    _require(type(value) is str and 0 < len(value) <= 4096, code, "bounded nonempty text required")


def _strings(value: object, code: str, *, empty: bool = False) -> list[str]:
    _require(type(value) is list, code, "exact list required")
    items = cast(list[object], value)
    for item in items:
        _text(item, code)
    strings = cast(list[str], items)
    _require((empty or bool(strings)) and len(strings) == len(set(strings)), code, "unique strings required")
    return strings


def _equal(value: object, expected: object, code: str) -> None:
    _require(canonical_json_bytes_v1(value) == canonical_json_bytes_v1(expected), code, "contract drift")


def _rows(value: object, fields: str, key: str, identities: set[str], code: str) -> list[dict[str, Any]]:
    _require(type(value) is list and len(value) == len(identities), code, "row count drift")
    rows = [_object(row, fields, code) for row in cast(list[object], value)]
    _equal(sorted(_strings([row[key] for row in rows], code)), sorted(identities), code)
    return rows


def _acyclic(tasks: list[dict[str, Any]], fields: tuple[str, ...]) -> None:
    remaining = {t["id"]: set().union(*(t[f] for f in fields)) for t in tasks}
    while remaining:
        ready = {key for key, deps in remaining.items() if not deps}
        _require(bool(ready), "DEPENDENCY_CYCLE", "dependency graph contains a cycle")
        remaining = {key: deps - ready for key, deps in remaining.items() if key not in ready}


def _tasks(plan: dict[str, Any]) -> list[dict[str, Any]]:
    raw = plan["tasks"]
    _require(type(raw) is list and len(raw) == 14, "TASK_IDS", "fourteen tasks required")
    tasks = [_object(t, TASK_FIELDS + (" route_start_requirements" if type(t) is dict and t.get("id") == "W08" else ""), "TASK_FIELDS") for t in raw]
    _equal(_strings([t["id"] for t in tasks], "TASK_IDS"), list(TASK_IDS), "TASK_IDS")
    for i, task in enumerate(tasks):
        for field in ("title", "invariant", "reviewer"):
            _text(task[field], "TASK_TEXT")
        for field in ("owned_paths", "acceptance_evidence", "remaining_nonclaims"):
            _strings(task[field], "TASK_TEXT")
        for path in task["owned_paths"]:
            _require(not Path(path).is_absolute() and ".." not in Path(path).parts and "\\" not in path, "TASK_PATH", "repository-relative path required")
        _require(task["status"] in ("OPEN", "IN_PROGRESS", "BLOCKED", "IMPLEMENTED", "COMPLETE"), "TASK_STATUS", "unknown advisory status")
        _equal(task["source_commit"], BASE_COMMIT, "TASK_SOURCE")
        for field, minimum in (("closure_dependencies", MIN_CLOSURE[i]), ("start_after", MIN_START[i])):
            deps = _strings(task[field], "DEPENDENCY_TYPE", empty=True)
            _require(set(deps) <= set(TASK_IDS), "UNKNOWN_DEPENDENCY", task["id"])
            _require(set(minimum) <= set(deps), "REQUIRED_DEPENDENCY", task["id"] + "." + field)
    for fields in (("closure_dependencies",), ("start_after",), ("closure_dependencies", "start_after")):
        _acyclic(tasks, fields)
    routes = _rows(tasks[8]["route_start_requirements"], "route_id required_lane_lifecycle_contracts required_publication_contract qualification_rule", "route_id", set(ROUTES), "ROUTE_CONTRACT")
    for row in routes:
        _equal(row["required_lane_lifecycle_contracts"], ROUTES[row["route_id"]], "ROUTE_CONTRACT")
        _equal(row["required_publication_contract"], "W06", "ROUTE_CONTRACT")
        _text(row["qualification_rule"], "ROUTE_CONTRACT")
    return tasks


def validate_plan_v3(plan: object, pinned_manifest: dict[str, object]) -> list[dict[str, Any]]:
    """Validate inert plan values against an independently source-pinned manifest."""
    p = _object(plan, PLAN_FIELDS, "PLAN_FIELDS")
    _source_rows(p)
    _equal(p["schema"], "zenodex/whole-program-plan/v3", "SCHEMA")
    _equal(p["status"], "RESEARCH_ONLY_CANDIDATE_PENDING_ADMISSION", "PLAN_STATUS")
    _equal(p["authority"], {k: "NONE" for k in ("production_authority", "settlement_authority", "release_authority", "value_movement_authority")}, "AUTHORITY")
    _equal(p["claim_ceiling"], CEILING, "CLAIM_CEILING")
    floor = _object(p["requirements_floor"], "capability_count lane_count route_count exclusion_count lanes required_cross_lane_routes explicit_exclusions expansion_rule", "REQUIREMENTS_FLOOR")
    _equal([floor[k] for k in ("capability_count", "lane_count", "route_count", "exclusion_count")], [103, 12, 4, 4], "REQUIREMENTS_FLOOR")
    for key in ("lanes", "required_cross_lane_routes", "explicit_exclusions"):
        _equal(floor[key], pinned_manifest[key], "REQUIREMENTS_FLOOR")
    _text(floor["expansion_rule"], "REQUIREMENTS_FLOOR")
    _equal(p["initial_zrpf_limits"], {"route_receipts_min": 1, "route_receipts_max": 8, "epoch_commands_min": 1, "epoch_commands_max": 64}, "ZRPF_LIMITS")
    _equal(p["milestones"], ["ISOLATED_SLICE_QUALIFIED", "FORMAL_CORE_COMPLETE", "PRODUCTION_VALUE_SAFETY_QUALIFIED", "WHOLE_PRODUCT_COMPLETE"], "MILESTONES")
    _equal(p["outcome_classes"], ["PRECOMMIT_REJECTION", "COMMITTED_SUCCESS", "EXACT_COMMITTED_RETRY", "INDETERMINATE_CLIENT_KNOWLEDGE"], "OUTCOMES")
    for key in ("policy_resolution", "coordination_rule"):
        _text(p[key], "PLAN_TEXT")
    _strings(p["nonclaims"], "PLAN_TEXT")
    history = _object(p["historical_findings"], "projection_D_plus september_G1_G14 SEC_candidate prior_opus_requests prior_codex_reviews prior_research_kernel_strategy", "HISTORICAL_FIELDS")
    for key, value in history.items():
        if key != "SEC_candidate":
            _text(value, "HISTORICAL_FIELDS")
    _equal(history["SEC_candidate"], {"commit": "b802c942a8c7ccf8bf17b1b61021cbd8c960b7ea", "status": "SEPARATE_CANDIDATE_REQUIRES_INTEGRATION_REVIEW"}, "SEC_CANDIDATE")
    rows = _rows(p["recovered_design_inputs"], "name sha256 classification disposition_path", "name", set(RECOVERED), "RECOVERED_INPUTS")
    for row in rows:
        _equal(row, {"name": row["name"], "sha256": RECOVERED[row["name"]], "classification": "HISTORICAL_USER_INTENT_AND_ADVISORY_ANALYSIS", "disposition_path": "docs/research/ZENODEX_WHOLE_PROGRAM_V3_AUTHORITY_DISCOVERY.md"}, "RECOVERED_INPUTS")
    return _tasks(p)


def _source_rows(plan: dict[str, object]) -> list[dict[str, Any]]:
    _equal(plan["integration_subject"], BASE_SUBJECT, "SUBJECT_BINDING")
    rows = _rows(plan["normative_and_historical_inputs"], "path commit sha256", "path", SOURCE_PATHS, "SOURCE_INPUTS")
    for row in rows:
        _equal(row["commit"], BASE_COMMIT, "SOURCE_PIN")
        _require(type(row["sha256"]) is str and re.fullmatch(r"[0-9a-f]{64}", row["sha256"]) is not None, "SOURCE_PIN", "hash shape")
    return rows


def _source_manifest(root: Path, plan: dict[str, object]) -> dict[str, object]:
    rows = _source_rows(plan)
    _run_git_v1(root, ("merge-base", "--is-ancestor", BASE_COMMIT, "HEAD"))
    for suffix, key in (("^", "parent"), ("^{tree}", "tree")):
        _equal(_run_git_v1(root, ("rev-parse", BASE_COMMIT + suffix))[1].strip(), BASE_SUBJECT[key], "SUBJECT_BINDING")
    manifest = b""
    for row in rows:
        oid = _run_git_v1(root, ("rev-parse", BASE_COMMIT + ":" + row["path"]))[1].strip()
        raw = read_blob_v1(GitReadPortV1(root), oid, row["path"])
        _equal(hashlib.sha256(raw).hexdigest(), row["sha256"], "SOURCE_PIN")
        if row["path"] == MANIFEST:
            _equal(row["sha256"], MANIFEST_SHA256, "SOURCE_PIN")
            manifest = raw
    return decode_json_object_v1(manifest, "pinned capability manifest")


def check_whole_program_plan_v3(*, root: Path = REPO_ROOT, plan_path: Path = DEFAULT_PLAN,
                                completed: tuple[object, ...] = ()) -> dict[str, Any]:
    """Read once, verify immutable sources, and report advisory readiness only."""
    report: dict[str, Any] = {"schema": "zenodex/whole-program-plan-check/v3", "ok": False,
        "findings": [], "eligible_next_starts": [], "conditional_route_starts": [],
        "advisory_completed": [], "production_authority": "NONE", "release_ready": False,
        "closed_value_movement_gate_count": 0, "claim_ceiling": dict(CEILING)}
    try:
        path = plan_path if plan_path.is_absolute() else root / plan_path
        raw = _read_bounded_regular_file_v1(path, MAX_PLAN_BYTES, "V3 plan")
        plan = decode_json_object_v1(raw, "V3 plan")
        _object(plan, PLAN_FIELDS, "PLAN_FIELDS")
        manifest = _source_manifest(root, plan)
        tasks = validate_plan_v3(plan, manifest)
        done = set(_strings(list(completed), "ADVISORY_TASKS", empty=True))
        _require(done <= set(TASK_IDS), "ADVISORY_TASKS", "unknown advisory task")
        ready = [t for t in tasks if t["id"] not in done and set(t["start_after"]) <= done]
        report.update(ok=True, plan_sha256=hashlib.sha256(raw).hexdigest(), requirements_floor=[103, 12, 4, 4],
                      advisory_completed=sorted(done), eligible_next_starts=[t["id"] for t in ready if t["id"] != "W08"])
        if any(t["id"] == "W08" for t in ready):
            report["conditional_route_starts"] = [dict(row, status="CONTRACTS_NOT_VERIFIED") for row in tasks[8]["route_start_requirements"]]
    except (PlanReject, RequirementsRejectV1, ShellRejectV1, AdmissionRejectV1) as exc:
        report["findings"] = [{"code": exc.code, "detail": exc.detail}]
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, default=DEFAULT_PLAN)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--completed", action="append", default=[])
    parser.add_argument("--json", action="store_true", help="JSON is always emitted")
    args = parser.parse_args(argv)
    report = check_whole_program_plan_v3(root=args.root, plan_path=args.plan, completed=tuple(args.completed))
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
