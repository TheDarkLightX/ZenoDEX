#!/usr/bin/env python3
"""Replay bounded evidence-DAG hitting-set contradiction checks."""

from __future__ import annotations

import argparse
import copy
import itertools
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_evidence_dag_hitting_set_contradictions_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_EVIDENCE_DAG_HITTING_SET_CONTRADICTIONS_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "evidence_dag_hitting_set_certificate_v1.tau"

MAX_SCENARIOS = 8
MAX_EXACT_SUBSETS = 1024


@dataclass(frozen=True)
class EvidenceTask:
    task_id: str
    cost: int
    covers: tuple[str, ...]
    deps: tuple[str, ...] = ()


@dataclass(frozen=True)
class EvidenceScenario:
    scenario_id: str
    tasks: tuple[EvidenceTask, ...]
    blocker_ids: tuple[str, ...]
    claim_blockers: Mapping[str, tuple[str, ...]]
    presented_task_ids: tuple[str, ...]
    expected_accept: bool
    expected_reject_reason: str | None
    no_authority_effect: bool = True
    note: str = ""


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _task(task_id: str, cost: int, covers: Sequence[str], deps: Sequence[str] = ()) -> EvidenceTask:
    return EvidenceTask(str(task_id), int(cost), tuple(sorted(set(covers))), tuple(sorted(set(deps))))


def _base_tasks() -> tuple[EvidenceTask, ...]:
    return (
        _task("claim_scope_scan", 1, ("claim_scope",)),
        _task("quote_receipt_replay", 2, ("quote_receipts",), ("claim_scope_scan",)),
        _task("source_manifest_scan", 1, ("source_manifest",)),
        _task("zk_receipt_manifest", 2, ("zk_receipts",), ("source_manifest_scan",)),
        _task("operator_attestation_review", 3, ("claim_scope", "source_manifest")),
        _task("broad_release_audit", 8, ("claim_scope", "quote_receipts", "source_manifest", "zk_receipts")),
    )


def _base_blockers() -> tuple[str, ...]:
    return ("claim_scope", "quote_receipts", "source_manifest", "zk_receipts")


def _base_claim_blockers() -> dict[str, tuple[str, ...]]:
    return {
        "public_quote_receipts": ("claim_scope", "quote_receipts"),
        "public_zk_receipts": ("source_manifest", "zk_receipts"),
    }


def _exact_ids(tasks: Sequence[EvidenceTask], blockers: Sequence[str], claim_blockers: Mapping[str, Sequence[str]]) -> tuple[str, ...]:
    result = exact_minimal_bundle(tasks, blockers, claim_blockers)
    if result["selected_task_ids"] is None:
        raise ValueError("base scenario must have an exact bundle")
    return tuple(result["selected_task_ids"])


def evidence_dag_scenarios() -> tuple[EvidenceScenario, ...]:
    base_tasks = _base_tasks()
    base_blockers = _base_blockers()
    base_claims = _base_claim_blockers()
    base_exact = _exact_ids(base_tasks, base_blockers, base_claims)
    cycle_tasks = tuple(
        EvidenceTask(task.task_id, task.cost, task.covers, ("quote_receipt_replay",) if task.task_id == "claim_scope_scan" else task.deps)
        for task in base_tasks
    )
    missing_zk_tasks = tuple(task for task in base_tasks if task.task_id != "zk_receipt_manifest" and "zk_receipts" not in task.covers)
    non_minimal = tuple(sorted(set(base_exact + ("broad_release_audit",))))
    tie_tasks = (
        _task("claim_scope_scan", 1, ("claim_scope",)),
        _task("quote_receipt_replay", 2, ("quote_receipts",)),
        _task("a_manifest_combo", 3, ("source_manifest", "zk_receipts")),
        _task("z_manifest_combo", 3, ("source_manifest", "zk_receipts")),
    )
    tie_blockers = _base_blockers()
    tie_claims = _base_claim_blockers()
    tie_presented = ("claim_scope_scan", "quote_receipt_replay", "z_manifest_combo")
    return (
        EvidenceScenario(
            "valid_minimal_bundle",
            base_tasks,
            base_blockers,
            base_claims,
            base_exact,
            True,
            None,
            note="Bounded evidence DAG has a unique cost/count/tie-minimal bundle.",
        ),
        EvidenceScenario(
            "dependency_cycle_reject",
            cycle_tasks,
            base_blockers,
            base_claims,
            base_exact,
            False,
            "graph_cycle",
            note="A claim-scope task and quote replay task form a dependency cycle.",
        ),
        EvidenceScenario(
            "missing_blocker_candidate_reject",
            missing_zk_tasks,
            base_blockers,
            base_claims,
            tuple(task_id for task_id in base_exact if task_id != "zk_receipt_manifest"),
            False,
            "missing_blocker_coverage",
            note="No remaining candidate covers the zk receipt blocker.",
        ),
        EvidenceScenario(
            "non_minimal_bundle_reject",
            base_tasks,
            base_blockers,
            base_claims,
            non_minimal,
            False,
            "objective_not_minimal",
            note="The presented bundle covers all blockers but includes a redundant broad audit.",
        ),
        EvidenceScenario(
            "tie_break_violation_reject",
            tie_tasks,
            tie_blockers,
            tie_claims,
            tie_presented,
            False,
            "deterministic_tie_violation",
            note="An equal-cost and equal-count bundle violates lexicographic tie-breaking.",
        ),
        EvidenceScenario(
            "authority_boundary_reject",
            base_tasks,
            base_blockers,
            base_claims,
            base_exact,
            False,
            "authority_boundary_disabled",
            no_authority_effect=False,
            note="A valid optimizer result is rejected when the no-authority rail is disabled.",
        ),
    )


def _task_by_id(tasks: Sequence[EvidenceTask]) -> dict[str, EvidenceTask]:
    out: dict[str, EvidenceTask] = {}
    for task in tasks:
        if task.task_id in out:
            raise ValueError(f"duplicate task_id: {task.task_id}")
        out[task.task_id] = task
    return out


def _graph_acyclic(tasks: Sequence[EvidenceTask]) -> bool:
    by_id = _task_by_id(tasks)
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(task_id: str) -> bool:
        if task_id in visited:
            return True
        if task_id in visiting:
            return False
        task = by_id.get(task_id)
        if task is None:
            return False
        visiting.add(task_id)
        for dep in task.deps:
            if dep not in by_id or not visit(dep):
                return False
        visiting.remove(task_id)
        visited.add(task_id)
        return True

    return all(visit(task.task_id) for task in tasks)


def _covered_blockers(selected: Sequence[EvidenceTask]) -> set[str]:
    covered: set[str] = set()
    for task in selected:
        covered.update(task.covers)
    return covered


def _dependency_closure_ok(selected_ids: set[str], by_id: Mapping[str, EvidenceTask]) -> bool:
    for task_id in selected_ids:
        task = by_id.get(task_id)
        if task is None:
            return False
        if any(dep not in selected_ids for dep in task.deps):
            return False
    return True


def _claim_path_coverage_ok(covered: set[str], claim_blockers: Mapping[str, Sequence[str]]) -> bool:
    return all(set(required).issubset(covered) for required in claim_blockers.values())


def _bundle_key(selected: Sequence[EvidenceTask]) -> tuple[int, int, tuple[str, ...]]:
    return (sum(task.cost for task in selected), len(selected), tuple(sorted(task.task_id for task in selected)))


def exact_minimal_bundle(
    tasks: Sequence[EvidenceTask],
    blocker_ids: Sequence[str],
    claim_blockers: Mapping[str, Sequence[str]],
) -> dict[str, Any]:
    by_id = _task_by_id(tasks)
    graph_acyclic = _graph_acyclic(tasks)
    blocker_set = set(blocker_ids)
    exact_subset_count = 0
    best: tuple[EvidenceTask, ...] | None = None
    best_key: tuple[int, int, tuple[str, ...]] | None = None
    if graph_acyclic:
        ordered = tuple(sorted(tasks, key=lambda task: task.task_id))
        for width in range(len(ordered) + 1):
            for subset in itertools.combinations(ordered, width):
                exact_subset_count += 1
                selected_ids = {task.task_id for task in subset}
                if not _dependency_closure_ok(selected_ids, by_id):
                    continue
                covered = _covered_blockers(subset)
                if not blocker_set.issubset(covered):
                    continue
                if not _claim_path_coverage_ok(covered, claim_blockers):
                    continue
                key = _bundle_key(subset)
                if best_key is None or key < best_key:
                    best = tuple(sorted(subset, key=lambda task: task.task_id))
                    best_key = key
    return {
        "graph_acyclic": graph_acyclic,
        "exact_subset_count": exact_subset_count,
        "selected_task_ids": [task.task_id for task in best] if best is not None else None,
        "bundle_key": list(best_key) if best_key is not None else None,
    }


def _evaluate_scenario(scenario: EvidenceScenario) -> dict[str, Any]:
    by_id = _task_by_id(scenario.tasks)
    presented = tuple(by_id[task_id] for task_id in scenario.presented_task_ids if task_id in by_id)
    missing_presented_ids = sorted(set(scenario.presented_task_ids) - set(by_id))
    selected_ids = {task.task_id for task in presented}
    covered = _covered_blockers(presented)
    exact = exact_minimal_bundle(scenario.tasks, scenario.blocker_ids, scenario.claim_blockers)
    exact_ids = tuple(exact["selected_task_ids"] or ())
    presented_key = _bundle_key(presented) if not missing_presented_ids else None
    exact_key = tuple(exact["bundle_key"]) if exact["bundle_key"] is not None else None
    structural = {
        "graph_acyclic_ok": bool(exact["graph_acyclic"]),
        "claim_path_coverage_ok": _claim_path_coverage_ok(covered, scenario.claim_blockers),
        "blocker_coverage_ok": set(scenario.blocker_ids).issubset(covered),
        "dependency_closure_ok": _dependency_closure_ok(selected_ids, by_id),
    }
    objective_minimal_ok = bool(exact_key is not None and presented_key is not None and presented_key[:2] == exact_key[:2])
    deterministic_tie_ok = bool(objective_minimal_ok and tuple(sorted(scenario.presented_task_ids)) == exact_ids)
    flags = {
        **structural,
        "objective_minimal_ok": objective_minimal_ok,
        "deterministic_tie_ok": deterministic_tie_ok,
        "resource_budget_ok": exact["exact_subset_count"] <= MAX_EXACT_SUBSETS,
        "no_authority_effect": bool(scenario.no_authority_effect),
        "nonvacuous_bundle": bool(scenario.presented_task_ids),
        "deterministic_replay_ok": True,
    }
    reject_reasons: list[str] = []
    if not flags["graph_acyclic_ok"]:
        reject_reasons.append("graph_cycle")
    if not flags["blocker_coverage_ok"] or not flags["claim_path_coverage_ok"]:
        reject_reasons.append("missing_blocker_coverage")
    if not flags["dependency_closure_ok"]:
        reject_reasons.append("dependency_not_closed")
    if not flags["objective_minimal_ok"]:
        reject_reasons.append("objective_not_minimal")
    if flags["objective_minimal_ok"] and not flags["deterministic_tie_ok"]:
        reject_reasons.append("deterministic_tie_violation")
    if not flags["no_authority_effect"]:
        reject_reasons.append("authority_boundary_disabled")
    if not flags["resource_budget_ok"]:
        reject_reasons.append("resource_budget_exceeded")
    host_accept = all(flags.values())
    return {
        "scenario_id": scenario.scenario_id,
        "note": scenario.note,
        "expected_accept": scenario.expected_accept,
        "expected_reject_reason": scenario.expected_reject_reason,
        "host_accept": host_accept,
        "reject_reasons": reject_reasons,
        "flags": {key: int(value) for key, value in flags.items()},
        "exact": exact,
        "presented_task_ids": list(scenario.presented_task_ids),
        "presented_bundle_key": list(presented_key) if presented_key is not None else None,
        "missing_presented_task_ids": missing_presented_ids,
        "covered_blockers": sorted(covered),
        "task_count": len(scenario.tasks),
        "blocker_count": len(scenario.blocker_ids),
    }


def _tau_step(flags: Mapping[str, int], *, active: int = 1, overrides: Mapping[str, int] | None = None) -> dict[str, int]:
    values = {
        "i1": int(active),
        "i2": int(flags.get("graph_acyclic_ok", 0)),
        "i3": int(flags.get("claim_path_coverage_ok", 0)),
        "i4": int(flags.get("blocker_coverage_ok", 0)),
        "i5": int(flags.get("dependency_closure_ok", 0)),
        "i6": int(flags.get("objective_minimal_ok", 0)),
        "i7": int(flags.get("deterministic_tie_ok", 0)),
        "i8": int(flags.get("negative_cases_ok", 0)),
        "i9": int(flags.get("resource_budget_ok", 0)),
        "i10": int(flags.get("no_authority_effect", 0)),
        "i11": int(flags.get("nonvacuous_bundle", 0)),
        "i12": int(flags.get("deterministic_replay_ok", 0)),
    }
    if overrides:
        values.update({key: int(value) for key, value in overrides.items()})
    return values


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _run_tau_steps(steps: Sequence[Mapping[str, int]]) -> tuple[str | None, dict[int, dict[str, int]]]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return None, {}
    return tau_bin, run_tau_spec_steps(tau_bin=tau_bin, spec_path=TAU_SPEC, steps=list(steps), timeout_s=15.0)


def _run_tau_cases(flags: Mapping[str, int], rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    cases = [
        TauCase(
            "evidence_dag_pass",
            _tau_step(flags),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0},
            "All host-computed evidence-DAG facts admit the advisory certificate.",
        ),
        TauCase("cycle_reject", _tau_step(flags, overrides={"i2": 0}), {"o1": 0, "o4": 0}, "Dependency cycles fail closed."),
        TauCase("coverage_reject", _tau_step(flags, overrides={"i4": 0}), {"o1": 0, "o4": 0}, "Missing blocker coverage fails closed."),
        TauCase("minimality_reject", _tau_step(flags, overrides={"i6": 0}), {"o2": 0, "o4": 0}, "Non-minimal bundles fail closed."),
        TauCase("tie_reject", _tau_step(flags, overrides={"i7": 0}), {"o2": 0, "o4": 0}, "Deterministic tie violations fail closed."),
        TauCase("authority_reject", _tau_step(flags, overrides={"i10": 0}), {"o3": 0, "o4": 0}, "Authority effects fail closed."),
        TauCase("inactive_safe", _tau_step(flags, active=0), {"o4": 0, "o5": 1}, "Inactive requests do not admit certificates."),
    ]
    scenario_steps = [_tau_step(row["flags"] | {"negative_cases_ok": flags["negative_cases_ok"]}) for row in rows]
    tau_bin, outputs = _run_tau_steps([case.step for case in cases] + scenario_steps)
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "cases": [], "scenario_cases": []}
    case_rows: list[dict[str, Any]] = []
    ok = True
    for idx, case in enumerate(cases):
        got = outputs.get(idx, {})
        mismatches = {
            key: {"expected": value, "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != value
        }
        ok = ok and not mismatches
        case_rows.append(
            {
                "case_id": case.case_id,
                "ok": not mismatches,
                "expected": case.expected,
                "got": got,
                "mismatches": mismatches,
                "rationale": case.rationale,
            }
        )
    scenario_case_rows: list[dict[str, Any]] = []
    offset = len(cases)
    for idx, row in enumerate(rows):
        got = outputs.get(offset + idx, {})
        expected_o4 = int(bool(row["expected_accept"]))
        mismatch = got.get("o4") != expected_o4
        ok = ok and not mismatch
        scenario_case_rows.append(
            {
                "scenario_id": row["scenario_id"],
                "ok": not mismatch,
                "expected_o4": expected_o4,
                "got": got,
            }
        )
    return {
        "ok": ok,
        "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
        "tau_bin": tau_bin,
        "tau_version": _tau_version(tau_bin),
        "cases": case_rows,
        "scenario_cases": scenario_case_rows,
    }


def _mutation_checks(flags: Mapping[str, int]) -> list[dict[str, Any]]:
    mutations = (
        ("drop_acyclicity", {"i2": 0}, "acyclicity is load-bearing"),
        ("drop_claim_path_coverage", {"i3": 0}, "claim path coverage is load-bearing"),
        ("drop_blocker_coverage", {"i4": 0}, "blocker coverage is load-bearing"),
        ("drop_dependency_closure", {"i5": 0}, "dependency closure is load-bearing"),
        ("drop_minimality", {"i6": 0}, "minimality is load-bearing"),
        ("drop_tie_break", {"i7": 0}, "deterministic tie-breaking is load-bearing"),
        ("drop_authority_boundary", {"i10": 0}, "no-authority boundary is load-bearing"),
    )
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    rows: list[dict[str, Any]] = []
    for mutation_id, overrides, rationale in mutations:
        if not tau_bin:
            rows.append({"mutation_id": mutation_id, "accepted": False, "skipped": True, "rationale": rationale})
            continue
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=TAU_SPEC,
            steps=[_tau_step(flags, overrides=overrides)],
            timeout_s=15.0,
        )
        rows.append(
            {
                "mutation_id": mutation_id,
                "accepted": bool(outputs.get(0, {}).get("o4") == 1),
                "skipped": False,
                "got": outputs.get(0, {}),
                "rationale": rationale,
            }
        )
    return rows


def build_report() -> dict[str, Any]:
    scenarios = evidence_dag_scenarios()
    rows = [_evaluate_scenario(scenario) for scenario in scenarios]
    replay_rows = [_evaluate_scenario(scenario) for scenario in scenarios]
    deterministic_replay_ok = all(
        left["flags"] == right["flags"]
        and left["exact"] == right["exact"]
        and left["host_accept"] == right["host_accept"]
        and left["reject_reasons"] == right["reject_reasons"]
        for left, right in zip(rows, replay_rows, strict=True)
    )
    negative_rows = [row for row in rows if not bool(row["expected_accept"])]
    false_accept_rows = [row for row in negative_rows if bool(row["host_accept"])]
    expected_positive_rows = [row for row in rows if bool(row["expected_accept"])]
    max_subset_count = max(int(row["exact"]["exact_subset_count"]) for row in rows)
    flags = {
        "graph_acyclic_ok": int(all(row["flags"]["graph_acyclic_ok"] for row in expected_positive_rows)),
        "claim_path_coverage_ok": int(all(row["flags"]["claim_path_coverage_ok"] for row in expected_positive_rows)),
        "blocker_coverage_ok": int(all(row["flags"]["blocker_coverage_ok"] for row in expected_positive_rows)),
        "dependency_closure_ok": int(all(row["flags"]["dependency_closure_ok"] for row in expected_positive_rows)),
        "objective_minimal_ok": int(all(row["flags"]["objective_minimal_ok"] for row in expected_positive_rows)),
        "deterministic_tie_ok": int(all(row["flags"]["deterministic_tie_ok"] for row in expected_positive_rows)),
        "negative_cases_ok": int(bool(negative_rows) and not false_accept_rows),
        "resource_budget_ok": int(len(rows) <= MAX_SCENARIOS and max_subset_count <= MAX_EXACT_SUBSETS),
        "no_authority_effect": 1,
        "nonvacuous_bundle": int(all(row["flags"]["nonvacuous_bundle"] for row in expected_positive_rows)),
        "deterministic_replay_ok": int(deterministic_replay_ok),
    }
    mutation_rows = _mutation_checks(flags)
    if any(bool(row["accepted"]) for row in mutation_rows):
        flags = copy.deepcopy(flags)
        flags["negative_cases_ok"] = 0
    tau = _run_tau_cases(flags, rows)
    ok = (
        all(value == 1 for value in flags.values())
        and bool(tau["ok"])
        and all(not bool(row["accepted"]) for row in mutation_rows)
        and all(bool(row["host_accept"]) == bool(row["expected_accept"]) for row in rows)
        and all(
            row["expected_reject_reason"] is None or row["expected_reject_reason"] in row["reject_reasons"]
            for row in rows
        )
    )
    return {
        "schema": "zenodex.evidence_dag_hitting_set_contradictions_report.v1",
        "date": "2026-06-28",
        "ok": bool(ok),
        "spec_id": "evidence_dag_hitting_set_certificate_v1",
        "scenario_count": len(rows),
        "negative_case_count": len(negative_rows),
        "false_accept_count": len(false_accept_rows),
        "max_exact_subset_count": max_subset_count,
        "flags": flags,
        "tau": tau,
        "mutation_checks": mutation_rows,
        "scenarios": rows,
        "claim": (
            "A bounded public-assurance evidence DAG can be checked as an exact hitting-set certificate: "
            "the host enumerates minimal blocker-closing evidence bundles, rejects cycle, missing-coverage, "
            "non-minimal, tie-break, and authority-boundary contradictions, and projects only those facts into Tau."
        ),
        "non_claims": [
            "This is an advisory public-assurance planning certificate, not production-promotion authority.",
            "Tau does not enumerate evidence bundles, parse repository claims, or decide which work should be merged.",
            "The bounded corpus is synthetic; it stress-tests the claim shape rather than proving every future assurance graph.",
        ],
        "replay_command": "python3 tools/check_evidence_dag_hitting_set_contradictions.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX Evidence DAG Hitting-Set Contradiction Search - 2026-06-28",
        "",
        "## Executive Result",
        "",
        str(report["claim"]),
        "",
        f"- Scenarios: `{report['scenario_count']}`",
        f"- Negative cases: `{report['negative_case_count']}`",
        f"- False accepts: `{report['false_accept_count']}`",
        f"- Max exact subsets enumerated: `{report['max_exact_subset_count']}`",
        f"- Tau replay ok: `{report['tau']['ok']}`",
        "",
        "## Scenario Table",
        "",
        "| scenario | expected | host accept | reject reasons | exact subsets | selected exact bundle | presented bundle |",
        "| --- | --- | --- | --- | ---: | --- | --- |",
    ]
    for row in report["scenarios"]:
        lines.append(
            f"| `{row['scenario_id']}` | `{row['expected_accept']}` | `{row['host_accept']}` | "
            f"`{','.join(row['reject_reasons'])}` | `{row['exact']['exact_subset_count']}` | "
            f"`{row['exact']['selected_task_ids']}` | `{row['presented_task_ids']}` |"
        )
    lines.extend(
        [
            "",
            "## Tau Boundary",
            "",
            "`src/tau_specs/recommended/evidence_dag_hitting_set_certificate_v1.tau` admits only host-projected facts: graph acyclicity, claim-path coverage, blocker coverage, dependency closure, objective minimality, deterministic tie-breaking, negative-case rejection, resource budget, nonvacuity, deterministic replay, and no authority effects.",
            "",
            "## Mutation Checks",
            "",
            "| mutation | accepted | rationale |",
            "| --- | --- | --- |",
        ]
    )
    for row in report["mutation_checks"]:
        lines.append(f"| `{row['mutation_id']}` | `{row['accepted']}` | {row['rationale']} |")
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path = REPORT_JSON) -> dict[str, Any]:
    report = build_report()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(REPORT_JSON))
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "spec_id": report["spec_id"],
                "scenario_count": report["scenario_count"],
                "negative_case_count": report["negative_case_count"],
                "false_accept_count": report["false_accept_count"],
                "max_exact_subset_count": report["max_exact_subset_count"],
                "tau_ok": report["tau"]["ok"],
                "report": str(REPORT_MD),
                "json": str(Path(args.output_json)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
