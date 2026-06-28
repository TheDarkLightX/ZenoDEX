#!/usr/bin/env python3
"""Replay the evidence-DAG hitting-set Tau certificate breakthrough."""

from __future__ import annotations

import json
import subprocess
import sys
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_evidence_dag_hitting_set_breakthrough_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_EVIDENCE_DAG_HITTING_SET_BREAKTHROUGH_20260628.md"
CERT_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "evidence_dag_hitting_set_certificate_v1.tau"


@dataclass(frozen=True)
class PublicClaim:
    claim_id: str
    blockers: tuple[str, ...]


@dataclass(frozen=True)
class EvidenceTask:
    task_id: str
    covers: tuple[str, ...]
    dependencies: tuple[str, ...]
    cost: int
    quality_tier: int


@dataclass(frozen=True)
class Scenario:
    scenario_id: str
    claims: tuple[PublicClaim, ...]
    tasks: tuple[EvidenceTask, ...]
    existing_nodes: tuple[str, ...]
    certificate_task_ids: tuple[str, ...]
    min_quality_tier: int = 2
    max_tasks: int = 16
    max_blockers: int = 16
    max_claims: int = 8


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]


def _powerset(items: Sequence[EvidenceTask]) -> Iterable[tuple[EvidenceTask, ...]]:
    for size in range(len(items) + 1):
        for combo in combinations(items, size):
            yield combo


def _required_blockers(claims: Sequence[PublicClaim]) -> tuple[str, ...]:
    return tuple(sorted({blocker for claim in claims for blocker in claim.blockers}))


def _task_map(tasks: Sequence[EvidenceTask]) -> dict[str, EvidenceTask]:
    out: dict[str, EvidenceTask] = {}
    for task in tasks:
        if task.task_id in out:
            raise ValueError(f"duplicate evidence task id: {task.task_id}")
        out[task.task_id] = task
    return out


def _detect_dependency_issues(scenario: Scenario) -> dict[str, Any]:
    tasks_by_id = _task_map(scenario.tasks)
    existing = set(scenario.existing_nodes)
    missing: list[dict[str, str]] = []
    edges: dict[str, tuple[str, ...]] = {}
    for task in scenario.tasks:
        task_deps: list[str] = []
        for dep in task.dependencies:
            if dep in tasks_by_id:
                task_deps.append(dep)
            elif dep not in existing:
                missing.append({"task": task.task_id, "missing_dependency": dep})
        edges[task.task_id] = tuple(task_deps)

    state: dict[str, str] = {}
    stack: list[str] = []
    cycle: list[str] = []

    def visit(node: str) -> bool:
        nonlocal cycle
        mark = state.get(node)
        if mark == "done":
            return False
        if mark == "visiting":
            start = stack.index(node)
            cycle = stack[start:] + [node]
            return True
        state[node] = "visiting"
        stack.append(node)
        for dep in edges.get(node, ()):
            if visit(dep):
                return True
        stack.pop()
        state[node] = "done"
        return False

    for task_id in sorted(edges):
        if visit(task_id):
            break

    return {
        "acyclic_ok": not cycle,
        "cycle": cycle,
        "missing_dependencies": missing,
        "missing_dependency_ok": not missing,
    }


def _dependency_closed(selected: Sequence[EvidenceTask], scenario: Scenario) -> bool:
    selected_ids = {task.task_id for task in selected}
    all_task_ids = {task.task_id for task in scenario.tasks}
    existing = set(scenario.existing_nodes)
    for task in selected:
        for dep in task.dependencies:
            if dep in all_task_ids and dep not in selected_ids:
                return False
            if dep not in all_task_ids and dep not in existing:
                return False
    return True


def _covered_blockers(selected: Sequence[EvidenceTask]) -> set[str]:
    return {blocker for task in selected for blocker in task.covers}


def _eligible_tasks(scenario: Scenario) -> tuple[EvidenceTask, ...]:
    return tuple(task for task in scenario.tasks if task.quality_tier >= scenario.min_quality_tier)


def _claim_path_ok(scenario: Scenario, required: set[str], eligible: Sequence[EvidenceTask]) -> bool:
    if not scenario.claims:
        return False
    coverable = _covered_blockers(eligible)
    return bool(required) and all(claim.blockers and set(claim.blockers).issubset(coverable) for claim in scenario.claims)


def _score(selected: Sequence[EvidenceTask]) -> tuple[int, int, tuple[str, ...]]:
    return (len(selected), sum(task.cost for task in selected), tuple(sorted(task.task_id for task in selected)))


def _solve_exact(scenario: Scenario) -> dict[str, Any]:
    required = set(_required_blockers(scenario.claims))
    eligible = tuple(sorted(_eligible_tasks(scenario), key=lambda task: task.task_id))
    best: tuple[EvidenceTask, ...] | None = None
    best_score: tuple[int, int, tuple[str, ...]] | None = None
    feasible_count = 0
    subset_count = 0

    for subset in _powerset(eligible):
        subset_count += 1
        if not _dependency_closed(subset, scenario):
            continue
        if not required.issubset(_covered_blockers(subset)):
            continue
        feasible_count += 1
        score = _score(subset)
        if best_score is None or score < best_score:
            best = subset
            best_score = score

    if best is None or best_score is None:
        return {
            "ok": False,
            "error": "no_feasible_evidence_task_bundle",
            "subset_count": subset_count,
            "feasible_count": feasible_count,
            "selected_task_ids": [],
            "selected_task_count": 0,
            "total_cost": None,
        }

    return {
        "ok": True,
        "subset_count": subset_count,
        "feasible_count": feasible_count,
        "selected_task_ids": list(best_score[2]),
        "selected_task_count": best_score[0],
        "total_cost": best_score[1],
    }


def _certificate_analysis(scenario: Scenario, exact: Mapping[str, Any]) -> dict[str, Any]:
    tasks_by_id = _task_map(scenario.tasks)
    selected_ids = tuple(sorted(scenario.certificate_task_ids))
    missing_selected = [task_id for task_id in selected_ids if task_id not in tasks_by_id]
    selected = tuple(tasks_by_id[task_id] for task_id in selected_ids if task_id in tasks_by_id)
    required = set(_required_blockers(scenario.claims))
    covered = _covered_blockers(selected)
    quality_floor_ok = not missing_selected and all(task.quality_tier >= scenario.min_quality_tier for task in selected)
    blocker_cover_ok = not missing_selected and required.issubset(covered)
    dependency_closed_ok = not missing_selected and _dependency_closed(selected, scenario)
    objective_score = _score(selected) if not missing_selected else None
    exact_score = (
        exact["selected_task_count"],
        exact["total_cost"],
        tuple(exact["selected_task_ids"]),
    ) if exact.get("ok") else None
    objective_minimal_ok = bool(exact_score is not None and objective_score is not None and objective_score[:2] == exact_score[:2])
    deterministic_tie_ok = bool(exact_score is not None and objective_score == exact_score)
    redundancy_pruned_ok = True
    for task in selected:
        without = tuple(other for other in selected if other.task_id != task.task_id)
        if required.issubset(_covered_blockers(without)):
            redundancy_pruned_ok = False
            break

    return {
        "selected_task_ids": list(selected_ids),
        "missing_selected_task_ids": missing_selected,
        "covered_blockers": sorted(covered),
        "blocker_cover_ok": blocker_cover_ok,
        "dependency_closed_ok": dependency_closed_ok,
        "quality_floor_ok": quality_floor_ok,
        "objective_minimal_ok": objective_minimal_ok,
        "deterministic_tie_ok": deterministic_tie_ok,
        "redundancy_pruned_ok": redundancy_pruned_ok,
        "objective_score": list(objective_score) if objective_score is not None else None,
        "exact_score": list(exact_score) if exact_score is not None else None,
    }


def _analyze_scenario(scenario: Scenario) -> dict[str, Any]:
    required = set(_required_blockers(scenario.claims))
    eligible = _eligible_tasks(scenario)
    deps = _detect_dependency_issues(scenario)
    exact = _solve_exact(scenario)
    cert = _certificate_analysis(scenario, exact)
    graph_bounded_ok = (
        len(scenario.tasks) <= scenario.max_tasks
        and len(required) <= scenario.max_blockers
        and len(scenario.claims) <= scenario.max_claims
    )
    every_claim_has_path_ok = _claim_path_ok(scenario, required, eligible)
    resource_budget_ok = graph_bounded_ok and exact.get("subset_count", 0) <= 2 ** scenario.max_tasks
    ok = bool(
        graph_bounded_ok
        and deps["acyclic_ok"]
        and deps["missing_dependency_ok"]
        and every_claim_has_path_ok
        and exact["ok"]
        and cert["blocker_cover_ok"]
        and cert["dependency_closed_ok"]
        and cert["quality_floor_ok"]
        and cert["objective_minimal_ok"]
        and cert["deterministic_tie_ok"]
        and cert["redundancy_pruned_ok"]
        and resource_budget_ok
    )
    return {
        "scenario_id": scenario.scenario_id,
        "ok": ok,
        "claim_count": len(scenario.claims),
        "task_count": len(scenario.tasks),
        "eligible_task_count": len(eligible),
        "blocker_count": len(required),
        "required_blockers": sorted(required),
        "graph_bounded_ok": graph_bounded_ok,
        "every_claim_has_path_ok": every_claim_has_path_ok,
        "resource_budget_ok": resource_budget_ok,
        "dependency": deps,
        "exact_solution": exact,
        "certificate": cert,
    }


def _base_claims() -> tuple[PublicClaim, ...]:
    return (
        PublicClaim("tau_research_report_claim", ("tau_syntax_current", "replay_report_ok", "contradiction_cases_ok")),
        PublicClaim("public_claim_scope_claim", ("claims_registry_ok", "public_claim_scope_ok", "no_authority_boundary_ok")),
        PublicClaim("promotion_evidence_claim", ("focused_pytest_ok", "rk_evidence_ok", "replay_report_ok", "no_authority_boundary_ok")),
    )


def _base_tasks() -> tuple[EvidenceTask, ...]:
    return (
        EvidenceTask("tau_replay_bundle", ("tau_syntax_current", "focused_pytest_ok", "replay_report_ok", "contradiction_cases_ok"), ("tau_spec_source",), 3, 3),
        EvidenceTask("public_claim_gate_bundle", ("claims_registry_ok", "public_claim_scope_ok", "no_authority_boundary_ok"), ("claims_registry_source",), 2, 3),
        EvidenceTask("research_kernel_packet", ("rk_evidence_ok", "replay_report_ok", "contradiction_cases_ok"), ("tau_replay_bundle",), 1, 3),
        EvidenceTask("research_kernel_packet_alt", ("rk_evidence_ok", "replay_report_ok", "contradiction_cases_ok"), ("tau_replay_bundle",), 1, 3),
        EvidenceTask("single_tau_syntax", ("tau_syntax_current",), ("tau_spec_source",), 1, 2),
        EvidenceTask("single_focused_pytest", ("focused_pytest_ok",), ("source_code",), 1, 2),
        EvidenceTask("single_replay_report", ("replay_report_ok",), ("source_code",), 1, 2),
        EvidenceTask("single_contradiction_cases", ("contradiction_cases_ok",), ("source_code",), 1, 2),
        EvidenceTask("single_claims_registry", ("claims_registry_ok",), ("claims_registry_source",), 1, 2),
        EvidenceTask("single_public_claim_scope", ("public_claim_scope_ok",), ("claims_registry_source",), 1, 2),
        EvidenceTask("single_no_authority_boundary", ("no_authority_boundary_ok",), ("source_code",), 1, 2),
        EvidenceTask("single_rk_evidence", ("rk_evidence_ok",), ("source_code",), 1, 2),
        EvidenceTask("stale_prose_review", ("public_claim_scope_ok", "no_authority_boundary_ok"), ("source_code",), 1, 1),
    )


def _base_scenario(certificate_task_ids: Sequence[str] | None = None) -> Scenario:
    certificate = tuple(certificate_task_ids or ("public_claim_gate_bundle", "research_kernel_packet", "tau_replay_bundle"))
    return Scenario(
        scenario_id="repo_inspired_public_assurance_blockers",
        claims=_base_claims(),
        tasks=_base_tasks(),
        existing_nodes=("source_code", "tau_spec_source", "claims_registry_source"),
        certificate_task_ids=certificate,
    )


def _cycle_scenario() -> Scenario:
    tasks: list[EvidenceTask] = []
    for task in _base_tasks():
        if task.task_id == "tau_replay_bundle":
            tasks.append(EvidenceTask(task.task_id, task.covers, ("research_kernel_packet",), task.cost, task.quality_tier))
        else:
            tasks.append(task)
    return Scenario(
        scenario_id="synthetic_cycle_reject",
        claims=_base_claims(),
        tasks=tuple(tasks),
        existing_nodes=("source_code", "tau_spec_source", "claims_registry_source"),
        certificate_task_ids=("public_claim_gate_bundle", "research_kernel_packet", "tau_replay_bundle"),
    )


def _missing_path_scenario() -> Scenario:
    tasks = tuple(task for task in _base_tasks() if "rk_evidence_ok" not in task.covers)
    return Scenario(
        scenario_id="synthetic_missing_path_reject",
        claims=_base_claims(),
        tasks=tasks,
        existing_nodes=("source_code", "tau_spec_source", "claims_registry_source"),
        certificate_task_ids=("public_claim_gate_bundle", "tau_replay_bundle"),
    )


def _nonminimal_scenario() -> Scenario:
    return _base_scenario(("public_claim_gate_bundle", "research_kernel_packet", "single_no_authority_boundary", "tau_replay_bundle"))


def _tie_break_scenario() -> Scenario:
    return _base_scenario(("public_claim_gate_bundle", "research_kernel_packet_alt", "tau_replay_bundle"))


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _tau_facts(base: Mapping[str, Any], cycle: Mapping[str, Any], missing: Mapping[str, Any], nonminimal: Mapping[str, Any]) -> dict[str, int]:
    cert = base["certificate"]
    dep = base["dependency"]
    return {
        "graph_bounded_ok": int(base["graph_bounded_ok"]),
        "acyclic_ok": int(dep["acyclic_ok"] and dep["missing_dependency_ok"]),
        "every_claim_has_path_ok": int(base["every_claim_has_path_ok"]),
        "blocker_cover_ok": int(cert["blocker_cover_ok"] and cert["dependency_closed_ok"]),
        "objective_minimal_ok": int(cert["objective_minimal_ok"]),
        "deterministic_tie_ok": int(cert["deterministic_tie_ok"]),
        "quality_floor_ok": int(cert["quality_floor_ok"]),
        "redundancy_pruned_ok": int(cert["redundancy_pruned_ok"]),
        "synthetic_cycle_reject_ok": int(cycle["dependency"]["acyclic_ok"] is False and cycle["ok"] is False),
        "missing_path_reject_ok": int(missing["every_claim_has_path_ok"] is False and missing["ok"] is False),
        "nonminimal_bundle_reject_ok": int(nonminimal["certificate"]["objective_minimal_ok"] is False and nonminimal["ok"] is False),
        "resource_budget_ok": int(base["resource_budget_ok"]),
    }


def _certificate_tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    pass_step = {
        "i1": 1,
        "i2": int(facts["graph_bounded_ok"]),
        "i3": int(facts["acyclic_ok"]),
        "i4": int(facts["every_claim_has_path_ok"]),
        "i5": int(facts["blocker_cover_ok"]),
        "i6": int(facts["objective_minimal_ok"]),
        "i7": int(facts["deterministic_tie_ok"]),
        "i8": int(facts["quality_floor_ok"]),
        "i9": int(facts["redundancy_pruned_ok"]),
        "i10": int(facts["synthetic_cycle_reject_ok"]),
        "i11": int(facts["missing_path_reject_ok"]),
        "i12": int(facts["nonminimal_bundle_reject_ok"]),
        "i13": int(facts["resource_budget_ok"]),
        "i14": 1,
        "i15": 1,
    }
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauCase("certificate_pass", pass_step, {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 0}),
        TauCase("cycle_guard_reject", {**pass_step, "i3": 0}, {"o1": 0, "o5": 0}),
        TauCase("missing_path_guard_reject", {**pass_step, "i4": 0}, {"o1": 0, "o5": 0}),
        TauCase("blocker_cover_reject", {**pass_step, "i5": 0}, {"o2": 0, "o5": 0}),
        TauCase("minimality_reject", {**pass_step, "i6": 0}, {"o2": 0, "o5": 0}),
        TauCase("tie_break_reject", {**pass_step, "i7": 0}, {"o2": 0, "o5": 0}),
        TauCase("quality_floor_reject", {**pass_step, "i8": 0}, {"o2": 0, "o5": 0}),
        TauCase("redundancy_prune_reject", {**pass_step, "i9": 0}, {"o2": 0, "o5": 0}),
        TauCase("cycle_refutation_missing_reject", {**pass_step, "i10": 0}, {"o3": 0, "o5": 0}),
        TauCase("missing_path_refutation_missing_reject", {**pass_step, "i11": 0}, {"o3": 0, "o5": 0}),
        TauCase("nonminimal_refutation_missing_reject", {**pass_step, "i12": 0}, {"o3": 0, "o5": 0}),
        TauCase("resource_budget_reject", {**pass_step, "i13": 0}, {"o4": 0, "o5": 0}),
        TauCase("advisory_boundary_reject", {**pass_step, "i14": 0}, {"o4": 0, "o5": 0}),
        TauCase("authority_boundary_reject", {**pass_step, "i15": 0}, {"o4": 0, "o5": 0}),
        TauCase("inactive_safe", inactive, {"o5": 0, "o6": 1}),
    )


def _run_tau_cases(tau_bin: str | None, cases: tuple[TauCase, ...]) -> dict[str, Any]:
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "spec_path": str(CERT_SPEC.relative_to(REPO_ROOT)), "cases": []}
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=CERT_SPEC, steps=[case.step for case in cases], timeout_s=30.0)
    out_cases: list[dict[str, Any]] = []
    ok = True
    invalid_accepts = 0
    for idx, case in enumerate(cases):
        got = {str(key): int(value) for key, value in outputs.get(idx, {}).items()}
        mismatches = {key: {"expected": value, "got": got.get(key)} for key, value in case.expected.items() if got.get(key) != value}
        if got.get("o5", 0) == 1 and case.expected.get("o5") == 0:
            invalid_accepts += 1
        if mismatches:
            ok = False
        out_cases.append({"case_id": case.case_id, "ok": not mismatches, "expected": case.expected, "got": got, "mismatches": mismatches})
    return {
        "ok": ok and invalid_accepts == 0,
        "spec_path": str(CERT_SPEC.relative_to(REPO_ROOT)),
        "cases": out_cases,
        "case_count": len(cases),
        "invalid_accepts": invalid_accepts,
    }


def build_report() -> dict[str, Any]:
    base = _analyze_scenario(_base_scenario())
    cycle = _analyze_scenario(_cycle_scenario())
    missing = _analyze_scenario(_missing_path_scenario())
    nonminimal = _analyze_scenario(_nonminimal_scenario())
    tie_break = _analyze_scenario(_tie_break_scenario())
    facts = _tau_facts(base, cycle, missing, nonminimal)
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    tau = _run_tau_cases(tau_bin, _certificate_tau_cases(facts))
    naive_single_purpose_count = base["blocker_count"]
    selected_count = base["exact_solution"]["selected_task_count"]
    reduction_tasks = naive_single_purpose_count - selected_count
    reduction_ratio = f"{naive_single_purpose_count}:{selected_count}"
    ok = bool(
        base["ok"]
        and tau["ok"]
        and all(value == 1 for value in facts.values())
        and cycle["ok"] is False
        and missing["ok"] is False
        and nonminimal["ok"] is False
        and tie_break["certificate"]["objective_minimal_ok"] is True
        and tie_break["certificate"]["deterministic_tie_ok"] is False
        and selected_count == 3
        and naive_single_purpose_count == 8
    )
    return {
        "schema": "zenodex.evidence_dag_hitting_set_breakthrough_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "breakthrough": {
            "name": "Evidence-DAG hitting-set certificate",
            "summary": "A bounded public-assurance blocker graph is reduced to an exact minimum evidence-task bundle, then certified by Tau using host-projected graph, minimality, refutation, and authority-boundary facts.",
            "authority_boundary": "Research certificate only. Tau has no settlement, liquidation, oracle-update, production-promotion, or state-root authority.",
        },
        "tau": {
            "tau_bin": tau_bin,
            "tau_version": _tau_version(tau_bin),
            "certificate": tau,
            "supported_subset": "Tau 0.7.0-alpha host-projected sbf formulas: host computes graph search and comparisons; Tau composes booleans.",
        },
        "facts": facts,
        "base_scenario": base,
        "negative_scenarios": {
            "cycle": cycle,
            "missing_path": missing,
            "nonminimal_certificate": nonminimal,
            "deterministic_tie": tie_break,
        },
        "compression": {
            "naive_single_purpose_task_count": naive_single_purpose_count,
            "selected_task_count": selected_count,
            "reduction_tasks": reduction_tasks,
            "reduction_ratio": reduction_ratio,
        },
        "spec_frontier": [
            {
                "spec": "evidence_dag_hitting_set_certificate_v1.tau",
                "benefit": "Turns assurance backlog selection into an exact bounded optimization problem with cycle, coverage, minimality, and authority-boundary gates.",
                "status": "implemented_in_this_report",
            },
            {
                "spec": "ab_ordering_subset_dp_certificate_v1.tau",
                "benefit": "Host can compute Held-Karp style subset DP for AB ordering and Tau can certify candidate completeness, exact bounded optimality flags, and negative oracle coverage.",
                "status": "frontier_candidate",
            },
            {
                "spec": "cow_hungarian_matching_certificate_v1.tau",
                "benefit": "Host can solve CoW pairing as maximum-weight bipartite matching and Tau can certify feasibility, optimality witness checks, and settlement authority separation.",
                "status": "frontier_candidate",
            },
        ],
        "non_claims": [
            "This does not parse arbitrary prose into a complete evidence graph.",
            "This does not change production-promotion posture or claims-registry semantics.",
            "The exact minimum is over the declared bounded blocker corpus and eligible task list.",
            "Tau does not compute graph search, hitting sets, signatures, test execution, or Research Kernel promotion.",
            "External legal, hardware, operator, and live-network assumptions remain explicit non-claims.",
        ],
        "replay_command": "python3 tools/zenodex_evidence_dag_hitting_set_breakthrough_20260628.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Evidence-DAG Hitting-Set Breakthrough - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(str(report["breakthrough"]["summary"]))
    lines.append("")
    lines.append(str(report["breakthrough"]["authority_boundary"]))
    lines.append("")
    lines.append(f"- Spec: `{report['tau']['certificate']['spec_path']}`")
    lines.append(f"- Tau version: `{report['tau']['tau_version']}`")
    lines.append(f"- Public claims in bounded model: `{report['base_scenario']['claim_count']}`")
    lines.append(f"- Blockers in bounded model: `{report['base_scenario']['blocker_count']}`")
    lines.append(f"- Evidence tasks in bounded model: `{report['base_scenario']['task_count']}`")
    lines.append(f"- Exact subset evaluations: `{report['base_scenario']['exact_solution']['subset_count']}`")
    lines.append(f"- Naive single-purpose tasks: `{report['compression']['naive_single_purpose_task_count']}`")
    lines.append(f"- Exact selected tasks: `{report['compression']['selected_task_count']}`")
    lines.append(f"- Compression: `{report['compression']['reduction_ratio']}`")
    lines.append(f"- Tau invalid accepts: `{report['tau']['certificate']['invalid_accepts']}`")
    lines.append("")
    lines.append("## Breakthrough Shape")
    lines.append("")
    lines.append("The public-assurance backlog is represented as:")
    lines.append("")
    lines.append("```text")
    lines.append("public claims -> blockers -> eligible evidence tasks -> task dependencies")
    lines.append("```")
    lines.append("")
    lines.append("The host computes the exact minimum evidence-task bundle over the bounded corpus. Tau certifies the projected facts: bounded graph, acyclic dependencies, every-claim path coverage, blocker coverage, objective minimality, deterministic tie-breaking, quality floor, redundancy pruning, negative-case rejection, resource bounds, and advisory-only authority.")
    lines.append("")
    lines.append("## Exact Bundle")
    lines.append("")
    lines.append("| selected task | covers | dependencies |")
    lines.append("| --- | --- | --- |")
    task_by_id = {task.task_id: task for task in _base_tasks()}
    for task_id in report["base_scenario"]["exact_solution"]["selected_task_ids"]:
        task = task_by_id[task_id]
        lines.append(f"| `{task.task_id}` | `{', '.join(task.covers)}` | `{', '.join(task.dependencies)}` |")
    lines.append("")
    lines.append("The exact bundle closes eight blockers with three evidence tasks. The deterministic tie-break chooses `research_kernel_packet` over an equivalent alternative with the same cost and cover.")
    lines.append("")
    lines.append("## Tau Certificate Cases")
    lines.append("")
    lines.append("| case | ok | primary output |")
    lines.append("| --- | --- | ---: |")
    for case in report["tau"]["certificate"]["cases"]:
        lines.append(f"| `{case['case_id']}` | `{case['ok']}` | `{case['got'].get('o5')}` |")
    lines.append("")
    lines.append("## New Tau Specification Frontier For ZenoDEX")
    lines.append("")
    lines.append("| spec | status | benefit |")
    lines.append("| --- | --- | --- |")
    for item in report["spec_frontier"]:
        lines.append(f"| `{item['spec']}` | `{item['status']}` | {item['benefit']} |")
    lines.append("")
    lines.append("## Tau Language Constraint Learned")
    lines.append("")
    lines.append(f"{report['tau']['supported_subset']} This keeps the spec small, replayable, and compatible with the current local Tau binary while preserving the verifier boundary.")
    lines.append("")
    lines.append("## Negative Knowledge")
    lines.append("")
    lines.append("- A cyclic dependency graph is rejected before certificate admission.")
    lines.append("- A public claim with an uncovered blocker is rejected.")
    lines.append("- A non-minimal evidence bundle is rejected.")
    lines.append("- A minimum-cost tie that violates deterministic ordering is rejected.")
    lines.append("- A Tau certificate with authority effects disabled is accepted only as inactive-safe, not as a positive certificate.")
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(str(report["replay_command"]))
    lines.append("```")
    lines.append("")
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "compression": report["compression"]["reduction_ratio"],
                "subset_evaluations": report["base_scenario"]["exact_solution"]["subset_count"],
                "tau_cases": report["tau"]["certificate"]["case_count"],
                "invalid_accepts": report["tau"]["certificate"]["invalid_accepts"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
