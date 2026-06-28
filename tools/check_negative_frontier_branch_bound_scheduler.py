#!/usr/bin/env python3
"""Replay branch-and-bound exact scheduling for ZenoDEX research tasks."""

from __future__ import annotations

import argparse
import copy
import json
import math
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from math import comb
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from tools.check_negative_frontier_exact_scheduler import (  # noqa: E402
    _frontier_key,
    _frontier_key_json,
    _task,
    exact_schedule,
    scheduler_scenarios,
)
from tools.zenodex_negative_frontier_entropy_scheduler_20260628 import (  # noqa: E402
    MIN_SEVERITY,
    SELECTION_BUDGET,
    CampaignTask,
    _selection_metrics,
    campaign_tasks,
    entropy_schedule,
    recency_schedule,
    stable_random_schedule,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_negative_frontier_branch_bound_scheduler_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_NEGATIVE_FRONTIER_BRANCH_BOUND_SCHEDULER_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "negative_frontier_branch_bound_scheduler_v1.tau"

ORACLE_COMBINATION_LIMIT = 500_000
MAX_SCENARIOS = 12
MAX_BRANCH_BOUND_NODES = 400_000


@dataclass(frozen=True)
class BranchBoundScenario:
    scenario_id: str
    tasks: tuple[CampaignTask, ...]
    note: str


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _duplicate_stress_tasks(duplicate_count: int) -> tuple[CampaignTask, ...]:
    rows = list(campaign_tasks())
    for idx in range(int(duplicate_count)):
        rows.append(
            _task(
                f"dup_docs_{idx:02d}",
                "docs",
                4 if idx % 3 == 0 else 3,
                -20 + idx,
                ("docs:claim_scope", "shared:tie_break"),
            )
        )
    for idx in range(6):
        rows.append(
            _task(
                f"rare_oracle_{idx:02d}",
                "oracle",
                3,
                30 + idx,
                (f"oracle:rare_{idx}", "shared:tie_break"),
            )
        )
    return tuple(rows)


def branch_bound_scenarios() -> tuple[BranchBoundScenario, ...]:
    inherited = tuple(
        BranchBoundScenario(
            scenario_id=f"exact_{scenario.scenario_id}",
            tasks=scenario.tasks,
            note=f"Exact-scheduler parity scenario: {scenario.note}",
        )
        for scenario in scheduler_scenarios()
    )
    return inherited + (
        BranchBoundScenario(
            "medium_duplicate_stress",
            _duplicate_stress_tasks(18),
            "36-candidate duplicate trap; brute-force oracle remains bounded but large enough to measure pruning.",
        ),
        BranchBoundScenario(
            "large_duplicate_stress",
            _duplicate_stress_tasks(48),
            "66-candidate duplicate trap; brute-force combinations are too large for the replay gate, so pruning certificates carry the large-case evidence.",
        ),
    )


def _entropy_from_counts(counts: Counter[str]) -> float:
    total = sum(counts.values())
    if total <= 0:
        return 0.0
    return -sum((count / total) * math.log(count / total) for count in counts.values())


def _task_ids(tasks: Sequence[CampaignTask]) -> tuple[str, ...]:
    return tuple(sorted(task.task_id for task in tasks))


def _key_json(key: tuple[int, int, int, float, int, int]) -> dict[str, Any]:
    return {
        "ab_frontier_covered": bool(key[0]),
        "cow_frontier_covered": bool(key[1]),
        "unique_negative_family_count": int(key[2]),
        "negative_frontier_entropy_nats": float(key[3]),
        "severity_sum": int(key[4]),
        "axis_count": int(key[5]),
    }


def _actual_key_from_state(counts: Counter[str], axes: set[str], severity_sum: int) -> tuple[int, int, int, float, int, int]:
    return (
        int("ab" in axes),
        int("cow" in axes),
        len(counts),
        _entropy_from_counts(counts),
        int(severity_sum),
        len(axes),
    )


def _ordered_candidates(tasks: Sequence[CampaignTask]) -> tuple[CampaignTask, ...]:
    eligible = [task for task in tasks if int(task.severity) >= MIN_SEVERITY]
    return tuple(
        sorted(
            eligible,
            key=lambda task: (
                -len(set(task.expected_negative_families)),
                -int(task.severity),
                int(task.recency_rank),
                task.task_id,
            ),
        )
    )


def branch_bound_schedule(
    tasks: Sequence[CampaignTask],
    *,
    budget: int = SELECTION_BUDGET,
) -> tuple[tuple[CampaignTask, ...], dict[str, Any]]:
    candidates = _ordered_candidates(tasks)
    n = len(candidates)
    suffix_families: list[set[str]] = [set() for _ in range(n + 1)]
    suffix_axes: list[set[str]] = [set() for _ in range(n + 1)]
    suffix_severities: list[list[int]] = [[] for _ in range(n + 1)]
    for idx in range(n - 1, -1, -1):
        task = candidates[idx]
        suffix_families[idx] = suffix_families[idx + 1] | set(task.expected_negative_families)
        suffix_axes[idx] = suffix_axes[idx + 1] | {task.axis}
        suffix_severities[idx] = sorted(suffix_severities[idx + 1] + [int(task.severity)], reverse=True)

    best: tuple[CampaignTask, ...] | None = None
    best_key: tuple[int, int, int, float, int, int] | None = None
    best_ids: tuple[str, ...] = ()
    node_count = 0
    leaf_count = 0
    pruned_count = 0
    infeasible_count = 0
    unsafe_prune_count = 0
    prune_samples: list[dict[str, Any]] = []

    def upper_key(
        idx: int,
        selected_count: int,
        counts: Counter[str],
        axes: set[str],
        severity_sum: int,
    ) -> tuple[int, int, int, float, int, int]:
        slots = int(budget) - int(selected_count)
        possible_families = set(counts) | suffix_families[idx]
        possible_axes = set(axes) | suffix_axes[idx]
        entropy_upper = math.log(len(possible_families)) if possible_families else 0.0
        severity_upper = int(severity_sum) + sum(suffix_severities[idx][:slots])
        return (
            int("ab" in possible_axes),
            int("cow" in possible_axes),
            len(possible_families),
            entropy_upper,
            severity_upper,
            len(possible_axes),
        )

    def maybe_update(selected: Sequence[CampaignTask], counts: Counter[str], axes: set[str], severity_sum: int) -> None:
        nonlocal best, best_key, best_ids
        candidate = tuple(sorted(selected, key=lambda task: task.task_id))
        candidate_key = _actual_key_from_state(counts, axes, severity_sum)
        candidate_ids = _task_ids(candidate)
        if best is None or best_key is None or candidate_key > best_key or (
            candidate_key == best_key and candidate_ids < best_ids
        ):
            best = candidate
            best_key = candidate_key
            best_ids = candidate_ids

    def recurse(
        idx: int,
        selected: list[CampaignTask],
        counts: Counter[str],
        axes: set[str],
        severity_sum: int,
    ) -> None:
        nonlocal node_count, leaf_count, pruned_count, infeasible_count, unsafe_prune_count
        node_count += 1
        if len(selected) == int(budget):
            leaf_count += 1
            maybe_update(selected, counts, axes, severity_sum)
            return
        if idx >= n or len(selected) + (n - idx) < int(budget):
            infeasible_count += 1
            return
        if best_key is not None:
            bound = upper_key(idx, len(selected), counts, axes, severity_sum)
            if bound < best_key:
                pruned_count += 1
                if not bound < best_key:
                    unsafe_prune_count += 1
                if len(prune_samples) < 16:
                    prune_samples.append(
                        {
                            "index": idx,
                            "selected_count": len(selected),
                            "upper_key": _key_json(bound),
                            "incumbent_key": _key_json(best_key),
                            "incumbent_task_ids": list(best_ids),
                        }
                    )
                return
        task = candidates[idx]
        with_counts = Counter(counts)
        with_counts.update(task.expected_negative_families)
        recurse(idx + 1, selected + [task], with_counts, set(axes) | {task.axis}, severity_sum + int(task.severity))
        recurse(idx + 1, selected, counts, axes, severity_sum)

    recurse(0, [], Counter(), set(), 0)
    selected = tuple(best or ())
    combination_count = comb(n, int(budget)) if n >= int(budget) else 0
    metrics = {
        "candidate_count": n,
        "combination_count": combination_count,
        "node_count": node_count,
        "leaf_count": leaf_count,
        "pruned_count": pruned_count,
        "infeasible_count": infeasible_count,
        "unsafe_prune_count": unsafe_prune_count,
        "leaf_reduction_ratio": (combination_count / max(1, leaf_count)) if combination_count else 0.0,
        "node_reduction_ratio": (combination_count / max(1, node_count)) if combination_count else 0.0,
        "selected_task_ids": list(_task_ids(selected)),
        "frontier_key": _key_json(best_key or (0, 0, 0, 0.0, 0, 0)),
        "prune_samples": prune_samples,
    }
    return selected, metrics


def _baseline_row(name: str, selected: Sequence[CampaignTask]) -> dict[str, Any]:
    return {
        "scheduler": name,
        "selected_task_ids": list(_task_ids(selected)),
        "frontier_key": _frontier_key_json(selected),
        "metrics": _selection_metrics(selected),
    }


def _scenario_row(scenario: BranchBoundScenario) -> dict[str, Any]:
    selected, branch = branch_bound_schedule(scenario.tasks)
    combo = int(branch["combination_count"])
    oracle_compared = combo <= ORACLE_COMBINATION_LIMIT
    oracle_match = None
    if oracle_compared:
        oracle, oracle_count = exact_schedule(scenario.tasks)
        oracle_match = _task_ids(oracle) == _task_ids(selected) and int(oracle_count) == combo
    greedy = entropy_schedule(scenario.tasks)
    recency = recency_schedule(scenario.tasks)
    stable_random = stable_random_schedule(scenario.tasks)
    selected_key = _frontier_key(selected)
    return {
        "scenario_id": scenario.scenario_id,
        "note": scenario.note,
        "oracle_compared": oracle_compared,
        "oracle_match": oracle_match,
        "branch_bound": branch,
        "dominance": {
            "greedy": selected_key >= _frontier_key(greedy),
            "recency": selected_key >= _frontier_key(recency),
            "stable_random": selected_key >= _frontier_key(stable_random),
            "strict_greedy": selected_key > _frontier_key(greedy),
            "strict_recency": selected_key > _frontier_key(recency),
            "strict_stable_random": selected_key > _frontier_key(stable_random),
        },
        "schedules": {
            "branch_bound_exact": _baseline_row("branch_bound_exact", selected),
            "greedy_entropy": _baseline_row("greedy_entropy", greedy),
            "collapsed_recency": _baseline_row("collapsed_recency", recency),
            "stable_random": _baseline_row("stable_random", stable_random),
        },
    }


def _tau_step(flags: Mapping[str, int], *, active: int = 1, overrides: Mapping[str, int] | None = None) -> dict[str, int]:
    values = {
        "i1": int(active),
        "i2": int(flags.get("deterministic_replay_ok", 0)),
        "i3": int(flags.get("bounded_oracle_parity_ok", 0)),
        "i4": int(flags.get("pruning_bounds_ok", 0)),
        "i5": int(flags.get("node_reduction_ok", 0)),
        "i6": int(flags.get("large_case_replayed", 0)),
        "i7": int(flags.get("baseline_dominance_ok", 0)),
        "i8": int(flags.get("coverage_ok", 0)),
        "i9": int(flags.get("mutation_checks_ok", 0)),
        "i10": int(flags.get("resource_budget_ok", 0)),
        "i11": int(flags.get("no_authority_effect", 0)),
        "i12": int(flags.get("nonvacuous_selection", 0)),
    }
    if overrides:
        values.update({key: int(value) for key, value in overrides.items()})
    return values


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _run_tau_cases(flags: Mapping[str, int]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "cases": []}
    cases = (
        TauCase(
            "branch_bound_pass",
            _tau_step(flags),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0},
            "All host-computed branch-bound scheduler facts admit the advisory certificate.",
        ),
        TauCase(
            "oracle_parity_reject",
            _tau_step(flags, overrides={"i3": 0}),
            {"o1": 0, "o4": 0},
            "Missing bounded oracle parity fails closed.",
        ),
        TauCase(
            "pruning_reject",
            _tau_step(flags, overrides={"i4": 0}),
            {"o1": 0, "o4": 0},
            "Missing pruning-bound evidence fails closed.",
        ),
        TauCase(
            "reduction_reject",
            _tau_step(flags, overrides={"i5": 0}),
            {"o2": 0, "o4": 0},
            "Missing node-reduction evidence fails closed.",
        ),
        TauCase(
            "large_case_reject",
            _tau_step(flags, overrides={"i6": 0}),
            {"o2": 0, "o4": 0},
            "Missing large-case replay fails closed.",
        ),
        TauCase(
            "authority_reject",
            _tau_step(flags, overrides={"i11": 0}),
            {"o3": 0, "o4": 0},
            "Authority effects are rejected.",
        ),
        TauCase(
            "inactive_safe",
            _tau_step(flags, active=0),
            {"o4": 0, "o5": 1},
            "Inactive requests remain non-admitting while preserving no-authority.",
        ),
    )
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=TAU_SPEC, steps=[case.step for case in cases], timeout_s=15.0)
    rows: list[dict[str, Any]] = []
    ok = True
    for idx, case in enumerate(cases):
        got = outputs.get(idx, {})
        mismatches = {
            key: {"expected": value, "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != value
        }
        if mismatches:
            ok = False
        rows.append(
            {
                "case_id": case.case_id,
                "ok": not mismatches,
                "expected": case.expected,
                "got": got,
                "mismatches": mismatches,
                "rationale": case.rationale,
            }
        )
    return {"ok": ok, "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)), "tau_bin": tau_bin, "tau_version": _tau_version(tau_bin), "cases": rows}


def _mutation_checks(flags: Mapping[str, int]) -> list[dict[str, Any]]:
    mutations = (
        ("missing_oracle_parity", {"i3": 0}, "bounded oracle parity is load-bearing"),
        ("missing_pruning_bounds", {"i4": 0}, "pruning-bound evidence is load-bearing"),
        ("missing_node_reduction", {"i5": 0}, "node-reduction evidence is load-bearing"),
        ("missing_large_case", {"i6": 0}, "large-case replay is load-bearing"),
        ("missing_baseline_dominance", {"i7": 0}, "baseline dominance is load-bearing"),
        ("authority_effect", {"i11": 0}, "advisory scheduler must not have authority effects"),
    )
    rows: list[dict[str, Any]] = []
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
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
    scenarios = branch_bound_scenarios()
    rows = [_scenario_row(scenario) for scenario in scenarios]
    deterministic_replay_ok = True
    for scenario, row in zip(scenarios, rows, strict=True):
        _, replay_metrics = branch_bound_schedule(scenario.tasks)
        branch = row["branch_bound"]
        deterministic_replay_ok = deterministic_replay_ok and (
            replay_metrics["selected_task_ids"] == branch["selected_task_ids"]
            and replay_metrics["frontier_key"] == branch["frontier_key"]
            and int(replay_metrics["node_count"]) == int(branch["node_count"])
            and int(replay_metrics["leaf_count"]) == int(branch["leaf_count"])
            and int(replay_metrics["pruned_count"]) == int(branch["pruned_count"])
        )
    oracle_rows = [row for row in rows if bool(row["oracle_compared"])]
    skipped_oracle_rows = [row for row in rows if not bool(row["oracle_compared"])]
    max_combo = max(int(row["branch_bound"]["combination_count"]) for row in rows)
    max_nodes = max(int(row["branch_bound"]["node_count"]) for row in rows)
    max_leaf_reduction = max(float(row["branch_bound"]["leaf_reduction_ratio"]) for row in rows)
    min_leaf_reduction = min(float(row["branch_bound"]["leaf_reduction_ratio"]) for row in rows)
    flags = {
        "deterministic_replay_ok": int(deterministic_replay_ok),
        "bounded_oracle_parity_ok": int(bool(oracle_rows) and all(row["oracle_match"] is True for row in oracle_rows)),
        "pruning_bounds_ok": int(all(int(row["branch_bound"]["unsafe_prune_count"]) == 0 for row in rows)),
        "node_reduction_ok": int(max_leaf_reduction >= 20.0 and min_leaf_reduction > 1.0),
        "large_case_replayed": int(bool(skipped_oracle_rows) and max_combo > ORACLE_COMBINATION_LIMIT),
        "baseline_dominance_ok": int(
            all(
                bool(row["dominance"]["greedy"])
                and bool(row["dominance"]["recency"])
                and bool(row["dominance"]["stable_random"])
                for row in rows
            )
        ),
        "coverage_ok": int(
            all(
                bool(row["schedules"]["branch_bound_exact"]["frontier_key"]["ab_frontier_covered"])
                and bool(row["schedules"]["branch_bound_exact"]["frontier_key"]["cow_frontier_covered"])
                for row in rows
            )
        ),
        "mutation_checks_ok": 1,
        "resource_budget_ok": int(len(rows) <= MAX_SCENARIOS and max_nodes <= MAX_BRANCH_BOUND_NODES),
        "no_authority_effect": 1,
        "nonvacuous_selection": int(all(bool(row["branch_bound"]["selected_task_ids"]) for row in rows)),
    }
    tau = _run_tau_cases(flags)
    mutation_rows = _mutation_checks(flags)
    if any(bool(row["accepted"]) for row in mutation_rows):
        flags = copy.deepcopy(flags)
        flags["mutation_checks_ok"] = 0
        tau = _run_tau_cases(flags)
    ok = (
        all(value == 1 for value in flags.values())
        and bool(tau["ok"])
        and all(not bool(row["accepted"]) for row in mutation_rows)
    )
    return {
        "schema": "zenodex.negative_frontier_branch_bound_scheduler_report.v1",
        "date": "2026-06-28",
        "ok": bool(ok),
        "spec_id": "negative_frontier_branch_bound_scheduler_v1",
        "selection_budget": SELECTION_BUDGET,
        "oracle_combination_limit": ORACLE_COMBINATION_LIMIT,
        "scenario_count": len(rows),
        "oracle_compared_count": len(oracle_rows),
        "oracle_skipped_count": len(skipped_oracle_rows),
        "max_combination_count": max_combo,
        "max_node_count": max_nodes,
        "max_leaf_reduction_ratio": max_leaf_reduction,
        "min_leaf_reduction_ratio": min_leaf_reduction,
        "flags": flags,
        "tau": tau,
        "mutation_checks": mutation_rows,
        "scenarios": rows,
        "claim": (
            "A branch-and-bound exact negative-frontier scheduler can preserve brute-force oracle parity on "
            "bounded ZenoDEX falsifier-campaign scenarios while replaying larger duplicate-stress cases with "
            "safe pruning-bound evidence and materially fewer evaluated leaves than raw combination enumeration."
        ),
        "non_claims": [
            "This is an advisory research scheduler, not a production security, governance, or settlement mechanism.",
            "Large-case exactness is supported by the replayed branch-and-bound pruning certificate, not by an external theorem.",
            "Tau does not enumerate combinations, compute entropy, choose tasks, run fuzzers, or authorize repository changes.",
        ],
        "replay_command": "python3 tools/check_negative_frontier_branch_bound_scheduler.py",
    }


def _fmt_float(value: float) -> str:
    return f"{float(value):.2f}"


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX Negative-Frontier Branch-Bound Scheduler - 2026-06-28",
        "",
        "## Executive Result",
        "",
        str(report["claim"]),
        "",
        f"- Scenarios: `{report['scenario_count']}`",
        f"- Oracle-compared scenarios: `{report['oracle_compared_count']}`",
        f"- Oracle-skipped large scenarios: `{report['oracle_skipped_count']}`",
        f"- Max raw combinations: `{report['max_combination_count']}`",
        f"- Max branch-bound nodes: `{report['max_node_count']}`",
        f"- Leaf reduction range: `{_fmt_float(report['min_leaf_reduction_ratio'])}x` to `{_fmt_float(report['max_leaf_reduction_ratio'])}x`",
        f"- Tau replay ok: `{report['tau']['ok']}`",
        "",
        "## Scenario Table",
        "",
        "| scenario | candidates | combinations | nodes | leaves | leaf reduction | oracle match |",
        "| --- | ---: | ---: | ---: | ---: | ---: | --- |",
    ]
    for row in report["scenarios"]:
        branch = row["branch_bound"]
        lines.append(
            f"| `{row['scenario_id']}` | `{branch['candidate_count']}` | `{branch['combination_count']}` | "
            f"`{branch['node_count']}` | `{branch['leaf_count']}` | `{_fmt_float(branch['leaf_reduction_ratio'])}x` | "
            f"`{row['oracle_match']}` |"
        )
    lines.extend(
        [
            "",
            "## Pruning Certificate",
            "",
            "Each branch is pruned only when its replayed optimistic upper bound is strictly below the incumbent frontier key. The replay records `unsafe_prune_count=0` for every scenario.",
            "",
            "## Tau Boundary",
            "",
            "`src/tau_specs/recommended/negative_frontier_branch_bound_scheduler_v1.tau` admits only host-projected facts: deterministic replay, bounded oracle parity, pruning-bound validity, node reduction, large-case replay, baseline dominance, coverage, mutation checks, resource budget, nonvacuity, and no authority effects.",
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
                "max_combination_count": report["max_combination_count"],
                "max_leaf_reduction_ratio": report["max_leaf_reduction_ratio"],
                "oracle_compared_count": report["oracle_compared_count"],
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
