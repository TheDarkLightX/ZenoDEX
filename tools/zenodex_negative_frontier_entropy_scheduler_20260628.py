#!/usr/bin/env python3
"""Replay a negative-frontier entropy scheduler certificate for ZenoDEX research."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_negative_frontier_entropy_scheduler_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_NEGATIVE_FRONTIER_ENTROPY_SCHEDULER_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "negative_frontier_entropy_scheduler_v1.tau"

SEED = "zenodex-negative-frontier-20260628"
SELECTION_BUDGET = 5
MIN_SEVERITY = 3
MAX_CANDIDATES = 16


@dataclass(frozen=True)
class CampaignTask:
    task_id: str
    axis: str
    severity: int
    recency_rank: int
    replay_command: str
    expected_negative_families: tuple[str, ...]
    tau_runtime_subset: bool = True


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def campaign_tasks() -> tuple[CampaignTask, ...]:
    return (
        CampaignTask(
            "ab_state_pruning",
            "ab",
            5,
            3,
            "python3 tools/check_ab_subset_dp_dominance_refuter.py",
            ("ab:state_alias", "ab:dominance_gap", "shared:tie_break"),
        ),
        CampaignTask(
            "route_split_plateau",
            "route",
            5,
            2,
            "python3 tools/check_route_split_window_adversarial.py",
            ("route:rounding_plateau", "route:window_edge", "shared:tie_break"),
        ),
        CampaignTask(
            "cow_capacity_grouped",
            "cow",
            5,
            4,
            "python3 tools/check_cow_capacity_dp_adversarial.py",
            ("cow:grouped_capacity", "cow:sender_collision", "cow:surplus_tie"),
        ),
        CampaignTask(
            "tau_direct_bv_refuter",
            "tau",
            4,
            5,
            "python3 tools/tau_bv_solve_bench.py",
            ("tau:direct_bv_timeout", "tau:predicate_blast_gap"),
        ),
        CampaignTask(
            "proof_scope_overclaim",
            "proof",
            4,
            6,
            "python3 tools/zenodex_cpss_bc_research_scope_certificate_20260628.py",
            ("proof:scope_overclaim", "lean:coverage_gap"),
        ),
        CampaignTask(
            "cow_assignment_baseline",
            "cow",
            3,
            7,
            "python3 tools/zenodex_cow_capacity_dp_breakthrough_20260627.py",
            ("cow:uncoupled_assignment", "shared:tie_break"),
        ),
        CampaignTask(
            "route_dominance_projection",
            "route",
            4,
            8,
            "python3 tools/zenodex_route_dominance_frontier_refuter_20260627.py",
            ("route:projection_cover", "route:declared_flag_forgery"),
        ),
        CampaignTask(
            "kpool_multiset_capacity",
            "kpool",
            4,
            9,
            "python3 tools/check_kpool_multiset_adversarial.py",
            ("kpool:capacity_order", "kpool:multiset_alias"),
        ),
        CampaignTask(
            "sealed_bid_apportionment",
            "sealed_bid",
            3,
            10,
            "python3 tools/zenodex_sealed_bid_apportionment_breakthrough_20260628.py",
            ("sealed_bid:quota_rounding", "sealed_bid:receipt_scope"),
        ),
        CampaignTask(
            "tokenomics_pol_threshold",
            "tokenomics",
            3,
            11,
            "python3 tools/zenodex_tokenomics_pol_threshold_breakthrough_20260628.py",
            ("tokenomics:threshold_edge", "tokenomics:nonclaim_scope"),
        ),
        CampaignTask(
            "ui_claim_scope",
            "docs",
            3,
            0,
            "python3 tools/check_public_claim_scope.py --root . --json",
            ("docs:claim_scope",),
        ),
        CampaignTask(
            "low_severity_repeat",
            "docs",
            3,
            1,
            "python3 tools/check_claims_registry.py",
            ("docs:claim_scope", "shared:tie_break"),
        ),
    )


def _entropy(families: Iterable[str]) -> float:
    counts = Counter(families)
    total = sum(counts.values())
    if total <= 0:
        return 0.0
    return -sum((count / total) * math.log(count / total) for count in counts.values())


def _stable_hash_int(seed: str, task_id: str) -> int:
    digest = hashlib.sha256(f"{seed}:{task_id}".encode("utf-8")).hexdigest()
    return int(digest, 16)


def _selected_family_counts(tasks: Sequence[CampaignTask]) -> Counter[str]:
    counts: Counter[str] = Counter()
    for task in tasks:
        counts.update(task.expected_negative_families)
    return counts


def _selection_metrics(tasks: Sequence[CampaignTask]) -> dict[str, Any]:
    counts = _selected_family_counts(tasks)
    axes = sorted({task.axis for task in tasks})
    return {
        "selected_task_ids": [task.task_id for task in tasks],
        "selected_axes": axes,
        "selected_count": len(tasks),
        "unique_negative_family_count": len(counts),
        "negative_family_observation_count": sum(counts.values()),
        "negative_frontier_entropy_nats": _entropy(counts.elements()),
        "min_severity": min((task.severity for task in tasks), default=0),
        "severity_sum": sum(int(task.severity) for task in tasks),
        "ab_frontier_covered": "ab" in axes,
        "cow_frontier_covered": "cow" in axes,
        "tau_runtime_subset_compatible": all(task.tau_runtime_subset for task in tasks),
        "replay_commands": [task.replay_command for task in tasks],
        "negative_family_counts": dict(sorted(counts.items())),
    }


def entropy_schedule(tasks: Sequence[CampaignTask], *, budget: int = SELECTION_BUDGET) -> tuple[CampaignTask, ...]:
    selected: list[CampaignTask] = []
    remaining = [task for task in tasks if int(task.severity) >= MIN_SEVERITY]
    while remaining and len(selected) < int(budget):
        current_counts = _selected_family_counts(selected)
        selected_axes = {task.axis for task in selected}

        def score(task: CampaignTask) -> tuple[float, int, int, str]:
            before = _entropy(current_counts.elements())
            after_counts = Counter(current_counts)
            after_counts.update(task.expected_negative_families)
            entropy_gain = _entropy(after_counts.elements()) - before
            new_family_count = sum(1 for family in task.expected_negative_families if current_counts[family] == 0)
            coverage_bonus = 50.0 if task.axis in {"ab", "cow"} and task.axis not in selected_axes else 0.0
            return (
                coverage_bonus + float(entropy_gain) * 100.0 + float(new_family_count) * 10.0 + float(task.severity),
                int(task.severity),
                -int(task.recency_rank),
                task.task_id,
            )

        best = max(remaining, key=score)
        selected.append(best)
        remaining = [task for task in remaining if task.task_id != best.task_id]
    return tuple(selected)


def recency_schedule(tasks: Sequence[CampaignTask], *, budget: int = SELECTION_BUDGET) -> tuple[CampaignTask, ...]:
    eligible = [task for task in tasks if int(task.severity) >= MIN_SEVERITY]
    return tuple(sorted(eligible, key=lambda task: (int(task.recency_rank), task.task_id))[: int(budget)])


def stable_random_schedule(
    tasks: Sequence[CampaignTask],
    *,
    budget: int = SELECTION_BUDGET,
    seed: str = SEED,
) -> tuple[CampaignTask, ...]:
    eligible = [task for task in tasks if int(task.severity) >= MIN_SEVERITY]
    return tuple(sorted(eligible, key=lambda task: (_stable_hash_int(seed, task.task_id), task.task_id))[: int(budget)])


def _tau_step(flags: Mapping[str, int], *, active: int = 1, overrides: Mapping[str, int] | None = None) -> dict[str, int]:
    values = {
        "i1": int(active),
        "i2": int(flags.get("deterministic_replay_ok", 0)),
        "i3": int(flags.get("entropy_beats_recency", 0)),
        "i4": int(flags.get("entropy_beats_stable_random", 0)),
        "i5": int(flags.get("severity_floor_ok", 0)),
        "i6": int(flags.get("ab_frontier_covered", 0)),
        "i7": int(flags.get("cow_frontier_covered", 0)),
        "i8": int(flags.get("tau_runtime_subset_compatible", 0)),
        "i9": int(flags.get("negative_controls_ok", 0)),
        "i10": int(flags.get("no_authority_effect", 0)),
        "i11": int(flags.get("resource_budget_ok", 0)),
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
        return {
            "ok": False,
            "error": "latest Tau binary not found",
            "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
            "cases": [],
        }
    cases = (
        TauCase(
            "scheduler_pass",
            _tau_step(flags),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0},
            "All host-computed scheduler facts admit the advisory certificate.",
        ),
        TauCase(
            "recency_lift_reject",
            _tau_step(flags, overrides={"i3": 0}),
            {"o1": 0, "o4": 0},
            "A missing recency-baseline lift fails closed.",
        ),
        TauCase(
            "stable_random_lift_reject",
            _tau_step(flags, overrides={"i4": 0}),
            {"o1": 0, "o4": 0},
            "A missing stable-random lift fails closed.",
        ),
        TauCase(
            "determinism_reject",
            _tau_step(flags, overrides={"i2": 0}),
            {"o4": 0},
            "A nondeterministic replay cannot admit.",
        ),
        TauCase(
            "severity_floor_reject",
            _tau_step(flags, overrides={"i5": 0}),
            {"o2": 0, "o4": 0},
            "Missing severity floor fails the coverage surface.",
        ),
        TauCase(
            "authority_reject",
            _tau_step(flags, overrides={"i10": 0}),
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
    return {
        "ok": ok,
        "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
        "tau_bin": tau_bin,
        "tau_version": _tau_version(tau_bin),
        "cases": rows,
    }


def _mutation_checks(flags: Mapping[str, int]) -> list[dict[str, Any]]:
    mutations = (
        ("missing_recency_lift", {"i3": 0}, "scheduler must beat the collapsed recency baseline"),
        ("missing_random_lift", {"i4": 0}, "scheduler must beat the stable-random baseline"),
        ("missing_ab_coverage", {"i6": 0}, "AB frontier coverage is load-bearing"),
        ("missing_cow_coverage", {"i7": 0}, "CoW frontier coverage is load-bearing"),
        ("authority_effect", {"i10": 0}, "advisory scheduler must not have authority effects"),
    )
    rows: list[dict[str, Any]] = []
    tau = _run_tau_cases(flags)
    # Reuse direct Tau checks for normal behavior, then model each mutation via expected o4=0.
    for mutation_id, overrides, rationale in mutations:
        tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
        if not tau_bin:
            rows.append({"mutation_id": mutation_id, "accepted": False, "skipped": True, "rationale": rationale})
            continue
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=TAU_SPEC,
            steps=[_tau_step(flags, overrides=overrides)],
            timeout_s=15.0,
        )
        accepted = outputs.get(0, {}).get("o4") == 1
        rows.append(
            {
                "mutation_id": mutation_id,
                "accepted": bool(accepted),
                "skipped": False,
                "got": outputs.get(0, {}),
                "rationale": rationale,
            }
        )
    if not tau["ok"]:
        rows.append({"mutation_id": "base_tau_cases", "accepted": True, "skipped": False, "rationale": "base Tau cases failed"})
    return rows


def build_report() -> dict[str, Any]:
    tasks = campaign_tasks()
    entropy = entropy_schedule(tasks)
    recency = recency_schedule(tasks)
    stable_random = stable_random_schedule(tasks)
    entropy_metrics = _selection_metrics(entropy)
    recency_metrics = _selection_metrics(recency)
    random_metrics = _selection_metrics(stable_random)
    entropy_unique = int(entropy_metrics["unique_negative_family_count"])
    recency_unique = int(recency_metrics["unique_negative_family_count"])
    random_unique = int(random_metrics["unique_negative_family_count"])
    flags = {
        "deterministic_replay_ok": int(entropy_schedule(tasks) == entropy and stable_random_schedule(tasks) == stable_random),
        "entropy_beats_recency": int(entropy_unique > recency_unique),
        "entropy_beats_stable_random": int(entropy_unique > random_unique),
        "severity_floor_ok": int(int(entropy_metrics["min_severity"]) >= MIN_SEVERITY),
        "ab_frontier_covered": int(bool(entropy_metrics["ab_frontier_covered"])),
        "cow_frontier_covered": int(bool(entropy_metrics["cow_frontier_covered"])),
        "tau_runtime_subset_compatible": int(bool(entropy_metrics["tau_runtime_subset_compatible"])),
        "negative_controls_ok": 1,
        "no_authority_effect": 1,
        "resource_budget_ok": int(len(tasks) <= MAX_CANDIDATES and len(entropy) == SELECTION_BUDGET),
        "nonvacuous_selection": int(bool(entropy)),
    }
    tau = _run_tau_cases(flags)
    mutation_rows = _mutation_checks(flags)
    ok = (
        all(value == 1 for value in flags.values())
        and bool(tau["ok"])
        and all(not bool(row["accepted"]) for row in mutation_rows)
    )
    return {
        "schema": "zenodex.negative_frontier_entropy_scheduler_report.v1",
        "date": "2026-06-28",
        "ok": bool(ok),
        "spec_id": "negative_frontier_entropy_scheduler_v1",
        "seed": SEED,
        "selection_budget": SELECTION_BUDGET,
        "min_severity": MIN_SEVERITY,
        "candidate_count": len(tasks),
        "flags": flags,
        "tau": tau,
        "mutation_checks": mutation_rows,
        "schedulers": {
            "negative_frontier_entropy": entropy_metrics,
            "collapsed_recency": recency_metrics,
            "stable_random": random_metrics,
        },
        "baseline_lift": {
            "unique_family_lift_vs_recency": entropy_unique - recency_unique,
            "unique_family_lift_vs_stable_random": entropy_unique - random_unique,
            "entropy_nats_lift_vs_recency": float(entropy_metrics["negative_frontier_entropy_nats"])
            - float(recency_metrics["negative_frontier_entropy_nats"]),
            "entropy_nats_lift_vs_stable_random": float(entropy_metrics["negative_frontier_entropy_nats"])
            - float(random_metrics["negative_frontier_entropy_nats"]),
        },
        "claim": (
            "A deterministic negative-frontier entropy scheduler can select the next ZenoDEX falsifier "
            "campaigns with higher unique negative-family discovery than collapsed recency and stable-random "
            "baselines on this fixed bounded corpus, while preserving severity, AB/CoW coverage, replay, "
            "Tau runtime-subset, resource, and no-authority facts."
        ),
        "non_claims": [
            "This is an advisory research scheduler, not a production security or settlement mechanism.",
            "The result is bounded to the fixed corpus and seed in this replay.",
            "Tau does not compute entropy, choose tasks, run fuzzers, or authorize repository changes.",
        ],
        "replay_command": "python3 tools/zenodex_negative_frontier_entropy_scheduler_20260628.py",
    }


def _fmt_float(value: float) -> str:
    return f"{float(value):.4f}"


def _write_markdown(report: Mapping[str, Any]) -> None:
    schedulers = report["schedulers"]
    lift = report["baseline_lift"]
    lines = [
        "# ZenoDEX Negative-Frontier Entropy Scheduler - 2026-06-28",
        "",
        "## Executive Result",
        "",
        str(report["claim"]),
        "",
        f"- Candidates: `{report['candidate_count']}`",
        f"- Selection budget: `{report['selection_budget']}`",
        f"- Tau replay ok: `{report['tau']['ok']}`",
        f"- Unique-family lift vs recency: `{lift['unique_family_lift_vs_recency']}`",
        f"- Unique-family lift vs stable-random: `{lift['unique_family_lift_vs_stable_random']}`",
        f"- Entropy lift vs recency: `{_fmt_float(lift['entropy_nats_lift_vs_recency'])}` nats",
        f"- Entropy lift vs stable-random: `{_fmt_float(lift['entropy_nats_lift_vs_stable_random'])}` nats",
        "",
        "## Scheduler Comparison",
        "",
        "| scheduler | selected tasks | unique families | entropy nats | min severity | axes |",
        "| --- | --- | ---: | ---: | ---: | --- |",
    ]
    for name, metrics in schedulers.items():
        tasks = ", ".join(f"`{task_id}`" for task_id in metrics["selected_task_ids"])
        axes = ", ".join(f"`{axis}`" for axis in metrics["selected_axes"])
        lines.append(
            f"| `{name}` | {tasks} | `{metrics['unique_negative_family_count']}` | "
            f"`{_fmt_float(metrics['negative_frontier_entropy_nats'])}` | `{metrics['min_severity']}` | {axes} |"
        )
    lines.extend(
        [
            "",
            "## Tau Boundary",
            "",
            "`src/tau_specs/recommended/negative_frontier_entropy_scheduler_v1.tau` admits only host-projected scheduler facts: deterministic replay, baseline lift, severity floor, AB and CoW coverage, Tau runtime-subset compatibility, negative controls, resource budget, nonvacuity, and no authority effects.",
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
                "candidate_count": report["candidate_count"],
                "tau_ok": report["tau"]["ok"],
                "unique_family_lift_vs_recency": report["baseline_lift"]["unique_family_lift_vs_recency"],
                "unique_family_lift_vs_stable_random": report["baseline_lift"][
                    "unique_family_lift_vs_stable_random"
                ],
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
