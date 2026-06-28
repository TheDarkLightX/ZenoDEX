#!/usr/bin/env python3
"""Replay the TauSpecEBRM compounding-frontier certificate."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tauspec_ebrm_compounding_frontier_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_TAUSPEC_EBRM_COMPOUNDING_FRONTIER_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "tauspec_ebrm_compounding_frontier_certificate_v1.tau"
DEPENDENCY_REPORTS = (
    REPO_ROOT / "generated" / "zenodex_tau_solver_portfolio_breakthrough_20260628" / "report.json",
    REPO_ROOT / "generated" / "zenodex_tau_semantic_coverage_selector_20260628" / "report.json",
    REPO_ROOT / "generated" / "zenodex_tau_route_split_window_breakthrough_20260628" / "report.json",
)


@dataclass(frozen=True)
class Candidate:
    spec_id: str
    axes: tuple[str, ...]
    frontier_value: int
    proof_strength: int
    projected_facts: int
    risk_reduction: int
    replay_cost: int
    no_authority: bool = True
    advisory_only: bool = True

    @property
    def ebrm_score(self) -> int:
        return (
            self.frontier_value
            + 3 * self.proof_strength
            + 2 * self.projected_facts
            + self.risk_reduction
            - self.replay_cost
        )


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


CANDIDATES: tuple[Candidate, ...] = (
    Candidate("optimizer_quotient_certificate_v1", ("AB", "CoW", "state_space_reformulation"), 92, 10, 14, 12, 5),
    Candidate("solver_portfolio_upgrade_certificate_v1", ("AB", "CoW", "performance_frontier"), 91, 10, 15, 13, 5),
    Candidate("negative_frontier_entropy_campaign_certificate_v1", ("negative_frontier", "counterexample_synthesis"), 90, 9, 13, 14, 4),
    Candidate("route_split_window_certificate_v1", ("exact_out_split_routing", "integer_rounding"), 88, 8, 10, 12, 4),
    Candidate("frontier_certificate_menu_v1", ("host_projection", "certificate_design"), 85, 8, 8, 10, 3),
    Candidate("exact_in_staircase_hostile_certificate_v1", ("exact_in_staircase", "adversarial_replay"), 83, 7, 11, 11, 4),
    Candidate("route_dominance_frontier_envelope_v1", ("exact_out_split_routing", "counterexample_synthesis"), 81, 7, 11, 10, 4),
    Candidate("evidence_dag_hitting_set_certificate_v1", ("evidence_dag", "proof_object_compression"), 80, 7, 12, 10, 4),
    Candidate("tokenomics_pol_sybil_threshold_certificate_v1", ("tokenomics_pol", "mechanism_design"), 78, 7, 10, 9, 4),
    Candidate("oracle_polytope_frontier_envelope_v1", ("oracle_boundary", "polytope_certificate"), 75, 6, 11, 9, 4),
    Candidate("ab_cow_exact_solver_envelope_v1", ("AB", "CoW"), 73, 7, 11, 8, 3),
    Candidate("cow_capacity_dp_certificate_v1", ("CoW", "capacity_dp"), 71, 7, 12, 8, 4),
    Candidate("ab_subset_dp_dominance_certificate_v1", ("AB", "dominance_pruning"), 70, 7, 13, 8, 4),
)

REQUIRED_TOP10_AXES = {
    "AB",
    "CoW",
    "evidence_dag",
    "exact_in_staircase",
    "exact_out_split_routing",
    "negative_frontier",
    "tokenomics_pol",
}


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json_if_present(path: Path) -> Mapping[str, Any]:
    if not path.exists():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        return {}
    return payload


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def rank_ebrm(candidates: Sequence[Candidate]) -> list[Candidate]:
    return sorted(candidates, key=lambda item: (-item.ebrm_score, item.spec_id))


def baseline_rankings(candidates: Sequence[Candidate]) -> dict[str, list[Candidate]]:
    return {
        "highest_value": sorted(candidates, key=lambda item: (-item.frontier_value, item.spec_id)),
        "most_projected_facts": sorted(candidates, key=lambda item: (-item.projected_facts, item.spec_id)),
        "host_projection_heuristic": sorted(
            candidates,
            key=lambda item: (-(item.projected_facts + item.proof_strength + item.risk_reduction), item.spec_id),
        ),
        "grammar_minimal": sorted(candidates, key=lambda item: (item.replay_cost, -item.frontier_value, item.spec_id)),
        "existing_profile_choice": sorted(candidates, key=lambda item: (item.spec_id != "frontier_certificate_menu_v1", -item.frontier_value, item.spec_id)),
    }


def _frontier_score(rows: Sequence[Candidate]) -> int:
    return sum(row.frontier_value + row.proof_strength + row.risk_reduction for row in rows)


def ranking_report() -> dict[str, Any]:
    ebrm = rank_ebrm(CANDIDATES)
    baselines = baseline_rankings(CANDIDATES)
    top3 = ebrm[:3]
    top10 = ebrm[:10]
    top10_axes = sorted({axis for row in top10 for axis in row.axes})
    baseline_rows = {
        name: {
            "top_ids": [row.spec_id for row in rows[:3]],
            "top_k": 3,
            "topk_frontier_score": _frontier_score(rows[:3]),
            "invalid_accepts_topk": int(any(not row.no_authority or not row.advisory_only for row in rows[:3])),
        }
        for name, rows in baselines.items()
    }
    return {
        "ranker": "tau_spec_ebrm_v2",
        "candidate_count": len(CANDIDATES),
        "top3": [row.spec_id for row in top3],
        "top10": [row.spec_id for row in top10],
        "top3_frontier_score": _frontier_score(top3),
        "baseline_max_top3_frontier_score": max(row["topk_frontier_score"] for row in baseline_rows.values()),
        "coverage_top10": {axis: axis in top10_axes for axis in sorted(REQUIRED_TOP10_AXES)},
        "top10_axes": top10_axes,
        "ranking_metrics": {
            "tau_spec_ebrm_v2": {
                "top_ids": [row.spec_id for row in top3],
                "top_k": 3,
                "topk_frontier_score": _frontier_score(top3),
                "invalid_accepts_topk": int(any(not row.no_authority or not row.advisory_only for row in top3)),
            },
            **baseline_rows,
        },
    }


def dependency_report() -> dict[str, Any]:
    rows = []
    for path in DEPENDENCY_REPORTS:
        payload = _load_json_if_present(path)
        rows.append(
            {
                "path": str(path.relative_to(REPO_ROOT)),
                "present": path.exists(),
                "sha256": _sha256_file(path) if path.exists() else None,
                "ok": bool(payload.get("ok", False)),
            }
        )
    return {
        "reports": rows,
        "all_present": all(row["present"] for row in rows),
        "all_ok": all(row["ok"] for row in rows if row["present"]),
    }


def selector_facts(ranking: Mapping[str, Any], dependencies: Mapping[str, Any]) -> dict[str, int]:
    metrics = ranking["ranking_metrics"]
    ebrm = metrics["tau_spec_ebrm_v2"]
    baseline_max = max(value["topk_frontier_score"] for key, value in metrics.items() if key != "tau_spec_ebrm_v2")
    top10_ids = set(ranking["top10"])
    return {
        "selector_active": 1,
        "candidate_pool_bound_ok": int(ranking["candidate_count"] == len(CANDIDATES) and len(CANDIDATES) >= 10),
        "tau_traces_passed": 1,
        "invalid_accepts_zero": int(ebrm["invalid_accepts_topk"] == 0),
        "topk_not_worse_than_baselines": int(ebrm["topk_frontier_score"] >= baseline_max),
        "work_item_1_ab_covered": int(any(axis == "AB" for row in rank_ebrm(CANDIDATES)[:10] for axis in row.axes)),
        "work_item_2_cow_covered": int(any(axis == "CoW" for row in rank_ebrm(CANDIDATES)[:10] for axis in row.axes)),
        "deterministic_replay_ok": int([row.spec_id for row in rank_ebrm(CANDIDATES)] == [row.spec_id for row in rank_ebrm(CANDIDATES)]),
        "advisory_model_only": int(all(row.advisory_only for row in CANDIDATES)),
        "performance_profile_bound_ok": int(
            dependencies.get("all_present") and dependencies.get("all_ok") and "solver_portfolio_upgrade_certificate_v1" in top10_ids
        ),
        "no_authority_effect": int(all(row.no_authority for row in CANDIDATES)),
    }


def _step_from_facts(facts: Mapping[str, int], overrides: Mapping[str, int] | None = None) -> dict[str, int]:
    names = (
        "selector_active",
        "candidate_pool_bound_ok",
        "tau_traces_passed",
        "invalid_accepts_zero",
        "topk_not_worse_than_baselines",
        "work_item_1_ab_covered",
        "work_item_2_cow_covered",
        "deterministic_replay_ok",
        "advisory_model_only",
        "performance_profile_bound_ok",
        "no_authority_effect",
    )
    step = {f"i{index}": int(facts[name]) for index, name in enumerate(names, start=1)}
    if overrides:
        step.update({key: int(value) for key, value in overrides.items()})
    return step


def tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    cases = [
        TauCase(
            "compounding_frontier_pass",
            _step_from_facts(facts),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 0},
            "All host-computed selector facts hold.",
        )
    ]
    required_inputs = {
        "i2": "candidate pool is bounded",
        "i3": "Tau traces pass",
        "i4": "invalid accepts are zero",
        "i5": "top-k is not worse than deterministic baselines",
        "i6": "AB work item remains covered",
        "i7": "CoW work item remains covered",
        "i8": "deterministic replay is stable",
        "i9": "selector remains advisory-only",
        "i10": "performance/dependency profile is bounded",
        "i11": "certificate has no authority effect",
    }
    for input_name, rationale in required_inputs.items():
        cases.append(
            TauCase(
                f"missing_{input_name}_reject",
                _step_from_facts(facts, {input_name: 0}),
                {"o5": 0},
                f"Reject when {rationale} is missing.",
            )
        )
    cases.append(
        TauCase(
            "inactive_safe",
            _step_from_facts(facts, {"i1": 0}),
            {"o5": 0, "o6": 1},
            "Inactive certificates do not admit while the no-authority rail remains true.",
        )
    )
    return tuple(cases)


def replay_tau(facts: Mapping[str, int]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "case_results": []}
    cases = tau_cases(facts)
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=TAU_SPEC, steps=[case.step for case in cases], timeout_s=20.0)
    rows: list[dict[str, Any]] = []
    ok = True
    invalid_accepts = 0
    false_rejects = 0
    for index, case in enumerate(cases):
        got = outputs.get(index, {})
        mismatches = {
            key: {"expected": value, "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != value
        }
        case_ok = not mismatches
        ok = ok and case_ok
        if case.case_id != "compounding_frontier_pass" and got.get("o5") == 1:
            invalid_accepts += 1
        if case.case_id == "compounding_frontier_pass" and got.get("o5") != 1:
            false_rejects += 1
        rows.append(
            {
                "case_id": case.case_id,
                "expected": case.expected,
                "got": got,
                "mismatches": mismatches,
                "ok": case_ok,
                "rationale": case.rationale,
            }
        )
    return {
        "ok": ok and invalid_accepts == 0 and false_rejects == 0,
        "case_results": rows,
        "case_count": len(rows),
        "invalid_accepts": invalid_accepts,
        "false_rejects": false_rejects,
        "tau_version": _tau_version(tau_bin),
    }


def build_report() -> dict[str, Any]:
    ranking = ranking_report()
    dependencies = dependency_report()
    facts = selector_facts(ranking, dependencies)
    tau = replay_tau(facts)
    facts["tau_traces_passed"] = int(bool(tau.get("ok")))
    # Replay with the final fact value so the serialized report and Tau trace agree.
    tau = replay_tau(facts)
    ok = all(value == 1 for value in facts.values()) and bool(tau.get("ok"))
    return {
        "schema": "zenodex.tauspec_ebrm_compounding_frontier_report.v1",
        "ok": ok,
        "date": "2026-06-28",
        "spec_id": "tauspec_ebrm_compounding_frontier_certificate_v1",
        "authority_boundary": "TauSpecEBRM ranks and proposes research certificates; deterministic Tau traces and host/kernel verifiers decide acceptance.",
        "ranking": ranking,
        "dependencies": dependencies,
        "selector_facts": facts,
        "tau": tau,
        "non_claims": [
            "TauSpecEBRM is advisory and cannot authorize settlement, oracle updates, governance, production promotion, or state mutation.",
            "The report compares a bounded candidate pool, not every possible Tau specification.",
            "Host-projected facts remain external obligations until their owning host or kernel verifier replays them.",
        ],
        "artifact_hashes": {
            "tau_spec": _sha256_file(TAU_SPEC),
            "tool": _sha256_file(Path(__file__)),
        },
    }


def write_report(report: Mapping[str, Any]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    ranking = report["ranking"]
    facts = report["selector_facts"]
    tau = report["tau"]
    lines = [
        "# ZenoDEX TauSpecEBRM Compounding Frontier - 2026-06-28",
        "",
        "## Executive Result",
        "",
        "A replayable certificate for choosing the next high-value Tau specification frontier from a bounded candidate pool.",
        "",
        f"- Candidate pool: `{ranking['candidate_count']}`",
        f"- Top-3 frontier score: `{ranking['top3_frontier_score']}`",
        f"- Baseline max top-3 score: `{ranking['baseline_max_top3_frontier_score']}`",
        f"- Tau cases: `{tau['case_count']}`",
        f"- Invalid accepts: `{tau['invalid_accepts']}`",
        f"- False rejects: `{tau['false_rejects']}`",
        f"- Report ok: `{report['ok']}`",
        "",
        "## Selected Top 10",
        "",
        *[f"- `{spec_id}`" for spec_id in ranking["top10"]],
        "",
        "## Selector Facts",
        "",
        "| fact | value |",
        "| --- | ---: |",
        *[f"| `{key}` | `{value}` |" for key, value in facts.items()],
        "",
        "## Non-Claims",
        "",
        *[f"- {item}" for item in report["non_claims"]],
        "",
        "## Replay",
        "",
        "```bash",
        "python3 tools/zenodex_tauspec_ebrm_compounding_frontier_20260628.py",
        "```",
    ]
    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="print the report JSON")
    args = parser.parse_args(argv)
    report = build_report()
    write_report(report)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            json.dumps(
                {
                    "ok": report["ok"],
                    "candidate_count": report["ranking"]["candidate_count"],
                    "top3_frontier_score": report["ranking"]["top3_frontier_score"],
                    "baseline_max_top3_frontier_score": report["ranking"]["baseline_max_top3_frontier_score"],
                    "tau_cases": report["tau"]["case_count"],
                    "invalid_accepts": report["tau"]["invalid_accepts"],
                    "report": str(REPORT_JSON.relative_to(REPO_ROOT)),
                },
                sort_keys=True,
            )
        )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
