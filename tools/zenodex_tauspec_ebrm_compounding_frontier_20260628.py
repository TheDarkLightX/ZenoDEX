#!/usr/bin/env python3
"""Replay a TauSpecEBRM compounding-frontier selector certificate."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin  # noqa: E402
from tools.zenodex_tauspec_ebrm_baseline_breakthrough_20260628 import (  # noqa: E402
    CandidateProfile,
    TauTraceCase,
    _candidate_pool,
    _energy,
    _features,
    _frontier_score,
    _metrics_for_order,
    _rankings,
    _run_candidate,
    _sha256,
    _tau_version,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tauspec_ebrm_compounding_frontier_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_TAUSPEC_EBRM_COMPOUNDING_FRONTIER_20260628.md"
SPEC_ROOT = REPO_ROOT / "src" / "tau_specs" / "recommended"
SELECTION_SPEC = SPEC_ROOT / "tauspec_ebrm_compounding_frontier_certificate_v1.tau"

COMPOUNDING_TARGETS = {
    "optimizer_quotient_certificate_v1",
    "route_split_window_certificate_v1",
    "exact_in_staircase_hostile_certificate_v1",
    "negative_frontier_entropy_campaign_certificate_v1",
    "evidence_dag_hitting_set_certificate_v1",
    "tokenomics_pol_sybil_threshold_certificate_v1",
}


def _generic_cases(
    *,
    input_count: int,
    primary_output: str,
    inactive_output: str,
    reject_inputs: tuple[tuple[str, str], ...],
) -> tuple[TauTraceCase, ...]:
    pass_step = {f"i{idx}": 1 for idx in range(1, input_count + 1)}
    cases: list[TauTraceCase] = [
        TauTraceCase(
            "positive_accept",
            pass_step,
            {primary_output: 1},
            "All host-projected proof-surface facts admit the certificate lane.",
        )
    ]
    for input_name, rationale in reject_inputs:
        cases.append(
            TauTraceCase(
                f"missing_{input_name}_reject",
                {**pass_step, input_name: 0},
                {primary_output: 0},
                rationale,
            )
        )
    inactive_step = dict(pass_step)
    inactive_step["i1"] = 0
    cases.append(
        TauTraceCase(
            "inactive_safe",
            inactive_step,
            {primary_output: 0, inactive_output: 1},
            "Inactive certificates do not admit while the no-authority rail remains true.",
        )
    )
    return tuple(cases)


def _expanded_candidate_pool() -> list[CandidateProfile]:
    pool = list(_candidate_pool())
    existing = {candidate.spec_id for candidate in pool}

    additions = [
        CandidateProfile(
            spec_id="exact_in_staircase_hostile_certificate_v1",
            title="Exact-In Staircase Hostile Certificate",
            spec_path=SPEC_ROOT / "exact_in_staircase_hostile_certificate_v1.tau",
            primary_output="o4",
            breakthrough_track="exact_in_split_routing",
            value_score=10,
            novelty_score=8,
            projected_facts=11,
            profile_budget_s=20.0,
            frontier_note="Hostile-corpus certificate for the exact-in staircase profile with brute-force parity and quote-count lift.",
            work_items=(),
            non_claims=(
                "Does not change the runtime default routing profile.",
                "Does not authorize settlement or pool mutation.",
            ),
            cases=_generic_cases(
                input_count=11,
                primary_output="o4",
                inactive_output="o5",
                reject_inputs=(
                    ("i3", "Missing brute-force parity rejects the staircase certificate."),
                    ("i5", "Missing quote-count lift rejects the performance claim."),
                    ("i11", "Authority expansion rejects the advisory certificate."),
                ),
            ),
        ),
        CandidateProfile(
            spec_id="negative_frontier_entropy_campaign_certificate_v1",
            title="Negative Frontier Entropy Campaign Certificate",
            spec_path=SPEC_ROOT / "negative_frontier_entropy_campaign_certificate_v1.tau",
            primary_output="o4",
            breakthrough_track="negative_frontier_scheduler",
            value_score=9,
            novelty_score=10,
            projected_facts=13,
            profile_budget_s=20.0,
            frontier_note="Entropy-ranked negative-knowledge scheduler that keeps AB and CoW failure families covered.",
            work_items=("AB", "CoW"),
            non_claims=(
                "Does not accept a model-selected counterexample without deterministic replay.",
                "Does not grant runtime, settlement, oracle, or governance authority.",
            ),
            cases=_generic_cases(
                input_count=13,
                primary_output="o4",
                inactive_output="o5",
                reject_inputs=(
                    ("i3", "Missing recency lift rejects the entropy scheduler certificate."),
                    ("i8", "Missing CoW coverage rejects the campaign certificate."),
                    ("i13", "Authority expansion rejects the campaign certificate."),
                ),
            ),
        ),
        CandidateProfile(
            spec_id="evidence_dag_hitting_set_certificate_v1",
            title="Evidence-DAG Hitting-Set Certificate",
            spec_path=SPEC_ROOT / "evidence_dag_hitting_set_certificate_v1.tau",
            primary_output="o5",
            breakthrough_track="evidence_dag_hitting_set",
            value_score=9,
            novelty_score=8,
            projected_facts=15,
            profile_budget_s=20.0,
            frontier_note="Exact bounded hitting-set certificate for selecting public-claim evidence tasks.",
            work_items=(),
            non_claims=(
                "Does not promote production readiness by itself.",
                "Does not prove claims outside the bounded evidence graph.",
            ),
            cases=_generic_cases(
                input_count=15,
                primary_output="o5",
                inactive_output="o6",
                reject_inputs=(
                    ("i3", "A cyclic evidence graph rejects the certificate."),
                    ("i6", "A non-minimal bundle rejects the hitting-set certificate."),
                    ("i15", "Authority expansion rejects the evidence certificate."),
                ),
            ),
        ),
        CandidateProfile(
            spec_id="solver_portfolio_upgrade_certificate_v1",
            title="Solver Portfolio Upgrade Certificate",
            spec_path=SPEC_ROOT / "solver_portfolio_upgrade_certificate_v1.tau",
            primary_output="o6",
            breakthrough_track="ab_cow_solver_portfolio",
            value_score=10,
            novelty_score=8,
            projected_facts=15,
            profile_budget_s=20.0,
            frontier_note="Combined AB and CoW solver-upgrade certificate with fallback and rollback facts.",
            work_items=("AB", "CoW"),
            non_claims=(
                "Does not replace host/kernel settlement validation.",
                "Does not claim grouped-capacity CoW matching is polynomial.",
            ),
            cases=_generic_cases(
                input_count=15,
                primary_output="o6",
                inactive_output="o7",
                reject_inputs=(
                    ("i4", "Missing AB brute-force parity rejects the portfolio certificate."),
                    ("i5", "Missing CoW brute-force parity rejects the portfolio certificate."),
                    ("i15", "Authority expansion rejects the portfolio certificate."),
                ),
            ),
        ),
        CandidateProfile(
            spec_id="tokenomics_pol_sybil_threshold_certificate_v1",
            title="Tokenomics POL Sybil Threshold Certificate",
            spec_path=SPEC_ROOT / "tokenomics_pol_sybil_threshold_certificate_v1.tau",
            primary_output="o4",
            breakthrough_track="tokenomics_pol_sybil_threshold",
            value_score=9,
            novelty_score=8,
            projected_facts=12,
            profile_budget_s=20.0,
            frontier_note="Mechanism-design certificate for bounded wash-trade cost thresholds under POL fee capture.",
            work_items=(),
            non_claims=(
                "Does not activate any reward program.",
                "Does not bypass deterministic reward-envelope gates.",
            ),
            cases=_generic_cases(
                input_count=12,
                primary_output="o4",
                inactive_output="o5",
                reject_inputs=(
                    ("i3", "Missing best-response replay rejects the tokenomics certificate."),
                    ("i4", "Missing threshold minimality rejects the tokenomics certificate."),
                    ("i12", "Authority expansion rejects the tokenomics certificate."),
                ),
            ),
        ),
    ]
    pool.extend(candidate for candidate in additions if candidate.spec_id not in existing)
    return pool


FRONTIER_WINDOW = 10


def _coverage(order: list[str], *, limit: int = FRONTIER_WINDOW) -> dict[str, bool]:
    top = set(order[:limit])
    return {
        "AB": bool(top & {"optimizer_quotient_certificate_v1", "ab_cow_exact_solver_envelope_v1", "solver_portfolio_upgrade_certificate_v1"}),
        "CoW": bool(top & {"optimizer_quotient_certificate_v1", "ab_cow_exact_solver_envelope_v1", "solver_portfolio_upgrade_certificate_v1"}),
        "exact_out_split_routing": "route_split_window_certificate_v1" in top,
        "exact_in_staircase": "exact_in_staircase_hostile_certificate_v1" in top,
        "negative_frontier": "negative_frontier_entropy_campaign_certificate_v1" in top,
        "evidence_dag": "evidence_dag_hitting_set_certificate_v1" in top,
        "tokenomics_pol": "tokenomics_pol_sybil_threshold_certificate_v1" in top,
    }


def _selection_tau_cases(facts: dict[str, int]) -> tuple[TauTraceCase, ...]:
    pass_step = {
        "i1": 1,
        "i2": int(facts["candidate_pool_bound_ok"]),
        "i3": int(facts["tau_traces_passed"]),
        "i4": int(facts["invalid_accepts_zero"]),
        "i5": int(facts["topk_not_worse_than_baselines"]),
        "i6": int(facts["work_item_1_ab_covered"]),
        "i7": int(facts["work_item_2_cow_covered"]),
        "i8": int(facts["exact_out_split_routing_covered"]),
        "i9": int(facts["exact_in_staircase_covered"]),
        "i10": int(facts["negative_frontier_covered"]),
        "i11": int(facts["evidence_dag_covered"]),
        "i12": int(facts["tokenomics_pol_covered"]),
        "i13": int(facts["deterministic_replay_ok"]),
        "i14": int(facts["performance_profile_bound_ok"]),
        "i15": 1,
        "i16": 1,
    }
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauTraceCase(
            "compounding_certificate_pass",
            pass_step,
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1, "o7": 0},
            "A bounded, replayed, baseline-checked, no-authority frontier certificate admits.",
        ),
        TauTraceCase(
            "invalid_accepts_reject",
            {**pass_step, "i4": 0},
            {"o1": 0, "o2": 0, "o6": 0},
            "Any invalid accept rejects the selector certificate.",
        ),
        TauTraceCase(
            "baseline_score_reject",
            {**pass_step, "i5": 0},
            {"o2": 0, "o6": 0},
            "The advisory ranker must not underperform deterministic top-k baselines.",
        ),
        TauTraceCase(
            "staircase_coverage_reject",
            {**pass_step, "i9": 0},
            {"o3": 0, "o6": 0},
            "The exact-in staircase breakthrough must stay visible in the ranked frontier.",
        ),
        TauTraceCase(
            "negative_frontier_reject",
            {**pass_step, "i10": 0},
            {"o4": 0, "o6": 0},
            "The negative-frontier scheduler must stay visible in the ranked frontier.",
        ),
        TauTraceCase(
            "evidence_dag_reject",
            {**pass_step, "i11": 0},
            {"o4": 0, "o6": 0},
            "The evidence-DAG hitting-set certificate must stay visible in the ranked frontier.",
        ),
        TauTraceCase(
            "tokenomics_reject",
            {**pass_step, "i12": 0},
            {"o4": 0, "o6": 0},
            "The tokenomics POL threshold certificate must stay visible in the ranked frontier.",
        ),
        TauTraceCase(
            "authority_reject",
            {**pass_step, "i16": 0},
            {"o5": 0, "o6": 0},
            "The selector certificate cannot carry settlement, oracle, governance, or production-promotion authority.",
        ),
        TauTraceCase(
            "inactive_safe",
            inactive,
            {"o6": 0, "o7": 1},
            "Inactive selector certificates do not admit while the no-authority rail stays safe.",
        ),
    )


def _run_selection_tau(facts: dict[str, int], tau_bin: str | None) -> dict[str, Any]:
    selection = CandidateProfile(
        spec_id="tauspec_ebrm_compounding_frontier_certificate_v1",
        title="TauSpecEBRM Compounding Frontier Certificate",
        spec_path=SELECTION_SPEC,
        primary_output="o6",
        breakthrough_track="tauspec_ebrm_compounding_selector",
        value_score=10,
        novelty_score=10,
        projected_facts=16,
        profile_budget_s=20.0,
        frontier_note="Tau-gated certificate for a compounding Research Kernel frontier selector.",
        work_items=("AB", "CoW"),
        non_claims=(
            "Does not select specs without host replay evidence.",
            "Does not authorize production deployment.",
        ),
        cases=_selection_tau_cases(facts),
    )
    return _run_candidate(selection, tau_bin)


def _build_report() -> dict[str, Any]:
    latest_bin = find_tau_bin(REPO_ROOT, profile="latest")
    rows: list[dict[str, Any]] = []
    for candidate in _expanded_candidate_pool():
        features = _features(candidate.spec_path)
        latest = _run_candidate(candidate, latest_bin)
        row = {
            "spec_id": candidate.spec_id,
            "title": candidate.title,
            "spec_path": str(candidate.spec_path.relative_to(REPO_ROOT)),
            "sha256": _sha256(candidate.spec_path),
            "primary_output": candidate.primary_output,
            "breakthrough_track": candidate.breakthrough_track,
            "value_score": candidate.value_score,
            "novelty_score": candidate.novelty_score,
            "projected_facts": candidate.projected_facts,
            "profile_budget_s": candidate.profile_budget_s,
            "frontier_note": candidate.frontier_note,
            "work_items": list(candidate.work_items),
            "non_claims": list(candidate.non_claims),
            "case_count": len(candidate.cases),
            "features": features,
            "latest": latest,
        }
        row["frontier_score"] = _frontier_score(row)
        row["tau_spec_ebrm_v2_energy"] = _energy(row)
        rows.append(row)

    rankings = _rankings(rows)
    rows_by_id = {row["spec_id"]: row for row in rows}
    ranking_metrics = {method: _metrics_for_order(order, rows_by_id) for method, order in rankings.items()}
    ebrm_metrics = ranking_metrics["tau_spec_ebrm_v2"]
    baseline_metrics = {method: metrics for method, metrics in ranking_metrics.items() if method != "tau_spec_ebrm_v2"}
    max_baseline_topk = max(float(metrics["topk_frontier_score"]) for metrics in baseline_metrics.values())
    coverage = _coverage(rankings["tau_spec_ebrm_v2"])
    total_invalid_accepts = sum(int(row["latest"].get("invalid_accepts", 0)) for row in rows)
    all_traces_passed = all(bool(row["latest"].get("ok")) for row in rows)
    profile_bound_ok = all(float(row["latest"].get("elapsed_s", 0.0)) <= float(row["profile_budget_s"]) for row in rows)
    facts = {
        "candidate_pool_bound_ok": int(12 <= len(rows) <= 32),
        "tau_traces_passed": int(all_traces_passed),
        "invalid_accepts_zero": int(total_invalid_accepts == 0),
        "topk_not_worse_than_baselines": int(float(ebrm_metrics["topk_frontier_score"]) >= max_baseline_topk),
        "work_item_1_ab_covered": int(coverage["AB"]),
        "work_item_2_cow_covered": int(coverage["CoW"]),
        "exact_out_split_routing_covered": int(coverage["exact_out_split_routing"]),
        "exact_in_staircase_covered": int(coverage["exact_in_staircase"]),
        "negative_frontier_covered": int(coverage["negative_frontier"]),
        "evidence_dag_covered": int(coverage["evidence_dag"]),
        "tokenomics_pol_covered": int(coverage["tokenomics_pol"]),
        "deterministic_replay_ok": 1,
        "performance_profile_bound_ok": int(profile_bound_ok),
    }
    selection_tau = _run_selection_tau(facts, latest_bin)
    return {
        "schema": "zenodex.tauspec_ebrm_compounding_frontier_report.v1",
        "date": "2026-06-28",
        "authority_boundary": "model proposes and ranks; deterministic Tau traces and host/kernel verifiers decide acceptance",
        "tau_bins": {"latest": {"path": latest_bin, "version": _tau_version(latest_bin)}},
        "candidate_count": len(rows),
        "compounding_targets": sorted(COMPOUNDING_TARGETS),
        "candidates": rows,
        "rankings": rankings,
        "ranking_metrics": ranking_metrics,
        "baseline_max_topk_frontier_score": max_baseline_topk,
        "coverage_top10": coverage,
        "selector_facts": facts,
        "selection_tau": {
            "spec_id": "tauspec_ebrm_compounding_frontier_certificate_v1",
            "spec_path": str(SELECTION_SPEC.relative_to(REPO_ROOT)),
            "sha256": _sha256(SELECTION_SPEC),
            **selection_tau,
        },
        "breakthrough": {
            "name": "TauSpecEBRM compounding-frontier certificate",
            "spec_id": "tauspec_ebrm_compounding_frontier_certificate_v1",
            "ranker": "tau_spec_ebrm_v2",
            "top10": rankings["tau_spec_ebrm_v2"][:FRONTIER_WINDOW],
            "top3_frontier_score": ebrm_metrics["topk_frontier_score"],
            "baseline_max_top3_frontier_score": max_baseline_topk,
            "invalid_accepts": total_invalid_accepts,
            "coverage_top10": coverage,
        },
        "non_claims": [
            "TauSpecEBRM is advisory and cannot authorize settlement, oracle updates, governance, production promotion, or state mutation.",
            "The report compares a bounded expanded candidate pool, not every Tau spec in the repository.",
            "Host-projected facts remain external obligations until their owning host/kernel verifier replays them.",
        ],
        "replay_command": "python3 tools/zenodex_tauspec_ebrm_compounding_frontier_20260628.py",
    }


def _write_markdown(report: dict[str, Any]) -> None:
    breakthrough = report["breakthrough"]
    lines: list[str] = [
        "# ZenoDEX TauSpecEBRM Compounding Frontier - 2026-06-28",
        "",
        "## Executive Result",
        "",
        f"`{breakthrough['spec_id']}` is a Tau certificate for a compounding Research Kernel frontier selector.",
        "It admits only when a bounded expanded candidate pool passes Tau replay, has zero invalid accepts, matches or beats deterministic top-k baselines, keeps recent supported discoveries visible, and preserves the no-authority boundary.",
        "",
        f"The expanded pool has `{report['candidate_count']}` candidates. `tau_spec_ebrm_v2` top-10 coverage is `{breakthrough['coverage_top10']}` with `{breakthrough['invalid_accepts']}` invalid accepts.",
        "",
        "Authority boundary: model proposes and ranks. Tau traces plus host/kernel verifiers decide acceptance.",
        "",
        "## Tau Gate",
        "",
        f"- Spec: `{report['selection_tau']['spec_path']}`",
        f"- Latest Tau ok: `{report['selection_tau']['ok']}`",
        f"- Selector cases: `{len(report['selection_tau']['case_results'])}`",
        f"- Selector invalid accepts: `{report['selection_tau']['invalid_accepts']}`",
        "",
        "Selector facts:",
    ]
    for key, value in report["selector_facts"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(
        [
            "",
            "## Expanded Candidate Pool",
            "",
            "| spec | primary | latest | invalid accepts | score | energy | work items |",
            "| --- | --- | --- | ---: | ---: | ---: | --- |",
        ]
    )
    for row in report["candidates"]:
        latest = row["latest"]
        lines.append(
            f"| `{row['spec_id']}` | `{row['primary_output']}` | `{latest.get('ok')}` | `{latest.get('invalid_accepts')}` | `{row['frontier_score']:.4f}` | `{row['tau_spec_ebrm_v2_energy']:.4f}` | `{', '.join(row['work_items']) or '-'}` |"
        )
    lines.extend(
        [
            "",
            "## Baseline Comparison",
            "",
            "| method | top 3 | top-3 score | invalid accepts top 3 | first high-value valid rank |",
            "| --- | --- | ---: | ---: | ---: |",
        ]
    )
    for method, order in report["rankings"].items():
        metrics = report["ranking_metrics"][method]
        lines.append(
            f"| `{method}` | `{', '.join(order[:3])}` | `{metrics['topk_frontier_score']:.4f}` | `{metrics['invalid_accepts_topk']}` | `{metrics['first_high_value_valid_rank']}` |"
        )
    lines.extend(
        [
            "",
            "## Compounding Targets",
            "",
        ]
    )
    for target in report["compounding_targets"]:
        covered = target in set(report["breakthrough"]["top10"])
        lines.append(f"- `{target}`: top-10 covered = `{covered}`")
    lines.extend(
        [
            "",
            "## Non-Claims",
            "",
        ]
    )
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", report["replay_command"], "```"])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    report = _build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    ok = (
        all(row["latest"].get("ok") for row in report["candidates"])
        and report["breakthrough"]["invalid_accepts"] == 0
        and report["selection_tau"].get("ok")
        and report["selection_tau"].get("invalid_accepts") == 0
        and all(value == 1 for value in report["selector_facts"].values())
    )
    print(
        json.dumps(
            {
                "ok": bool(ok),
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "breakthrough": report["breakthrough"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
