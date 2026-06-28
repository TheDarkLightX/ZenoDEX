#!/usr/bin/env python3
"""Replay the Tau solver-portfolio upgrade certificate breakthrough."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from tools.zenodex_ab_cow_algorithm_breakthrough_20260627 import (  # noqa: E402
    _build_report as build_ab_cow_report,
)
from tools.zenodex_cow_capacity_dp_breakthrough_20260627 import (  # noqa: E402
    build_report as build_cow_capacity_report,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tau_solver_portfolio_breakthrough_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_TAU_SOLVER_PORTFOLIO_BREAKTHROUGH_20260628.md"
SPEC_PATH = REPO_ROOT / "src" / "tau_specs" / "recommended" / "solver_portfolio_upgrade_certificate_v1.tau"


@dataclass(frozen=True)
class TauTraceCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _negative_replay_ok(ab_cow: dict[str, Any]) -> bool:
    cases = ab_cow["tau_envelope"]["cases"]
    rejected = [
        case
        for case in cases
        if case["ok"] and int(case["expected"].get("o6", 1)) == 0 and int(case["got"].get("o6", 1)) == 0
    ]
    return len(rejected) >= 2


def _portfolio_facts(ab_cow: dict[str, Any], cow_capacity: dict[str, Any]) -> dict[str, int]:
    ab = ab_cow["ab_ordering"]
    cow = ab_cow["cow_matching"]
    ab_proxy = ab["n12_permutation_vs_compressed_proxy"]
    cow_proxy = cow["n20_perfect_matching_vs_hungarian_proxy"]

    ab_parity = bool(ab["ok"] and all(case["ok"] for case in ab["exactness_cases"]) and ab["measured_n8"]["same_order"])
    cow_parity = bool(
        cow["ok"]
        and all(case["ok"] and case["same_pair_id_tie"] for case in cow["exactness_cases"])
        and cow["canonical_tie_fuzzer"]["mismatch_count"] == 0
    )
    cow_capacity_scope = bool(
        cow["current_core_policy"]["assignment_surface"] == "uncoupled sender balances"
        and "bounded exact DP" in cow["current_core_policy"]["fallback_surface"]
        and cow_capacity["ok"]
        and cow_capacity["exact_mismatch_count"] == 0
        and cow_capacity["core_mismatch_count"] == 0
    )
    performance_floor = bool(
        float(ab_proxy["ratio"]) >= 100.0
        and float(cow_proxy["ratio"]) >= 1_000_000.0
        and int(cow_capacity["greedy_lift_case_count"]) > 0
    )
    return {
        "certificate_active": 1,
        "ab_solver_candidate_present": int(bool(ab["ok"])),
        "cow_solver_candidate_present": int(bool(cow["ok"])),
        "ab_bruteforce_oracle_parity_ok": int(ab_parity),
        "cow_bruteforce_oracle_parity_ok": int(cow_parity),
        "ab_full_state_scope_ok": int(
            ab["current_core_policy"]["state"]
            == "processed set + directional reserves + per-sender remaining balances"
            and int(ab["current_core_policy"]["fallback_after"]) == 12
        ),
        "cow_uncoupled_or_bounded_capacity_scope_ok": int(cow_capacity_scope),
        "negative_replay_ok": int(_negative_replay_ok(ab_cow)),
        "deterministic_tie_ok": int(cow["canonical_tie_fuzzer"]["mismatch_count"] == 0),
        "performance_floor_ok": int(performance_floor),
        "resource_budget_ok": int(bool(ab_cow["ok"] and cow_capacity["ok"] and ab_cow["tau_envelope"]["ok"])),
        "fallback_paths_ok": int(
            int(ab["current_core_policy"]["fallback_after"]) == 12
            and "greedy/fail-closed" in cow["current_core_policy"]["fallback_surface"]
            and "not a polynomial algorithm" in " ".join(cow_capacity["non_claims"])
        ),
        "rollback_available": 1,
        "advisory_model_only": 1,
        "no_authority_effect": 1,
    }


def _step_from_facts(facts: dict[str, int]) -> dict[str, int]:
    ordered_names = [
        "certificate_active",
        "ab_solver_candidate_present",
        "cow_solver_candidate_present",
        "ab_bruteforce_oracle_parity_ok",
        "cow_bruteforce_oracle_parity_ok",
        "ab_full_state_scope_ok",
        "cow_uncoupled_or_bounded_capacity_scope_ok",
        "negative_replay_ok",
        "deterministic_tie_ok",
        "performance_floor_ok",
        "resource_budget_ok",
        "fallback_paths_ok",
        "rollback_available",
        "advisory_model_only",
        "no_authority_effect",
    ]
    return {f"i{idx}": int(facts[name]) for idx, name in enumerate(ordered_names, start=1)}


def _tau_cases(facts: dict[str, int]) -> tuple[TauTraceCase, ...]:
    pass_step = _step_from_facts(facts)
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauTraceCase(
            "portfolio_pass",
            pass_step,
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1, "o7": 0},
            "AB and CoW solver evidence, performance floor, fallback, rollback, and no-authority facts all hold.",
        ),
        TauTraceCase(
            "ab_parity_reject",
            {**pass_step, "i4": 0},
            {"o1": 0, "o3": 0, "o6": 0},
            "AB subset-DP promotion fails when brute-force parity is missing.",
        ),
        TauTraceCase(
            "cow_scope_reject",
            {**pass_step, "i7": 0},
            {"o2": 0, "o3": 0, "o6": 0},
            "CoW promotion fails when uncoupled or bounded-capacity scope is not proven.",
        ),
        TauTraceCase(
            "negative_replay_reject",
            {**pass_step, "i8": 0},
            {"o3": 0, "o6": 0},
            "A portfolio without negative replay cannot be promoted.",
        ),
        TauTraceCase(
            "performance_reject",
            {**pass_step, "i10": 0},
            {"o4": 0, "o6": 0},
            "A portfolio that does not clear the host-computed performance floor is rejected.",
        ),
        TauTraceCase(
            "rollback_reject",
            {**pass_step, "i13": 0},
            {"o5": 0, "o6": 0},
            "Solver rollout requires an explicit fallback or rollback path.",
        ),
        TauTraceCase(
            "authority_reject",
            {**pass_step, "i15": 0},
            {"o5": 0, "o6": 0, "o7": 0},
            "The certificate cannot carry settlement, oracle, governance, or state-root authority.",
        ),
        TauTraceCase(
            "inactive_safe",
            inactive,
            {"o1": 0, "o2": 0, "o6": 0, "o7": 1},
            "Inactive portfolio certificates do not admit while the no-authority rail remains true.",
        ),
    )


def _run_tau(facts: dict[str, int], tau_bin: str | None) -> dict[str, Any]:
    cases = _tau_cases(facts)
    if not tau_bin:
        return {
            "ok": False,
            "error": "latest Tau binary not found",
            "case_results": [],
            "invalid_accepts": 0,
        }
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC_PATH,
        steps=[case.step for case in cases],
        timeout_s=15.0,
    )
    invalid_accepts = 0
    case_results: list[dict[str, Any]] = []
    ok = True
    for index, case in enumerate(cases):
        got = {str(key): int(value) for key, value in outputs.get(index, {}).items()}
        mismatches = {
            key: {"expected": int(value), "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != int(value)
        }
        expected_primary = int(case.expected.get("o6", 0))
        if expected_primary == 0 and got.get("o6") == 1:
            invalid_accepts += 1
        if mismatches:
            ok = False
        case_results.append(
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
        "ok": ok and invalid_accepts == 0,
        "case_results": case_results,
        "invalid_accepts": invalid_accepts,
    }


def _build_report() -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    ab_cow = build_ab_cow_report()
    cow_capacity = build_cow_capacity_report()
    facts = _portfolio_facts(ab_cow, cow_capacity)
    tau = _run_tau(facts, tau_bin)
    ok = bool(all(value == 1 for value in facts.values()) and tau["ok"])
    return {
        "schema": "zenodex.tau_solver_portfolio_breakthrough_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "breakthrough": {
            "name": "Tau solver-portfolio upgrade certificate",
            "spec_id": "solver_portfolio_upgrade_certificate_v1",
            "summary": "Tau now gates a combined AB/CoW solver-upgrade decision with host-computed parity, capacity-scope, performance, fallback, rollback, negative replay, and no-authority facts.",
            "authority_boundary": "Tau admits the portfolio certificate only. Host/kernel verifiers remain authoritative for settlement and state transitions.",
        },
        "tau": {
            "spec_path": str(SPEC_PATH.relative_to(REPO_ROOT)),
            "sha256": _sha256(SPEC_PATH),
            "tau_bin": tau_bin,
            "tau_version": _tau_version(tau_bin),
            **tau,
        },
        "portfolio_facts": facts,
        "work_items": {
            "1_ab_ordering": {
                "status": "covered",
                "evidence": "bounded full-state subset DP with brute-force parity and explicit fallback after 12",
                "non_claim": "The certificate does not claim a compressed Held-Karp state is sound for integer CPMM ordering.",
            },
            "2_cow_matching": {
                "status": "covered",
                "evidence": "uncoupled Hungarian assignment plus bounded coupled-capacity DP evidence",
                "non_claim": "The certificate does not claim arbitrary grouped-capacity CoW matching is polynomial.",
            },
        },
        "supporting_reports": {
            "ab_cow_ok": ab_cow["ok"],
            "cow_capacity_ok": cow_capacity["ok"],
            "ab_n12_proxy_ratio": ab_cow["ab_ordering"]["n12_permutation_vs_compressed_proxy"]["ratio"],
            "cow_n20_proxy_ratio": ab_cow["cow_matching"]["n20_perfect_matching_vs_hungarian_proxy"]["ratio"],
            "cow_capacity_greedy_lift_cases": cow_capacity["greedy_lift_case_count"],
            "cow_capacity_exact_mismatch_count": cow_capacity["exact_mismatch_count"],
            "cow_capacity_core_mismatch_count": cow_capacity["core_mismatch_count"],
        },
        "new_tau_spec_patterns": [
            {
                "pattern": "solver_portfolio_upgrade_certificate",
                "benefit": "Promotes AB and CoW algorithm upgrades only when independent solver evidence and rollout rails agree.",
            },
            {
                "pattern": "negative_knowledge_gate",
                "benefit": "Turns known failed simplifications into reject bits before they become public or production claims.",
            },
            {
                "pattern": "performance_floor_gate",
                "benefit": "Lets host-computed complexity evidence participate in Tau admission without putting timing arithmetic inside Tau.",
            },
            {
                "pattern": "advisory_model_boundary_gate",
                "benefit": "Keeps EBRM or research selectors in proposal/ranking mode while deterministic verifiers decide acceptance.",
            },
        ],
        "non_claims": [
            "The certificate is a research and rollout evidence gate, not a settlement verifier.",
            "All numeric complexity, matching, CPMM, and DP computations stay host-side.",
            "The performance floor is host-computed evidence over bounded reports, not a Tau timing measurement.",
            "Rollback availability is an external rollout fact supplied to Tau and must be backed by deployment evidence before production use.",
        ],
        "replay_command": "python3 tools/zenodex_tau_solver_portfolio_breakthrough_20260628.py",
    }


def _write_markdown(report: dict[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Tau Solver Portfolio Breakthrough - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(report["breakthrough"]["summary"])
    lines.append("")
    lines.append(report["breakthrough"]["authority_boundary"])
    lines.append("")
    lines.append("## Tau Specification")
    lines.append("")
    tau = report["tau"]
    lines.append(f"- Spec: `{tau['spec_path']}`")
    lines.append(f"- Latest Tau: `{tau.get('tau_version')}`")
    lines.append(f"- Tau cases: `{len(tau['case_results'])}`")
    lines.append(f"- Invalid accepts: `{tau['invalid_accepts']}`")
    lines.append("")
    lines.append("## Portfolio Facts")
    lines.append("")
    for key, value in report["portfolio_facts"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.append("")
    lines.append("## Work Items")
    lines.append("")
    lines.append("### 1. AB Ordering")
    lines.append("")
    lines.append(report["work_items"]["1_ab_ordering"]["evidence"])
    lines.append(report["work_items"]["1_ab_ordering"]["non_claim"])
    lines.append("")
    lines.append("### 2. CoW Matching")
    lines.append("")
    lines.append(report["work_items"]["2_cow_matching"]["evidence"])
    lines.append(report["work_items"]["2_cow_matching"]["non_claim"])
    lines.append("")
    lines.append("## New Tau Specification Patterns")
    lines.append("")
    for item in report["new_tau_spec_patterns"]:
        lines.append(f"- `{item['pattern']}`: {item['benefit']}")
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(report["replay_command"])
    lines.append("```")
    lines.append("")
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    report = _build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "tau_cases": len(report["tau"]["case_results"]),
                "invalid_accepts": report["tau"]["invalid_accepts"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
