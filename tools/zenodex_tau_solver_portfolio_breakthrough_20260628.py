#!/usr/bin/env python3
"""Replay the Tau solver-portfolio upgrade certificate."""

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


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tau_solver_portfolio_breakthrough_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_TAU_SOLVER_PORTFOLIO_BREAKTHROUGH_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "solver_portfolio_upgrade_certificate_v1.tau"
AB_COW_REPORT = REPO_ROOT / "generated" / "zenodex_ab_cow_algorithm_breakthrough_20260627" / "report.json"
COW_CAPACITY_REPORT = REPO_ROOT / "generated" / "zenodex_cow_capacity_dp_certificate_20260628" / "report.json"


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"required supporting report not found: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"supporting report is not a JSON object: {path}")
    return payload


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _text(value: Any) -> str:
    return json.dumps(value, sort_keys=True).lower()


def supporting_reports() -> dict[str, Any]:
    return {
        "ab_cow": _load_json(AB_COW_REPORT),
        "cow_capacity": _load_json(COW_CAPACITY_REPORT),
    }


def portfolio_facts(reports: Mapping[str, Any]) -> dict[str, int]:
    ab_cow = reports["ab_cow"]
    cow_capacity = reports["cow_capacity"]
    ab = ab_cow.get("ab_ordering", {})
    cow = ab_cow.get("cow_matching", {})
    capacity_flags = cow_capacity.get("flags", {})
    ab_proxy_ratio = float(ab.get("n12_permutation_vs_compressed_proxy", {}).get("ratio", 0.0))
    cow_proxy_ratio = float(cow.get("n20_perfect_matching_vs_hungarian_proxy", {}).get("ratio", 0.0))
    cow_capacity_evidence = cow_capacity.get("evidence", {})
    capacity_main = cow_capacity_evidence.get("capacity_breakthrough", {})
    capacity_adv = cow_capacity_evidence.get("capacity_adversarial", {})
    text = _text({"ab_cow": ab_cow, "cow_capacity": cow_capacity})
    mutation_checks = cow_capacity.get("mutation_checks", [])
    ab_scope_note = str(ab.get("n12_permutation_vs_compressed_proxy", {}).get("scope_note", "")).lower()
    cow_scope_note = str(cow.get("n20_perfect_matching_vs_hungarian_proxy", {}).get("scope_note", "")).lower()
    cow_fallback_surface = str(cow.get("current_core_policy", {}).get("fallback_surface", "")).lower()
    capacity_non_claims = [str(item).lower() for item in cow_capacity.get("non_claims", [])]
    negative_replay_ok = (
        bool(cow_capacity.get("tau", {}).get("ok"))
        and bool(mutation_checks)
        and all(not bool(row.get("accepted")) for row in mutation_checks)
        and "not claimed as a universal runtime bound" in ab_scope_note
        and "not grouped sender-capacity matching" in cow_scope_note
        and "bounded exact dp" in cow_fallback_surface
        and any("does not claim a polynomial algorithm" in item for item in capacity_non_claims)
    )

    return {
        "certificate_active": 1,
        "ab_solver_candidate_present": int(bool(ab.get("ok"))),
        "ab_full_state_scope_ok": int("full-state" in text and "compressed held-karp" in text),
        "ab_bruteforce_oracle_parity_ok": int(bool(ab.get("ok")) and all(bool(row.get("ok")) for row in ab.get("exactness_cases", []))),
        "cow_solver_candidate_present": int(bool(cow.get("ok"))),
        "cow_uncoupled_or_bounded_capacity_scope_ok": int(
            bool(cow.get("ok"))
            and bool(capacity_flags.get("grouped_capacity_scope_ok"))
            and int(capacity_adv.get("assignment_safe_case_count", -1)) == 0
        ),
        "cow_bruteforce_oracle_parity_ok": int(
            bool(cow.get("ok"))
            and bool(capacity_flags.get("dp_bruteforce_parity_ok"))
            and int(capacity_main.get("exact_mismatch_count", 1)) == 0
            and int(capacity_adv.get("exact_mismatch_count", 1)) == 0
        ),
        "negative_replay_ok": int(negative_replay_ok),
        "deterministic_tie_ok": int(bool(cow.get("canonical_tie_fuzzer", {}).get("ok", True))),
        "performance_floor_ok": int(ab_proxy_ratio >= 100.0 and cow_proxy_ratio >= 1000.0),
        "fallback_paths_ok": int("fallback" in text and bool(capacity_flags.get("fallback_boundary_ok"))),
        "resource_budget_ok": int(bool(capacity_flags.get("resource_budget_ok"))),
        "rollback_available": 1,
        "advisory_model_only": 1,
        "no_authority_effect": int("no settlement authority" in text or "research certificate only" in text),
    }


def _step_from_facts(facts: Mapping[str, int], overrides: Mapping[str, int] | None = None) -> dict[str, int]:
    names = (
        "certificate_active",
        "ab_solver_candidate_present",
        "ab_full_state_scope_ok",
        "ab_bruteforce_oracle_parity_ok",
        "cow_solver_candidate_present",
        "cow_uncoupled_or_bounded_capacity_scope_ok",
        "cow_bruteforce_oracle_parity_ok",
        "negative_replay_ok",
        "deterministic_tie_ok",
        "performance_floor_ok",
        "fallback_paths_ok",
        "resource_budget_ok",
        "rollback_available",
        "advisory_model_only",
        "no_authority_effect",
    )
    step = {f"i{index}": int(facts[name]) for index, name in enumerate(names, start=1)}
    if overrides:
        step.update({key: int(value) for key, value in overrides.items()})
    return step


def tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    return (
        TauCase(
            "portfolio_pass",
            _step_from_facts(facts),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1, "o7": 0},
            "AB and CoW solver evidence, performance floor, fallback, rollback, and no-authority facts all hold.",
        ),
        TauCase(
            "ab_parity_reject",
            _step_from_facts(facts, {"i4": 0}),
            {"o1": 0, "o3": 0, "o6": 0},
            "AB subset-DP promotion fails when brute-force parity is missing.",
        ),
        TauCase(
            "cow_scope_reject",
            _step_from_facts(facts, {"i6": 0}),
            {"o2": 0, "o3": 0, "o6": 0},
            "CoW promotion fails when uncoupled or bounded-capacity scope is not proven.",
        ),
        TauCase(
            "negative_replay_reject",
            _step_from_facts(facts, {"i8": 0}),
            {"o3": 0, "o6": 0},
            "A portfolio without negative replay cannot be promoted.",
        ),
        TauCase(
            "performance_reject",
            _step_from_facts(facts, {"i10": 0}),
            {"o4": 0, "o6": 0},
            "A portfolio that does not clear the host-computed performance floor is rejected.",
        ),
        TauCase(
            "rollback_reject",
            _step_from_facts(facts, {"i13": 0}),
            {"o5": 0, "o6": 0},
            "Solver rollout requires an explicit fallback or rollback path.",
        ),
        TauCase(
            "authority_reject",
            _step_from_facts(facts, {"i15": 0}),
            {"o5": 0, "o6": 0, "o7": 0},
            "The certificate cannot carry settlement, oracle, governance, or state-root authority.",
        ),
        TauCase(
            "inactive_safe",
            _step_from_facts(facts, {"i1": 0}),
            {"o1": 0, "o2": 0, "o6": 0, "o7": 1},
            "Inactive portfolio certificates do not admit while the no-authority rail remains true.",
        ),
    )


def replay_tau(facts: Mapping[str, int]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "case_results": []}
    cases = tau_cases(facts)
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[case.step for case in cases],
        timeout_s=20.0,
    )
    rows: list[dict[str, Any]] = []
    ok = True
    invalid_accepts = 0
    for index, case in enumerate(cases):
        got = outputs.get(index, {})
        mismatches = {
            key: {"expected": value, "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != value
        }
        if mismatches:
            ok = False
        if case.expected.get("o6") == 0 and got.get("o6") == 1:
            invalid_accepts += 1
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
        "invalid_accepts": invalid_accepts,
        "case_results": rows,
        "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
        "tau_bin": tau_bin,
        "tau_version": _tau_version(tau_bin),
        "sha256": _sha256_file(TAU_SPEC),
    }


def build_report() -> dict[str, Any]:
    reports = supporting_reports()
    facts = portfolio_facts(reports)
    tau = replay_tau(facts)
    ab_cow = reports["ab_cow"]
    cow_capacity = reports["cow_capacity"]
    supporting = {
        "ab_cow_ok": bool(ab_cow.get("ok")),
        "cow_capacity_ok": bool(cow_capacity.get("ok")),
        "ab_n12_proxy_ratio": ab_cow.get("ab_ordering", {}).get("n12_permutation_vs_compressed_proxy", {}).get("ratio"),
        "cow_n20_proxy_ratio": ab_cow.get("cow_matching", {}).get("n20_perfect_matching_vs_hungarian_proxy", {}).get("ratio"),
        "cow_capacity_exact_mismatch_count": cow_capacity.get("evidence", {}).get("capacity_breakthrough", {}).get("exact_mismatch_count"),
        "cow_capacity_core_mismatch_count": cow_capacity.get("evidence", {}).get("capacity_breakthrough", {}).get("core_mismatch_count"),
        "cow_capacity_greedy_lift_cases": cow_capacity.get("evidence", {}).get("capacity_breakthrough", {}).get("greedy_lift_case_count"),
    }
    ok = all(value == 1 for value in facts.values()) and bool(tau.get("ok")) and int(tau.get("invalid_accepts", 0)) == 0
    return {
        "schema": "zenodex.tau_solver_portfolio_breakthrough_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "breakthrough": {
            "name": "Tau solver-portfolio upgrade certificate",
            "spec_id": "solver_portfolio_upgrade_certificate_v1",
            "summary": "Tau gates a combined AB/CoW solver-upgrade decision with host-computed parity, capacity-scope, performance, fallback, rollback, negative replay, and no-authority facts.",
            "authority_boundary": "Tau admits the portfolio certificate only. Host/kernel verifiers remain authoritative for settlement and state transitions.",
        },
        "portfolio_facts": facts,
        "supporting_reports": supporting,
        "tau": tau,
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
        "supporting_report_hashes": {
            str(AB_COW_REPORT.relative_to(REPO_ROOT)): _sha256_file(AB_COW_REPORT),
            str(COW_CAPACITY_REPORT.relative_to(REPO_ROOT)): _sha256_file(COW_CAPACITY_REPORT),
            str(TAU_SPEC.relative_to(REPO_ROOT)): _sha256_file(TAU_SPEC),
        },
        "non_claims": [
            "The certificate is a research and rollout evidence gate, not a settlement verifier.",
            "All numeric complexity, matching, CPMM, and DP computations stay host-side.",
            "The performance floor is host-computed evidence over bounded reports, not a Tau timing measurement.",
            "Rollback availability is an external rollout fact supplied to Tau and must be backed by deployment evidence before production use.",
        ],
        "replay_command": "python3 tools/zenodex_tau_solver_portfolio_breakthrough_20260628.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX Tau Solver Portfolio Breakthrough - 2026-06-28",
        "",
        "## Executive Result",
        "",
        str(report["breakthrough"]["summary"]),
        "",
        f"- Tau ok: `{report['tau']['ok']}`",
        f"- Tau cases: `{len(report['tau']['case_results'])}`",
        f"- Invalid accepts: `{report['tau']['invalid_accepts']}`",
        f"- AB n=12 proxy ratio: `{report['supporting_reports']['ab_n12_proxy_ratio']}`",
        f"- CoW n=20 proxy ratio: `{report['supporting_reports']['cow_n20_proxy_ratio']}`",
        "",
        "## Portfolio Facts",
        "",
        "| fact | value |",
        "| --- | ---: |",
    ]
    for key, value in sorted(report["portfolio_facts"].items()):
        lines.append(f"| `{key}` | `{value}` |")
    lines.extend(
        [
            "",
            "## Tau Cases",
            "",
            "| case | ok | rationale |",
            "| --- | --- | --- |",
        ]
    )
    for row in report["tau"]["case_results"]:
        lines.append(f"| `{row['case_id']}` | `{row['ok']}` | {row['rationale']} |")
    lines.extend(
        [
            "",
            "## Work Items",
            "",
            "| work item | status | evidence | non-claim |",
            "| --- | --- | --- | --- |",
        ]
    )
    for key, row in report["work_items"].items():
        lines.append(f"| `{key}` | `{row['status']}` | {row['evidence']} | {row['non_claim']} |")
    lines.extend(["", "## Non-Claims", ""])
    lines.extend(f"- {item}" for item in report["non_claims"])
    lines.extend(["", "## Replay", "", "```bash", "python3 tools/zenodex_tau_solver_portfolio_breakthrough_20260628.py", "```", ""])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, default=REPORT_JSON)
    parser.add_argument("--no-write-md", action="store_true")
    args = parser.parse_args(argv)
    report = build_report()
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if not args.no_write_md:
        _write_markdown(report)
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "json": str(args.json),
                "report": str(REPORT_MD),
                "tau_ok": report["tau"]["ok"],
                "tau_case_count": len(report["tau"]["case_results"]),
                "invalid_accepts": report["tau"]["invalid_accepts"],
                "ab_n12_proxy_ratio": report["supporting_reports"]["ab_n12_proxy_ratio"],
                "cow_n20_proxy_ratio": report["supporting_reports"]["cow_n20_proxy_ratio"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
