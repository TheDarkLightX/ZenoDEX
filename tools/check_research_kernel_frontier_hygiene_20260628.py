#!/usr/bin/env python3
"""Build a local receipt that maps stale Research Kernel frontier items to closures."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = REPO_ROOT / "generated" / "zenodex_research_kernel_frontier_hygiene_20260628"
REPORT_JSON = OUT_DIR / "report.json"


class ReceiptError(ValueError):
    """Raised when a local closure receipt cannot be trusted."""


@dataclass(frozen=True)
class ClosureSpec:
    closure_id: str
    frontier_atom_id: str
    frontier_status: str
    closure_kind: str
    summary: str
    resolver_artifacts: tuple[str, ...]
    report_path: str
    replay_command: tuple[str, ...]
    validator: Callable[[Mapping[str, Any]], dict[str, Any]]


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _repo_path(path: str) -> Path:
    full = (REPO_ROOT / path).resolve()
    if full != REPO_ROOT and REPO_ROOT not in full.parents:
        raise ReceiptError(f"path escapes repo: {path}")
    return full


def _require_tracked(path: str) -> dict[str, str]:
    full = _repo_path(path)
    if not full.exists():
        raise ReceiptError(f"missing artifact: {path}")
    proc = subprocess.run(
        ["git", "ls-files", "--error-unmatch", path],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise ReceiptError(f"artifact is not tracked by git: {path}")
    return {"path": path, "sha256": _sha256(full)}


def _load_report(path: str) -> dict[str, Any]:
    full = _repo_path(path)
    if not full.exists():
        raise ReceiptError(f"missing generated report: {path}")
    data = json.loads(full.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ReceiptError(f"generated report is not an object: {path}")
    return data


def _require(condition: bool, reason: str, checks: dict[str, Any]) -> None:
    checks[reason] = bool(condition)
    if not condition:
        raise ReceiptError(reason)


def _all_flags_true(flags: Mapping[str, Any]) -> bool:
    return bool(flags) and all(value == 1 or value is True for value in flags.values())


def _all_mutations_rejected(rows: Sequence[Mapping[str, Any]]) -> bool:
    return bool(rows) and all(row.get("accepted") is False for row in rows)


def _validate_exact_scheduler(report: Mapping[str, Any]) -> dict[str, Any]:
    checks: dict[str, Any] = {}
    _require(report.get("schema") == "zenodex.negative_frontier_exact_scheduler_report.v1", "schema_ok", checks)
    _require(report.get("ok") is True, "report_ok", checks)
    _require(report.get("tau", {}).get("ok") is True, "tau_ok", checks)
    _require(_all_flags_true(report.get("flags", {})), "flags_all_true", checks)
    _require(_all_mutations_rejected(report.get("mutation_checks", [])), "mutations_rejected", checks)
    _require(report.get("total_combinations", 0) >= 10_000, "exact_search_nontrivial", checks)
    _require(report.get("scenario_count", 0) >= 6, "scenario_count_ok", checks)
    _require(
        all(row.get("exact_search_complete") is True for row in report.get("scenarios", [])),
        "all_scenarios_complete",
        checks,
    )
    strict = report.get("strict_dominance_counts", {})
    _require(strict.get("greedy", 0) >= 3, "greedy_strict_wins_ok", checks)
    _require(strict.get("recency", 0) >= 3, "recency_strict_wins_ok", checks)
    _require(strict.get("stable_random", 0) >= 3, "stable_random_strict_wins_ok", checks)
    return checks


def _validate_route_split(report: Mapping[str, Any]) -> dict[str, Any]:
    checks: dict[str, Any] = {}
    _require(report.get("schema") == "zenodex.route_split_window_adversarial_report.v1", "schema_ok", checks)
    _require(report.get("ok") is True, "report_ok", checks)
    _require(report.get("tau", {}).get("ok") is True, "tau_ok", checks)
    _require(report.get("case_count", 0) >= 20, "hostile_case_count_ok", checks)
    _require(report.get("mismatch_count") == 0, "oracle_mismatch_zero", checks)
    _require(
        report.get("naive_first_difference_monotonicity_failure_count", 0) >= 20,
        "negative_knowledge_nonvacuous",
        checks,
    )
    _require(report.get("min_quote_call_reduction_ratio", 0.0) > 3.0, "quote_reduction_floor_ok", checks)
    _require(_all_mutations_rejected(report.get("mutation_checks", [])), "mutations_rejected", checks)
    return checks


def _validate_cpss_scope(report: Mapping[str, Any]) -> dict[str, Any]:
    checks: dict[str, Any] = {}
    _require(report.get("schema") == "zenodex.cpss_bc_research_scope_certificate_report.v1", "schema_ok", checks)
    _require(report.get("tau", {}).get("ok") is True, "tau_ok", checks)
    _require(report.get("tau", {}).get("invalid_accepts") == 0, "tau_invalid_accepts_zero", checks)
    _require(report.get("lean", {}).get("compile_ok") is True, "lean_compile_ok", checks)
    _require(report.get("lean", {}).get("no_forbidden_tokens") is True, "lean_no_forbidden_tokens", checks)
    _require(len(report.get("lean", {}).get("files", [])) >= 5, "lean_file_count_ok", checks)
    _require(_all_flags_true(report.get("facts", {})), "facts_all_true", checks)
    non_claims = "\n".join(str(item) for item in report.get("non_claims", []))
    _require("group strategyproofness" in non_claims, "group_sp_nonclaim_present", checks)
    _require("universal CPSS greedy dominance" in non_claims, "greedy_dominance_nonclaim_present", checks)
    return checks


def _validate_ab_dominance(report: Mapping[str, Any]) -> dict[str, Any]:
    checks: dict[str, Any] = {}
    _require(report.get("schema") == "zenodex.ab_subset_dp_dominance_certificate_report.v1", "schema_ok", checks)
    _require(report.get("ok") is True, "report_ok", checks)
    _require(report.get("tau", {}).get("ok") is True, "tau_ok", checks)
    _require(_all_flags_true(report.get("flags", {})), "flags_all_true", checks)
    _require(_all_mutations_rejected(report.get("mutation_checks", [])), "mutations_rejected", checks)
    evidence = report.get("evidence", {})
    parity = evidence.get("parity_reduction", {}).get("aggregate_reductions", {})
    adversarial = evidence.get("adversarial_corpus", {}).get("summary", {})
    boundary = evidence.get("boundary_refuter", {})
    _require(parity.get("state_insertion", 0.0) > 10.0, "state_reduction_nonvacuous", checks)
    _require(adversarial.get("case_count", 0) >= 30, "adversarial_case_count_ok", checks)
    _require(boundary.get("exact_out_counterexample_found") is True, "exact_out_boundary_refuted", checks)
    _require(boundary.get("mixed_direction_counterexample_found") is True, "mixed_direction_boundary_refuted", checks)
    return checks


def _validate_cow_capacity(report: Mapping[str, Any]) -> dict[str, Any]:
    checks: dict[str, Any] = {}
    _require(report.get("schema") == "zenodex.cow_capacity_dp_certificate_report.v1", "schema_ok", checks)
    _require(report.get("ok") is True, "report_ok", checks)
    _require(report.get("tau", {}).get("ok") is True, "tau_ok", checks)
    _require(_all_flags_true(report.get("flags", {})), "flags_all_true", checks)
    _require(_all_mutations_rejected(report.get("mutation_checks", [])), "mutations_rejected", checks)
    evidence = report.get("evidence", {})
    breakthrough = evidence.get("capacity_breakthrough", {})
    adversarial = evidence.get("capacity_adversarial", {})
    envelope = evidence.get("shared_ab_cow_envelope", {})
    _require(breakthrough.get("exact_mismatch_count") == 0, "exact_mismatch_zero", checks)
    _require(breakthrough.get("core_mismatch_count") == 0, "core_mismatch_zero", checks)
    _require(breakthrough.get("greedy_lift_case_count", 0) >= 5, "greedy_lift_nonvacuous", checks)
    _require(adversarial.get("case_count", 0) >= 20, "adversarial_case_count_ok", checks)
    _require(adversarial.get("greedy_lift_case_count", 0) >= 10, "adversarial_lift_nonvacuous", checks)
    _require(envelope.get("tau_ok") is True, "shared_envelope_tau_ok", checks)
    return checks


def closure_specs() -> tuple[ClosureSpec, ...]:
    return (
        ClosureSpec(
            closure_id="negative_frontier_exact_scheduler_closes_entropy_refutation",
            frontier_atom_id="atom_db8d68413cd34328",
            frontier_status="UNDER_TEST",
            closure_kind="resolves",
            summary=(
                "Exact bounded scheduler replay closes the entropy-scheduler refutation risk by exhaustive "
                "subset selection, deterministic replay, baseline dominance, mutation rejection, and no-authority facts."
            ),
            resolver_artifacts=(
                "tools/check_negative_frontier_exact_scheduler.py",
                "tests/tau/test_negative_frontier_exact_scheduler_20260628.py",
                "src/tau_specs/recommended/negative_frontier_exact_scheduler_v1.tau",
                "docs/research/ZENODEX_NEGATIVE_FRONTIER_EXACT_SCHEDULER_20260628.md",
            ),
            report_path="generated/zenodex_negative_frontier_exact_scheduler_20260628/report.json",
            replay_command=("python3", "tools/check_negative_frontier_exact_scheduler.py"),
            validator=_validate_exact_scheduler,
        ),
        ClosureSpec(
            closure_id="route_split_hostile_corpus_bounds_tau_ablation_risk",
            frontier_atom_id="atom_2d749c2ecd2e4c9a",
            frontier_status="UNDER_TEST",
            closure_kind="bounds",
            summary=(
                "Route split-window hostile replay bounds the Tau ablation risk with 24 oracle-parity cases, "
                "explicit negative knowledge for naive discrete convexity, mutation rejection, and no settlement authority."
            ),
            resolver_artifacts=(
                "tools/check_route_split_window_adversarial.py",
                "tests/tau/test_route_split_window_adversarial_20260628.py",
                "src/tau_specs/recommended/route_split_window_certificate_v1.tau",
                "docs/research/ZENODEX_ROUTE_SPLIT_WINDOW_ADVERSARIAL_20260628.md",
            ),
            report_path="generated/zenodex_route_split_window_adversarial_20260628/report.json",
            replay_command=("python3", "tools/check_route_split_window_adversarial.py"),
            validator=_validate_route_split,
        ),
        ClosureSpec(
            closure_id="cpss_scope_certificate_closes_scope_audit_risk",
            frontier_atom_id="atom_86d2810ce9ad4b50",
            frontier_status="UNDER_TEST",
            closure_kind="resolves",
            summary=(
                "CPSS-BC scope certificate closes the scope-audit risk by requiring Lean compile evidence, "
                "forbidden-token scans, scoped formal claims, falsification records, and no-authority facts."
            ),
            resolver_artifacts=(
                "tools/zenodex_cpss_bc_research_scope_certificate_20260628.py",
                "tests/tau/test_zenodex_cpss_bc_research_scope_certificate_20260628.py",
                "src/tau_specs/recommended/cpss_bc_research_scope_certificate_v1.tau",
                "docs/research/ZENODEX_CPSS_BC_RESEARCH_SCOPE_CERTIFICATE_20260628.md",
                "lean-mathlib/Proofs/CompressedStateSubsetDP.lean",
                "lean-mathlib/Proofs/CommitRevealStrategyproof.lean",
                "lean-mathlib/Proofs/CommitRevealBothParamsSP.lean",
                "lean-mathlib/Proofs/WindowBound.lean",
                "lean-mathlib/Proofs/StrongConcavityWindowBound.lean",
            ),
            report_path="generated/zenodex_cpss_bc_research_scope_certificate_20260628/report.json",
            replay_command=("python3", "tools/zenodex_cpss_bc_research_scope_certificate_20260628.py"),
            validator=_validate_cpss_scope,
        ),
        ClosureSpec(
            closure_id="ab_dominance_certificate_bounds_held_karp_candidate",
            frontier_atom_id="atom_28ea53e1ebcc4f97",
            frontier_status="CANDIDATE",
            closure_kind="bounds",
            summary=(
                "AB subset-DP dominance certificate upgrades the Held-Karp candidate into a scoped boundary: "
                "same-pool same-direction exact-in dominance is supported, while exact-out and mixed-direction "
                "extensions are explicitly refuted."
            ),
            resolver_artifacts=(
                "tools/check_ab_subset_dp_dominance_certificate.py",
                "tests/tau/test_ab_subset_dp_dominance_certificate_20260628.py",
                "src/tau_specs/recommended/ab_subset_dp_dominance_certificate_v1.tau",
                "docs/research/ZENODEX_AB_SUBSET_DP_DOMINANCE_CERTIFICATE_20260628.md",
            ),
            report_path="generated/zenodex_ab_subset_dp_dominance_certificate_20260628/report.json",
            replay_command=("python3", "tools/check_ab_subset_dp_dominance_certificate.py"),
            validator=_validate_ab_dominance,
        ),
        ClosureSpec(
            closure_id="cow_capacity_dp_certificate_extends_matching_frontier",
            frontier_atom_id="cow_capacity_grouped_frontier_20260628",
            frontier_status="SUPPORTED_LOCAL",
            closure_kind="supports",
            summary=(
                "CoW capacity-DP certificate records the boundary beyond uncoupled Hungarian assignment: bounded "
                "grouped-capacity cases are solved by exact DP with brute-force parity and adversarial greedy-lift checks."
            ),
            resolver_artifacts=(
                "tools/check_cow_capacity_dp_certificate.py",
                "tests/tau/test_cow_capacity_dp_certificate_20260628.py",
                "src/tau_specs/recommended/cow_capacity_dp_certificate_v1.tau",
                "docs/research/ZENODEX_COW_CAPACITY_DP_CERTIFICATE_20260628.md",
            ),
            report_path="generated/zenodex_cow_capacity_dp_certificate_20260628/report.json",
            replay_command=("python3", "tools/check_cow_capacity_dp_certificate.py"),
            validator=_validate_cow_capacity,
        ),
    )


def _rk_edge_type_for(spec: ClosureSpec) -> str:
    if spec.frontier_status == "UNDER_TEST":
        return "SUPERSEDES"
    if spec.frontier_status == "CANDIDATE":
        return "SPECIALIZES"
    return "SUPPORTS"


def _refresh_reports(specs: Sequence[ClosureSpec]) -> None:
    seen: set[tuple[str, ...]] = set()
    for spec in specs:
        if spec.replay_command in seen:
            continue
        seen.add(spec.replay_command)
        proc = subprocess.run(
            list(spec.replay_command),
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
            timeout=180,
        )
        if proc.returncode != 0:
            raise ReceiptError(
                f"refresh failed for {' '.join(spec.replay_command)}\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
            )


def build_report(*, refresh: bool = False) -> dict[str, Any]:
    specs = closure_specs()
    if refresh:
        _refresh_reports(specs)

    closures: list[dict[str, Any]] = []
    for spec in specs:
        artifacts = [_require_tracked(path) for path in spec.resolver_artifacts]
        report = _load_report(spec.report_path)
        checks = spec.validator(report)
        closures.append(
            {
                "closure_id": spec.closure_id,
                "frontier_atom_id": spec.frontier_atom_id,
                "frontier_status": spec.frontier_status,
                "closure_kind": spec.closure_kind,
                "summary": spec.summary,
                "resolver_artifacts": artifacts,
                "report_path": spec.report_path,
                "report_sha256": _sha256(_repo_path(spec.report_path)),
                "replay_command": " ".join(spec.replay_command),
                "checks": checks,
                "closed": all(checks.values()),
            }
        )

    stale_risks = [row for row in closures if row["frontier_status"] == "UNDER_TEST"]
    report = {
        "schema": "zenodex.research_kernel_frontier_hygiene.v1",
        "date": "2026-06-28",
        "ok": bool(closures) and all(row["closed"] for row in closures),
        "closure_count": len(closures),
        "stale_risk_closure_count": len(stale_risks),
        "resolved_count": sum(1 for row in closures if row["closure_kind"] == "resolves"),
        "bounded_count": sum(1 for row in closures if row["closure_kind"] == "bounds"),
        "supported_local_count": sum(1 for row in closures if row["closure_kind"] == "supports"),
        "closures": closures,
        "research_kernel_edges_to_add": [
            {
                "source_atom_id": "atom_zenodex_research_kernel_frontier_hygiene_20260628",
                "target_atom_id": row["frontier_atom_id"],
                "edge_type": _rk_edge_type_for(
                    next(spec for spec in specs if spec.frontier_atom_id == row["frontier_atom_id"])
                ),
                "closure_kind": row["closure_kind"],
                "rationale": row["summary"],
            }
            for row in closures
            if row["frontier_atom_id"].startswith("atom_")
        ],
        "non_claims": [
            "This receipt does not mutate Research Kernel frontier ranking by itself; explicit RK edges are required.",
            "This receipt does not rerun every underlying proof by default; use --refresh to rebuild prerequisite reports.",
            "This receipt records research-evidence closure only and grants no settlement, governance, state-root, or production authority.",
            "Generated report JSON files are replay outputs; tracked source artifacts and replay commands are the durable evidence handles.",
        ],
        "replay_command": "python3 tools/check_research_kernel_frontier_hygiene_20260628.py",
        "refresh_command": "python3 tools/check_research_kernel_frontier_hygiene_20260628.py --refresh",
    }
    if not report["ok"]:
        raise ReceiptError("one or more closure rows failed")
    return report


def write_report(report: Mapping[str, Any]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh", action="store_true", help="rebuild prerequisite generated reports before checking")
    parser.add_argument("--json-only", action="store_true", help="suppress human summary output")
    args = parser.parse_args(list(argv) if argv is not None else None)

    try:
        report = build_report(refresh=args.refresh)
        write_report(report)
    except ReceiptError as exc:
        print(f"research-kernel frontier hygiene check failed: {exc}", file=sys.stderr)
        return 1

    if not args.json_only:
        print(json.dumps({"ok": report["ok"], "closure_count": report["closure_count"]}, indent=2, sort_keys=True))
        print(f"wrote {REPORT_JSON.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
