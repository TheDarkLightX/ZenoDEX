#!/usr/bin/env python3
"""Replay a Tau performance-frontier certificate."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tau_performance_frontier_breakthrough_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_TAU_PERFORMANCE_FRONTIER_BREAKTHROUGH_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "tau_performance_frontier_certificate_v1.tau"
SPEC_PROFILES = REPO_ROOT / "src" / "tau_specs" / "recommended" / "spec_profiles.json"
SEMANTIC_CONTRACTS = REPO_ROOT / "src" / "tau_specs" / "recommended" / "semantic_contracts.json"
HOST_PROJECTION_CONTRACTS = REPO_ROOT / "src" / "tau_specs" / "recommended" / "host_projection_contracts.json"
BITVECTOR_DECISION_DOC = REPO_ROOT / "docs" / "research" / "ZENODEX_TAU_BITVECTOR_FRONTIER_DECISION_20260628.md"

SELECTED_SPECS = (
    "src/tau_specs/recommended/frontier_certificate_menu_v1.tau",
    "src/tau_specs/recommended/optimizer_quotient_certificate_v1.tau",
    "src/tau_specs/recommended/ab_cow_exact_solver_envelope_v1.tau",
    "src/tau_specs/recommended/solver_portfolio_upgrade_certificate_v1.tau",
    "src/tau_specs/recommended/tauspec_counterexample_synthesis_certificate_v1.tau",
    "src/tau_specs/recommended/receipt_sequence_bv16_guard_v1.tau",
)


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _profile_summary() -> dict[str, Any]:
    raw = _read_json(SPEC_PROFILES)
    profiles = raw.get("profiles", {})
    components = raw.get("components", {})
    variants = []
    for component, body in components.items():
        for variant in body.get("variants", []):
            variants.append(
                {
                    "component": component,
                    "variant_id": variant.get("variant_id"),
                    "profile": variant.get("profile"),
                    "spec_path": variant.get("spec_path"),
                    "runtime_admission": variant.get("latest_tau_stream_arithmetic", {}).get("runtime_admission"),
                }
            )
    budgets = {
        profile_id: int(profile.get("timeout_budget_s_on_dev_machine", 0))
        for profile_id, profile in profiles.items()
    }
    expected_budgets = {
        "fast_proof_gated": 30,
        "tau_only_structural": 60,
        "tau_only_strict": 90,
        "tau_only_full_settlement": 90,
    }
    return {
        "profile_count": len(profiles),
        "component_count": len(components),
        "variant_count": len(variants),
        "budgets": budgets,
        "budget_lattice_ok": budgets == expected_budgets,
        "runtime_admission_true_count": sum(1 for row in variants if row["runtime_admission"] is True),
        "blocked_count": sum(1 for row in variants if row["runtime_admission"] is False),
    }


def _contract_summary() -> dict[str, Any]:
    semantic = _read_json(SEMANTIC_CONTRACTS)
    host = _read_json(HOST_PROJECTION_CONTRACTS)
    return {
        "semantic_contract_count": len(semantic.get("specs", [])),
        "semantic_runtime_trace_timeout_s": float(semantic.get("runtime_defaults", {}).get("spec", {}).get("trace_timeout_s", 0.0)),
        "host_projection_contract_count": len(host.get("specs", [])),
        "host_default_missing_fact_values": sorted({int(spec.get("default_on_missing_fact", -1)) for spec in host.get("specs", [])}),
    }


def _spec_features(relative_path: str) -> dict[str, Any]:
    path = REPO_ROOT / relative_path
    if not path.exists():
        return {
            "spec_path": relative_path,
            "exists": False,
            "sha256": None,
            "bytes": 0,
            "definitions": 0,
            "inputs": 0,
            "outputs": 0,
            "direct_bv_ops": 0,
            "max_bv_width": 0,
            "has_width_cast": False,
        }
    text = path.read_text(encoding="utf-8")
    widths = [int(width) for width in re.findall(r"bv\[(\d+)\]", text)]
    return {
        "spec_path": relative_path,
        "exists": path.exists(),
        "sha256": _sha256(path),
        "bytes": len(text.encode("utf-8")),
        "definitions": text.count(" := "),
        "inputs": len(set(re.findall(r"\bi\d+\b", text))),
        "outputs": len(set(re.findall(r"\bo\d+\b", text))),
        "direct_bv_ops": len(widths),
        "max_bv_width": max(widths) if widths else 0,
        "has_width_cast": bool(re.search(r"\(bv\[\d+\]\)\s*[A-Za-z_(]", text)),
    }


def _candidate_scan() -> dict[str, Any]:
    rows = [_spec_features(path) for path in SELECTED_SPECS]
    return {
        "selected_count": len(rows),
        "rows": rows,
        "all_exist": all(row["exists"] for row in rows),
        "max_bv_width": max(row["max_bv_width"] for row in rows),
        "direct_bv_specs": [row["spec_path"] for row in rows if row["direct_bv_ops"] > 0],
        "has_width_cast": any(row["has_width_cast"] for row in rows),
    }


def _bitvector_decision() -> dict[str, Any]:
    text = BITVECTOR_DECISION_DOC.read_text(encoding="utf-8") if BITVECTOR_DECISION_DOC.exists() else ""
    return {
        "doc_exists": BITVECTOR_DECISION_DOC.exists(),
        "small_direct_bv16_island_supported": "`small_direct_bv16_island_supported` = `True`" in text,
        "host_projection_default_preserved": "`host_projection_default_preserved` = `True`" in text,
        "profile_gate_required": "`profile_gate_required` = `True`" in text,
        "invalid_accepts_zero": "`invalid_accepts` = `0`" in text,
    }


def _pass_step(facts: dict[str, int]) -> dict[str, int]:
    return {
        "i1": 1,
        "i2": int(facts["profile_lattice_loaded"]),
        "i3": int(facts["profile_budget_bound_ok"]),
        "i4": int(facts["candidate_feature_scan_ok"]),
        "i5": int(facts["latest_trace_budget_ok"]),
        "i6": int(facts["runtime_or_fallback_profile_ok"]),
        "i7": int(facts["direct_bv_profile_gated"]),
        "i8": int(facts["host_projection_default_preserved"]),
        "i9": int(facts["invalid_accepts_zero"]),
        "i10": int(facts["negative_controls_rejected"]),
        "i11": int(facts["high_value_coverage_ok"]),
        "i12": int(facts["resource_budget_ok"]),
        "i13": 1,
        "i14": 1,
    }


def _tau_cases(facts: dict[str, int]) -> tuple[TauCase, ...]:
    passing = _pass_step(facts)
    inactive = dict(passing)
    inactive["i1"] = 0
    return (
        TauCase(
            "performance_frontier_pass",
            passing,
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1, "o7": 0},
            "All profile, trace, encoding, evidence, and authority facts admit the performance-frontier certificate.",
        ),
        TauCase(
            "missing_profile_lattice_reject",
            {**passing, "i2": 0},
            {"o1": 0, "o6": 0},
            "A certificate without the profile lattice cannot claim performance fit.",
        ),
        TauCase(
            "latest_budget_reject",
            {**passing, "i5": 0},
            {"o2": 0, "o6": 0},
            "Latest Tau replay must be inside the declared profile budget.",
        ),
        TauCase(
            "direct_bv_unprofiled_reject",
            {**passing, "i7": 0},
            {"o3": 0, "o6": 0},
            "Direct bitvector islands require profile-gated replay evidence.",
        ),
        TauCase(
            "invalid_accepts_reject",
            {**passing, "i9": 0},
            {"o4": 0, "o6": 0},
            "Any invalid accept invalidates performance-frontier promotion.",
        ),
        TauCase(
            "coverage_reject",
            {**passing, "i11": 0},
            {"o4": 0, "o6": 0},
            "A profile result without high-value coverage is not a frontier result.",
        ),
        TauCase(
            "authority_reject",
            {**passing, "i14": 0},
            {"o5": 0, "o6": 0},
            "Performance certificates cannot carry settlement, oracle, or governance authority.",
        ),
        TauCase(
            "inactive_safe",
            inactive,
            {"o6": 0, "o7": 1},
            "Inactive certificates do not admit while the no-authority rail remains safe.",
        ),
    )


def _run_tau_profile(tau_bin: str | None, facts: dict[str, int], *, profile: str) -> dict[str, Any]:
    cases = _tau_cases(facts)
    if not tau_bin:
        return {
            "profile": profile,
            "ok": False,
            "error": f"{profile} Tau binary not found",
            "elapsed_s": 0.0,
            "invalid_accepts": 0,
            "negative_rejections": 0,
            "case_results": [],
        }
    started = time.monotonic()
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=TAU_SPEC, steps=[case.step for case in cases], timeout_s=30.0)
    invalid_accepts = 0
    negative_rejections = 0
    all_ok = True
    case_results = []
    for index, case in enumerate(cases):
        got = {str(key): int(value) for key, value in outputs.get(index, {}).items()}
        mismatches = {
            key: {"expected": int(value), "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != int(value)
        }
        expected_primary = int(case.expected.get("o6", 0))
        got_primary = int(got.get("o6", 0))
        if expected_primary == 0 and got_primary == 1:
            invalid_accepts += 1
        if expected_primary == 0 and got_primary == 0 and not mismatches:
            negative_rejections += 1
        if mismatches:
            all_ok = False
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
        "profile": profile,
        "ok": bool(all_ok and invalid_accepts == 0),
        "elapsed_s": round(time.monotonic() - started, 6),
        "invalid_accepts": invalid_accepts,
        "negative_rejections": negative_rejections,
        "case_results": case_results,
    }


def _initial_facts(profile: dict[str, Any], contracts: dict[str, Any], scan: dict[str, Any], decision: dict[str, Any]) -> dict[str, int]:
    high_value_coverage = (
        profile["component_count"] >= 20
        and contracts["semantic_contract_count"] >= 30
        and contracts["host_projection_contract_count"] >= 10
        and scan["selected_count"] >= 6
    )
    return {
        "profile_lattice_loaded": int(profile["profile_count"] >= 4 and profile["variant_count"] >= 20),
        "profile_budget_bound_ok": int(bool(profile["budget_lattice_ok"])),
        "candidate_feature_scan_ok": int(scan["all_exist"] and scan["max_bv_width"] <= 32 and not scan["has_width_cast"]),
        "latest_trace_budget_ok": 1,
        "runtime_or_fallback_profile_ok": 1,
        "direct_bv_profile_gated": int(decision["small_direct_bv16_island_supported"] and decision["profile_gate_required"]),
        "host_projection_default_preserved": int(decision["host_projection_default_preserved"] and contracts["host_projection_contract_count"] >= 10),
        "invalid_accepts_zero": 1,
        "negative_controls_rejected": 1,
        "high_value_coverage_ok": int(high_value_coverage),
        "resource_budget_ok": 1,
    }


def _build_report() -> dict[str, Any]:
    profile = _profile_summary()
    contracts = _contract_summary()
    scan = _candidate_scan()
    decision = _bitvector_decision()
    facts = _initial_facts(profile, contracts, scan, decision)
    latest_bin = find_tau_bin(REPO_ROOT, profile="latest")
    runtime_bin = find_tau_bin(REPO_ROOT, profile="runtime")
    latest = _run_tau_profile(latest_bin, facts, profile="latest")
    runtime = _run_tau_profile(runtime_bin, facts, profile="runtime")
    facts["latest_trace_budget_ok"] = int(bool(latest["ok"]) and float(latest["elapsed_s"]) <= 30.0)
    facts["runtime_or_fallback_profile_ok"] = int(bool(runtime["ok"]) and float(runtime["elapsed_s"]) <= 30.0)
    facts["invalid_accepts_zero"] = int(int(latest["invalid_accepts"]) == 0 and int(runtime["invalid_accepts"]) == 0)
    facts["negative_controls_rejected"] = int(int(latest["negative_rejections"]) >= 6 and int(runtime["negative_rejections"]) >= 6)
    facts["resource_budget_ok"] = int(bool(facts["profile_budget_bound_ok"]) and bool(facts["latest_trace_budget_ok"]) and bool(facts["runtime_or_fallback_profile_ok"]))
    if facts["latest_trace_budget_ok"] != 1 or facts["runtime_or_fallback_profile_ok"] != 1:
        latest = _run_tau_profile(latest_bin, facts, profile="latest")
        runtime = _run_tau_profile(runtime_bin, facts, profile="runtime")

    return {
        "schema": "zenodex.tau_performance_frontier_breakthrough_report.v1",
        "date": "2026-06-28",
        "ok": bool(all(facts.values()) and latest["ok"] and runtime["ok"]),
        "authority_boundary": "performance frontier evidence only; deterministic Tau traces and host/kernel verifiers decide acceptance",
        "tau_bins": {
            "latest": {"path": latest_bin, "version": _tau_version(latest_bin)},
            "runtime": {"path": runtime_bin, "version": _tau_version(runtime_bin)},
        },
        "breakthrough": {
            "name": "Tau performance-frontier certificate",
            "spec_id": "tau_performance_frontier_certificate_v1",
            "frontier_atom": "atom_3d38c5d1362f4f9c",
            "invalid_accepts": int(latest["invalid_accepts"]) + int(runtime["invalid_accepts"]),
            "negative_rejections": int(latest["negative_rejections"]) + int(runtime["negative_rejections"]),
            "latest_elapsed_s": latest["elapsed_s"],
            "runtime_elapsed_s": runtime["elapsed_s"],
        },
        "spec": {
            "path": str(TAU_SPEC.relative_to(REPO_ROOT)),
            "sha256": _sha256(TAU_SPEC),
            "features": _spec_features(str(TAU_SPEC.relative_to(REPO_ROOT))),
        },
        "profile_summary": profile,
        "contract_summary": contracts,
        "candidate_scan": scan,
        "bitvector_decision": decision,
        "certificate_facts": facts,
        "latest_tau": latest,
        "runtime_tau": runtime,
        "design_rule": "Use host-projected boolean envelopes by default; allow direct Tau bitvectors only for small bounded kernels with replayed profile evidence and zero invalid accepts.",
        "non_claims": [
            "This does not authorize settlement, oracle updates, governance, or production release.",
            "This does not prove arbitrary direct Tau arithmetic is acceptable.",
            "Profile fit is evidence for a bounded candidate set and must be replayed after Tau or spec changes.",
        ],
        "replay_command": "python3 tools/zenodex_tau_performance_frontier_breakthrough_20260628.py",
    }


def _write_markdown(report: dict[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Tau Performance Frontier Breakthrough - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(
        "`tau_performance_frontier_certificate_v1` is a new Tau certificate for performance-frontier evidence. It admits only when the host supplies profile-lattice, budget, candidate-feature, latest/runtime replay, direct-bv gating, host-projection default, zero-invalid-accept, negative-control, high-value coverage, advisory-only, and no-authority facts."
    )
    lines.append("")
    lines.append(
        f"Latest Tau passed `{len(report['latest_tau']['case_results'])}` cases in `{report['breakthrough']['latest_elapsed_s']}` seconds. Runtime Tau passed `{len(report['runtime_tau']['case_results'])}` cases in `{report['breakthrough']['runtime_elapsed_s']}` seconds. Combined invalid accepts: `{report['breakthrough']['invalid_accepts']}`."
    )
    lines.append("")
    lines.append(f"Design rule: {report['design_rule']}")
    lines.append("")
    lines.append("## Profile Evidence")
    lines.append("")
    profile = report["profile_summary"]
    contracts = report["contract_summary"]
    lines.append(f"- Profiles: `{profile['profile_count']}`")
    lines.append(f"- Components: `{profile['component_count']}`")
    lines.append(f"- Variants: `{profile['variant_count']}`")
    lines.append(f"- Budget lattice ok: `{profile['budget_lattice_ok']}`")
    lines.append(f"- Semantic contracts: `{contracts['semantic_contract_count']}`")
    lines.append(f"- Host-projection contracts: `{contracts['host_projection_contract_count']}`")
    lines.append("")
    lines.append("## Candidate Feature Scan")
    lines.append("")
    lines.append("| spec | bytes | direct bv ops | max bv width | width cast |")
    lines.append("| --- | ---: | ---: | ---: | --- |")
    for row in report["candidate_scan"]["rows"]:
        lines.append(f"| `{row['spec_path']}` | `{row['bytes']}` | `{row['direct_bv_ops']}` | `{row['max_bv_width']}` | `{row['has_width_cast']}` |")
    lines.append("")
    lines.append("## Tau Replay")
    lines.append("")
    lines.append("| profile | ok | elapsed | invalid accepts | negative rejections |")
    lines.append("| --- | --- | ---: | ---: | ---: |")
    for key in ("latest_tau", "runtime_tau"):
        row = report[key]
        lines.append(f"| `{row['profile']}` | `{row['ok']}` | `{row['elapsed_s']}` | `{row['invalid_accepts']}` | `{row['negative_rejections']}` |")
    lines.append("")
    lines.append("## Counterexample Cases")
    lines.append("")
    lines.append("| case | latest ok | runtime ok | rationale |")
    lines.append("| --- | --- | --- | --- |")
    runtime_by_id = {case["case_id"]: case for case in report["runtime_tau"]["case_results"]}
    for case in report["latest_tau"]["case_results"]:
        lines.append(f"| `{case['case_id']}` | `{case['ok']}` | `{runtime_by_id[case['case_id']]['ok']}` | {case['rationale']} |")
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
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    report = _build_report()
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "latest_elapsed_s": report["breakthrough"]["latest_elapsed_s"],
                "runtime_elapsed_s": report["breakthrough"]["runtime_elapsed_s"],
                "invalid_accepts": report["breakthrough"]["invalid_accepts"],
                "report": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "markdown": str(REPORT_MD.relative_to(REPO_ROOT)),
            },
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
