#!/usr/bin/env python3
"""Replay the perps risk-antichain certificate breakthrough."""

from __future__ import annotations

import json
import subprocess
import sys
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from tools.check_perp_risk_envelope_containment_v1 import (  # noqa: E402
    _evaluate_risk_envelope,
    check_perp_risk_envelope_containment_v1,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_perp_risk_antichain_breakthrough_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_PERP_RISK_ANTICHAIN_BREAKTHROUGH_20260628.md"
ANTICHAIN_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "perp_risk_antichain_certificate_v1.tau"
RISK_ENVELOPE_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "perp_risk_envelope_proof_gate_v1.tau"


PRIMITIVE_AXES = (
    "mark_oracle_gap_bad",
    "mark_drift_bad",
    "oracle_drift_bad",
    "open_interest_cap_bad",
    "funding_cap_bad",
    "liq_penalty_cap_bad",
    "insurance_floor_bad",
    "stale_oracle_flag",
    "breaker_active_flag",
    "margin_bad",
    "proof_missing",
    "binding_missing",
)

OVERALL_MINIMAL_REJECT_AXES = (
    "mark_oracle_gap_bad",
    "mark_drift_bad",
    "oracle_drift_bad",
    "open_interest_cap_bad",
    "funding_cap_bad",
    "liq_penalty_cap_bad",
    "insurance_floor_bad",
    "margin_bad",
    "proof_missing",
    "binding_missing",
)

COMPONENT_BOUNDARY = {
    "o1_mark_oracle_gap": (("mark_oracle_gap_bad",),),
    "o2_mark_drift": (("mark_drift_bad",),),
    "o3_oracle_drift": (("oracle_drift_bad",),),
    "o4_open_interest_cap": (("open_interest_cap_bad",),),
    "o5_funding_cap": (("funding_cap_bad",),),
    "o6_liq_penalty_cap": (("liq_penalty_cap_bad",),),
    "o7_insurance_floor": (("insurance_floor_bad",),),
    "o8_stale_guard": (("proof_missing", "stale_oracle_flag"),),
    "o9_breaker_guard": (("breaker_active_flag", "proof_missing"),),
    "o10_margin_guard": (("margin_bad",),),
}


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]


def _powerset(items: tuple[str, ...]) -> Iterable[frozenset[str]]:
    for size in range(len(items) + 1):
        for combo in combinations(items, size):
            yield frozenset(combo)


def _risk_outputs(active_axes: frozenset[str]) -> dict[str, bool]:
    proof_ok = "proof_missing" not in active_axes
    binding_ok = "binding_missing" not in active_axes
    mark_oracle_gap_ok = "mark_oracle_gap_bad" not in active_axes
    mark_drift_ok = "mark_drift_bad" not in active_axes
    oracle_drift_ok = "oracle_drift_bad" not in active_axes
    oi_cap_ok = "open_interest_cap_bad" not in active_axes
    funding_cap_ok = "funding_cap_bad" not in active_axes
    liq_penalty_cap_ok = "liq_penalty_cap_bad" not in active_axes
    insurance_floor_ok = "insurance_floor_bad" not in active_axes
    stale_guard_ok = ("stale_oracle_flag" not in active_axes) or proof_ok
    breaker_guard_ok = ("breaker_active_flag" not in active_axes) or proof_ok
    margin_guard_ok = "margin_bad" not in active_axes
    risk_envelope_ok = bool(
        mark_oracle_gap_ok
        and mark_drift_ok
        and oracle_drift_ok
        and oi_cap_ok
        and funding_cap_ok
        and liq_penalty_cap_ok
        and insurance_floor_ok
        and stale_guard_ok
        and breaker_guard_ok
        and margin_guard_ok
        and proof_ok
        and binding_ok
    )
    return {
        "mark_oracle_gap_ok": mark_oracle_gap_ok,
        "mark_drift_ok": mark_drift_ok,
        "oracle_drift_ok": oracle_drift_ok,
        "oi_cap_ok": oi_cap_ok,
        "funding_cap_ok": funding_cap_ok,
        "liq_penalty_cap_ok": liq_penalty_cap_ok,
        "insurance_floor_ok": insurance_floor_ok,
        "stale_guard_ok": stale_guard_ok,
        "breaker_guard_ok": breaker_guard_ok,
        "margin_guard_ok": margin_guard_ok,
        "risk_envelope_ok": risk_envelope_ok,
    }


def _lattice_report() -> dict[str, Any]:
    states = list(_powerset(PRIMITIVE_AXES))
    outcomes = {state: _risk_outputs(state)["risk_envelope_ok"] for state in states}
    monotonicity_violations: list[dict[str, list[str]]] = []
    for lower in states:
        if outcomes[lower]:
            continue
        for upper in states:
            if lower < upper and outcomes[upper]:
                monotonicity_violations.append({"lower": sorted(lower), "upper": sorted(upper)})

    minimal_rejects = []
    for state in states:
        if outcomes[state]:
            continue
        proper_subsets = [frozenset(subset) for subset in _powerset(tuple(state)) if frozenset(subset) != state]
        if all(outcomes[subset] for subset in proper_subsets):
            minimal_rejects.append(tuple(sorted(state)))
    expected = tuple((axis,) for axis in OVERALL_MINIMAL_REJECT_AXES)
    minimal_ok = tuple(sorted(minimal_rejects)) == tuple(sorted(expected))

    component_ok = True
    component_rows: list[dict[str, Any]] = []
    for output_id, boundaries in COMPONENT_BOUNDARY.items():
        normalized = tuple(tuple(sorted(boundary)) for boundary in boundaries)
        for boundary in normalized:
            active = frozenset(boundary)
            outputs = _risk_outputs(active)
            key = output_id.split("_", 1)[1] + "_ok"
            if output_id.startswith("o1_"):
                key = "mark_oracle_gap_ok"
            elif output_id.startswith("o2_"):
                key = "mark_drift_ok"
            elif output_id.startswith("o3_"):
                key = "oracle_drift_ok"
            elif output_id.startswith("o4_"):
                key = "oi_cap_ok"
            elif output_id.startswith("o5_"):
                key = "funding_cap_ok"
            elif output_id.startswith("o6_"):
                key = "liq_penalty_cap_ok"
            elif output_id.startswith("o7_"):
                key = "insurance_floor_ok"
            elif output_id.startswith("o8_"):
                key = "stale_guard_ok"
            elif output_id.startswith("o9_"):
                key = "breaker_guard_ok"
            elif output_id.startswith("o10_"):
                key = "margin_guard_ok"
            rejected = outputs[key] is False
            component_ok = component_ok and rejected
            component_rows.append({"output_id": output_id, "boundary": list(boundary), "rejects": rejected})

    proof_dominates = (
        ("stale_oracle_flag",) not in minimal_rejects
        and ("breaker_active_flag",) not in minimal_rejects
        and ("proof_missing",) in minimal_rejects
        and _risk_outputs(frozenset({"stale_oracle_flag"}))["risk_envelope_ok"] is True
        and _risk_outputs(frozenset({"breaker_active_flag"}))["risk_envelope_ok"] is True
        and _risk_outputs(frozenset({"proof_missing"}))["risk_envelope_ok"] is False
    )

    return {
        "primitive_axis_count": len(PRIMITIVE_AXES),
        "dense_state_count": len(states),
        "accepted_state_count": sum(1 for ok in outcomes.values() if ok),
        "rejected_state_count": sum(1 for ok in outcomes.values() if not ok),
        "overall_minimal_reject_count": len(minimal_rejects),
        "overall_minimal_rejects": [list(row) for row in sorted(minimal_rejects)],
        "expected_overall_minimal_rejects": [list(row) for row in sorted(expected)],
        "component_boundary_count": sum(len(v) for v in COMPONENT_BOUNDARY.values()),
        "component_boundaries": component_rows,
        "monotonicity_ok": not monotonicity_violations,
        "monotonicity_violations": monotonicity_violations[:10],
        "overall_antichain_minimal_ok": minimal_ok,
        "component_antichain_coverage_ok": component_ok,
        "proof_dominates_stale_breaker_ok": proof_dominates,
        "compression_ratio_dense_to_overall_antichain": f"{len(states)}:{len(minimal_rejects)}",
    }


def _base_witness() -> dict[str, Any]:
    return {
        "mark_price_e8": 1_000_000,
        "oracle_price_e8": 1_000_000,
        "prev_mark_price_e8": 1_000_000,
        "prev_oracle_price_e8": 1_000_000,
        "open_interest": 100,
        "max_open_interest": 100,
        "funding_abs_bps": 10,
        "funding_cap_bps": 10,
        "liq_penalty_bps": 50,
        "liq_penalty_cap_bps": 50,
        "insurance_balance": 1_000,
        "insurance_floor": 1_000,
        "stale_oracle_flag": False,
        "breaker_active_flag": False,
        "proof_ok": True,
        "binding_ok": True,
        "has_open_positions": True,
        "margin_ratio_bps": 600,
        "maint_margin_bps": 500,
        "max_mark_oracle_gap_abs": 100,
        "max_mark_drift_abs": 100,
        "max_oracle_drift_abs": 100,
    }


def _witness_for_axis(axis: str) -> dict[str, Any]:
    witness = dict(_base_witness())
    if axis == "mark_oracle_gap_bad":
        witness["mark_price_e8"] = witness["oracle_price_e8"] + witness["max_mark_oracle_gap_abs"] + 1
        witness["prev_mark_price_e8"] = witness["mark_price_e8"]
    elif axis == "mark_drift_bad":
        witness["mark_price_e8"] = witness["prev_mark_price_e8"] + witness["max_mark_drift_abs"] + 1
        witness["oracle_price_e8"] = witness["mark_price_e8"]
        witness["prev_oracle_price_e8"] = witness["oracle_price_e8"]
    elif axis == "oracle_drift_bad":
        witness["oracle_price_e8"] = witness["prev_oracle_price_e8"] + witness["max_oracle_drift_abs"] + 1
        witness["mark_price_e8"] = witness["oracle_price_e8"]
        witness["prev_mark_price_e8"] = witness["mark_price_e8"]
    elif axis == "open_interest_cap_bad":
        witness["open_interest"] = witness["max_open_interest"] + 1
    elif axis == "funding_cap_bad":
        witness["funding_abs_bps"] = witness["funding_cap_bps"] + 1
    elif axis == "liq_penalty_cap_bad":
        witness["liq_penalty_bps"] = witness["liq_penalty_cap_bps"] + 1
    elif axis == "insurance_floor_bad":
        witness["insurance_balance"] = witness["insurance_floor"] - 1
    elif axis == "margin_bad":
        witness["margin_ratio_bps"] = witness["maint_margin_bps"] - 1
    elif axis == "proof_missing":
        witness["proof_ok"] = False
    elif axis == "binding_missing":
        witness["binding_ok"] = False
    elif axis == "stale_oracle_flag":
        witness["stale_oracle_flag"] = True
    elif axis == "breaker_active_flag":
        witness["breaker_active_flag"] = True
    else:
        raise ValueError(f"unknown axis: {axis}")
    return witness


def _step_from_witness(witness: Mapping[str, Any]) -> dict[str, int]:
    keys = (
        "mark_price_e8",
        "oracle_price_e8",
        "prev_mark_price_e8",
        "prev_oracle_price_e8",
        "open_interest",
        "max_open_interest",
        "funding_abs_bps",
        "funding_cap_bps",
        "liq_penalty_bps",
        "liq_penalty_cap_bps",
        "insurance_balance",
        "insurance_floor",
        "stale_oracle_flag",
        "breaker_active_flag",
        "proof_ok",
        "binding_ok",
        "has_open_positions",
        "margin_ratio_bps",
        "maint_margin_bps",
        "max_mark_oracle_gap_abs",
        "max_mark_drift_abs",
        "max_oracle_drift_abs",
    )
    step: dict[str, int] = {}
    for index, key in enumerate(keys, start=1):
        value = witness[key]
        step[f"i{index}"] = int(value) if not isinstance(value, bool) else int(value)
    return step


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _antichain_tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    pass_step = {
        "i1": 1,
        "i2": int(facts["dense_lattice_enumerated"]),
        "i3": int(facts["monotonicity_ok"]),
        "i4": int(facts["overall_antichain_minimal_ok"]),
        "i5": int(facts["component_antichain_coverage_ok"]),
        "i6": int(facts["containment_replay_ok"]),
        "i7": int(facts["tau_risk_envelope_parity_ok"]),
        "i8": int(facts["proof_dominates_stale_breaker_ok"]),
        "i9": int(facts["resource_budget_ok"]),
        "i10": 1,
        "i11": 1,
    }
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauCase("antichain_certificate_pass", pass_step, {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 0}),
        TauCase("monotonicity_reject", {**pass_step, "i3": 0}, {"o1": 0, "o5": 0}),
        TauCase("minimal_antichain_reject", {**pass_step, "i4": 0}, {"o2": 0, "o5": 0}),
        TauCase("component_coverage_reject", {**pass_step, "i5": 0}, {"o2": 0, "o5": 0}),
        TauCase("containment_replay_reject", {**pass_step, "i6": 0}, {"o3": 0, "o5": 0}),
        TauCase("tau_parity_reject", {**pass_step, "i7": 0}, {"o3": 0, "o5": 0}),
        TauCase("proof_domination_reject", {**pass_step, "i8": 0}, {"o2": 0, "o5": 0}),
        TauCase("authority_reject", {**pass_step, "i11": 0}, {"o4": 0, "o5": 0}),
        TauCase("inactive_safe", inactive, {"o5": 0, "o6": 1}),
    )


def _run_tau_cases(tau_bin: str | None, spec_path: Path, cases: tuple[TauCase, ...], *, timeout_s: float) -> dict[str, Any]:
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "spec_path": str(spec_path.relative_to(REPO_ROOT)), "cases": []}
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=[case.step for case in cases], timeout_s=timeout_s)
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
        "spec_path": str(spec_path.relative_to(REPO_ROOT)),
        "cases": out_cases,
        "case_count": len(cases),
        "invalid_accepts": invalid_accepts,
    }


def _risk_envelope_tau_check(tau_bin: str | None) -> dict[str, Any]:
    cases = (
        TauCase("risk_envelope_pass", _step_from_witness(_base_witness()), {"o11": 1}),
        TauCase("mark_gap_reject", _step_from_witness(_witness_for_axis("mark_oracle_gap_bad")), {"o1": 0, "o11": 0}),
        TauCase("margin_reject", _step_from_witness(_witness_for_axis("margin_bad")), {"o10": 0, "o11": 0}),
        TauCase("binding_reject", _step_from_witness(_witness_for_axis("binding_missing")), {"o11": 0}),
    )
    return _run_tau_cases(tau_bin, RISK_ENVELOPE_SPEC, cases, timeout_s=20.0)


def _numeric_boundary_check() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    ok = True
    for axis in OVERALL_MINIMAL_REJECT_AXES:
        result = _evaluate_risk_envelope(**_witness_for_axis(axis))
        rejects = result["risk_envelope_ok"] is False
        ok = ok and rejects
        rows.append({"axis": axis, "risk_envelope_ok": result["risk_envelope_ok"], "rejects": rejects})
    stale_only = _evaluate_risk_envelope(**_witness_for_axis("stale_oracle_flag"))
    breaker_only = _evaluate_risk_envelope(**_witness_for_axis("breaker_active_flag"))
    return {
        "ok": ok and stale_only["risk_envelope_ok"] is True and breaker_only["risk_envelope_ok"] is True,
        "minimal_axis_rows": rows,
        "stale_only_risk_envelope_ok": stale_only["risk_envelope_ok"],
        "breaker_only_risk_envelope_ok": breaker_only["risk_envelope_ok"],
    }


def build_report() -> dict[str, Any]:
    lattice = _lattice_report()
    containment = check_perp_risk_envelope_containment_v1()
    numeric = _numeric_boundary_check()
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    risk_tau = _risk_envelope_tau_check(tau_bin)
    facts = {
        "dense_lattice_enumerated": int(lattice["dense_state_count"] == 2 ** len(PRIMITIVE_AXES)),
        "monotonicity_ok": int(lattice["monotonicity_ok"]),
        "overall_antichain_minimal_ok": int(lattice["overall_antichain_minimal_ok"] and numeric["ok"]),
        "component_antichain_coverage_ok": int(lattice["component_antichain_coverage_ok"]),
        "containment_replay_ok": int(containment["ok"]),
        "tau_risk_envelope_parity_ok": int(risk_tau["ok"]),
        "proof_dominates_stale_breaker_ok": int(lattice["proof_dominates_stale_breaker_ok"]),
        "resource_budget_ok": int(lattice["dense_state_count"] <= 4096 and lattice["overall_minimal_reject_count"] <= 16),
    }
    antichain_tau = _run_tau_cases(tau_bin, ANTICHAIN_SPEC, _antichain_tau_cases(facts), timeout_s=20.0)
    ok = bool(
        all(value == 1 for value in facts.values())
        and antichain_tau["ok"]
        and risk_tau["ok"]
        and numeric["ok"]
        and containment["ok"]
    )
    return {
        "schema": "zenodex.perp_risk_antichain_breakthrough_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "breakthrough": {
            "name": "Perps risk-antichain certificate",
            "summary": "A bounded primitive perps risk lattice compresses from dense scenario replay to a minimal rejection antichain while Tau gates only the host-replayed certificate facts.",
            "authority_boundary": "Research certificate only. Tau has no settlement, liquidation, oracle-update, or state-root authority.",
        },
        "tau": {
            "tau_bin": tau_bin,
            "tau_version": _tau_version(tau_bin),
            "antichain_certificate": antichain_tau,
            "risk_envelope_direct": risk_tau,
        },
        "facts": facts,
        "lattice": lattice,
        "numeric_boundary": numeric,
        "containment_replay": containment,
        "non_claims": [
            "This does not change perps runtime risk-gate semantics.",
            "The antichain is over the declared bounded primitive-risk lattice, not every possible perps market state.",
            "Tau does not compute numeric risk, enumerate states, liquidate positions, settle funding, or update oracles.",
            "Proof availability and binding remain host-supplied obligations.",
        ],
        "replay_command": "python3 tools/zenodex_perp_risk_antichain_breakthrough_20260628.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Perps Risk Antichain Breakthrough - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(str(report["breakthrough"]["summary"]))
    lines.append("")
    lines.append(str(report["breakthrough"]["authority_boundary"]))
    lines.append("")
    lines.append(f"- Spec: `{report['tau']['antichain_certificate']['spec_path']}`")
    lines.append(f"- Direct risk spec: `{report['tau']['risk_envelope_direct']['spec_path']}`")
    lines.append(f"- Tau version: `{report['tau']['tau_version']}`")
    lines.append(f"- Dense risk states: `{report['lattice']['dense_state_count']}`")
    lines.append(f"- Minimal overall rejection antichain: `{report['lattice']['overall_minimal_reject_count']}`")
    lines.append(f"- Compression: `{report['lattice']['compression_ratio_dense_to_overall_antichain']}`")
    lines.append(f"- Certificate invalid accepts: `{report['tau']['antichain_certificate']['invalid_accepts']}`")
    lines.append("")
    lines.append("## Minimal Overall Rejection Antichain")
    lines.append("")
    lines.append("| boundary | reason |")
    lines.append("| --- | --- |")
    for boundary in report["lattice"]["overall_minimal_rejects"]:
        lines.append(f"| `{boundary}` | Any one of these primitive failures rejects the overall risk envelope. |")
    lines.append("")
    lines.append("Stale-oracle and breaker flags are component guard boundaries only when proof is missing; proof absence already dominates them for the overall envelope.")
    lines.append("")
    lines.append("## Tau Certificate Cases")
    lines.append("")
    lines.append("| case | ok | primary |")
    lines.append("| --- | --- | ---: |")
    for case in report["tau"]["antichain_certificate"]["cases"]:
        lines.append(f"| `{case['case_id']}` | `{case['ok']}` | `{case['got'].get('o5')}` |")
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
                "dense_state_count": report["lattice"]["dense_state_count"],
                "overall_minimal_reject_count": report["lattice"]["overall_minimal_reject_count"],
                "tau_cases": report["tau"]["antichain_certificate"]["case_count"],
                "invalid_accepts": report["tau"]["antichain_certificate"]["invalid_accepts"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
