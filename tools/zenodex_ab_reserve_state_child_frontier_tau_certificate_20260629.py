#!/usr/bin/env python3
"""Replay the AB reserve-state child-frontier Tau certificate."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

_TAU_RUNNER_SPEC = importlib.util.spec_from_file_location(
    "zenodex_tau_runner_direct", REPO_ROOT / "src" / "integration" / "tau_runner.py"
)
if _TAU_RUNNER_SPEC is None or _TAU_RUNNER_SPEC.loader is None:
    raise RuntimeError("could not load tau_runner.py")
_TAU_RUNNER = importlib.util.module_from_spec(_TAU_RUNNER_SPEC)
sys.modules[_TAU_RUNNER_SPEC.name] = _TAU_RUNNER
_TAU_RUNNER_SPEC.loader.exec_module(_TAU_RUNNER)
find_tau_bin = _TAU_RUNNER.find_tau_bin
run_tau_spec_steps = _TAU_RUNNER.run_tau_spec_steps

SPEC_ID = "ab_reserve_state_child_frontier_certificate_v1"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / f"{SPEC_ID}.tau"
LEAN_FILE = REPO_ROOT / "lean-mathlib" / "Proofs" / "ABReserveStateQuotient.lean"
OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_reserve_state_child_frontier_tau_certificate_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_RESERVE_STATE_CHILD_FRONTIER_TAU_CERTIFICATE_20260629.md"

REPORT_PATHS = {
    "n7_child_frontier": REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_generation_20260629"
    / "report.json",
    "n8_child_frontier_sample": REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_n8_sample_20260629"
    / "report.json",
    "transition_projection": REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_transition_projection_20260629"
    / "report.json",
    "reserve_state_quotient_n7": REPO_ROOT
    / "generated"
    / "zenodex_ab_strict_zero_min_reserve_state_quotient_certificate_20260629"
    / "report.json",
    "reserve_state_quotient_n8_sample": REPO_ROOT
    / "generated"
    / "zenodex_ab_strict_zero_min_reserve_state_quotient_n8_sample_20260629"
    / "report.json",
}


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _display_path(path: str | Path | None) -> str | None:
    if path is None:
        return None
    resolved = Path(path).resolve()
    try:
        return str(resolved.relative_to(REPO_ROOT))
    except ValueError:
        return str(resolved)


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _search(report: Mapping[str, Any]) -> Mapping[str, Any]:
    search = report.get("search")
    if not isinstance(search, Mapping):
        return {}
    return search


def _contains(text: str, *needles: str) -> bool:
    lowered = text.lower()
    return all(needle.lower() in lowered for needle in needles)


def _authority_boundary_ok(report: Mapping[str, Any]) -> bool:
    text = " ".join(
        [
            str(report.get("authority_boundary", "")),
            " ".join(str(item) for item in report.get("non_claims", [])),
        ]
    ).lower()
    return (
        "no settlement" in text
        and "state-root" in text
        and "production" in text
        and ("governance" in text or "routing" in text)
    )


def _negative_controls_ok(report: Mapping[str, Any], minimum: int) -> bool:
    search = _search(report)
    return (
        int(search.get("negative_control_count", 0)) >= minimum
        and int(search.get("negative_control_accept_count", -1)) == 0
    )


def _deterministic_replay_ok(report: Mapping[str, Any]) -> bool:
    replay = report.get("deterministic_replay")
    return isinstance(replay, Mapping) and bool(replay.get("ok")) is True


def _compile_lean() -> dict[str, Any]:
    started = time.monotonic()
    proc = subprocess.run(
        ["lake", "env", "lean", "Proofs/ABReserveStateQuotient.lean"],
        cwd=REPO_ROOT / "lean-mathlib",
        capture_output=True,
        text=True,
        timeout=90,
        check=False,
    )
    text = LEAN_FILE.read_text(encoding="utf-8")
    markers = (
        "def ReserveState.afterStep",
        "theorem reserveStateQuotientInvariant_afterStep",
        "theorem reserveStateQuotientInvariant_familySuffixExecutable",
        "structure ReserveStateQuotientObservedSummary",
        "theorem reserveStateQuotientObservedSummary_validates",
    )
    return {
        "path": str(LEAN_FILE.relative_to(REPO_ROOT)),
        "ok": proc.returncode == 0,
        "returncode": proc.returncode,
        "elapsed_s": round(time.monotonic() - started, 6),
        "stdout": proc.stdout[-2000:],
        "stderr": proc.stderr[-2000:],
        "sha256": _sha256(LEAN_FILE),
        "markers_present": {marker: marker in text for marker in markers},
    }


def _load_reports() -> dict[str, dict[str, Any]]:
    return {name: _read_json(path) for name, path in REPORT_PATHS.items()}


def _fact_bundle(reports: Mapping[str, Mapping[str, Any]], lean: Mapping[str, Any]) -> dict[str, int]:
    n7_frontier = reports["n7_child_frontier"]
    n8_frontier = reports["n8_child_frontier_sample"]
    transition = reports["transition_projection"]
    quotient_n7 = reports["reserve_state_quotient_n7"]
    quotient_n8 = reports["reserve_state_quotient_n8_sample"]

    n7s = _search(n7_frontier)
    n8s = _search(n8_frontier)
    ts = _search(transition)
    q7s = _search(quotient_n7)
    q8s = _search(quotient_n8)

    strict_scope_text = " ".join(
        str(report.get("summary", "")) + " " + " ".join(str(item) for item in report.get("non_claims", []))
        for report in reports.values()
    )
    strict_zero_min_scope_ok = _contains(strict_scope_text, "strict zero-min", "zero-min")

    n7_child_frontier_ok = (
        bool(n7_frontier.get("ok"))
        and int(n7s.get("child_mask_count", -1)) == 508
        and int(n7s.get("frontier_equal_count", -2)) == int(n7s.get("child_mask_count", -1))
        and int(n7s.get("missing_child_state_count", -1)) == 0
        and int(n7s.get("extra_generated_state_count", -1)) == 0
        and int(n7s.get("predecessor_transition_executable_count", -1))
        == int(n7s.get("predecessor_transition_count", -2))
    )

    n8_sample_child_frontier_ok = (
        bool(n8_frontier.get("ok"))
        and int(n8s.get("valid_case_count", -1)) == 3
        and int(n8s.get("sampled_child_mask_count", -1)) == 51
        and int(n8s.get("frontier_equal_count", -2)) == int(n8s.get("sampled_child_mask_count", -1))
        and int(n8s.get("sampled_child_state_count", -1)) == int(n8s.get("generated_state_count", -2))
        and int(n8s.get("missing_child_state_count", -1)) == 0
        and int(n8s.get("extra_generated_state_count", -1)) == 0
    )

    transition_projection_ok = (
        bool(transition.get("ok"))
        and int(ts.get("transition_projection_count", -1)) == 1792
        and int(ts.get("selected_child_membership_count", -2)) == int(ts.get("selected_transition_count", -1))
        and int(ts.get("candidate_child_membership_count", -2)) == int(ts.get("candidate_transition_count", -1))
        and int(ts.get("candidate_min_reserve_check_count", -2)) == int(ts.get("candidate_transition_count", -1))
        and int(ts.get("candidate_processed_match_count", -2)) == int(ts.get("candidate_transition_count", -1))
        and int(ts.get("candidate_transition_executable_count", -2)) == int(ts.get("candidate_transition_count", -1))
    )

    observed_summary_bridge_ok = (
        bool(quotient_n7.get("ok"))
        and bool(quotient_n8.get("ok"))
        and int(q7s.get("lean_observed_summary_count", 0)) > 0
        and int(q8s.get("lean_observed_summary_count", 0)) > 0
        and int(q7s.get("selected_suffix_executable_count", -1)) == int(q7s.get("lean_observed_summary_count", -2))
        and int(q8s.get("selected_suffix_executable_count", -1)) == int(q8s.get("lean_observed_summary_count", -2))
    )

    deterministic_replay_ok = all(_deterministic_replay_ok(report) for report in reports.values())
    negative_controls_ok = (
        _negative_controls_ok(n7_frontier, 7)
        and _negative_controls_ok(n8_frontier, 7)
        and _negative_controls_ok(transition, 7)
        and _negative_controls_ok(quotient_n7, 12)
        and _negative_controls_ok(quotient_n8, 12)
    )
    refinement_nonclaim = _contains(strict_scope_text, "python-to-lean") or _contains(
        strict_scope_text, "lean-to-python"
    )
    scope_nonclaims_bound = (
        all(_authority_boundary_ok(report) for report in reports.values())
        and refinement_nonclaim
        and _contains(strict_scope_text, "canonical tie", "nonzero min")
    )
    lean_afterstep_contract_ok = bool(lean.get("ok")) and all(
        bool(value) for value in dict(lean.get("markers_present", {})).values()
    )
    frontier_nonvacuous = (
        int(n7s.get("child_state_count", 0)) > 0
        and int(n7s.get("generated_state_count", 0)) > 0
        and int(n8s.get("sampled_child_state_count", 0)) > 0
        and int(n8s.get("generated_state_count", 0)) > 0
    )
    n8_sample_bounded = (
        bool(n8_frontier.get("ok"))
        and _contains(" ".join(str(item) for item in n8_frontier.get("non_claims", [])), "bounded deterministic n=8 sample", "not exhaustive n=8 coverage")
        and int(n8s.get("sample_plan", {}).get("bit_count", 0)) == 8
        and int(n8s.get("sampled_child_mask_count", 0)) == 51
    )

    return {
        "strict_zero_min_scope_ok": int(strict_zero_min_scope_ok),
        "n7_child_frontier_ok": int(n7_child_frontier_ok),
        "n8_sample_child_frontier_ok": int(n8_sample_child_frontier_ok),
        "transition_projection_ok": int(transition_projection_ok),
        "observed_summary_bridge_ok": int(observed_summary_bridge_ok),
        "lean_afterstep_contract_ok": int(lean_afterstep_contract_ok),
        "deterministic_replay_ok": int(deterministic_replay_ok),
        "negative_controls_ok": int(negative_controls_ok),
        "scope_nonclaims_bound": int(scope_nonclaims_bound),
        "no_authority_effect": 1,
        "frontier_nonvacuous": int(frontier_nonvacuous),
        "n8_sample_bounded": int(n8_sample_bounded),
    }


def _tau_cases(facts: Mapping[str, int]) -> tuple[TauCase, ...]:
    pass_step = {
        "i1": 1,
        "i2": int(facts["strict_zero_min_scope_ok"]),
        "i3": int(facts["n7_child_frontier_ok"]),
        "i4": int(facts["n8_sample_child_frontier_ok"]),
        "i5": int(facts["transition_projection_ok"]),
        "i6": int(facts["observed_summary_bridge_ok"]),
        "i7": int(facts["lean_afterstep_contract_ok"]),
        "i8": int(facts["deterministic_replay_ok"]),
        "i9": int(facts["negative_controls_ok"]),
        "i10": int(facts["scope_nonclaims_bound"]),
        "i11": int(facts["no_authority_effect"]),
        "i12": int(facts["frontier_nonvacuous"]),
        "i13": int(facts["n8_sample_bounded"]),
    }
    inactive = dict(pass_step)
    inactive["i1"] = 0
    return (
        TauCase(
            "child_frontier_certificate_pass",
            pass_step,
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 1, "o7": 0},
            "All scoped host, Lean, replay, negative-control, and no-authority facts admit the research certificate.",
        ),
        TauCase(
            "missing_n7_child_frontier_reject",
            {**pass_step, "i3": 0},
            {"o2": 0, "o6": 0},
            "The exhaustive n=7 child-frontier host evidence must remain present.",
        ),
        TauCase(
            "missing_n8_sample_reject",
            {**pass_step, "i4": 0},
            {"o2": 0, "o6": 0},
            "The bounded n=8 sample extension must remain present.",
        ),
        TauCase(
            "missing_transition_projection_reject",
            {**pass_step, "i5": 0},
            {"o3": 0, "o6": 0},
            "The child-frontier certificate must keep the transition-projection bridge.",
        ),
        TauCase(
            "missing_observed_summary_bridge_reject",
            {**pass_step, "i6": 0},
            {"o3": 0, "o6": 0},
            "The observed-summary bridge must remain bound to the certificate.",
        ),
        TauCase(
            "missing_lean_contract_reject",
            {**pass_step, "i7": 0},
            {"o3": 0, "o6": 0},
            "The Lean ReserveState.afterStep contract must compile and expose the expected markers.",
        ),
        TauCase(
            "missing_negative_controls_reject",
            {**pass_step, "i9": 0},
            {"o4": 0, "o6": 0},
            "Malformed or over-scoped packets must remain rejected.",
        ),
        TauCase(
            "missing_scope_nonclaims_reject",
            {**pass_step, "i10": 0},
            {"o1": 0, "o6": 0},
            "The no-refinement, no-tie-order, no-nonzero-min, and no-authority non-claims must remain explicit.",
        ),
        TauCase(
            "missing_bounded_n8_scope_reject",
            {**pass_step, "i13": 0},
            {"o1": 0, "o6": 0},
            "The n=8 evidence must remain explicitly marked as a bounded sample.",
        ),
        TauCase(
            "authority_reject",
            {**pass_step, "i11": 0},
            {"o5": 0, "o6": 0},
            "The certificate cannot carry settlement, state-root, production, or governance authority.",
        ),
        TauCase(
            "inactive_safe",
            inactive,
            {"o6": 0, "o7": 1},
            "Inactive certificates do not admit while the no-authority rail remains true.",
        ),
    )


def _run_tau(facts: Mapping[str, int]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    cases = _tau_cases(facts)
    if not tau_bin:
        return {
            "ok": False,
            "skipped": True,
            "error": "latest Tau binary not found",
            "case_results": [],
            "invalid_accepts": 0,
            "tau_bin": None,
            "tau_version": None,
        }
    proc = subprocess.run(
        [tau_bin, "--version"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[case.step for case in cases],
        timeout_s=20.0,
    )
    invalid_accepts = 0
    case_results = []
    ok = True
    for index, case in enumerate(cases):
        got = {str(key): int(value) for key, value in outputs.get(index, {}).items()}
        mismatches = {
            key: {"expected": int(value), "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != int(value)
        }
        if case.expected.get("o6") == 0 and got.get("o6") == 1:
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
        "skipped": False,
        "case_results": case_results,
        "invalid_accepts": invalid_accepts,
        "tau_bin": _display_path(tau_bin),
        "tau_version": (proc.stdout + proc.stderr).strip(),
    }


def _build_report() -> dict[str, Any]:
    reports = _load_reports()
    lean = _compile_lean()
    facts = _fact_bundle(reports, lean)
    tau = _run_tau(facts)
    return {
        "schema": "zenodex.ab_reserve_state_child_frontier_tau_certificate_report.v1",
        "date": "2026-06-29",
        "authority_boundary": "research evidence only; no settlement, state-root, production, governance, routing, matching, or pool-mutation authority",
        "spec": {
            "id": SPEC_ID,
            "path": str(TAU_SPEC.relative_to(REPO_ROOT)),
            "sha256": _sha256(TAU_SPEC),
        },
        "source_reports": {
            name: {
                "path": str(REPORT_PATHS[name].relative_to(REPO_ROOT)),
                "sha256": _sha256(REPORT_PATHS[name]),
                "ok": bool(report.get("ok")),
                "schema": report.get("schema"),
            }
            for name, report in reports.items()
        },
        "lean": lean,
        "facts": facts,
        "tau": tau,
        "breakthrough": {
            "name": "AB reserve-state child-frontier Tau certificate",
            "spec_id": SPEC_ID,
            "tau_cases": len(tau["case_results"]),
            "invalid_accepts": tau["invalid_accepts"],
            "scoped_claims": [
                "n=7 child-frontier equality is bound to a host report",
                "n=8 child-frontier extension is bound as a sampled report",
                "transition projection and observed-summary bridges are required",
                "Lean afterStep and observed-summary markers must compile",
                "negative controls and no-authority rails are mandatory",
            ],
        },
        "non_claims": [
            "This certificate does not prove Python-to-Lean refinement.",
            "This certificate does not prove child-frontier generation in Lean.",
            "This certificate does not claim exhaustive n=8 coverage.",
            "This certificate does not define canonical tie order.",
            "This certificate does not cover nonzero min_amount_out behavior.",
            "This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.",
        ],
        "replay_command": "python3 tools/zenodex_ab_reserve_state_child_frontier_tau_certificate_20260629.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX AB Reserve-State Child-Frontier Tau Certificate - 2026-06-29",
        "",
        "## Executive Result",
        "",
        "`ab_reserve_state_child_frontier_certificate_v1` admits the reserve-state child-frontier research bundle only when the n=7 host evidence, bounded n=8 sample, transition projection, observed-summary bridge, Lean contract markers, deterministic replay, negative controls, scoped non-claims, and no-authority rail are all present.",
        "",
        "Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.",
        "",
        "## Facts",
        "",
    ]
    for key, value in report["facts"].items():
        lines.append(f"- `{key}` = `{value}`")
    lines.extend(["", "## Source Reports", "", "| report | ok | schema |", "| --- | --- | --- |"])
    for name, row in report["source_reports"].items():
        lines.append(f"| `{name}` | `{row['ok']}` | `{row['schema']}` |")
    lines.extend(["", "## Tau Cases", "", "| case | ok | admitted |", "| --- | --- | ---: |"])
    for case in report["tau"]["case_results"]:
        lines.append(f"| `{case['case_id']}` | `{case['ok']}` | `{case['got'].get('o6')}` |")
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```"])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    report = _build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    ok = (
        all(value == 1 for value in report["facts"].values())
        and bool(report["lean"]["ok"])
        and bool(report["tau"]["ok"])
        and int(report["tau"]["invalid_accepts"]) == 0
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
