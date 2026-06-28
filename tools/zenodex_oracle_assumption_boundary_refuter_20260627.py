#!/usr/bin/env python3
"""Refute hidden-assumption admits for the oracle Tau frontier envelope."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "tools"))

from zenodex_oracle_coupled_inequality_certificate_20260627 import build_certificate  # noqa: E402
from zenodex_oracle_economic_security import sample_envelope  # noqa: E402
from zenodex_oracle_polytope_compiler_20260627 import compile_polytope  # noqa: E402

sys.path.insert(0, str(REPO_ROOT))
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_oracle_assumption_boundary_refuter_20260627"
REPORT_PATH = REPO_ROOT / "docs" / "research" / "ZENODEX_ORACLE_ASSUMPTION_BOUNDARY_REFUTER_20260627.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "oracle_polytope_frontier_envelope_v1.tau"


FACT_TO_STREAM = {
    "oracle_param_update_requested": "i1",
    "interval_nonempty": "i2",
    "honest_challenge_profitable_interval_ok": "i3",
    "frivolous_dispute_deterrence_interval_ok": "i4",
    "slash_covers_cheat_gain_interval_ok": "i5",
    "point_verifier_parity_ok": "i6",
    "all_boundary_walls_checked": "i7",
    "mev_assumption_declared": "i8",
    "probability_assumption_declared": "i9",
    "no_oracle_update_authority": "i10",
    "fail_closed_default_ok": "i11",
}


@dataclass(frozen=True)
class BoundaryCase:
    case_id: str
    mutated_facts: Mapping[str, bool]
    expected_failed_flags: tuple[str, ...]
    note: str


def _tau_step_from_facts(facts: Mapping[str, bool]) -> dict[str, int]:
    return {stream: 1 if bool(facts.get(name, False)) else 0 for name, stream in FACT_TO_STREAM.items()}


def _all_true_step() -> dict[str, int]:
    return {f"i{idx}": 1 for idx in range(1, 12)}


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _run_tau_steps(steps: list[dict[str, int]]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "case_outputs": []}
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=TAU_SPEC, steps=steps, timeout_s=10.0)
    return {
        "ok": True,
        "tau_bin": tau_bin,
        "tau_version": _tau_version(tau_bin),
        "case_outputs": [outputs.get(idx, {}) for idx in range(len(steps))],
    }


def _base_facts() -> dict[str, bool]:
    report = compile_polytope()
    return {key: bool(value) for key, value in report["tau_oracle_polytope_facts"].items()}


def _host_certificate_ok() -> bool:
    certificate = build_certificate(sample_envelope())
    return bool(certificate["certificate_ok"] and certificate["verifier_ok"] and certificate["parity_ok"])


def _cases() -> tuple[BoundaryCase, ...]:
    return (
        BoundaryCase(
            "valid_oracle_envelope_accepts",
            {},
            tuple(),
            "All interval, parity, boundary, assumption, and authority facts are true.",
        ),
        BoundaryCase(
            "missing_boundary_walls_rejects",
            {"all_boundary_walls_checked": False},
            ("i7",),
            "An interval certificate without boundary-wall replay cannot be admitted.",
        ),
        BoundaryCase(
            "hidden_mev_assumption_rejects",
            {"mev_assumption_declared": False},
            ("i8",),
            "The max-extractable-value assumption must be explicit.",
        ),
        BoundaryCase(
            "hidden_probability_assumption_rejects",
            {"probability_assumption_declared": False},
            ("i9",),
            "Challenge-probability and reporting assumptions must be explicit.",
        ),
        BoundaryCase(
            "oracle_update_authority_rejects",
            {"no_oracle_update_authority": False},
            ("i10",),
            "The Tau envelope must not carry oracle-update authority.",
        ),
        BoundaryCase(
            "missing_fail_closed_default_rejects",
            {"fail_closed_default_ok": False},
            ("i11",),
            "Missing host fail-closed default must reject the certificate path.",
        ),
        BoundaryCase(
            "point_verifier_parity_missing_rejects",
            {"point_verifier_parity_ok": False},
            ("i6",),
            "The interval compiler cannot widen beyond point-verifier parity.",
        ),
        BoundaryCase(
            "honest_challenge_interval_missing_rejects",
            {"honest_challenge_profitable_interval_ok": False},
            ("i3",),
            "Economic interval facts remain load-bearing even when external assumptions are disclosed.",
        ),
    )


def _case_facts(base: Mapping[str, bool], case: BoundaryCase) -> dict[str, bool]:
    facts = dict(base)
    facts.update({key: bool(value) for key, value in case.mutated_facts.items()})
    return facts


def run_refuter() -> dict[str, Any]:
    base = _base_facts()
    host_certificate_ok = _host_certificate_ok()
    cases = _cases()
    computed_steps = [_tau_step_from_facts(_case_facts(base, case)) for case in cases]
    declared_steps = [_all_true_step() for _case in cases]
    tau_computed = _run_tau_steps(computed_steps)
    tau_declared = _run_tau_steps(declared_steps)

    rows: list[dict[str, Any]] = []
    false_declared_admits = 0
    computed_false_admits = 0
    for idx, case in enumerate(cases):
        facts = _case_facts(base, case)
        failed_flags = tuple(stream for name, stream in FACT_TO_STREAM.items() if not bool(facts.get(name, False)))
        host_ok = host_certificate_ok and not failed_flags
        computed_output = tau_computed.get("case_outputs", [{}])[idx] if tau_computed.get("case_outputs") else {}
        declared_output = tau_declared.get("case_outputs", [{}])[idx] if tau_declared.get("case_outputs") else {}
        computed_accepts = computed_output.get("o5") == 1
        declared_accepts = declared_output.get("o5") == 1
        false_declared_admits += int(declared_accepts and not host_ok)
        computed_false_admits += int(computed_accepts and not host_ok)
        rows.append(
            {
                "case_id": case.case_id,
                "note": case.note,
                "host_ok": host_ok,
                "failed_flags": list(failed_flags),
                "expected_failed_flags": list(case.expected_failed_flags),
                "expected_failed_flags_match": tuple(sorted(failed_flags)) == tuple(sorted(case.expected_failed_flags)),
                "computed_tau_accepts": computed_accepts,
                "declared_tau_accepts": declared_accepts,
                "computed_tau_output": computed_output,
                "declared_tau_output": declared_output,
                "computed_step": computed_steps[idx],
            }
        )
    negative_rows = [row for row in rows if not row["host_ok"]]
    return {
        "schema": "zenodex.oracle_assumption_boundary_refuter_report.v1",
        "ok": tau_computed.get("ok") is True
        and tau_declared.get("ok") is True
        and host_certificate_ok
        and all(row["expected_failed_flags_match"] for row in rows)
        and computed_false_admits == 0
        and false_declared_admits == len(negative_rows),
        "case_count": len(rows),
        "negative_case_count": len(negative_rows),
        "false_declared_admit_count": false_declared_admits,
        "computed_false_admit_count": computed_false_admits,
        "host_certificate_ok": host_certificate_ok,
        "tau_computed": {key: value for key, value in tau_computed.items() if key != "case_outputs"},
        "tau_declared": {key: value for key, value in tau_declared.items() if key != "case_outputs"},
        "cases": rows,
        "non_claims": [
            "This refuter checks the Tau proof-surface boundary; it does not estimate MEV, probability, or oracle truth.",
            "Forged all-true flags can still admit, so host computation of facts remains mandatory.",
            "The pointwise economic-security verifier remains authoritative.",
        ],
        "replay_command": "python3 tools/zenodex_oracle_assumption_boundary_refuter_20260627.py",
    }


def _write_markdown(report: Mapping[str, Any], output: Path) -> None:
    lines: list[str] = []
    lines.append("# Zeno Oracle Assumption Boundary Refuter - 2026-06-27")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(
        "This artifact checks that the oracle Tau envelope rejects hidden assumptions and missing authority-boundary facts when host-computed flags are used."
    )
    lines.append(
        f"Cases: `{report['case_count']}`. Negative cases: `{report['negative_case_count']}`. Forged declared Tau admits: `{report['false_declared_admit_count']}`. Computed-flag false admits: `{report['computed_false_admit_count']}`. Overall: `ok={report['ok']}`."
    )
    lines.append("")
    lines.append("Result: Tau is a compact guard for declared proof-surface facts; the host must compute those facts from replayed interval, assumption, and authority evidence.")
    lines.append("")
    lines.append("## Cases")
    lines.append("")
    lines.append("| case | host ok | Tau with declared flags | Tau with computed flags | failed flags |")
    lines.append("| --- | --- | --- | --- | --- |")
    for row in report["cases"]:
        failed = ", ".join(f"`{flag}`" for flag in row["failed_flags"]) or "none"
        lines.append(
            f"| `{row['case_id']}` | `{row['host_ok']}` | `{row['declared_tau_accepts']}` | `{row['computed_tau_accepts']}` | {failed} |"
        )
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
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path, output_md: Path) -> dict[str, Any]:
    report = run_refuter()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report, output_md)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(OUT_DIR / "report.json"))
    parser.add_argument("--output-md", default=str(REPORT_PATH))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json), Path(args.output_md))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "case_count": report["case_count"],
                "false_declared_admit_count": report["false_declared_admit_count"],
                "computed_false_admit_count": report["computed_false_admit_count"],
                "json": str(Path(args.output_json)),
                "report": str(Path(args.output_md)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
