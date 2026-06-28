#!/usr/bin/env python3
"""Replay a Tau-gated grouped-capacity CoW exact-DP certificate."""

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


OUT_DIR = REPO_ROOT / "generated" / "zenodex_cow_capacity_dp_certificate_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_COW_CAPACITY_DP_CERTIFICATE_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "cow_capacity_dp_certificate_v1.tau"

TOOL_COMMANDS: dict[str, tuple[str, ...]] = {
    "capacity_breakthrough": ("tools/zenodex_cow_capacity_dp_breakthrough_20260627.py",),
    "capacity_adversarial": ("tools/check_cow_capacity_dp_adversarial.py",),
    "shared_ab_cow_envelope": ("tools/zenodex_ab_cow_algorithm_breakthrough_20260627.py",),
}


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _sha256_json(value: Any) -> str:
    return hashlib.sha256(_canonical_json_bytes(value)).hexdigest()


def _strip_timing(value: Any) -> Any:
    if isinstance(value, dict):
        return {
            key: _strip_timing(item)
            for key, item in value.items()
            if key
            not in {
                "elapsed_ms",
                "timing_s",
                "timing_ms",
                "bruteforce_s",
                "subset_dp_s",
                "assignment_s",
                "greedy_s",
                "capacity_dp_s",
                "speedup",
            }
        }
    if isinstance(value, list):
        return [_strip_timing(item) for item in value]
    return value


def _run_json_command(command: Sequence[str], *, timeout_s: float = 120.0) -> dict[str, Any]:
    proc = subprocess.run(
        [sys.executable, *command],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=timeout_s,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"{' '.join(command)} failed with rc={proc.returncode}: {(proc.stdout + proc.stderr)[:1000]}"
        )

    if command[0] == "tools/zenodex_cow_capacity_dp_breakthrough_20260627.py":
        return json.loads(
            (REPO_ROOT / "generated" / "zenodex_cow_capacity_dp_breakthrough_20260627" / "report.json").read_text(
                encoding="utf-8"
            )
        )
    if command[0] == "tools/zenodex_ab_cow_algorithm_breakthrough_20260627.py":
        return json.loads(
            (REPO_ROOT / "generated" / "zenodex_ab_cow_algorithm_breakthrough_20260627" / "report.json").read_text(
                encoding="utf-8"
            )
        )

    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"{' '.join(command)} did not emit JSON: {proc.stdout[:1000]}") from exc
    if not isinstance(payload, dict):
        raise RuntimeError(f"{' '.join(command)} emitted a non-object JSON payload")
    return payload


def run_evidence_tools() -> dict[str, dict[str, Any]]:
    return {name: _run_json_command(command) for name, command in TOOL_COMMANDS.items()}


def _deterministic_replay(first: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    second = run_evidence_tools()
    rows: list[dict[str, Any]] = []
    ok = True
    for name in sorted(TOOL_COMMANDS):
        first_hash = _sha256_json(_strip_timing(first[name]))
        second_hash = _sha256_json(_strip_timing(second[name]))
        same = first_hash == second_hash
        if not same:
            ok = False
        rows.append(
            {
                "tool": name,
                "same": same,
                "first_hash": first_hash,
                "second_hash": second_hash,
            }
        )
    return {"ok": ok, "rows": rows}


def _int_field(payload: Mapping[str, Any], key: str) -> int:
    try:
        return int(payload.get(key, 0))
    except (TypeError, ValueError):
        return 0


def _has_text(payload: Mapping[str, Any], *needles: str) -> bool:
    text = json.dumps(payload, sort_keys=True).lower()
    return all(needle.lower() in text for needle in needles)


def _non_claim_text(payload: Mapping[str, Any]) -> str:
    items = payload.get("non_claims", [])
    if not isinstance(items, list):
        return ""
    return "\n".join(str(item).lower() for item in items)


def _shared_tau_has_case(shared: Mapping[str, Any], case_id: str) -> bool:
    tau = shared.get("tau_envelope", {})
    if not isinstance(tau, Mapping):
        return False
    cases = tau.get("cases", [])
    if not isinstance(cases, list):
        return False
    return any(isinstance(row, Mapping) and row.get("case_id") == case_id and bool(row.get("ok")) for row in cases)


def evidence_flags(
    evidence: Mapping[str, Mapping[str, Any]],
    deterministic_replay: Mapping[str, Any],
) -> dict[str, int]:
    main = evidence["capacity_breakthrough"]
    adversarial = evidence["capacity_adversarial"]
    shared = evidence["shared_ab_cow_envelope"]
    main_non_claims = _non_claim_text(main)
    adversarial_non_claims = _non_claim_text(adversarial)

    grouped_capacity_scope_ok = int(
        bool(main.get("ok"))
        and bool(adversarial.get("ok"))
        and _int_field(main, "case_count") > 0
        and _int_field(adversarial, "assignment_safe_case_count") == 0
        and "bounded exact dp for small grouped-capacity cow batches" in main_non_claims
        and "not a polynomial algorithm" in main_non_claims
    )
    dp_bruteforce_parity_ok = int(
        _int_field(main, "exact_mismatch_count") == 0
        and _int_field(adversarial, "exact_mismatch_count") == 0
        and all(bool(row.get("dp_matches_bruteforce")) for row in main.get("cases", []))
        and all(bool(row.get("dp_matches_bruteforce")) for row in adversarial.get("cases", []))
    )
    core_selector_dp_parity_ok = int(
        _int_field(main, "core_mismatch_count") == 0
        and _int_field(adversarial, "core_mismatch_count") == 0
        and all(bool(row.get("core_selector_matches_dp")) for row in main.get("cases", []))
        and all(bool(row.get("core_selector_matches_dp")) for row in adversarial.get("cases", []))
    )
    adversarial_corpus_ok = int(
        bool(adversarial.get("ok"))
        and _int_field(adversarial, "case_count") == 20
        and _int_field(adversarial, "pattern_count") == 5
        and _int_field(adversarial, "variants_per_pattern") == 4
        and _int_field(adversarial, "assignment_safe_case_count") == 0
    )
    greedy_lift_nonvacuous = int(
        _int_field(main, "greedy_lift_case_count") >= 2
        and _int_field(adversarial, "greedy_lift_case_count") >= 8
        and _int_field(adversarial, "max_volume_lift") > 0
        and _int_field(adversarial, "max_surplus_lift") > 0
    )
    resource_budget_ok = int(
        _int_field(main, "max_total_candidates") <= 9
        and _int_field(adversarial, "max_candidate_count") <= 14
        and _int_field(main, "case_count") <= 5
        and _int_field(adversarial, "case_count") <= 20
    )
    deterministic_replay_ok = int(bool(deterministic_replay.get("ok")))
    fallback_boundary_ok = int(
        "large coupled batches still retain the greedy/fail-closed fallback" in main_non_claims
        and "bounded to small coupled-capacity cow batches" in adversarial_non_claims
    )
    no_settlement_authority = int(
        "no settlement authority" in main_non_claims
        and "settlement authority remains" in adversarial_non_claims
        and _has_text(main.get("breakthrough", {}), "fail-closed", "balance checks")
    )
    settlement_materialization_boundary_ok = int(
        _has_text(main.get("breakthrough", {}), "settlement materialization", "fail-closed aggregate balance checks")
    )
    exact_assignment_boundary_ok = int(
        bool(shared.get("ok"))
        and bool(shared.get("cow_matching", {}).get("ok"))
        and bool(shared.get("tau_envelope", {}).get("ok"))
        and _shared_tau_has_case(shared, "cow_item_2_pass")
        and _shared_tau_has_case(shared, "coupled_capacity_reject")
    )
    return {
        "grouped_capacity_scope_ok": grouped_capacity_scope_ok,
        "dp_bruteforce_parity_ok": dp_bruteforce_parity_ok,
        "core_selector_dp_parity_ok": core_selector_dp_parity_ok,
        "adversarial_corpus_ok": adversarial_corpus_ok,
        "greedy_lift_nonvacuous": greedy_lift_nonvacuous,
        "resource_budget_ok": resource_budget_ok,
        "deterministic_replay_ok": deterministic_replay_ok,
        "fallback_boundary_ok": fallback_boundary_ok,
        "no_settlement_authority": no_settlement_authority,
        "settlement_materialization_boundary_ok": settlement_materialization_boundary_ok,
        "exact_assignment_boundary_ok": exact_assignment_boundary_ok,
    }


def _tau_step(flags: Mapping[str, int], *, active: int = 1, overrides: Mapping[str, int] | None = None) -> dict[str, int]:
    values = {
        "i1": int(active),
        "i2": int(flags.get("grouped_capacity_scope_ok", 0)),
        "i3": int(flags.get("dp_bruteforce_parity_ok", 0)),
        "i4": int(flags.get("core_selector_dp_parity_ok", 0)),
        "i5": int(flags.get("adversarial_corpus_ok", 0)),
        "i6": int(flags.get("greedy_lift_nonvacuous", 0)),
        "i7": int(flags.get("resource_budget_ok", 0)),
        "i8": int(flags.get("deterministic_replay_ok", 0)),
        "i9": int(flags.get("fallback_boundary_ok", 0)),
        "i10": int(flags.get("no_settlement_authority", 0)),
        "i11": int(flags.get("settlement_materialization_boundary_ok", 0)),
        "i12": int(flags.get("exact_assignment_boundary_ok", 0)),
    }
    if overrides:
        values.update({key: int(value) for key, value in overrides.items()})
    return values


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _run_tau_cases(base_flags: Mapping[str, int]) -> dict[str, Any]:
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
            "cow_capacity_certificate_pass",
            _tau_step(base_flags),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 0},
            "All host-computed proof-surface facts admit the grouped-capacity CoW certificate.",
        ),
        TauCase(
            "scope_reject",
            _tau_step(base_flags, overrides={"i2": 0}),
            {"o1": 0, "o5": 0},
            "Missing grouped-capacity scope fails closed.",
        ),
        TauCase(
            "bruteforce_parity_reject",
            _tau_step(base_flags, overrides={"i3": 0}),
            {"o2": 0, "o5": 0},
            "Missing DP versus brute-force parity fails closed.",
        ),
        TauCase(
            "core_selector_reject",
            _tau_step(base_flags, overrides={"i4": 0}),
            {"o2": 0, "o5": 0},
            "Missing core-selector parity fails closed.",
        ),
        TauCase(
            "adversarial_reject",
            _tau_step(base_flags, overrides={"i5": 0}),
            {"o2": 0, "o5": 0},
            "Missing adversarial corpus evidence fails closed.",
        ),
        TauCase(
            "lift_reject",
            _tau_step(base_flags, overrides={"i6": 0}),
            {"o3": 0, "o5": 0},
            "Missing nonvacuous lift evidence fails closed.",
        ),
        TauCase(
            "determinism_reject",
            _tau_step(base_flags, overrides={"i8": 0}),
            {"o3": 0, "o5": 0},
            "Missing deterministic replay fails closed.",
        ),
        TauCase(
            "fallback_boundary_reject",
            _tau_step(base_flags, overrides={"i9": 0}),
            {"o1": 0, "o5": 0},
            "Missing fallback boundary rejects the certificate.",
        ),
        TauCase(
            "authority_reject",
            _tau_step(base_flags, overrides={"i10": 0}),
            {"o4": 0, "o5": 0, "o6": 0},
            "Any settlement-authority effect rejects the certificate.",
        ),
        TauCase(
            "assignment_boundary_reject",
            _tau_step(base_flags, overrides={"i12": 0}),
            {"o1": 0, "o5": 0},
            "Missing separation from the uncoupled assignment surface fails closed.",
        ),
        TauCase(
            "inactive_safe",
            _tau_step(base_flags, active=0),
            {"o5": 0, "o6": 1},
            "Inactive certificates do not admit while no-authority remains true.",
        ),
    )
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[case.step for case in cases],
        timeout_s=20.0,
    )
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


def _mutation_checks(tau: Mapping[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for case in tau.get("cases", []):
        if case.get("case_id") in {"cow_capacity_certificate_pass", "inactive_safe"}:
            continue
        got = case.get("got", {})
        accepted = isinstance(got, Mapping) and int(got.get("o5", 0)) == 1
        rows.append(
            {
                "mutation_id": case.get("case_id"),
                "accepted": bool(accepted),
                "rationale": case.get("rationale"),
            }
        )
    return rows


def _evidence_summary(evidence: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    main = evidence["capacity_breakthrough"]
    adversarial = evidence["capacity_adversarial"]
    shared = evidence["shared_ab_cow_envelope"]
    return {
        "capacity_breakthrough": {
            "ok": bool(main.get("ok")),
            "case_count": main.get("case_count"),
            "exact_mismatch_count": main.get("exact_mismatch_count"),
            "core_mismatch_count": main.get("core_mismatch_count"),
            "greedy_lift_case_count": main.get("greedy_lift_case_count"),
            "max_total_candidates": main.get("max_total_candidates"),
        },
        "capacity_adversarial": {
            "ok": bool(adversarial.get("ok")),
            "seed": adversarial.get("seed"),
            "case_count": adversarial.get("case_count"),
            "pattern_count": adversarial.get("pattern_count"),
            "variants_per_pattern": adversarial.get("variants_per_pattern"),
            "exact_mismatch_count": adversarial.get("exact_mismatch_count"),
            "core_mismatch_count": adversarial.get("core_mismatch_count"),
            "assignment_safe_case_count": adversarial.get("assignment_safe_case_count"),
            "greedy_lift_case_count": adversarial.get("greedy_lift_case_count"),
            "max_candidate_count": adversarial.get("max_candidate_count"),
            "max_volume_lift": adversarial.get("max_volume_lift"),
            "max_surplus_lift": adversarial.get("max_surplus_lift"),
            "pattern_summary": adversarial.get("pattern_summary"),
        },
        "shared_ab_cow_envelope": {
            "ok": bool(shared.get("ok")),
            "tau_ok": bool(shared.get("tau_envelope", {}).get("ok")),
            "cow_matching_ok": bool(shared.get("cow_matching", {}).get("ok")),
            "tau_cases": [row.get("case_id") for row in shared.get("tau_envelope", {}).get("cases", [])],
        },
    }


def build_report() -> dict[str, Any]:
    evidence = run_evidence_tools()
    deterministic = _deterministic_replay(evidence)
    flags = evidence_flags(evidence, deterministic)
    tau = _run_tau_cases(flags)
    mutation_rows = _mutation_checks(tau)
    ok = all(int(value) == 1 for value in flags.values()) and bool(tau.get("ok")) and all(
        not bool(row["accepted"]) for row in mutation_rows
    )
    return {
        "schema": "zenodex.cow_capacity_dp_certificate_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "spec_id": "cow_capacity_dp_certificate_v1",
        "summary": (
            "A Tau host-projected certificate gates bounded grouped-capacity CoW exact-DP evidence by "
            "requiring DP/brute-force parity, core-selector parity, adversarial coupled-sender cases, "
            "nonvacuous greedy lift, resource limits, deterministic replay, fallback boundaries, separation "
            "from the uncoupled assignment surface, and no settlement authority."
        ),
        "authority_boundary": (
            "Tau admits a research certificate only. It does not select CoW pairs, compute matching or DP, "
            "materialize settlement, mutate balances, or authorize state roots."
        ),
        "flags": flags,
        "tau": tau,
        "evidence": _evidence_summary(evidence),
        "deterministic_replay": deterministic,
        "mutation_checks": mutation_rows,
        "non_claims": [
            "This is a research certificate, not production activation.",
            "The exact DP claim is bounded to small grouped-capacity CoW batches.",
            "This does not claim a polynomial algorithm for arbitrary grouped-capacity matching.",
            "Uncoupled large batches remain on the Hungarian assignment surface; large coupled batches retain fallback bounds.",
            "Settlement authority remains with deterministic fail-closed materialization and balance checks.",
        ],
        "replay_command": "python3 tools/check_cow_capacity_dp_certificate.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    evidence = report["evidence"]
    main = evidence["capacity_breakthrough"]
    adversarial = evidence["capacity_adversarial"]
    shared = evidence["shared_ab_cow_envelope"]
    flags = report["flags"]
    tau = report["tau"]

    lines: list[str] = []
    lines.append("# ZenoDEX CoW Capacity-DP Certificate - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(str(report["summary"]))
    lines.append("")
    lines.append(str(report["authority_boundary"]))
    lines.append("")
    lines.append("## Tau Specification")
    lines.append("")
    lines.append(f"- Spec: `{tau['spec_path']}`")
    lines.append(f"- Latest Tau: `{tau.get('tau_version')}`")
    lines.append(f"- Tau trace replay ok: `{tau['ok']}`")
    lines.append(f"- Certificate ok: `{report['ok']}`")
    lines.append("")
    lines.append("## Evidence Summary")
    lines.append("")
    lines.append("| component | result | key receipt |")
    lines.append("| --- | --- | --- |")
    lines.append(
        f"| capacity breakthrough | `{main['ok']}` | `{main['case_count']}` cases, exact mismatches `{main['exact_mismatch_count']}`, core mismatches `{main['core_mismatch_count']}`, greedy lifts `{main['greedy_lift_case_count']}`, max candidates `{main['max_total_candidates']}` |"
    )
    lines.append(
        f"| adversarial corpus | `{adversarial['ok']}` | `{adversarial['case_count']}` cases, `{adversarial['pattern_count']}` patterns, assignment-safe cases `{adversarial['assignment_safe_case_count']}`, greedy lifts `{adversarial['greedy_lift_case_count']}`, max candidates `{adversarial['max_candidate_count']}` |"
    )
    lines.append(
        f"| shared AB/CoW envelope | `{shared['ok']}` | Tau ok `{shared['tau_ok']}`, CoW matching ok `{shared['cow_matching_ok']}`, Tau cases `{', '.join(shared['tau_cases'])}` |"
    )
    lines.append("")
    lines.append("## Certificate Flags")
    lines.append("")
    lines.append("| flag | value |")
    lines.append("| --- | ---: |")
    for key in sorted(flags):
        lines.append(f"| `{key}` | `{flags[key]}` |")
    lines.append("")
    lines.append("## Tau Mode Checks")
    lines.append("")
    lines.append("| case | ok | rationale |")
    lines.append("| --- | --- | --- |")
    for row in tau["cases"]:
        lines.append(f"| `{row['case_id']}` | `{row['ok']}` | {row['rationale']} |")
    lines.append("")
    lines.append("## Mutation Checks")
    lines.append("")
    lines.append("| mutation | accepted | rationale |")
    lines.append("| --- | --- | --- |")
    for row in report["mutation_checks"]:
        lines.append(f"| `{row['mutation_id']}` | `{row['accepted']}` | {row['rationale']} |")
    lines.append("")
    lines.append("## Pattern Coverage")
    lines.append("")
    lines.append("| pattern | cases | exact mismatches | core mismatches | greedy lifts |")
    lines.append("| --- | ---: | ---: | ---: | ---: |")
    for pattern, row in sorted(adversarial["pattern_summary"].items()):
        lines.append(
            f"| `{pattern}` | `{row['cases']}` | `{row['exact_mismatches']}` | `{row['core_mismatches']}` | `{row['greedy_lifts']}` |"
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


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "report": str(REPORT_MD),
                "json": str(Path(args.output_json)),
                "tau_ok": report["tau"]["ok"],
                "flag_count": len(report["flags"]),
                "capacity_case_count": report["evidence"]["capacity_breakthrough"]["case_count"],
                "adversarial_case_count": report["evidence"]["capacity_adversarial"]["case_count"],
                "mutation_accepts": sum(1 for row in report["mutation_checks"] if row["accepted"]),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
