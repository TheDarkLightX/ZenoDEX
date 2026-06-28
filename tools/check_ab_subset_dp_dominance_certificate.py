#!/usr/bin/env python3
"""Replay a Tau-gated AB subset-DP dominance-pruning certificate."""

from __future__ import annotations

import argparse
import copy
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


OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_subset_dp_dominance_certificate_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_SUBSET_DP_DOMINANCE_CERTIFICATE_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "ab_subset_dp_dominance_certificate_v1.tau"

TOOL_COMMANDS: dict[str, tuple[str, ...]] = {
    "dominance_refuter": ("tools/check_ab_subset_dp_dominance_candidate.py",),
    "parity_reduction": ("tools/check_ab_subset_dp_dominance_pruning.py",),
    "adversarial_corpus": ("tools/check_ab_subset_dp_dominance_adversarial.py",),
    "boundary_refuter": ("tools/check_ab_subset_dp_dominance_boundary_refuter.py",),
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
        return {key: _strip_timing(item) for key, item in value.items() if key != "elapsed_ms"}
    if isinstance(value, list):
        return [_strip_timing(item) for item in value]
    return value


def _run_json_tool(command: Sequence[str], *, timeout_s: float = 90.0) -> dict[str, Any]:
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
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"{' '.join(command)} did not emit JSON: {proc.stdout[:1000]}") from exc
    if not isinstance(payload, dict):
        raise RuntimeError(f"{' '.join(command)} emitted a non-object JSON payload")
    return payload


def run_evidence_tools() -> dict[str, dict[str, Any]]:
    return {name: _run_json_tool(command) for name, command in TOOL_COMMANDS.items()}


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


def _summary(payload: Mapping[str, Any]) -> Mapping[str, Any]:
    value = payload.get("summary", {})
    return value if isinstance(value, Mapping) else {}


def _stats(payload: Mapping[str, Any]) -> Mapping[str, Any]:
    value = payload.get("stats", {})
    return value if isinstance(value, Mapping) else {}


def _reduction(payload: Mapping[str, Any], key: str) -> float:
    reductions = payload.get("aggregate_reductions", {})
    if not isinstance(reductions, Mapping):
        return 0.0
    try:
        return float(reductions.get(key, 0.0))
    except (TypeError, ValueError):
        return 0.0


def _int_field(payload: Mapping[str, Any], key: str) -> int:
    try:
        return int(payload.get(key, 0))
    except (TypeError, ValueError):
        return 0


def _scope_text(candidate: Mapping[str, Any]) -> str:
    rule = candidate.get("candidate_rule", {})
    if isinstance(rule, Mapping):
        domain = rule.get("domain", "")
        return str(domain)
    return ""


def _has_no_authority_rail(payload: Mapping[str, Any]) -> bool:
    non_claims = payload.get("non_claims", [])
    if not isinstance(non_claims, list):
        return False
    text = "\n".join(str(item).lower() for item in non_claims)
    return "no settlement authority" in text or "not modify production ordering" in text


def evidence_flags(
    evidence: Mapping[str, Mapping[str, Any]],
    deterministic_replay: Mapping[str, Any],
) -> dict[str, int]:
    candidate = evidence["dominance_refuter"]
    pruning = evidence["parity_reduction"]
    adversarial = evidence["adversarial_corpus"]
    boundary = evidence["boundary_refuter"]
    pruning_summary = _summary(pruning)
    adversarial_summary = _summary(adversarial)
    candidate_stats = _stats(candidate)

    scope_text = _scope_text(candidate).lower()
    boundary_exact_out = boundary.get("exact_out", {})
    boundary_mixed = boundary.get("mixed_direction", {})

    same_direction_exact_in_scope_ok = int(
        "same-direction" in scope_text
        and "exact-in" in scope_text
        and "same-pool" in scope_text
    )
    unpruned_parity_ok = int(
        bool(pruning.get("ok"))
        and _int_field(pruning_summary, "case_count") > 0
        and _int_field(pruning_summary, "mismatch_count") == 0
    )
    brute_force_parity_ok = int(
        _int_field(pruning_summary, "brute_mismatch_count") == 0
        and _int_field(adversarial_summary, "brute_mismatch_count") == 0
        and _int_field(pruning_summary, "case_count") > 0
        and _int_field(adversarial_summary, "case_count") > 0
    )
    dominance_refutation_ok = int(
        bool(candidate.get("ok"))
        and candidate.get("first_counterexample") is None
        and _int_field(candidate_stats, "dominance_pairs_checked") > 0
        and _int_field(candidate_stats, "suffix_permutations_checked") > 0
    )
    adversarial_corpus_ok = int(
        bool(adversarial.get("ok"))
        and _int_field(adversarial_summary, "case_count") > 0
        and _int_field(adversarial_summary, "mismatch_count") == 0
    )
    boundary_refuters_ok = int(
        bool(boundary.get("ok"))
        and isinstance(boundary_exact_out, Mapping)
        and isinstance(boundary_mixed, Mapping)
        and bool(boundary_exact_out.get("counterexample_found"))
        and bool(boundary_mixed.get("counterexample_found"))
    )
    state_reduction_ok = int(
        _reduction(pruning, "state_insertion") > 1.0
        and _reduction(adversarial, "state_insertion") > 1.0
    )
    transition_reduction_ok = int(
        _reduction(pruning, "transitions") > 1.0
        and _reduction(adversarial, "transitions") > 1.0
    )
    deterministic_replay_ok = int(bool(deterministic_replay.get("ok")))
    resource_budget_ok = int(
        _int_field(candidate_stats, "dominance_pairs_checked") <= 5_000
        and _int_field(candidate_stats, "suffix_permutations_checked") <= 20_000
        and _int_field(pruning_summary, "case_count") <= 24
        and _int_field(adversarial_summary, "case_count") <= 40
    )
    no_authority_effect = int(all(_has_no_authority_rail(payload) for payload in evidence.values()))
    nonvacuous_pruning = int(
        _int_field(pruning_summary, "total_dominated_insertions_skipped") > 0
        and _int_field(adversarial_summary, "total_dominated_insertions_skipped") > 0
    )

    return {
        "same_direction_exact_in_scope_ok": same_direction_exact_in_scope_ok,
        "unpruned_parity_ok": unpruned_parity_ok,
        "brute_force_parity_ok": brute_force_parity_ok,
        "dominance_refutation_ok": dominance_refutation_ok,
        "adversarial_corpus_ok": adversarial_corpus_ok,
        "boundary_refuters_ok": boundary_refuters_ok,
        "state_reduction_ok": state_reduction_ok,
        "transition_reduction_ok": transition_reduction_ok,
        "deterministic_replay_ok": deterministic_replay_ok,
        "resource_budget_ok": resource_budget_ok,
        "no_authority_effect": no_authority_effect,
        "nonvacuous_pruning": nonvacuous_pruning,
    }


def _tau_step(flags: Mapping[str, int], *, active: int = 1, overrides: Mapping[str, int] | None = None) -> dict[str, int]:
    values = {
        "i1": int(active),
        "i2": int(flags.get("same_direction_exact_in_scope_ok", 0)),
        "i3": int(flags.get("unpruned_parity_ok", 0)),
        "i4": int(flags.get("brute_force_parity_ok", 0)),
        "i5": int(flags.get("dominance_refutation_ok", 0)),
        "i6": int(flags.get("adversarial_corpus_ok", 0)),
        "i7": int(flags.get("boundary_refuters_ok", 0)),
        "i8": int(flags.get("state_reduction_ok", 0)),
        "i9": int(flags.get("transition_reduction_ok", 0)),
        "i10": int(flags.get("deterministic_replay_ok", 0)),
        "i11": int(flags.get("resource_budget_ok", 0)),
        "i12": int(flags.get("no_authority_effect", 0)),
        "i13": int(flags.get("nonvacuous_pruning", 0)),
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
            "ab_dominance_certificate_pass",
            _tau_step(base_flags),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1, "o6": 0},
            "All host-computed evidence facts admit the scoped dominance-pruning certificate.",
        ),
        TauCase(
            "parity_reject",
            _tau_step(base_flags, overrides={"i3": 0}),
            {"o1": 0, "o5": 0},
            "Missing unpruned DP parity fails closed.",
        ),
        TauCase(
            "brute_force_reject",
            _tau_step(base_flags, overrides={"i4": 0}),
            {"o1": 0, "o5": 0},
            "Missing brute-force parity fails closed.",
        ),
        TauCase(
            "dominance_refuter_reject",
            _tau_step(base_flags, overrides={"i5": 0}),
            {"o2": 0, "o5": 0},
            "A bounded dominance-refuter gap cannot admit the certificate.",
        ),
        TauCase(
            "boundary_refuter_reject",
            _tau_step(base_flags, overrides={"i7": 0}),
            {"o2": 0, "o5": 0},
            "Missing unsupported-domain boundary witnesses fail closed.",
        ),
        TauCase(
            "performance_reject",
            _tau_step(base_flags, overrides={"i8": 0}),
            {"o3": 0, "o5": 0},
            "Missing state-reduction evidence fails closed.",
        ),
        TauCase(
            "determinism_reject",
            _tau_step(base_flags, overrides={"i10": 0}),
            {"o4": 0, "o5": 0},
            "Missing deterministic replay fails closed.",
        ),
        TauCase(
            "authority_reject",
            _tau_step(base_flags, overrides={"i12": 0}),
            {"o4": 0, "o5": 0, "o6": 0},
            "A certificate with authority effects is rejected.",
        ),
        TauCase(
            "inactive_safe",
            _tau_step(base_flags, active=0),
            {"o5": 0, "o6": 1},
            "Inactive certificates do not admit while the no-authority rail remains true.",
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


def _mutation_checks(base_flags: Mapping[str, int]) -> list[dict[str, Any]]:
    tau = _run_tau_cases(base_flags)
    rows: list[dict[str, Any]] = []
    for case in tau.get("cases", []):
        if case.get("case_id") in {"ab_dominance_certificate_pass", "inactive_safe"}:
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
    candidate = evidence["dominance_refuter"]
    pruning = evidence["parity_reduction"]
    adversarial = evidence["adversarial_corpus"]
    boundary = evidence["boundary_refuter"]
    return {
        "dominance_refuter": {
            "ok": bool(candidate.get("ok")),
            "stats": dict(_stats(candidate)),
            "first_counterexample": candidate.get("first_counterexample"),
            "bounds": candidate.get("bounds"),
        },
        "parity_reduction": {
            "ok": bool(pruning.get("ok")),
            "summary": dict(_summary(pruning)),
            "aggregate_reductions": pruning.get("aggregate_reductions"),
            "bounds": pruning.get("bounds"),
        },
        "adversarial_corpus": {
            "ok": bool(adversarial.get("ok")),
            "seed": adversarial.get("seed"),
            "summary": dict(_summary(adversarial)),
            "aggregate_reductions": adversarial.get("aggregate_reductions"),
            "unsupported_domain_controls": adversarial.get("unsupported_domain_controls"),
        },
        "boundary_refuter": {
            "ok": bool(boundary.get("ok")),
            "boundary_decision": boundary.get("boundary_decision"),
            "exact_out_counterexample_found": bool(
                isinstance(boundary.get("exact_out"), Mapping)
                and boundary["exact_out"].get("counterexample_found")
            ),
            "mixed_direction_counterexample_found": bool(
                isinstance(boundary.get("mixed_direction"), Mapping)
                and boundary["mixed_direction"].get("counterexample_found")
            ),
            "exact_out_reason": boundary.get("exact_out", {}).get("reason")
            if isinstance(boundary.get("exact_out"), Mapping)
            else None,
            "mixed_direction_reason": boundary.get("mixed_direction", {}).get("reason")
            if isinstance(boundary.get("mixed_direction"), Mapping)
            else None,
        },
    }


def build_report() -> dict[str, Any]:
    evidence = run_evidence_tools()
    deterministic = _deterministic_replay(evidence)
    flags = evidence_flags(evidence, deterministic)
    tau = _run_tau_cases(flags)
    mutation_rows = _mutation_checks(flags)
    all_flags_ok = all(int(value) == 1 for value in flags.values())
    ok = bool(all_flags_ok and tau.get("ok") and all(not bool(row["accepted"]) for row in mutation_rows))
    return {
        "schema": "zenodex.ab_subset_dp_dominance_certificate_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "spec_id": "ab_subset_dp_dominance_certificate_v1",
        "summary": (
            "A Tau host-projected certificate gates same-pool, same-direction, exact-in AB subset-DP "
            "dominance pruning by requiring bounded DP parity, brute-force parity, dominance refutation, "
            "unsupported-domain boundary witnesses, replay determinism, resource limits, nonvacuous pruning, "
            "and no authority effects."
        ),
        "authority_boundary": (
            "Tau admits a research certificate only. It does not compute swaps, run DP, prune states, "
            "select AB orders, or authorize settlement."
        ),
        "flags": flags,
        "tau": tau,
        "evidence": _evidence_summary(evidence),
        "deterministic_replay": deterministic,
        "mutation_checks": mutation_rows,
        "new_specification_frontier": [
            {
                "spec": str(TAU_SPEC.relative_to(REPO_ROOT)),
                "benefit": (
                    "Turns AB dominance-pruned subset DP into a replay-gated research lane with explicit "
                    "unsupported-domain witnesses."
                ),
            },
            {
                "spec": "src/tau_specs/recommended/route_split_window_certificate_v1.tau",
                "benefit": "Existing route-split rail for local-window exact-out split certificates.",
            },
            {
                "spec": "src/tau_specs/recommended/negative_frontier_entropy_scheduler_v1.tau",
                "benefit": "Existing frontier-selection rail for high-value falsifier campaigns.",
            },
        ],
        "non_claims": [
            "This artifact is a research certificate, not a production ordering change.",
            "The dominance rule is scoped to same-pool, same-direction, exact-in AB subset-DP states.",
            "Exact-out and mixed-direction counterexamples are unsupported-domain boundary witnesses.",
            "Passing this bounded corpus is not a machine-checked proof of universal dominance.",
            "Tau does not compute the DP, dominance relation, swaps, balances, hashes, or settlement effects.",
        ],
        "replay_command": "python3 tools/check_ab_subset_dp_dominance_certificate.py",
    }


def _fmt_ratio(value: Any) -> str:
    try:
        return f"{float(value):.2f}x"
    except (TypeError, ValueError):
        return "n/a"


def _write_markdown(report: Mapping[str, Any]) -> None:
    evidence = report["evidence"]
    pruning = evidence["parity_reduction"]
    adversarial = evidence["adversarial_corpus"]
    candidate = evidence["dominance_refuter"]
    boundary = evidence["boundary_refuter"]
    flags = report["flags"]
    tau = report["tau"]

    lines: list[str] = []
    lines.append("# ZenoDEX AB Subset-DP Dominance Certificate - 2026-06-28")
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
    lines.append("The spec requires exact-in same-direction scope, unpruned DP parity, brute-force parity, bounded dominance refutation, adversarial parity, exact-out and mixed-direction boundary witnesses, performance evidence, deterministic replay, resource budget, and no authority effects.")
    lines.append("")
    lines.append("## Evidence Summary")
    lines.append("")
    lines.append("| component | result | key receipt |")
    lines.append("| --- | --- | --- |")
    lines.append(
        f"| dominance refuter | `{candidate['ok']}` | `{candidate['stats']['dominance_pairs_checked']}` checked pairs, `{candidate['stats']['suffix_permutations_checked']}` suffix permutations, first counterexample `{candidate['first_counterexample']}` |"
    )
    lines.append(
        f"| parity reduction | `{pruning['ok']}` | `{pruning['summary']['case_count']}` cases, state reduction `{_fmt_ratio(pruning['aggregate_reductions']['state_insertion'])}`, transition reduction `{_fmt_ratio(pruning['aggregate_reductions']['transitions'])}` |"
    )
    lines.append(
        f"| adversarial corpus | `{adversarial['ok']}` | `{adversarial['summary']['case_count']}` cases, seed `{adversarial['seed']}`, state reduction `{_fmt_ratio(adversarial['aggregate_reductions']['state_insertion'])}`, transition reduction `{_fmt_ratio(adversarial['aggregate_reductions']['transitions'])}` |"
    )
    lines.append(
        f"| boundary refuter | `{boundary['ok']}` | exact-out witness `{boundary['exact_out_counterexample_found']}`, mixed-direction witness `{boundary['mixed_direction_counterexample_found']}` |"
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
    lines.append("## Boundary Witnesses")
    lines.append("")
    lines.append(f"- Exact-out: {boundary['exact_out_reason']}")
    lines.append(f"- Mixed-direction: {boundary['mixed_direction_reason']}")
    lines.append("")
    lines.append("These witnesses are part of the certificate boundary. They prevent reusing the exact-in dominance rule in domains where its order relation is known to fail.")
    lines.append("")
    lines.append("## New Specification Frontier")
    lines.append("")
    for item in report["new_specification_frontier"]:
        lines.append(f"- `{item['spec']}`: {item['benefit']}")
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
                "dominance_pairs_checked": report["evidence"]["dominance_refuter"]["stats"]["dominance_pairs_checked"],
                "parity_case_count": report["evidence"]["parity_reduction"]["summary"]["case_count"],
                "adversarial_case_count": report["evidence"]["adversarial_corpus"]["summary"]["case_count"],
                "boundary_ok": report["evidence"]["boundary_refuter"]["ok"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
