#!/usr/bin/env python3
"""Replay a Tau-produced optimizer quotient-certificate breakthrough."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from tools.zenodex_route_dominance_frontier_refuter_20260627 import (  # noqa: E402
    ASSET_A,
    ASSET_B,
    ASSET_C,
    MAX_ROUTE_LABELS,
    RouteLabel,
    _label_to_json,
    _pool,
    _route_pools,
    enumerate_route_labels,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tau_optimizer_quotient_breakthrough_20260627"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_TAU_OPTIMIZER_QUOTIENT_BREAKTHROUGH_20260627.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "optimizer_quotient_certificate_v1.tau"


@dataclass(frozen=True)
class RouteCase:
    case_id: str
    pools: tuple[Any, ...]
    amount_out: int
    note: str


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


def _route_label_payloads(labels: tuple[RouteLabel, ...]) -> list[dict[str, Any]]:
    return [_label_to_json(label) for label in labels]


def route_domain_hash(labels: tuple[RouteLabel, ...]) -> str:
    return _sha256_json(_route_label_payloads(labels))


def build_quotient_certificate(labels: tuple[RouteLabel, ...]) -> dict[str, Any]:
    if not labels:
        raise ValueError("cannot build quotient certificate for an empty route domain")
    selected = min(labels, key=lambda label: label.objective_key)
    return {
        "schema": "zenodex.optimizer_quotient_certificate.v1",
        "domain_hash": route_domain_hash(labels),
        "label_count": len(labels),
        "mode": "route_dominance",
        "pruned_count": len(labels) - 1,
        "quotient_rule": "single_selected_label_dominates_full_domain_under_objective_key",
        "selected_objective_key": [int(selected.route.amount_in), list(selected.objective_key[1]), selected.route_id],
        "selected_route_id": selected.route_id,
    }


def verify_quotient_certificate(
    certificate: Mapping[str, Any],
    labels: tuple[RouteLabel, ...],
) -> dict[str, Any]:
    labels_by_id = {label.route_id: label for label in labels}
    selected = labels_by_id.get(str(certificate.get("selected_route_id", "")))
    best = min(labels, key=lambda label: label.objective_key) if labels else None
    label_count = certificate.get("label_count")
    pruned_count = certificate.get("pruned_count")
    expected_objective = (
        [int(selected.route.amount_in), list(selected.objective_key[1]), selected.route_id]
        if selected is not None
        else None
    )
    domain_commitment_ok = certificate.get("domain_hash") == route_domain_hash(labels)
    quotient_witness_ok = (
        selected is not None
        and best is not None
        and selected.route_id == best.route_id
        and label_count == len(labels)
        and pruned_count == max(0, len(labels) - 1)
    )
    canonical_winner_ok = (
        selected is not None
        and best is not None
        and selected.objective_key == best.objective_key
        and certificate.get("selected_objective_key") == expected_objective
    )
    replay_ok = selected is not None and int(selected.route.amount_in) > 0 and all(
        hop.amount_in > 0 and hop.amount_out > 0
        for leg in selected.route.legs
        for hop in leg.hops
    )
    projection_cover_ok = label_count == len(labels) and pruned_count == max(0, len(labels) - 1)
    arithmetic_scope_ok = bool(labels) and all(int(label.route.amount_in) > 0 for label in labels)
    resource_budget_ok = 0 < len(labels) <= MAX_ROUTE_LABELS
    flags = {
        "domain_commitment_ok": int(domain_commitment_ok),
        "quotient_witness_ok": int(quotient_witness_ok),
        "canonical_winner_ok": int(canonical_winner_ok),
        "replay_ok": int(replay_ok),
        "projection_cover_ok": int(projection_cover_ok),
        "arithmetic_scope_ok": int(arithmetic_scope_ok),
        "resource_budget_ok": int(resource_budget_ok),
    }
    failed = [name for name, value in flags.items() if value != 1]
    return {
        "ok": not failed,
        "flags": flags,
        "failed_flags": failed,
        "best_route_id": best.route_id if best else None,
        "selected_route_id": selected.route_id if selected else None,
        "label_count": len(labels),
    }


def _wide_route_pools() -> tuple[Any, ...]:
    return tuple(
        sorted(
            (
                _pool("p_ab_direct_0", ASSET_A, ASSET_B, 4_400, 1_800, 30),
                _pool("p_ab_direct_1", ASSET_A, ASSET_B, 5_300, 2_100, 30),
                _pool("p_ab_direct_2", ASSET_A, ASSET_B, 6_100, 2_450, 35),
                _pool("p_ab_direct_3", ASSET_A, ASSET_B, 7_200, 2_950, 45),
                _pool("p_ac_0", ASSET_A, ASSET_C, 4_700, 3_100, 30),
                _pool("p_cb_0", ASSET_C, ASSET_B, 4_900, 2_800, 30),
            ),
            key=lambda pool: pool.pool_id,
        )
    )


def _twohop_route_pools() -> tuple[Any, ...]:
    return tuple(
        sorted(
            (
                _pool("p_ab_direct_low_fee", ASSET_A, ASSET_B, 3_800, 1_260, 15),
                _pool("p_ab_direct_deep_fee", ASSET_A, ASSET_B, 7_000, 2_020, 60),
                _pool("p_ac_deep", ASSET_A, ASSET_C, 6_500, 4_600, 30),
                _pool("p_ac_thin", ASSET_A, ASSET_C, 2_400, 2_100, 20),
                _pool("p_cb_deep", ASSET_C, ASSET_B, 6_800, 4_200, 30),
                _pool("p_cb_fee", ASSET_C, ASSET_B, 4_500, 3_400, 80),
            ),
            key=lambda pool: pool.pool_id,
        )
    )


def route_cases() -> tuple[RouteCase, ...]:
    return (
        RouteCase(
            case_id="baseline_route_amount42",
            pools=_route_pools(),
            amount_out=42,
            note="Existing direct/two-hop/split exact-out route label domain.",
        ),
        RouteCase(
            case_id="wide_split_route_amount36",
            pools=_wide_route_pools(),
            amount_out=36,
            note="Four direct pools create a split-heavy bounded domain under the 256-label cap.",
        ),
        RouteCase(
            case_id="twohop_route_amount48",
            pools=_twohop_route_pools(),
            amount_out=48,
            note="Two-hop alternatives stress the domain hash and selected-label replay path.",
        ),
    )


def _route_case_result(case: RouteCase) -> dict[str, Any]:
    labels = enumerate_route_labels(case.pools, asset_in=ASSET_A, asset_out=ASSET_B, amount_out=case.amount_out)
    certificate = build_quotient_certificate(labels)
    verification = verify_quotient_certificate(certificate, labels)
    full_payload = _route_label_payloads(labels)
    full_domain_bytes = len(_canonical_json_bytes(full_payload))
    certificate_bytes = len(_canonical_json_bytes(certificate))
    compression_ratio = full_domain_bytes / certificate_bytes if certificate_bytes else None
    selected = min(labels, key=lambda label: label.objective_key) if labels else None
    return {
        "case_id": case.case_id,
        "note": case.note,
        "ok": verification["ok"] and certificate_bytes < full_domain_bytes,
        "amount_out": case.amount_out,
        "label_count": len(labels),
        "selected_route_id": selected.route_id if selected else None,
        "selected_amount_in": int(selected.route.amount_in) if selected else None,
        "domain_hash": certificate["domain_hash"],
        "full_domain_bytes": full_domain_bytes,
        "quotient_certificate_bytes": certificate_bytes,
        "compression_ratio": compression_ratio,
        "certificate": certificate,
        "verification": verification,
    }


def _sbf_step(*, active: int = 1, mode: str = "route", flags: Mapping[str, int] | None = None) -> dict[str, int]:
    values = {
        "i1": active,
        "i2": 1,
        "i3": 1,
        "i4": 1,
        "i5": 1,
        "i6": 1,
        "i7": 1,
        "i8": 1,
        "i9": 1,
        "i10": 1,
        "i11": 1,
        "i12": 0,
        "i13": 0,
        "i14": 0,
    }
    if mode == "route":
        values["i12"] = 1
    elif mode == "ab":
        values["i13"] = 1
    elif mode == "cow":
        values["i14"] = 1
    elif mode == "none":
        pass
    else:
        raise ValueError(f"unknown mode: {mode}")
    if flags:
        values.update({key: int(value) for key, value in flags.items()})
    return values


def tau_cases() -> tuple[TauCase, ...]:
    return (
        TauCase(
            "route_quotient_pass",
            _sbf_step(mode="route"),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0, "o6": 0, "o7": 1},
            "A fully verified route quotient certificate admits only the route output.",
        ),
        TauCase(
            "ab_work_item_1_pass",
            _sbf_step(mode="ab"),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 0, "o5": 1, "o6": 0, "o7": 1},
            "The same quotient surface admits an AB full-state subset-DP certificate.",
        ),
        TauCase(
            "cow_work_item_2_pass",
            _sbf_step(mode="cow"),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 0, "o5": 0, "o6": 1, "o7": 1},
            "The same quotient surface admits an uncoupled CoW assignment certificate.",
        ),
        TauCase(
            "domain_commitment_reject",
            _sbf_step(mode="route", flags={"i2": 0}),
            {"o2": 0, "o4": 0, "o7": 0},
            "A stale or mismatched domain hash fails closed.",
        ),
        TauCase(
            "quotient_witness_reject",
            _sbf_step(mode="route", flags={"i3": 0}),
            {"o2": 0, "o4": 0, "o7": 0},
            "A missing representative/dominator witness cannot admit.",
        ),
        TauCase(
            "two_modes_reject",
            _sbf_step(mode="route", flags={"i13": 1}),
            {"o1": 0, "o4": 0, "o5": 0, "o7": 0},
            "Two optimizer modes fail one-hot decoding.",
        ),
        TauCase(
            "authority_reject",
            _sbf_step(mode="cow", flags={"i10": 0}),
            {"o3": 0, "o6": 0, "o7": 0},
            "A certificate with authority-bearing effects is rejected.",
        ),
        TauCase(
            "inactive_safe",
            _sbf_step(active=0, mode="none", flags={"i2": 0, "i3": 0, "i4": 0, "i5": 0, "i6": 0, "i7": 0, "i8": 0, "i9": 1, "i11": 0}),
            {"o1": 0, "o2": 0, "o7": 0, "o8": 1},
            "Inactive requests do not admit, while the no-authority rail remains safe.",
        ),
    )


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _tau_git_head() -> str | None:
    proc = subprocess.run(
        ["git", "-C", "external/tau-lang", "rev-parse", "--short", "HEAD"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )
    if proc.returncode != 0:
        return None
    return proc.stdout.strip()


def _run_tau_cases() -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "cases": []}
    cases = tau_cases()
    started = time.monotonic()
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[case.step for case in cases],
        timeout_s=15.0,
    )
    elapsed_s = time.monotonic() - started
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
        "tau_bin": tau_bin,
        "tau_version": _tau_version(tau_bin),
        "tau_git_head": _tau_git_head(),
        "elapsed_s": elapsed_s,
        "cases": rows,
    }


def _mutated_certificate_checks() -> list[dict[str, Any]]:
    labels = enumerate_route_labels(route_cases()[0].pools, asset_in=ASSET_A, asset_out=ASSET_B, amount_out=route_cases()[0].amount_out)
    certificate = build_quotient_certificate(labels)
    mutations: list[tuple[str, dict[str, Any]]] = []
    bad_hash = copy.deepcopy(certificate)
    bad_hash["domain_hash"] = "0" * 64
    mutations.append(("bad_domain_hash", bad_hash))
    bad_selected = copy.deepcopy(certificate)
    bad_selected["selected_route_id"] = labels[-1].route_id
    mutations.append(("bad_selected_route", bad_selected))
    bad_count = copy.deepcopy(certificate)
    bad_count["label_count"] = int(bad_count["label_count"]) - 1
    mutations.append(("bad_label_count", bad_count))
    return [
        {
            "mutation": name,
            "accepted": verify_quotient_certificate(mutated, labels)["ok"],
            "failed_flags": verify_quotient_certificate(mutated, labels)["failed_flags"],
        }
        for name, mutated in mutations
    ]


def build_report() -> dict[str, Any]:
    route_rows = [_route_case_result(case) for case in route_cases()]
    tau = _run_tau_cases()
    mutation_rows = _mutated_certificate_checks()
    ratios = [float(row["compression_ratio"]) for row in route_rows if row["compression_ratio"] is not None]
    ok = (
        bool(route_rows)
        and all(row["ok"] for row in route_rows)
        and tau.get("ok") is True
        and all(not row["accepted"] for row in mutation_rows)
    )
    return {
        "schema": "zenodex.tau_optimizer_quotient_breakthrough_report.v1",
        "date": "2026-06-27",
        "ok": ok,
        "breakthrough": {
            "spec_id": "optimizer_quotient_certificate_v1",
            "summary": "A Tau host-projected quotient certificate turns bounded route-label domains into small domain-hash-bound proof packets and provides the same admission shape for AB ordering and CoW matching proof surfaces.",
            "authority_boundary": "Tau admits optimizer certificates only; deterministic host/kernel verifiers remain authoritative for settlement, routing, and matching.",
        },
        "tau": tau,
        "route_quotient": {
            "ok": all(row["ok"] for row in route_rows),
            "case_count": len(route_rows),
            "max_label_count": max(row["label_count"] for row in route_rows),
            "min_compression_ratio": min(ratios) if ratios else None,
            "max_compression_ratio": max(ratios) if ratios else None,
            "cases": route_rows,
        },
        "mutation_checks": mutation_rows,
        "algorithm_work_items": {
            "1": {
                "name": "AB ordering",
                "tau_mode": "mode_ab_ordering",
                "benefit": "The same quotient envelope can gate a domain-hash-bound full-state subset-DP certificate without putting DP state expansion in Tau.",
                "existing_artifact": "src/tau_specs/recommended/ab_cow_exact_solver_envelope_v1.tau",
            },
            "2": {
                "name": "CoW matching",
                "tau_mode": "mode_cow_matching",
                "benefit": "The same quotient envelope can gate an uncoupled Hungarian assignment certificate and reject stale, authority-bearing, or grouped-capacity proof surfaces.",
                "existing_artifact": "src/tau_specs/recommended/ab_cow_exact_solver_envelope_v1.tau",
            },
        },
        "tau_language_frontier": {
            "observed_latest_tau": tau.get("tau_version"),
            "observed_latest_checkout": tau.get("tau_git_head"),
            "effective_design_rule": "Use Tau for small Boolean proof-surface composition and mode diagnostics; keep hashes, large arithmetic, route enumeration, DP, and matching in deterministic host/kernel code.",
            "spec_complexity": {
                "inputs": 14,
                "outputs": 8,
                "host_projected_flags": 10,
                "direct_bv_ops": 0,
                "non_comment_lines": len(
                    [
                        line
                        for line in TAU_SPEC.read_text(encoding="utf-8").splitlines()
                        if line.strip() and not line.strip().startswith("#")
                    ]
                ),
                "bytes": len(TAU_SPEC.read_bytes()),
            },
        },
        "non_claims": [
            "The route measurement covers the bounded direct/two-hop/parallel-split label generator used by the refuter, not every possible path family.",
            "The quotient certificate commits to a recomputable domain; it is not useful without host replay of that domain.",
            "Tau does not compute the domain hash or the optimizer winner.",
            "The AB and CoW modes are proof-surface gates for existing host algorithms, not new settlement authority.",
        ],
        "replay_command": "python3 tools/zenodex_tau_optimizer_quotient_breakthrough_20260627.py",
    }


def write_markdown(report: Mapping[str, Any], output: Path) -> None:
    tau = report["tau"]
    route = report["route_quotient"]
    lines: list[str] = []
    lines.append("# ZenoDEX Tau Optimizer Quotient Breakthrough - 2026-06-27")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(report["breakthrough"]["summary"])
    lines.append("")
    lines.append(report["breakthrough"]["authority_boundary"])
    lines.append("")
    lines.append("## Breakthrough Specification")
    lines.append("")
    lines.append("- Spec: `src/tau_specs/recommended/optimizer_quotient_certificate_v1.tau`")
    lines.append(f"- Latest Tau: `{tau.get('tau_version')}`")
    lines.append(f"- Tau trace replay ok: `{tau.get('ok')}`")
    lines.append(f"- Tau elapsed: `{float(tau.get('elapsed_s') or 0.0):.6f}s`")
    lines.append("")
    lines.append("The spec accepts exactly one optimizer mode per step: route dominance, AB ordering, or CoW matching. It requires a domain commitment, quotient witness, canonical winner proof, replay, projection cover, arithmetic scope, resource budget, fallback, no-authority, and non-vacuity.")
    lines.append("")
    lines.append("## Route Quotient Evidence")
    lines.append("")
    lines.append(
        f"Route cases: `{route['case_count']}`. Max labels: `{route['max_label_count']}`. Min compression ratio: `{float(route['min_compression_ratio']):.2f}x`. Max compression ratio: `{float(route['max_compression_ratio']):.2f}x`."
    )
    lines.append("")
    lines.append("| case | labels | full bytes | cert bytes | ratio | selected |")
    lines.append("| --- | ---: | ---: | ---: | ---: | --- |")
    for row in route["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['label_count']}` | `{row['full_domain_bytes']}` | `{row['quotient_certificate_bytes']}` | `{float(row['compression_ratio']):.2f}x` | `{row['selected_route_id']}` |"
        )
    lines.append("")
    lines.append("The verifier recomputes the route-label domain, checks the domain hash, proves that the selected label is the canonical minimum under the objective key, and confirms that every omitted label is covered by the single selected representative.")
    lines.append("")
    lines.append("## Tau Mode Checks")
    lines.append("")
    lines.append("| case | ok | rationale |")
    lines.append("| --- | --- | --- |")
    for case in tau.get("cases", []):
        lines.append(f"| `{case['case_id']}` | `{case['ok']}` | {case['rationale']} |")
    lines.append("")
    lines.append("## Work Items 1 And 2")
    lines.append("")
    lines.append("### 1. AB Ordering")
    lines.append("")
    lines.append(report["algorithm_work_items"]["1"]["benefit"])
    lines.append("")
    lines.append("### 2. CoW Matching")
    lines.append("")
    lines.append(report["algorithm_work_items"]["2"]["benefit"])
    lines.append("")
    lines.append("## Tau Language Design Frontier")
    lines.append("")
    frontier = report["tau_language_frontier"]
    lines.append(frontier["effective_design_rule"])
    lines.append("")
    lines.append(
        f"This spec uses `{frontier['spec_complexity']['inputs']}` inputs, `{frontier['spec_complexity']['outputs']}` outputs, `{frontier['spec_complexity']['host_projected_flags']}` host-projected proof facts, and `{frontier['spec_complexity']['direct_bv_ops']}` direct bitvector operations."
    )
    lines.append("")
    lines.append("## Mutation Checks")
    lines.append("")
    lines.append("| mutation | accepted | failed flags |")
    lines.append("| --- | --- | --- |")
    for row in report["mutation_checks"]:
        failed = ", ".join(f"`{flag}`" for flag in row["failed_flags"]) or "none"
        lines.append(f"| `{row['mutation']}` | `{row['accepted']}` | {failed} |")
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


def run(output_json: Path = REPORT_JSON, output_md: Path = REPORT_MD) -> dict[str, Any]:
    report = build_report()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(report, output_md)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(REPORT_JSON))
    parser.add_argument("--output-md", default=str(REPORT_MD))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json), Path(args.output_md))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "breakthrough": report["breakthrough"]["spec_id"],
                "route_case_count": report["route_quotient"]["case_count"],
                "min_compression_ratio": report["route_quotient"]["min_compression_ratio"],
                "tau_ok": report["tau"].get("ok"),
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
