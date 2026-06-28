#!/usr/bin/env python3
"""Adversarial replay for the Tau route-split window certificate."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.zenodex_tau_route_split_window_breakthrough_20260628 import (  # noqa: E402
    MAX_FULL_SWEEP_POINTS,
    SplitCase,
    _full_scan,
    _pool,
    _run_tau_cases,
    _windowed_search,
    verify_split_certificate,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_route_split_window_adversarial_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_ROUTE_SPLIT_WINDOW_ADVERSARIAL_20260628.md"


def adversarial_split_cases() -> tuple[SplitCase, ...]:
    """Return deterministic CPMM exact-out split fixtures with full-sweep oracles."""
    families = (
        (
            "endpoint_low_fee",
            (6_000, 6_000, 9_000, 4_000, 30, 5, 2_000),
            "Endpoint winner with asymmetric reserves and lower fee on the second pool.",
        ),
        (
            "interior_plateau",
            (20_000, 15_000, 8_000, 12_000, 30, 75, 5_000),
            "Interior winner with integer rounding plateaus near the derivative seed.",
        ),
        (
            "large_endpoint",
            (12_000, 30_000, 17_000, 18_000, 15, 30, 9_000),
            "Wide-domain endpoint winner under unequal reserves.",
        ),
        (
            "rounding_gap",
            (4_000, 7_000, 25_000, 10_000, 30, 5, 4_000),
            "Interior winner where naive first-difference monotonicity fails.",
        ),
        (
            "fee_skew",
            (9_000, 11_000, 14_000, 9_000, 5, 95, 3_500),
            "Strong fee skew with interior-to-endpoint pressure.",
        ),
        (
            "deep_shallow",
            (5_000, 19_000, 50_000, 8_000, 100, 1, 6_500),
            "Deep input reserve against shallow output reserve with fee asymmetry.",
        ),
        (
            "zero_endpoint",
            (75_000, 9_500, 12_000, 22_000, 2, 88, 7_000),
            "Left endpoint winner where the canonical route uses only pool1 output.",
        ),
        (
            "balanced_tie_pressure",
            (10_500, 10_500, 10_600, 10_400, 30, 30, 5_000),
            "Near-symmetric reserves stress canonical tie-breaking around the middle.",
        ),
    )
    deltas = (0, 137, 509)
    rows: list[SplitCase] = []
    for family_idx, (family, params, note) in enumerate(families, start=1):
        reserve_a0, reserve_b0, reserve_a1, reserve_b1, fee0, fee1, amount_out = params
        for variant_idx, delta in enumerate(deltas):
            case_idx = (family_idx - 1) * len(deltas) + variant_idx + 1
            p0 = _pool(
                f"adv{case_idx:02d}_a",
                int(reserve_a0) + int(delta),
                int(reserve_b0) + 2 * int(delta),
                int(fee0),
            )
            p1 = _pool(
                f"adv{case_idx:02d}_b",
                int(reserve_a1) + 3 * int(delta),
                int(reserve_b1) + int(delta),
                int(fee1),
            )
            bounded_amount = min(
                int(amount_out) + int(delta) // 3,
                int(p0.reserve1) + int(p1.reserve1) - 2,
                MAX_FULL_SWEEP_POINTS - 2,
            )
            rows.append(
                SplitCase(
                    case_id=f"{family}_v{variant_idx}",
                    pool0=p0,
                    pool1=p1,
                    amount_out_total=int(bounded_amount),
                    window=32,
                    brute_force_max=512,
                    note=note,
                )
            )
    return tuple(rows)


def _certificate_from_replay(
    case: SplitCase,
    full: Mapping[str, Any],
    windowed: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "schema": "zenodex.route_split_window_certificate.v1",
        "case_id": case.case_id,
        "domain_hash": full["domain_hash"],
        "amount_out_total": int(case.amount_out_total),
        "window": int(case.window),
        "brute_force_max": int(case.brute_force_max),
        "lo": int(full["lo"]),
        "hi": int(full["hi"]),
        "feasible_split_count": int(full["feasible_split_count"]),
        "selected_q0": int(windowed["q0"]),
        "selected_q1": int(windowed["q1"]),
        "selected_amount_in_total": int(windowed["total_input"]),
        "search_point_count": int(windowed["search_point_count"]),
        "search_ranges": copy.deepcopy(windowed["search_ranges"]),
        "quotient_rule": "derivative_seed_plus_window_search_with_bounded_full_oracle_parity",
    }


def _winner_kind(q0: int, lo: int, hi: int) -> str:
    if int(q0) == int(lo):
        return "left_endpoint"
    if int(q0) == int(hi):
        return "right_endpoint"
    return "interior"


def _case_row(case: SplitCase) -> dict[str, Any]:
    full = _full_scan(case)
    windowed = _windowed_search(case)
    certificate = _certificate_from_replay(case, full, windowed)
    verification = verify_split_certificate(case, certificate)
    full_best = verification["full_scan"]["best"]
    replay = verification["windowed_search"]
    mismatch = (
        int(full_best["q0"]) != int(replay["q0"])
        or int(full_best["total_input"]) != int(replay["total_input"])
        or int(certificate["selected_q0"]) != int(full_best["q0"])
        or int(certificate["selected_amount_in_total"]) != int(full_best["total_input"])
    )
    full_quotes = int(verification["full_scan"]["quote_call_count"])
    window_quotes = int(replay["quote_call_count"])
    return {
        "case_id": case.case_id,
        "note": case.note,
        "ok": bool(verification["ok"]) and not mismatch,
        "full_window_mismatch": bool(mismatch),
        "winner_kind": _winner_kind(int(full_best["q0"]), int(full["lo"]), int(full["hi"])),
        "amount_out_total": int(case.amount_out_total),
        "feasible_split_count": int(full["feasible_split_count"]),
        "full_best_q0": int(full_best["q0"]),
        "windowed_q0": int(replay["q0"]),
        "best_amount_in_total": int(full_best["total_input"]),
        "full_scan_quote_calls": full_quotes,
        "windowed_quote_calls": window_quotes,
        "quote_call_reduction_ratio": full_quotes / window_quotes if window_quotes else None,
        "first_differences_nondecreasing": bool(
            full["integer_rounding_shape"]["first_differences_nondecreasing"]
        ),
        "min_q0_range": full["integer_rounding_shape"]["min_q0_range"],
        "failed_flags": verification["failed_flags"],
        "certificate": certificate,
    }


def _mutation_checks(case: SplitCase) -> list[dict[str, Any]]:
    full = _full_scan(case)
    windowed = _windowed_search(case)
    certificate = _certificate_from_replay(case, full, windowed)
    mutations: list[tuple[str, dict[str, Any], str]] = []

    bad_hash = dict(certificate)
    bad_hash["domain_hash"] = "0" * 64
    mutations.append(("bad_domain_hash", bad_hash, "domain hash must bind the full-sweep oracle surface"))

    bad_q0 = dict(certificate)
    bad_q0["selected_q0"] = int(certificate["selected_q0"]) + 1
    mutations.append(("bad_selected_q0", bad_q0, "winner index must match replay and bounded full sweep"))

    bad_amount = dict(certificate)
    bad_amount["selected_amount_in_total"] = int(certificate["selected_amount_in_total"]) - 1
    mutations.append(("bad_amount_in_total", bad_amount, "amount input total must replay exactly"))

    bad_points = dict(certificate)
    bad_points["search_point_count"] = int(certificate["search_point_count"]) + 1
    mutations.append(("bad_search_point_count", bad_points, "search point count must match the replayed ranges"))

    rows: list[dict[str, Any]] = []
    for mutation_id, mutated, rationale in mutations:
        verification = verify_split_certificate(case, mutated)
        rows.append(
            {
                "mutation_id": mutation_id,
                "accepted": bool(verification["ok"]),
                "failed_flags": verification["failed_flags"],
                "rationale": rationale,
            }
        )
    return rows


def build_report() -> dict[str, Any]:
    cases = adversarial_split_cases()
    case_rows = [_case_row(case) for case in cases]
    mutation_rows = _mutation_checks(cases[4])
    tau = _run_tau_cases(
        {
            "domain_nonempty": 1,
            "window_search_replayed": 1,
            "local_window_certificate_ok": 1,
            "full_oracle_parity_ok": 1,
            "quote_replay_ok": 1,
            "integer_rounding_scope_ok": 1,
            "resource_budget_ok": 1,
            "fallback_available_or_explicit_failure": 1,
            "no_settlement_authority": 1,
            "exact_out_scope_ok": 1,
        }
    )
    ratios = [float(row["quote_call_reduction_ratio"]) for row in case_rows if row["quote_call_reduction_ratio"]]
    winner_kinds = sorted({str(row["winner_kind"]) for row in case_rows})
    monotonic_failures = [row["case_id"] for row in case_rows if not bool(row["first_differences_nondecreasing"])]
    mismatch_count = sum(1 for row in case_rows if bool(row["full_window_mismatch"]))
    ok = (
        all(bool(row["ok"]) for row in case_rows)
        and mismatch_count == 0
        and bool(monotonic_failures)
        and all(not bool(row["accepted"]) for row in mutation_rows)
        and bool(tau["ok"])
    )
    return {
        "schema": "zenodex.route_split_window_adversarial_report.v1",
        "date": "2026-06-28",
        "ok": bool(ok),
        "case_count": len(case_rows),
        "mismatch_count": int(mismatch_count),
        "winner_kinds": winner_kinds,
        "naive_first_difference_monotonicity_failure_count": len(monotonic_failures),
        "min_quote_call_reduction_ratio": min(ratios) if ratios else None,
        "max_quote_call_reduction_ratio": max(ratios) if ratios else None,
        "total_full_scan_quote_calls": sum(int(row["full_scan_quote_calls"]) for row in case_rows),
        "total_windowed_quote_calls": sum(int(row["windowed_quote_calls"]) for row in case_rows),
        "tau": tau,
        "mutation_checks": mutation_rows,
        "cases": case_rows,
        "claim": (
            "The route_split_window_certificate_v1 Tau rail can admit host-projected exact-out two-pool "
            "split-window certificates across this deterministic adversarial corpus when bounded full-oracle "
            "parity, quote replay, local window coverage, resource bounds, fallback, exact-out scope, and "
            "no-authority facts all hold."
        ),
        "non_claims": [
            "This replay does not prove universal discrete convexity or pure ternary-search correctness.",
            "The bounded full-sweep oracle is a research certificate surface for these fixtures.",
            "Tau combines host-projected boolean facts only; it does not compute quotes, derivatives, hashes, or settlements.",
        ],
        "replay_command": "python3 tools/check_route_split_window_adversarial.py",
    }


def _fmt_ratio(value: float | None) -> str:
    return "n/a" if value is None else f"{float(value):.2f}x"


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX Route Split Window Adversarial Corpus - 2026-06-28",
        "",
        "## Executive Result",
        "",
        str(report["claim"]),
        "",
        f"- Cases: `{report['case_count']}`",
        f"- Full/window mismatches: `{report['mismatch_count']}`",
        f"- Winner kinds: `{', '.join(report['winner_kinds'])}`",
        f"- First-difference monotonicity failures: `{report['naive_first_difference_monotonicity_failure_count']}`",
        f"- Quote-call reduction range: `{_fmt_ratio(report['min_quote_call_reduction_ratio'])}` to `{_fmt_ratio(report['max_quote_call_reduction_ratio'])}`",
        f"- Total quote calls: full sweep `{report['total_full_scan_quote_calls']}`, windowed `{report['total_windowed_quote_calls']}`",
        f"- Tau replay ok: `{report['tau']['ok']}`",
        "",
        "## Why This Matters",
        "",
        "The earlier route-split report showed four showcase fixtures. This corpus broadens the evidence across endpoint, interior, fee-skewed, shallow/deep, zero-endpoint, and near-tie regimes. Every fixture is checked against a bounded full-sweep oracle before Tau admits the certificate lane.",
        "",
        "The first-difference failures are retained as negative knowledge: integer CPMM rounding is not a safe basis for a pure discrete-convex shortcut here. The supported pattern is host-computed replay facts plus a Tau no-authority certificate gate.",
        "",
        "## Case Table",
        "",
        "| case | winner | feasible splits | full quotes | window quotes | reduction | q0 | amount in | first-diff monotone |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |",
    ]
    for row in report["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['winner_kind']}` | `{row['feasible_split_count']}` | "
            f"`{row['full_scan_quote_calls']}` | `{row['windowed_quote_calls']}` | "
            f"`{_fmt_ratio(row['quote_call_reduction_ratio'])}` | `{row['windowed_q0']}` | "
            f"`{row['best_amount_in_total']}` | `{row['first_differences_nondecreasing']}` |"
        )
    lines.extend(
        [
            "",
            "## Mutation Checks",
            "",
            "| mutation | accepted | failed flags |",
            "| --- | --- | --- |",
        ]
    )
    for row in report["mutation_checks"]:
        failed = ", ".join(f"`{flag}`" for flag in row["failed_flags"]) or "none"
        lines.append(f"| `{row['mutation_id']}` | `{row['accepted']}` | {failed} |")
    lines.extend(
        [
            "",
            "## Tau Specification Boundary",
            "",
            "`src/tau_specs/recommended/route_split_window_certificate_v1.tau` remains a host-projected proof-surface gate. The host computes quotes, hashes, full-sweep parity, local-window coverage, and resource facts. Tau combines those facts and preserves the no-settlement-authority rail.",
            "",
            "## Non-Claims",
            "",
        ]
    )
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
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
                "case_count": report["case_count"],
                "mismatch_count": report["mismatch_count"],
                "tau_ok": report["tau"]["ok"],
                "min_quote_call_reduction_ratio": report["min_quote_call_reduction_ratio"],
                "max_quote_call_reduction_ratio": report["max_quote_call_reduction_ratio"],
                "first_difference_failure_count": report["naive_first_difference_monotonicity_failure_count"],
                "report": str(REPORT_MD),
                "json": str(Path(args.output_json)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
