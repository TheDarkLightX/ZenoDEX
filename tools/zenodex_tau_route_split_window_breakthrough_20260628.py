#!/usr/bin/env python3
"""Replay a Tau-gated exact-out split-window certificate breakthrough."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.split_routing_two_exact_out import (  # noqa: E402
    TwoPoolExactOutRequest,
    _best_split,
    _build_context,
)
from src.core.split_routing_pool_quotes import (  # noqa: E402
    quote_exact_out_for_pool as _quote_exact_out,
)
from src.core.split_routing_pool_quotes import (  # noqa: E402
    reserves_for_pool as _reserves_for,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tau_route_split_window_breakthrough_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_TAU_ROUTE_SPLIT_WINDOW_BREAKTHROUGH_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "route_split_window_certificate_v1.tau"

ASSET_A = "A"
ASSET_B = "B"
MAX_FULL_SWEEP_POINTS = 20_000


@dataclass(frozen=True)
class SplitCase:
    case_id: str
    pool0: PoolState
    pool1: PoolState
    amount_out_total: int
    window: int
    brute_force_max: int
    note: str


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _pool(pool_id: str, reserve_a: int, reserve_b: int, fee_bps: int) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0=ASSET_A,
        asset1=ASSET_B,
        reserve0=int(reserve_a),
        reserve1=int(reserve_b),
        fee_bps=int(fee_bps),
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def split_cases() -> tuple[SplitCase, ...]:
    return (
        SplitCase(
            case_id="endpoint_best_amount2000",
            pool0=_pool("p0", 6_000, 6_000, 30),
            pool1=_pool("p1", 9_000, 4_000, 5),
            amount_out_total=2_000,
            window=32,
            brute_force_max=512,
            note="Endpoint optimum with asymmetric reserves and lower-fee second pool.",
        ),
        SplitCase(
            case_id="interior_plateau_amount5000",
            pool0=_pool("p0", 20_000, 15_000, 30),
            pool1=_pool("p1", 8_000, 12_000, 75),
            amount_out_total=5_000,
            window=32,
            brute_force_max=512,
            note="Interior optimum with integer-rounding plateaus near the derivative seed.",
        ),
        SplitCase(
            case_id="large_endpoint_amount9000",
            pool0=_pool("p0", 12_000, 30_000, 15),
            pool1=_pool("p1", 17_000, 18_000, 30),
            amount_out_total=9_000,
            window=32,
            brute_force_max=512,
            note="Large endpoint optimum with a wide feasible split domain.",
        ),
        SplitCase(
            case_id="interior_rounding_gap_amount4000",
            pool0=_pool("p0", 4_000, 7_000, 30),
            pool1=_pool("p1", 25_000, 10_000, 5),
            amount_out_total=4_000,
            window=32,
            brute_force_max=512,
            note="Interior optimum where naive discrete-convex first differences fail under rounding.",
        ),
    )


def _canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _sha256_json(value: Any) -> str:
    return hashlib.sha256(_canonical_json_bytes(value)).hexdigest()


def _key_tuple(key: Any) -> tuple[Any, ...]:
    return (
        int(key.amount_in_total),
        int(key.leg_count),
        tuple((str(pool_id), int(amount_out)) for pool_id, amount_out in key.legs_lex),
    )


def _key_json(key: Any) -> dict[str, Any]:
    return {
        "amount_in_total": int(key.amount_in_total),
        "leg_count": int(key.leg_count),
        "legs_lex": [[str(pool_id), int(amount_out)] for pool_id, amount_out in key.legs_lex],
    }


def _request_for_case(case: SplitCase, quote_calls: list[tuple[str, int]] | None = None) -> TwoPoolExactOutRequest:
    def reserves_for(pool: PoolState) -> tuple[int, int] | None:
        return _reserves_for(pool, asset_in=ASSET_A, asset_out=ASSET_B)

    def quote_exact_out(pool: PoolState, amount_out: int) -> int:
        if quote_calls is not None:
            quote_calls.append((str(pool.pool_id), int(amount_out)))
        return _quote_exact_out(pool, asset_in=ASSET_A, asset_out=ASSET_B, amount_out=int(amount_out))

    return TwoPoolExactOutRequest(
        pool0=case.pool0,
        pool1=case.pool1,
        asset_in=ASSET_A,
        asset_out=ASSET_B,
        amount_out_total=int(case.amount_out_total),
        window=int(case.window),
        brute_force_max=int(case.brute_force_max),
        reserves_for=reserves_for,
        quote_exact_out=quote_exact_out,
    )


def _full_scan(case: SplitCase) -> dict[str, Any]:
    quote_calls: list[tuple[str, int]] = []
    ctx = _build_context(_request_for_case(case, quote_calls))
    rows: list[dict[str, Any]] = []
    for q0 in range(int(ctx.lo), int(ctx.hi) + 1):
        total_input = ctx.total_input_for_split(int(q0))
        if total_input is None:
            continue
        key = ctx.route_key_for_split(int(q0), int(total_input))
        rows.append(
            {
                "q0": int(q0),
                "q1": int(case.amount_out_total) - int(q0),
                "total_input": int(total_input),
                "canonical_key": _key_json(key),
                "_key_tuple": _key_tuple(key),
            }
        )
    if not rows:
        raise ValueError(f"empty exact-out split domain for {case.case_id}")
    best = min(rows, key=lambda row: (int(row["total_input"]), row["_key_tuple"]))
    values = [int(row["total_input"]) for row in rows]
    diffs = [values[idx + 1] - values[idx] for idx in range(len(values) - 1)]
    diffs_nondecreasing = all(diffs[idx] <= diffs[idx + 1] for idx in range(len(diffs) - 1))
    min_cost = min(values)
    min_q0s = [int(row["q0"]) for row in rows if int(row["total_input"]) == min_cost]
    min_q0s_contiguous = min_q0s == list(range(min(min_q0s), max(min_q0s) + 1))
    domain_payload = [
        {
            "q0": row["q0"],
            "q1": row["q1"],
            "total_input": row["total_input"],
            "canonical_key": row["canonical_key"],
        }
        for row in rows
    ]
    return {
        "lo": int(ctx.lo),
        "hi": int(ctx.hi),
        "span": int(ctx.span),
        "feasible_split_count": len(rows),
        "quote_call_count": len(quote_calls),
        "domain_hash": _sha256_json(domain_payload),
        "best": {
            "q0": int(best["q0"]),
            "q1": int(best["q1"]),
            "total_input": int(best["total_input"]),
            "canonical_key": best["canonical_key"],
        },
        "integer_rounding_shape": {
            "first_differences_nondecreasing": bool(diffs_nondecreasing),
            "min_q0s_contiguous": bool(min_q0s_contiguous),
            "min_q0_range": [min(min_q0s), max(min_q0s)],
            "negative_knowledge": (
                "Naive discrete-convex first-difference monotonicity failed on this bounded case."
                if not diffs_nondecreasing
                else "This bounded case did not falsify discrete-convex first-difference monotonicity."
            ),
        },
    }


def _search_ranges(ctx: Any, *, best_q0: int, window: int, brute_force_max: int) -> list[dict[str, Any]]:
    if int(ctx.amount_out_total) <= int(brute_force_max) or int(ctx.span) <= int(brute_force_max):
        return [{"kind": "bruteforce", "lo": int(ctx.lo), "hi": int(ctx.hi)}]

    ranges: list[dict[str, Any]] = []
    for center in sorted(ctx.window_centers(int(window))):
        ranges.append(
            {
                "kind": "center_window",
                "center": int(center),
                "lo": max(int(ctx.lo), int(center) - int(window)),
                "hi": min(int(ctx.hi), int(center) + int(window)),
            }
        )
    canon_left = max(128, 4 * int(window))
    ranges.append(
        {
            "kind": "canonical_left_sweep",
            "lo": max(int(ctx.lo), int(best_q0) - int(canon_left)),
            "hi": int(best_q0),
        }
    )
    ranges.append(
        {
            "kind": "final_selected_window",
            "lo": max(int(ctx.lo), int(best_q0) - int(window)),
            "hi": min(int(ctx.hi), int(best_q0) + int(window)),
        }
    )
    return ranges


def _search_points(ranges: list[Mapping[str, Any]]) -> set[int]:
    points: set[int] = set()
    for item in ranges:
        points.update(range(int(item["lo"]), int(item["hi"]) + 1))
    return points


def _windowed_search(case: SplitCase) -> dict[str, Any]:
    quote_calls: list[tuple[str, int]] = []
    ctx = _build_context(_request_for_case(case, quote_calls))
    best_in, best_q0 = _best_split(ctx, window=int(case.window), brute_force_max=int(case.brute_force_max))
    quote = ctx.materialize_quote(int(best_q0))
    ranges = _search_ranges(ctx, best_q0=int(best_q0), window=int(case.window), brute_force_max=int(case.brute_force_max))
    points = _search_points(ranges)
    local_lo = max(int(ctx.lo), int(best_q0) - int(case.window))
    local_hi = min(int(ctx.hi), int(best_q0) + int(case.window))
    local_window_points = set(range(local_lo, local_hi + 1))
    return {
        "q0": int(best_q0),
        "q1": int(case.amount_out_total) - int(best_q0),
        "total_input": int(best_in),
        "materialized_total_input": int(quote.amount_in_total),
        "amount_in_0": int(quote.amount_in_0),
        "amount_in_1": int(quote.amount_in_1),
        "amount_out_total": int(quote.amount_out_total),
        "quote_call_count": len(quote_calls),
        "search_ranges": ranges,
        "search_point_count": len(points),
        "local_window_points_covered": local_window_points.issubset(points),
        "best_point_searched": int(best_q0) in points,
    }


def build_split_certificate(case: SplitCase) -> dict[str, Any]:
    full = _full_scan(case)
    windowed = _windowed_search(case)
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


def verify_split_certificate(case: SplitCase, certificate: Mapping[str, Any]) -> dict[str, Any]:
    full = _full_scan(case)
    windowed = _windowed_search(case)
    domain_nonempty = int(full["feasible_split_count"]) > 0
    search_ranges = list(certificate.get("search_ranges", [])) if isinstance(certificate.get("search_ranges"), list) else []
    search_points = _search_points(search_ranges)
    selected_q0 = certificate.get("selected_q0")
    selected_amount_in = certificate.get("selected_amount_in_total")
    full_best = full["best"]
    window_search_replayed = (
        certificate.get("domain_hash") == full["domain_hash"]
        and certificate.get("amount_out_total") == int(case.amount_out_total)
        and certificate.get("window") == int(case.window)
        and certificate.get("brute_force_max") == int(case.brute_force_max)
        and selected_q0 == int(windowed["q0"])
        and selected_amount_in == int(windowed["total_input"])
    )
    local_window_ok = (
        int(windowed["q0"]) in search_points
        and int(certificate.get("search_point_count", -1)) == int(windowed["search_point_count"])
        and bool(windowed["local_window_points_covered"])
        and bool(windowed["best_point_searched"])
    )
    parity_ok = (
        int(windowed["q0"]) == int(full_best["q0"])
        and int(windowed["total_input"]) == int(full_best["total_input"])
        and selected_q0 == int(full_best["q0"])
        and selected_amount_in == int(full_best["total_input"])
    )
    quote_replay_ok = (
        int(windowed["materialized_total_input"]) == int(windowed["total_input"])
        and int(windowed["amount_out_total"]) == int(case.amount_out_total)
        and int(windowed["amount_in_0"]) + int(windowed["amount_in_1"]) == int(windowed["total_input"])
    )
    integer_rounding_scope_ok = (
        int(case.amount_out_total) > 0
        and int(full["lo"]) <= int(full_best["q0"]) <= int(full["hi"])
        and int(full_best["total_input"]) > 0
    )
    resource_budget_ok = (
        int(full["feasible_split_count"]) <= MAX_FULL_SWEEP_POINTS
        and int(windowed["quote_call_count"]) < int(full["quote_call_count"])
    )
    exact_out_scope_ok = (
        case.pool0.asset0 == ASSET_A
        and case.pool0.asset1 == ASSET_B
        and case.pool1.asset0 == ASSET_A
        and case.pool1.asset1 == ASSET_B
    )
    flags = {
        "domain_nonempty": int(domain_nonempty),
        "window_search_replayed": int(window_search_replayed),
        "local_window_certificate_ok": int(local_window_ok),
        "full_oracle_parity_ok": int(parity_ok),
        "quote_replay_ok": int(quote_replay_ok),
        "integer_rounding_scope_ok": int(integer_rounding_scope_ok),
        "resource_budget_ok": int(resource_budget_ok),
        "fallback_available_or_explicit_failure": 1,
        "no_settlement_authority": 1,
        "exact_out_scope_ok": int(exact_out_scope_ok),
    }
    failed = [name for name, value in flags.items() if int(value) != 1]
    full_quotes = int(full["quote_call_count"])
    window_quotes = int(windowed["quote_call_count"])
    return {
        "ok": not failed,
        "flags": flags,
        "failed_flags": failed,
        "full_scan": full,
        "windowed_search": windowed,
        "quote_call_reduction_ratio": full_quotes / window_quotes if window_quotes else None,
        "certificate": dict(certificate),
    }


def _tau_step(flags: Mapping[str, int], *, active: int = 1, overrides: Mapping[str, int] | None = None) -> dict[str, int]:
    values = {
        "i1": int(active),
        "i2": int(flags.get("domain_nonempty", 0)),
        "i3": int(flags.get("window_search_replayed", 0)),
        "i4": int(flags.get("local_window_certificate_ok", 0)),
        "i5": int(flags.get("full_oracle_parity_ok", 0)),
        "i6": int(flags.get("quote_replay_ok", 0)),
        "i7": int(flags.get("integer_rounding_scope_ok", 0)),
        "i8": int(flags.get("resource_budget_ok", 0)),
        "i9": int(flags.get("fallback_available_or_explicit_failure", 0)),
        "i10": int(flags.get("no_settlement_authority", 0)),
        "i11": int(flags.get("exact_out_scope_ok", 0)),
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
            "route_split_window_pass",
            _tau_step(base_flags),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0},
            "All host-computed proof-surface facts admit the split-window certificate lane.",
        ),
        TauCase(
            "parity_reject",
            _tau_step(base_flags, overrides={"i5": 0}),
            {"o2": 0, "o4": 0},
            "A missing bounded full-oracle parity fact fails closed.",
        ),
        TauCase(
            "local_window_reject",
            _tau_step(base_flags, overrides={"i4": 0}),
            {"o1": 0, "o4": 0},
            "A missing local window certificate cannot admit.",
        ),
        TauCase(
            "authority_reject",
            _tau_step(base_flags, overrides={"i10": 0}),
            {"o3": 0, "o4": 0},
            "A certificate with settlement authority effects is rejected.",
        ),
        TauCase(
            "inactive_safe",
            _tau_step(base_flags, active=0),
            {"o4": 0, "o5": 1},
            "Inactive requests do not admit while the no-authority rail remains true.",
        ),
    )
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[case.step for case in cases],
        timeout_s=15.0,
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


def _case_result(case: SplitCase) -> dict[str, Any]:
    certificate = build_split_certificate(case)
    verification = verify_split_certificate(case, certificate)
    return {
        "case_id": case.case_id,
        "note": case.note,
        "ok": verification["ok"],
        "amount_out_total": int(case.amount_out_total),
        "window": int(case.window),
        "brute_force_max": int(case.brute_force_max),
        "selected_q0": int(certificate["selected_q0"]),
        "selected_amount_in_total": int(certificate["selected_amount_in_total"]),
        "full_scan_quote_calls": int(verification["full_scan"]["quote_call_count"]),
        "windowed_quote_calls": int(verification["windowed_search"]["quote_call_count"]),
        "quote_call_reduction_ratio": verification["quote_call_reduction_ratio"],
        "feasible_split_count": int(verification["full_scan"]["feasible_split_count"]),
        "integer_rounding_shape": verification["full_scan"]["integer_rounding_shape"],
        "verification": {
            "ok": verification["ok"],
            "flags": verification["flags"],
            "failed_flags": verification["failed_flags"],
        },
        "certificate": certificate,
    }


def _mutation_checks(case: SplitCase) -> list[dict[str, Any]]:
    certificate = build_split_certificate(case)
    mutations: list[tuple[str, dict[str, Any]]] = []
    bad_hash = dict(certificate)
    bad_hash["domain_hash"] = "0" * 64
    mutations.append(("bad_domain_hash", bad_hash))
    bad_q0 = dict(certificate)
    bad_q0["selected_q0"] = int(certificate["selected_q0"]) + 1
    mutations.append(("bad_selected_q0", bad_q0))
    bad_points = dict(certificate)
    bad_points["search_point_count"] = int(certificate["search_point_count"]) + 1
    mutations.append(("bad_search_point_count", bad_points))

    rows: list[dict[str, Any]] = []
    for mutation_id, mutated in mutations:
        verification = verify_split_certificate(case, mutated)
        rows.append(
            {
                "mutation_id": mutation_id,
                "accepted": bool(verification["ok"]),
                "failed_flags": verification["failed_flags"],
            }
        )
    return rows


def _build_report() -> dict[str, Any]:
    case_rows = [_case_result(case) for case in split_cases()]
    mutation_rows = _mutation_checks(split_cases()[1])
    tau = _run_tau_cases(case_rows[0]["verification"]["flags"])
    ratios = [float(row["quote_call_reduction_ratio"]) for row in case_rows if row["quote_call_reduction_ratio"]]
    naive_convex_failures = [
        row["case_id"]
        for row in case_rows
        if not bool(row["integer_rounding_shape"]["first_differences_nondecreasing"])
    ]
    ok = (
        all(bool(row["ok"]) for row in case_rows)
        and tau["ok"] is True
        and all(not bool(row["accepted"]) for row in mutation_rows)
        and bool(naive_convex_failures)
    )
    return {
        "schema": "zenodex.tau_route_split_window_breakthrough_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "breakthrough": {
            "spec_id": "route_split_window_certificate_v1",
            "summary": (
                "A Tau host-projected certificate can guard exact-out two-pool split routing by requiring "
                "derivative-window replay, local-window coverage, bounded full-oracle parity, integer rounding "
                "scope, resource budget, fallback, and no-authority facts."
            ),
            "authority_boundary": "Tau admits a split-routing certificate lane only. It does not quote pools, choose routes, or authorize settlement.",
        },
        "tau": tau,
        "split_cases": {
            "case_count": len(case_rows),
            "min_quote_call_reduction_ratio": min(ratios) if ratios else None,
            "max_quote_call_reduction_ratio": max(ratios) if ratios else None,
            "naive_discrete_convex_failures": naive_convex_failures,
            "cases": case_rows,
        },
        "mutation_checks": mutation_rows,
        "work_items_1_and_2": {
            "ab_ordering": {
                "spec": "src/tau_specs/recommended/ab_cow_exact_solver_envelope_v1.tau",
                "report": "docs/research/ZENODEX_AB_COW_ALGORITHM_BREAKTHROUGH_20260627.md",
                "status": "Existing Tau rail for bounded AB full-state subset DP; replay command remains python3 tools/zenodex_ab_cow_algorithm_breakthrough_20260627.py.",
            },
            "cow_matching": {
                "spec": "src/tau_specs/recommended/ab_cow_exact_solver_envelope_v1.tau",
                "report": "docs/research/ZENODEX_AB_COW_ALGORITHM_BREAKTHROUGH_20260627.md",
                "status": "Existing Tau rail for uncoupled Hungarian CoW assignment and bounded coupled-capacity DP; grouped-capacity polynomial matching is not claimed.",
            },
        },
        "new_specification_frontier": [
            {
                "spec": "src/tau_specs/recommended/route_split_window_certificate_v1.tau",
                "benefit": "Gates exact-out two-pool split-window certificates and records when bounded full-oracle parity is required.",
            },
            {
                "spec": "src/tau_specs/recommended/optimizer_quotient_certificate_v1.tau",
                "benefit": "Compresses route, AB, and CoW optimizer proof surfaces into domain-hash-bound certificates.",
            },
            {
                "spec": "src/tau_specs/recommended/ab_cow_exact_solver_envelope_v1.tau",
                "benefit": "Covers work items 1 and 2: AB subset-DP/brute-force and CoW exact matching proof-surface facts.",
            },
        ],
        "non_claims": [
            "This artifact does not prove a universal continuous or discrete convexity theorem for integer CPMM exact-out split costs.",
            "The bounded full-oracle parity check is evidence for these fixtures; production verifiers still own route correctness.",
            "Tau does not compute quotes, hashes, derivatives, windows, or route winners.",
            "The AB/CoW entries are existing supported rails included to keep work items 1 and 2 in scope.",
        ],
        "replay_command": "python3 tools/zenodex_tau_route_split_window_breakthrough_20260628.py",
    }


def _fmt_ratio(value: float | None) -> str:
    if value is None:
        return "n/a"
    return f"{float(value):.2f}x"


def _write_markdown(report: Mapping[str, Any]) -> None:
    split = report["split_cases"]
    tau = report["tau"]
    lines: list[str] = []
    lines.append("# ZenoDEX Tau Route Split Window Breakthrough - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(str(report["breakthrough"]["summary"]))
    lines.append("")
    lines.append(str(report["breakthrough"]["authority_boundary"]))
    lines.append("")
    lines.append("## Breakthrough Specification")
    lines.append("")
    lines.append(f"- Spec: `{tau['spec_path']}`")
    lines.append(f"- Latest Tau: `{tau.get('tau_version')}`")
    lines.append(f"- Tau trace replay ok: `{tau['ok']}`")
    lines.append(f"- Split cases: `{split['case_count']}`")
    lines.append(f"- Quote-call reduction range: `{_fmt_ratio(split['min_quote_call_reduction_ratio'])}` to `{_fmt_ratio(split['max_quote_call_reduction_ratio'])}`")
    lines.append(f"- Naive discrete-convex failures: `{len(split['naive_discrete_convex_failures'])}`")
    lines.append("")
    lines.append("The spec requires derivative-window replay, local window coverage, bounded full-oracle parity, quote replay, integer rounding scope, resource budget, fallback, exact-out scope, and no settlement authority.")
    lines.append("")
    lines.append("## Split Evidence")
    lines.append("")
    lines.append("| case | feasible splits | full quotes | window quotes | reduction | selected q0 | amount in | first-diff monotone |")
    lines.append("| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |")
    for row in split["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['feasible_split_count']}` | `{row['full_scan_quote_calls']}` | `{row['windowed_quote_calls']}` | `{_fmt_ratio(row['quote_call_reduction_ratio'])}` | `{row['selected_q0']}` | `{row['selected_amount_in_total']}` | `{row['integer_rounding_shape']['first_differences_nondecreasing']}` |"
        )
    lines.append("")
    lines.append("The failed first-difference checks are recorded as negative knowledge. The certificate accepts only because bounded full-oracle parity and quote replay pass.")
    lines.append("")
    lines.append("## Tau Mode Checks")
    lines.append("")
    lines.append("| case | ok | rationale |")
    lines.append("| --- | --- | --- |")
    for row in tau["cases"]:
        lines.append(f"| `{row['case_id']}` | `{row['ok']}` | {row['rationale']} |")
    lines.append("")
    lines.append("## Work Items 1 And 2")
    lines.append("")
    lines.append("The earlier AB and CoW tracks remain in scope through `ab_cow_exact_solver_envelope_v1.tau`.")
    lines.append("")
    lines.append("1. AB ordering: bounded full-state subset DP/brute-force proof-surface rail. Replay: `python3 tools/zenodex_ab_cow_algorithm_breakthrough_20260627.py`.")
    lines.append("2. CoW matching: uncoupled Hungarian assignment plus bounded coupled-capacity DP proof-surface rail. Grouped-capacity polynomial matching is not claimed.")
    lines.append("")
    lines.append("## New Specification Frontier")
    lines.append("")
    for item in report["new_specification_frontier"]:
        lines.append(f"- `{item['spec']}`: {item['benefit']}")
    lines.append("")
    lines.append("## Mutation Checks")
    lines.append("")
    lines.append("| mutation | accepted | failed flags |")
    lines.append("| --- | --- | --- |")
    for row in report["mutation_checks"]:
        failed = ", ".join(f"`{flag}`" for flag in row["failed_flags"]) or "none"
        lines.append(f"| `{row['mutation_id']}` | `{row['accepted']}` | {failed} |")
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
    report = _build_report()
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
                "split_case_count": report["split_cases"]["case_count"],
                "min_quote_call_reduction_ratio": report["split_cases"]["min_quote_call_reduction_ratio"],
                "max_quote_call_reduction_ratio": report["split_cases"]["max_quote_call_reduction_ratio"],
                "naive_discrete_convex_failure_count": len(report["split_cases"]["naive_discrete_convex_failures"]),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
