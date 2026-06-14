#!/usr/bin/env python3
"""Replay runtime evidence for bounded exact-in split-routing staircase selection."""

from __future__ import annotations

import argparse
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from random import Random
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core import split_routing as split_routing_mod  # noqa: E402
from src.core.split_routing import (  # noqa: E402
    PoolXY,
    best_split_two_pools_exact_in,
    resolve_two_pool_split_search_params,
)
from tools.operator_report_output import emit_operator_json, write_public_json  # noqa: E402

SCHEMA = "zenodex/split-routing/staircase-runtime-evidence/v1"
FEE_CHOICES = (0, 1, 5, 30, 100, 250, 999, 2500, 5000, 9000, 9970, 9999)


@dataclass(frozen=True)
class SplitEvidenceCase:
    case_id: str
    family: str
    pool0: PoolXY
    pool1: PoolXY
    amount_in: int

    def to_dict(self) -> dict[str, Any]:
        return {
            "case_id": self.case_id,
            "family": self.family,
            "pool0": _pool_to_dict(self.pool0),
            "pool1": _pool_to_dict(self.pool1),
            "amount_in": int(self.amount_in),
        }


@dataclass(frozen=True)
class ProfileRun:
    ok: bool
    result: tuple[int, int] | None
    error: str | None
    quote_calls: int
    elapsed_ns: int

    def to_dict(self) -> dict[str, Any]:
        return {
            "ok": bool(self.ok),
            "result": None
            if self.result is None
            else {"amount_out": int(self.result[0]), "split_a": int(self.result[1])},
            "error": self.error,
            "quote_calls": int(self.quote_calls),
            "elapsed_ns": int(self.elapsed_ns),
        }


@dataclass(frozen=True)
class EvidenceCheck:
    check_id: str
    ok: bool
    detail: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "check_id": self.check_id,
            "ok": bool(self.ok),
            "detail": self.detail,
        }


def _pool_to_dict(pool: PoolXY) -> dict[str, int]:
    return {"x": int(pool.x), "y": int(pool.y), "fee_bps": int(pool.fee_bps)}


def _ratio_ge_num_denom(*, a: int, b: int, num: int, denom: int) -> bool:
    if b <= 0 or denom <= 0:
        return False
    return int(a) * int(denom) >= int(b) * int(num)


def _near_equal_bps(*, a: int, b: int, tol_bps: int) -> bool:
    if a <= 0 or b <= 0 or tol_bps < 0:
        return False
    return abs(int(a) - int(b)) * 10_000 <= int(tol_bps) * min(int(a), int(b))


def _legacy_adaptive_v6_resolution(pool0: PoolXY, pool1: PoolXY, amount_in: int) -> tuple[int, str]:
    """
    Resolve adaptive_v6 as it behaved before the bounded staircase selector.

    This intentionally mirrors the old v6 threshold ladder so the checker can
    compare the current default against the previous runtime policy without
    needing a second checkout.
    """
    D = int(amount_in)
    if D <= 0:
        return 64, "baseline"

    x0, y0, f0 = int(pool0.x), int(pool0.y), int(pool0.fee_bps)
    x1, y1, f1 = int(pool1.x), int(pool1.y), int(pool1.fee_bps)
    min_x = min(x0, x1)
    min_y = min(y0, y1)
    fee_gap = abs(int(f0) - int(f1))
    fee_max = max(int(f0), int(f1))

    x_ratio_hi = _ratio_ge_num_denom(a=max(x0, x1), b=max(1, min_x), num=3, denom=1)
    y_ratio_hi = _ratio_ge_num_denom(a=max(y0, y1), b=max(1, min_y), num=5, denom=1)
    near_sym_raw = _near_equal_bps(a=x0, b=y0, tol_bps=1500) or _near_equal_bps(a=x1, b=y1, tol_bps=1500)
    near_sym = bool(near_sym_raw and min_x <= 200)
    amt_med = bool(min_x > 0 and D >= 40 * int(min_x))
    amt_hi = bool(min_x > 0 and D >= 80 * int(min_x))
    amt_very_hi = bool(min_x > 0 and D >= 120 * int(min_x))
    imbalance_hi = bool(x_ratio_hi and y_ratio_hi)

    high6 = bool(amt_hi or fee_gap >= 110 or imbalance_hi or (near_sym and fee_gap >= 40))
    thin_out = bool(min_y <= 80)
    hard6 = bool(
        (amt_hi and fee_max >= 145)
        or (amt_very_hi and fee_gap >= 80)
        or (thin_out and amt_med and fee_max >= 145)
        or (amt_hi and min_y <= 44)
        or (imbalance_hi and fee_max >= 100)
    )
    extreme6 = bool(
        (amt_very_hi and fee_max >= 195)
        or (thin_out and amt_hi and fee_max >= 195)
        or (amt_very_hi and min_y <= 32)
    )
    if extreme6:
        return 128, "dense32"
    if hard6:
        return 96, "dense32"
    if high6:
        return 96, "dense24"
    return 64, "baseline_canon16"


def _run_profile(pool0: PoolXY, pool1: PoolXY, amount_in: int, *, profile: str, window: int = 64) -> ProfileRun:
    original = split_routing_mod.exact_out_for_pool_exact_in
    calls = {"n": 0}

    def counted(pool: PoolXY, amount: int) -> int:
        calls["n"] = int(calls["n"]) + 1
        return original(pool, amount)

    split_routing_mod.exact_out_for_pool_exact_in = counted  # type: ignore[assignment]
    start_ns = time.perf_counter_ns()
    try:
        result = best_split_two_pools_exact_in(
            pool0,
            pool1,
            int(amount_in),
            window=int(window),
            search_profile=str(profile),
        )
        elapsed_ns = time.perf_counter_ns() - start_ns
        return ProfileRun(
            ok=True,
            result=(int(result[0]), int(result[1])),
            error=None,
            quote_calls=int(calls["n"]),
            elapsed_ns=int(elapsed_ns),
        )
    except ValueError as exc:
        elapsed_ns = time.perf_counter_ns() - start_ns
        return ProfileRun(
            ok=False,
            result=None,
            error=str(exc),
            quote_calls=int(calls["n"]),
            elapsed_ns=int(elapsed_ns),
        )
    finally:
        split_routing_mod.exact_out_for_pool_exact_in = original  # type: ignore[assignment]


def _fixed_cases() -> list[SplitEvidenceCase]:
    return [
        SplitEvidenceCase(
            "fixed.known_gap",
            "curated_known_gap",
            PoolXY(x=87, y=80, fee_bps=75),
            PoolXY(x=46, y=66, fee_bps=11),
            6539,
        ),
        SplitEvidenceCase(
            "fixed.stress_small_out",
            "curated_stress_small_out",
            PoolXY(x=102, y=31, fee_bps=193),
            PoolXY(x=132, y=92, fee_bps=177),
            13704,
        ),
        SplitEvidenceCase(
            "fixed.output_improvement.high_fee_0",
            "curated_output_improvement",
            PoolXY(x=9, y=3124, fee_bps=9000),
            PoolXY(x=28, y=1229, fee_bps=9999),
            29508,
        ),
        SplitEvidenceCase(
            "fixed.output_improvement.high_fee_1",
            "curated_output_improvement",
            PoolXY(x=12, y=3095, fee_bps=9999),
            PoolXY(x=2, y=3418, fee_bps=9970),
            28775,
        ),
        SplitEvidenceCase(
            "fixed.output_improvement.thin_out",
            "curated_output_improvement",
            PoolXY(x=59, y=103, fee_bps=1),
            PoolXY(x=34, y=137, fee_bps=30),
            10734,
        ),
        SplitEvidenceCase(
            "fixed.deep_high_output_fallback",
            "curated_fallback",
            PoolXY(x=1_000_000, y=1_000_000, fee_bps=30),
            PoolXY(x=1_200_000, y=900_000, fee_bps=30),
            1_000_000,
        ),
    ]


def build_cases(*, seed: int, samples_per_family: int) -> list[SplitEvidenceCase]:
    rng = Random(int(seed))
    cases = _fixed_cases()
    n = max(0, int(samples_per_family))

    for index in range(n):
        pool0 = PoolXY(rng.randint(50, 5000), rng.randint(50, 5000), rng.choice(FEE_CHOICES))
        pool1 = PoolXY(rng.randint(50, 5000), rng.randint(50, 5000), rng.choice(FEE_CHOICES))
        cases.append(SplitEvidenceCase(f"random.balanced.{index}", "balanced", pool0, pool1, rng.randint(1, 3000)))

    for index in range(n):
        x0 = rng.randint(5, 60)
        x1 = rng.randint(5, 60)
        pool0 = PoolXY(x0, rng.randint(10, 300), rng.choice(FEE_CHOICES))
        pool1 = PoolXY(x1, rng.randint(10, 300), rng.choice(FEE_CHOICES))
        cases.append(
            SplitEvidenceCase(
                f"random.high_pressure.{index}",
                "high_pressure",
                pool0,
                pool1,
                rng.randint(100 * max(x0, x1), 200 * max(x0, x1)),
            )
        )

    for index in range(n):
        pool0 = PoolXY(rng.randint(1, 200), rng.randint(1, 80), rng.choice(FEE_CHOICES))
        pool1 = PoolXY(rng.randint(1, 200), rng.randint(1, 80), rng.choice(FEE_CHOICES))
        cases.append(SplitEvidenceCase(f"random.thin_out.{index}", "thin_out", pool0, pool1, rng.randint(100, 10_000)))

    for index in range(n):
        pool0 = PoolXY(rng.randint(20, 100), rng.randint(2000, 9000), rng.choice(FEE_CHOICES))
        pool1 = PoolXY(rng.randint(1000, 9000), rng.randint(20, 100), rng.choice(FEE_CHOICES))
        cases.append(
            SplitEvidenceCase(f"random.imbalanced.{index}", "imbalanced", pool0, pool1, rng.randint(50, 2500))
        )

    for index in range(n):
        pool0 = PoolXY(rng.randint(1, 12), rng.randint(1, 12), rng.choice(FEE_CHOICES))
        pool1 = PoolXY(rng.randint(1, 12), rng.randint(1, 12), rng.choice(FEE_CHOICES))
        cases.append(SplitEvidenceCase(f"random.tiny.{index}", "tiny", pool0, pool1, rng.randint(1, 40)))

    for index in range(n):
        pool0 = PoolXY(rng.randint(10_000, 1_000_000), rng.randint(10_000, 1_000_000), rng.choice((0, 30, 100)))
        pool1 = PoolXY(rng.randint(10_000, 1_000_000), rng.randint(10_000, 1_000_000), rng.choice((0, 30, 100)))
        cases.append(
            SplitEvidenceCase(
                f"random.deep_high_output.{index}",
                "deep_high_output",
                pool0,
                pool1,
                rng.randint(10_000, 1_000_000),
            )
        )

    for index in range(n):
        pool0 = PoolXY(rng.randint(1, 50), rng.randint(1000, 4000), rng.choice((5000, 9000, 9970, 9999)))
        pool1 = PoolXY(rng.randint(1, 50), rng.randint(1000, 4000), rng.choice((5000, 9000, 9970, 9999)))
        cases.append(
            SplitEvidenceCase(
                f"random.high_fee_plateau.{index}",
                "high_fee_plateau",
                pool0,
                pool1,
                rng.randint(1000, 30_000),
            )
        )

    return cases


def _case_record(case: SplitEvidenceCase) -> dict[str, Any]:
    current_window, current_profile = resolve_two_pool_split_search_params(
        case.pool0,
        case.pool1,
        int(case.amount_in),
        search_profile="adaptive_v6",
        window=96,
    )
    legacy_window, legacy_profile = _legacy_adaptive_v6_resolution(case.pool0, case.pool1, int(case.amount_in))
    current = _run_profile(case.pool0, case.pool1, int(case.amount_in), profile="adaptive_v6", window=64)
    legacy = _run_profile(case.pool0, case.pool1, int(case.amount_in), profile=legacy_profile, window=legacy_window)

    staircase: ProfileRun | None = None
    if current_profile == "staircase_v1":
        staircase = _run_profile(case.pool0, case.pool1, int(case.amount_in), profile="staircase_v1", window=0)

    output_delta = None
    split_delta = None
    if current.ok and legacy.ok and current.result is not None and legacy.result is not None:
        output_delta = int(current.result[0]) - int(legacy.result[0])
        split_delta = int(current.result[1]) - int(legacy.result[1])

    staircase_matches = None
    if staircase is not None:
        staircase_matches = bool(
            current.ok == staircase.ok
            and current.result == staircase.result
            and (current.ok or current.error == staircase.error)
        )

    return {
        **case.to_dict(),
        "current_resolution": {"window": int(current_window), "profile": str(current_profile)},
        "legacy_resolution": {"window": int(legacy_window), "profile": str(legacy_profile)},
        "current": current.to_dict(),
        "legacy_adaptive_v6_without_staircase": legacy.to_dict(),
        "explicit_staircase_v1": None if staircase is None else staircase.to_dict(),
        "output_delta_vs_legacy": output_delta,
        "split_delta_vs_legacy": split_delta,
        "quote_call_delta_vs_legacy": int(current.quote_calls) - int(legacy.quote_calls),
        "elapsed_ns_delta_vs_legacy": int(current.elapsed_ns) - int(legacy.elapsed_ns),
        "staircase_matches_current": staircase_matches,
    }


def build_split_routing_staircase_runtime_evidence(
    *,
    seed: int = 20260612,
    samples_per_family: int = 20,
    min_cases: int = 100,
    min_staircase_selected_cases: int = 1,
    min_output_improvement_cases: int = 1,
    max_output_regression_cases: int = 0,
    max_selected_staircase_mismatches: int = 0,
    max_fallback_result_mismatches: int = 0,
    max_fallback_call_overhead: int = 2,
) -> dict[str, Any]:
    cases = build_cases(seed=int(seed), samples_per_family=int(samples_per_family))
    records = [_case_record(case) for case in cases]

    selected = [record for record in records if record["current_resolution"]["profile"] == "staircase_v1"]
    fallback = [record for record in records if record["current_resolution"]["profile"] != "staircase_v1"]
    comparable = [
        record
        for record in records
        if record["current"]["ok"] and record["legacy_adaptive_v6_without_staircase"]["ok"]
    ]

    output_improvements = [record for record in comparable if int(record["output_delta_vs_legacy"]) > 0]
    output_regressions = [record for record in comparable if int(record["output_delta_vs_legacy"]) < 0]
    selected_staircase_mismatches = [
        record for record in selected if record.get("staircase_matches_current") is not True
    ]
    fallback_result_mismatches = [
        record
        for record in fallback
        if record["current"]["ok"] != record["legacy_adaptive_v6_without_staircase"]["ok"]
        or record["current"]["result"] != record["legacy_adaptive_v6_without_staircase"]["result"]
    ]
    fallback_call_overhead_violations = [
        record
        for record in fallback
        if int(record["quote_call_delta_vs_legacy"]) > int(max_fallback_call_overhead)
    ]
    selected_call_reductions = [record for record in selected if int(record["quote_call_delta_vs_legacy"]) < 0]
    selected_call_increases = [record for record in selected if int(record["quote_call_delta_vs_legacy"]) > 0]

    total_current_calls = sum(int(record["current"]["quote_calls"]) for record in records)
    total_legacy_calls = sum(int(record["legacy_adaptive_v6_without_staircase"]["quote_calls"]) for record in records)
    selected_current_calls = sum(int(record["current"]["quote_calls"]) for record in selected)
    selected_legacy_calls = sum(int(record["legacy_adaptive_v6_without_staircase"]["quote_calls"]) for record in selected)

    checks = [
        EvidenceCheck(
            "min_cases",
            len(records) >= int(min_cases),
            f"{len(records)} cases >= required {int(min_cases)}",
        ),
        EvidenceCheck(
            "staircase_selected_cases",
            len(selected) >= int(min_staircase_selected_cases),
            f"{len(selected)} selected >= required {int(min_staircase_selected_cases)}",
        ),
        EvidenceCheck(
            "selected_matches_explicit_staircase",
            len(selected_staircase_mismatches) <= int(max_selected_staircase_mismatches),
            f"{len(selected_staircase_mismatches)} mismatches <= allowed {int(max_selected_staircase_mismatches)}",
        ),
        EvidenceCheck(
            "no_output_regressions_vs_legacy",
            len(output_regressions) <= int(max_output_regression_cases),
            f"{len(output_regressions)} regressions <= allowed {int(max_output_regression_cases)}",
        ),
        EvidenceCheck(
            "output_improvement_witnesses",
            len(output_improvements) >= int(min_output_improvement_cases),
            f"{len(output_improvements)} improvements >= required {int(min_output_improvement_cases)}",
        ),
        EvidenceCheck(
            "fallback_result_matches_legacy",
            len(fallback_result_mismatches) <= int(max_fallback_result_mismatches),
            f"{len(fallback_result_mismatches)} mismatches <= allowed {int(max_fallback_result_mismatches)}",
        ),
        EvidenceCheck(
            "fallback_call_overhead_bounded",
            len(fallback_call_overhead_violations) == 0,
            f"{len(fallback_call_overhead_violations)} fallback cases exceeded +{int(max_fallback_call_overhead)} quote calls",
        ),
        EvidenceCheck(
            "selected_quote_calls_decrease_in_aggregate",
            selected_current_calls < selected_legacy_calls,
            f"selected current calls {selected_current_calls} < legacy calls {selected_legacy_calls}",
        ),
    ]

    summary = {
        "total_cases": len(records),
        "comparable_success_cases": len(comparable),
        "staircase_selected_cases": len(selected),
        "heuristic_fallback_cases": len(fallback),
        "output_improvement_cases": len(output_improvements),
        "output_regression_cases": len(output_regressions),
        "selected_staircase_mismatch_cases": len(selected_staircase_mismatches),
        "fallback_result_mismatch_cases": len(fallback_result_mismatches),
        "fallback_call_overhead_violation_cases": len(fallback_call_overhead_violations),
        "selected_quote_call_reduction_cases": len(selected_call_reductions),
        "selected_quote_call_increase_cases": len(selected_call_increases),
        "total_current_quote_calls": int(total_current_calls),
        "total_legacy_quote_calls": int(total_legacy_calls),
        "total_quote_call_delta_vs_legacy": int(total_current_calls - total_legacy_calls),
        "selected_current_quote_calls": int(selected_current_calls),
        "selected_legacy_quote_calls": int(selected_legacy_calls),
        "selected_quote_call_delta_vs_legacy": int(selected_current_calls - selected_legacy_calls),
        "max_output_improvement": max((int(record["output_delta_vs_legacy"]) for record in output_improvements), default=0),
        "max_output_regression": min((int(record["output_delta_vs_legacy"]) for record in output_regressions), default=0),
        "output_improvement_case_ids": [str(record["case_id"]) for record in output_improvements[:20]],
        "output_regression_case_ids": [str(record["case_id"]) for record in output_regressions[:20]],
        "selected_staircase_mismatch_case_ids": [str(record["case_id"]) for record in selected_staircase_mismatches[:20]],
        "fallback_result_mismatch_case_ids": [str(record["case_id"]) for record in fallback_result_mismatches[:20]],
    }

    report = {
        "schema": SCHEMA,
        "ok": all(check.ok for check in checks),
        "git_commit": _git_commit(),
        "claim_scope": (
            "adaptive_v6 exact-in split routing selects the Lean-backed staircase optimizer "
            "only when its output-level budget is bounded, otherwise preserving legacy heuristic results"
        ),
        "non_claims": [
            "wall-clock timings are local diagnostics, not a formal performance proof",
            "heuristic fallback cases are checked against legacy adaptive_v6 behavior, not exact optimality",
            "the corpus is deterministic synthetic evidence, not production traffic distribution",
        ],
        "config": {
            "seed": int(seed),
            "samples_per_family": int(samples_per_family),
            "min_cases": int(min_cases),
            "min_staircase_selected_cases": int(min_staircase_selected_cases),
            "min_output_improvement_cases": int(min_output_improvement_cases),
            "max_output_regression_cases": int(max_output_regression_cases),
            "max_selected_staircase_mismatches": int(max_selected_staircase_mismatches),
            "max_fallback_result_mismatches": int(max_fallback_result_mismatches),
            "max_fallback_call_overhead": int(max_fallback_call_overhead),
        },
        "summary": summary,
        "checks": [check.to_dict() for check in checks],
        "cases": records,
    }
    return report


def _git_commit() -> str | None:
    try:
        out = subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=ROOT,
            stderr=subprocess.DEVNULL,
            text=True,
        )
    except Exception:
        return None
    return out.strip()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260612)
    parser.add_argument("--samples-per-family", type=int, default=20)
    parser.add_argument("--min-cases", type=int, default=100)
    parser.add_argument("--min-staircase-selected-cases", type=int, default=1)
    parser.add_argument("--min-output-improvement-cases", type=int, default=1)
    parser.add_argument("--max-output-regression-cases", type=int, default=0)
    parser.add_argument("--max-selected-staircase-mismatches", type=int, default=0)
    parser.add_argument("--max-fallback-result-mismatches", type=int, default=0)
    parser.add_argument("--max-fallback-call-overhead", type=int, default=2)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument(
        "--console-summary-only",
        action="store_true",
        help="Print summary/checks to stdout while preserving full cases in --output-json.",
    )
    args = parser.parse_args(argv)

    report = build_split_routing_staircase_runtime_evidence(
        seed=int(args.seed),
        samples_per_family=int(args.samples_per_family),
        min_cases=int(args.min_cases),
        min_staircase_selected_cases=int(args.min_staircase_selected_cases),
        min_output_improvement_cases=int(args.min_output_improvement_cases),
        max_output_regression_cases=int(args.max_output_regression_cases),
        max_selected_staircase_mismatches=int(args.max_selected_staircase_mismatches),
        max_fallback_result_mismatches=int(args.max_fallback_result_mismatches),
        max_fallback_call_overhead=int(args.max_fallback_call_overhead),
    )
    if args.output_json is not None:
        write_public_json(args.output_json, report)
    emit_operator_json(_summary_report(report) if args.console_summary_only else report)
    return 0 if report["ok"] else 1


def _summary_report(report: dict[str, Any]) -> dict[str, Any]:
    return {
        key: value
        for key, value in report.items()
        if key in {"schema", "ok", "git_commit", "claim_scope", "non_claims", "config", "summary", "checks"}
    }


if __name__ == "__main__":
    raise SystemExit(main())
