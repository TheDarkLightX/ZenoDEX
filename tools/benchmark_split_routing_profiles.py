#!/usr/bin/env python3
"""Build a deterministic quote-count report for split-routing profiles.

The report is advisory promotion evidence. It compares profile outputs against
the brute-force oracle and counts exact quote calls; it does not change the live
route selector or make a production-readiness claim.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core import split_routing as split_routing_mod

PoolXY = split_routing_mod.PoolXY

DEFAULT_PROFILES = ("adaptive_v6", "dense24", "staircase_exact")


@dataclass(frozen=True)
class SplitRoutingBenchmarkCase:
    name: str
    pool0: PoolXY
    pool1: PoolXY
    amount_in: int
    tags: tuple[str, ...]


def default_benchmark_cases() -> tuple[SplitRoutingBenchmarkCase, ...]:
    return (
        SplitRoutingBenchmarkCase(
            name="known_dense_gap",
            pool0=PoolXY(x=87, y=80, fee_bps=75),
            pool1=PoolXY(x=46, y=66, fee_bps=11),
            amount_in=6_539,
            tags=("known_gap", "small_out"),
        ),
        SplitRoutingBenchmarkCase(
            name="high_pressure_small_out",
            pool0=PoolXY(x=108, y=48, fee_bps=85),
            pool1=PoolXY(x=83, y=41, fee_bps=35),
            amount_in=8_533,
            tags=("dense32_escalation", "small_out"),
        ),
        SplitRoutingBenchmarkCase(
            name="extreme_dense32_regime",
            pool0=PoolXY(x=102, y=31, fee_bps=193),
            pool1=PoolXY(x=132, y=92, fee_bps=177),
            amount_in=13_704,
            tags=("dense32_escalation", "high_pressure"),
        ),
        SplitRoutingBenchmarkCase(
            name="skewed_deep_thin",
            pool0=PoolXY(x=1, y=1_000_000, fee_bps=0),
            pool1=PoolXY(x=1_000_000, y=1_000_000, fee_bps=0),
            amount_in=8_000,
            tags=("skewed", "breakpoint_sparse"),
        ),
        SplitRoutingBenchmarkCase(
            name="endpoint_heavy_fee_gap",
            pool0=PoolXY(x=999_983, y=257, fee_bps=250),
            pool1=PoolXY(x=257, y=999_983, fee_bps=250),
            amount_in=8_000,
            tags=("endpoint", "skewed"),
        ),
        SplitRoutingBenchmarkCase(
            name="high_fee_plateau",
            pool0=PoolXY(x=7, y=31, fee_bps=9_900),
            pool1=PoolXY(x=11, y=37, fee_bps=9_800),
            amount_in=8_000,
            tags=("high_fee", "plateau"),
        ),
    )


def build_split_routing_profile_report(
    *,
    cases: Sequence[SplitRoutingBenchmarkCase] | None = None,
    profiles: Sequence[str] = DEFAULT_PROFILES,
    window: int = 64,
) -> dict[str, Any]:
    selected_cases = tuple(cases) if cases is not None else default_benchmark_cases()
    selected_profiles = tuple(str(profile) for profile in profiles)
    case_reports = [
        _case_report(case=case, profiles=selected_profiles, window=int(window))
        for case in selected_cases
    ]
    return {
        "schema": "zenodex/split_routing_profile_benchmark/v1",
        "window": int(window),
        "profiles": list(selected_profiles),
        "case_count": len(case_reports),
        "cases": case_reports,
        "summary": _summary(case_reports=case_reports, profiles=selected_profiles),
        "claim_scope": (
            "advisory quote-count and brute-force parity report; does not change "
            "the live default profile"
        ),
    }


def _case_report(
    *,
    case: SplitRoutingBenchmarkCase,
    profiles: Sequence[str],
    window: int,
) -> dict[str, Any]:
    oracle = _counted_call(
        lambda: split_routing_mod.brute_force_best_split_two_pools_exact_in(
            case.pool0,
            case.pool1,
            case.amount_in,
        )
    )
    profile_reports = {
        profile: _profile_report(case=case, profile=profile, oracle=oracle, window=window)
        for profile in profiles
    }
    return {
        "name": case.name,
        "amount_in": int(case.amount_in),
        "pool0": _pool_json(case.pool0),
        "pool1": _pool_json(case.pool1),
        "tags": list(case.tags),
        "oracle": oracle,
        "profiles": profile_reports,
    }


def _profile_report(
    *,
    case: SplitRoutingBenchmarkCase,
    profile: str,
    oracle: dict[str, Any],
    window: int,
) -> dict[str, Any]:
    result = _counted_call(
        lambda: split_routing_mod.best_split_two_pools_exact_in(
            case.pool0,
            case.pool1,
            case.amount_in,
            window=window,
            search_profile=profile,
        )
    )
    if result["status"] != "ok" or oracle["status"] != "ok":
        result["matches_oracle"] = False
        return result
    result["matches_oracle"] = (
        int(result["amount_out"]) == int(oracle["amount_out"])
        and int(result["split_a"]) == int(oracle["split_a"])
    )
    result["output_matches_oracle"] = int(result["amount_out"]) == int(oracle["amount_out"])
    result["leftmost_tie_break_matches_oracle"] = int(result["split_a"]) == int(oracle["split_a"])
    return result


def _counted_call(fn: Callable[[], tuple[int, int]]) -> dict[str, Any]:
    original_quote = split_routing_mod.exact_out_for_pool_exact_in
    calls = {"n": 0}

    def counted_quote(pool: PoolXY, amount: int) -> int:
        calls["n"] = int(calls["n"]) + 1
        return original_quote(pool, amount)

    split_routing_mod.exact_out_for_pool_exact_in = counted_quote  # type: ignore[assignment]
    try:
        try:
            amount_out, split_a = fn()
        except ValueError as exc:
            return {
                "status": "reject",
                "reason": str(exc),
                "quote_count": int(calls["n"]),
            }
    finally:
        split_routing_mod.exact_out_for_pool_exact_in = original_quote
    return {
        "status": "ok",
        "amount_out": int(amount_out),
        "split_a": int(split_a),
        "quote_count": int(calls["n"]),
    }


def _pool_json(pool: PoolXY) -> dict[str, int]:
    return {"x": int(pool.x), "y": int(pool.y), "fee_bps": int(pool.fee_bps)}


def _summary(*, case_reports: Sequence[dict[str, Any]], profiles: Sequence[str]) -> dict[str, Any]:
    summary: dict[str, Any] = {}
    for profile in profiles:
        rows = [case["profiles"][profile] for case in case_reports]
        ok_rows = [row for row in rows if row["status"] == "ok"]
        summary[profile] = {
            "ok_count": len(ok_rows),
            "reject_count": len(rows) - len(ok_rows),
            "oracle_match_count": sum(1 for row in ok_rows if row.get("matches_oracle") is True),
            "total_quote_count": sum(int(row["quote_count"]) for row in rows),
            "max_quote_count": max((int(row["quote_count"]) for row in rows), default=0),
        }
    return summary


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profiles", default=",".join(DEFAULT_PROFILES))
    parser.add_argument("--window", type=int, default=64)
    parser.add_argument("--output-json", type=Path)
    args = parser.parse_args(argv)

    profiles = tuple(part.strip() for part in args.profiles.split(",") if part.strip())
    report = build_split_routing_profile_report(profiles=profiles, window=args.window)
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    print(encoded)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
