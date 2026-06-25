#!/usr/bin/env python3
"""Build a deterministic quote-count report for k-pool split-routing solvers.

Compares the k-pool staircase optimizer against:
- the existing small-domain DP (best_small_domain_many_pool_exact_in),
- the existing greedy fallback (best_many_pool_exact_in_split with bounded iters),
- the brute-force oracle (for parity and reference quote count).

The report is advisory promotion evidence. It counts exact quote calls and
checks brute-force oracle parity; it does not change the live route selector.
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

from src.core.split_routing import PoolXY, exact_out_for_pool_exact_in
from src.core.split_routing_kpool_staircase import (
    _PoolSpec,
    staircase_k_pool_best_split,
    best_k_pool_exact_in_split,
    should_use_staircase_dp,
)
from src.core.split_routing_kpool_brute import _brute_force_k_pool_split
from src.core.split_routing_many_exact_in_small import best_small_domain_many_pool_exact_in
from src.core.split_routing_many_exact_in import (
    ManyPoolExactInRequest,
    best_many_pool_exact_in_split,
)
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


@dataclass(frozen=True)
class KPoolBenchmarkCase:
    name: str
    pools: tuple[tuple[str, PoolXY], ...]
    amount_in: int
    max_legs: int
    tags: tuple[str, ...]


def _pool_state(pid: str, p: PoolXY) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0="A",
        asset1="B",
        reserve0=int(p.x),
        reserve1=int(p.y),
        fee_bps=int(p.fee_bps),
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
    )


def default_benchmark_cases() -> tuple[KPoolBenchmarkCase, ...]:
    return (
        # --- Parity cases (small D, brute-force tractable) ---
        KPoolBenchmarkCase(
            name="two_pool_balanced_small",
            pools=(
                ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
                ("pool-b", PoolXY(x=8_000, y=12_000, fee_bps=30)),
            ),
            amount_in=200,
            max_legs=2,
            tags=("two_pool", "balanced", "parity"),
        ),
        KPoolBenchmarkCase(
            name="two_pool_skewed_small",
            pools=(
                ("pool-a", PoolXY(x=1, y=1_000_000, fee_bps=0)),
                ("pool-b", PoolXY(x=1_000_000, y=1_000_000, fee_bps=0)),
            ),
            amount_in=300,
            max_legs=2,
            tags=("two_pool", "skewed", "breakpoint_sparse", "parity"),
        ),
        KPoolBenchmarkCase(
            name="two_pool_high_fee_small",
            pools=(
                ("pool-a", PoolXY(x=7, y=31, fee_bps=9_900)),
                ("pool-b", PoolXY(x=11, y=37, fee_bps=9_800)),
            ),
            amount_in=200,
            max_legs=2,
            tags=("two_pool", "high_fee", "plateau", "parity"),
        ),
        KPoolBenchmarkCase(
            name="three_pool_balanced_small",
            pools=(
                ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
                ("pool-b", PoolXY(x=8_000, y=12_000, fee_bps=50)),
                ("pool-c", PoolXY(x=12_000, y=8_000, fee_bps=30)),
            ),
            amount_in=150,
            max_legs=3,
            tags=("three_pool", "balanced", "parity"),
        ),
        KPoolBenchmarkCase(
            name="three_pool_skewed_small",
            pools=(
                ("pool-a", PoolXY(x=1, y=100_000, fee_bps=0)),
                ("pool-b", PoolXY(x=100_000, y=100_000, fee_bps=0)),
                ("pool-c", PoolXY(x=50_000, y=200_000, fee_bps=10)),
            ),
            amount_in=200,
            max_legs=3,
            tags=("three_pool", "skewed", "parity"),
        ),
        KPoolBenchmarkCase(
            name="three_pool_high_fee_small",
            pools=(
                ("pool-a", PoolXY(x=7, y=31, fee_bps=9_900)),
                ("pool-b", PoolXY(x=11, y=37, fee_bps=9_800)),
                ("pool-c", PoolXY(x=13, y=41, fee_bps=9_700)),
            ),
            amount_in=150,
            max_legs=3,
            tags=("three_pool", "high_fee", "plateau", "parity"),
        ),
        KPoolBenchmarkCase(
            name="four_pool_balanced_small",
            pools=(
                ("pool-a", PoolXY(x=5_000, y=5_000, fee_bps=30)),
                ("pool-b", PoolXY(x=4_000, y=6_000, fee_bps=50)),
                ("pool-c", PoolXY(x=6_000, y=4_000, fee_bps=30)),
                ("pool-d", PoolXY(x=5_500, y=5_500, fee_bps=70)),
            ),
            amount_in=80,
            max_legs=4,
            tags=("four_pool", "balanced", "parity"),
        ),
        KPoolBenchmarkCase(
            name="four_pool_skewed_small",
            pools=(
                ("pool-a", PoolXY(x=1, y=50_000, fee_bps=0)),
                ("pool-b", PoolXY(x=50_000, y=50_000, fee_bps=0)),
                ("pool-c", PoolXY(x=25_000, y=100_000, fee_bps=10)),
                ("pool-d", PoolXY(x=10_000, y=10_000, fee_bps=100)),
            ),
            amount_in=100,
            max_legs=4,
            tags=("four_pool", "skewed", "parity"),
        ),
    )


def performance_benchmark_cases() -> tuple[KPoolBenchmarkCase, ...]:
    """Large-domain evidence cases.

    These are intentionally opt-in because some exact comparator paths are
    quadratic in D. The default benchmark set must stay suitable for quick CI
    smoke and local review loops.
    """
    return (
        KPoolBenchmarkCase(
            name="two_pool_balanced_large",
            pools=(
                ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
                ("pool-b", PoolXY(x=8_000, y=12_000, fee_bps=30)),
            ),
            amount_in=8_000,
            max_legs=2,
            tags=("two_pool", "balanced", "performance"),
        ),
        KPoolBenchmarkCase(
            name="two_pool_skewed_large",
            pools=(
                ("pool-a", PoolXY(x=1, y=1_000_000, fee_bps=0)),
                ("pool-b", PoolXY(x=1_000_000, y=1_000_000, fee_bps=0)),
            ),
            amount_in=8_000,
            max_legs=2,
            tags=("two_pool", "skewed", "breakpoint_sparse", "performance"),
        ),
        KPoolBenchmarkCase(
            name="two_pool_high_fee_large",
            pools=(
                ("pool-a", PoolXY(x=7, y=31, fee_bps=9_900)),
                ("pool-b", PoolXY(x=11, y=37, fee_bps=9_800)),
            ),
            amount_in=8_000,
            max_legs=2,
            tags=("two_pool", "high_fee", "plateau", "performance"),
        ),
        KPoolBenchmarkCase(
            name="three_pool_balanced_large",
            pools=(
                ("pool-a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
                ("pool-b", PoolXY(x=8_000, y=12_000, fee_bps=50)),
                ("pool-c", PoolXY(x=12_000, y=8_000, fee_bps=30)),
            ),
            amount_in=8_000,
            max_legs=3,
            tags=("three_pool", "balanced", "performance"),
        ),
        KPoolBenchmarkCase(
            name="three_pool_skewed_large",
            pools=(
                ("pool-a", PoolXY(x=1, y=100_000, fee_bps=0)),
                ("pool-b", PoolXY(x=100_000, y=100_000, fee_bps=0)),
                ("pool-c", PoolXY(x=50_000, y=200_000, fee_bps=10)),
            ),
            amount_in=8_000,
            max_legs=3,
            tags=("three_pool", "skewed", "performance"),
        ),
        KPoolBenchmarkCase(
            name="four_pool_balanced_large",
            pools=(
                ("pool-a", PoolXY(x=5_000, y=5_000, fee_bps=30)),
                ("pool-b", PoolXY(x=4_000, y=6_000, fee_bps=50)),
                ("pool-c", PoolXY(x=6_000, y=4_000, fee_bps=30)),
                ("pool-d", PoolXY(x=5_500, y=5_500, fee_bps=70)),
            ),
            amount_in=8_000,
            max_legs=4,
            tags=("four_pool", "balanced", "performance"),
        ),
        KPoolBenchmarkCase(
            name="four_pool_skewed_large",
            pools=(
                ("pool-a", PoolXY(x=1, y=50_000, fee_bps=0)),
                ("pool-b", PoolXY(x=50_000, y=50_000, fee_bps=0)),
                ("pool-c", PoolXY(x=25_000, y=100_000, fee_bps=10)),
                ("pool-d", PoolXY(x=10_000, y=10_000, fee_bps=100)),
            ),
            amount_in=8_000,
            max_legs=4,
            tags=("four_pool", "skewed", "performance"),
        ),
    )


def all_benchmark_cases() -> tuple[KPoolBenchmarkCase, ...]:
    return (*default_benchmark_cases(), *performance_benchmark_cases())


def _counted_quote(original: Callable[[PoolXY, int], int]) -> tuple[Callable[[PoolXY, int], int], dict[str, int]]:
    calls = {"n": 0}

    def counted(pool: PoolXY, amount: int) -> int:
        calls["n"] = int(calls["n"]) + 1
        return original(pool, int(amount))

    return counted, calls


def _min_valid_for_pool(pool: PoolXY, amount_in_total: int) -> int:
    for a in range(1, int(amount_in_total) + 1):
        try:
            exact_out_for_pool_exact_in(pool, int(a))
            return int(a)
        except ValueError:
            continue
    return int(amount_in_total) + 1


def _alloc_to_legs(alloc: dict[str, int]) -> tuple[tuple[str, int], ...]:
    return tuple(sorted((pid, int(amt)) for pid, amt in alloc.items() if int(amt) > 0))


def _alloc_total_out(
    alloc: dict[str, int],
    pools: dict[str, PoolXY],
    quote_fn: Callable[[PoolXY, int], int] | None = None,
) -> int:
    """Compute total output for an allocation.

    If quote_fn is provided, uses it (so quotes are counted in the caller's
    counter). Otherwise uses the uncounted direct quote (for parity checks
    where the total output must be exact, not counted).
    """
    total = 0
    for pid, amt in alloc.items():
        if int(amt) <= 0:
            continue
        if quote_fn is not None:
            total += int(quote_fn(pools[pid], int(amt)))
        else:
            total += int(exact_out_for_pool_exact_in(pools[pid], int(amt)))
    return int(total)


def _run_staircase(case: KPoolBenchmarkCase) -> dict[str, Any]:
    pools_dict = {pid: p for pid, p in case.pools}
    specs = [
        _PoolSpec(pool_id=pid, pool=p, min_valid=_min_valid_for_pool(p, int(case.amount_in)))
        for pid, p in case.pools
    ]
    counted, calls = _counted_quote(exact_out_for_pool_exact_in)
    try:
        alloc = staircase_k_pool_best_split(
            pool_specs=specs,
            amount_in_total=int(case.amount_in),
            max_legs=int(case.max_legs),
            quote_exact_in=counted,
        )
        return {
            "status": "ok",
            "alloc": alloc,
            "legs": _alloc_to_legs(alloc),
            "total_out": _alloc_total_out(alloc, pools_dict, quote_fn=counted),
            "quote_count": int(calls["n"]),
        }
    except ValueError as exc:
        return {"status": "reject", "reason": str(exc), "quote_count": int(calls["n"])}


def _run_adaptive(case: KPoolBenchmarkCase) -> dict[str, Any]:
    """Run the adaptive entry point that picks staircase vs existing DP."""
    pools_dict = {pid: p for pid, p in case.pools}
    specs = [
        _PoolSpec(pool_id=pid, pool=p, min_valid=_min_valid_for_pool(p, int(case.amount_in)))
        for pid, p in case.pools
    ]
    counted, calls = _counted_quote(exact_out_for_pool_exact_in)

    def small_dp_fn(*, pool_ids, amount_in_total, max_legs, quote_for_pool_id):
        return best_small_domain_many_pool_exact_in(
            pool_ids=pool_ids,
            amount_in_total=int(amount_in_total),
            max_legs=int(max_legs),
            quote_for_pool_id=quote_for_pool_id,
        )

    try:
        alloc = best_k_pool_exact_in_split(
            pool_specs=specs,
            amount_in_total=int(case.amount_in),
            max_legs=int(case.max_legs),
            quote_exact_in=counted,
            small_domain_dp_fn=small_dp_fn,
        )
        return {
            "status": "ok",
            "alloc": alloc,
            "legs": _alloc_to_legs(alloc),
            "total_out": _alloc_total_out(alloc, pools_dict, quote_fn=counted),
            "quote_count": int(calls["n"]),
        }
    except ValueError as exc:
        return {"status": "reject", "reason": str(exc), "quote_count": int(calls["n"])}


def _run_brute(case: KPoolBenchmarkCase) -> dict[str, Any]:
    pools_dict = {pid: p for pid, p in case.pools}
    brute_pools = [
        (pid, p, _min_valid_for_pool(p, int(case.amount_in)))
        for pid, p in case.pools
    ]
    counted, calls = _counted_quote(exact_out_for_pool_exact_in)
    try:
        alloc = _brute_force_k_pool_split(
            pools=brute_pools,
            amount_in_total=int(case.amount_in),
            max_legs=int(case.max_legs),
            quote_exact_in=counted,
        )
        return {
            "status": "ok",
            "alloc": alloc,
            "legs": _alloc_to_legs(alloc),
            "total_out": _alloc_total_out(alloc, pools_dict, quote_fn=counted),
            "quote_count": int(calls["n"]),
        }
    except ValueError as exc:
        return {"status": "reject", "reason": str(exc), "quote_count": int(calls["n"])}


def _run_small_domain_dp(case: KPoolBenchmarkCase) -> dict[str, Any]:
    pools_dict = {pid: p for pid, p in case.pools}
    pool_ids = [pid for pid, _ in case.pools]
    min_valids = {pid: _min_valid_for_pool(p, int(case.amount_in)) for pid, p in case.pools}

    def quote_for_pool_id(pool_id: str, amount: int) -> int | None:
        if int(amount) < int(min_valids[pool_id]):
            return None
        try:
            return int(exact_out_for_pool_exact_in(pools_dict[pool_id], int(amount)))
        except ValueError:
            return None

    counted, calls = _counted_quote(exact_out_for_pool_exact_in)

    def quote_for_pool_id_counted(pool_id: str, amount: int) -> int | None:
        if int(amount) < int(min_valids[pool_id]):
            return None
        if int(amount) <= 0:
            return 0
        try:
            return int(counted(pools_dict[pool_id], int(amount)))
        except ValueError:
            return None

    try:
        alloc = best_small_domain_many_pool_exact_in(
            pool_ids=pool_ids,
            amount_in_total=int(case.amount_in),
            max_legs=int(case.max_legs),
            quote_for_pool_id=quote_for_pool_id_counted,
        )
        return {
            "status": "ok",
            "alloc": alloc,
            "legs": _alloc_to_legs(alloc),
            "total_out": _alloc_total_out(alloc, pools_dict, quote_fn=counted),
            "quote_count": int(calls["n"]),
        }
    except ValueError as exc:
        return {"status": "reject", "reason": str(exc), "quote_count": int(calls["n"])}


def _run_greedy(case: KPoolBenchmarkCase) -> dict[str, Any]:
    """Run the existing greedy fallback via best_many_pool_exact_in_split.

    Uses a low max_iters to simulate the large-domain greedy path (the small-domain
    DP path is taken when amount_in <= min(max_iters, 512); we set max_iters=64
    so amount_in > 64 forces the greedy path for our benchmark cases.
    """
    pools_dict = {pid: p for pid, p in case.pools}
    pool_states = [_pool_state(pid, p) for pid, p in case.pools]

    def reserves_for(pool: PoolState) -> tuple[int, int] | None:
        return (int(pool.reserve0), int(pool.reserve1))

    counted, calls = _counted_quote(exact_out_for_pool_exact_in)

    def quote_exact_in_for_pool(pool: PoolState, amount: int) -> int:
        return int(counted(PoolXY(x=int(pool.reserve0), y=int(pool.reserve1), fee_bps=int(pool.fee_bps)), int(amount)))

    request = ManyPoolExactInRequest(
        pools=pool_states,
        asset_in="A",
        asset_out="B",
        amount_in_total=int(case.amount_in),
        max_legs=int(case.max_legs),
        max_candidates=int(case.max_legs),
        max_iters=64,
        reserves_for=reserves_for,
        quote_exact_in=quote_exact_in_for_pool,
    )
    try:
        quote = best_many_pool_exact_in_split(request)
        alloc = {leg.pool_id: int(leg.amount_in) for leg in quote.legs}
        # Fill in zero-alloc pools for comparison.
        for pid, _ in case.pools:
            alloc.setdefault(pid, 0)
        return {
            "status": "ok",
            "alloc": alloc,
            "legs": _alloc_to_legs(alloc),
            "total_out": int(quote.amount_out_total),
            "quote_count": int(calls["n"]),
        }
    except ValueError as exc:
        return {"status": "reject", "reason": str(exc), "quote_count": int(calls["n"])}


def _case_report(case: KPoolBenchmarkCase) -> dict[str, Any]:
    is_parity = "parity" in case.tags
    # Skip the brute-force oracle for large performance cases (exponential cost).
    brute = _run_brute(case) if is_parity else {"status": "skipped", "quote_count": 0}
    staircase = _run_staircase(case)
    adaptive = _run_adaptive(case)
    small_dp = _run_small_domain_dp(case)
    greedy = _run_greedy(case)

    # Mark parity against brute oracle (only for parity cases).
    for report in (staircase, adaptive, small_dp, greedy):
        if is_parity and report["status"] == "ok" and brute["status"] == "ok":
            report["matches_oracle"] = (
                int(report["total_out"]) == int(brute["total_out"])
                and report["legs"] == brute["legs"]
            )
            report["output_matches_oracle"] = int(report["total_out"]) == int(brute["total_out"])
            report["leftmost_tie_break_matches_oracle"] = report["legs"] == brute["legs"]
        elif not is_parity:
            report["matches_oracle"] = None
            report["output_matches_oracle"] = None
            report["leftmost_tie_break_matches_oracle"] = None
        else:
            report["matches_oracle"] = False
            report["output_matches_oracle"] = False
            report["leftmost_tie_break_matches_oracle"] = False

    return {
        "name": case.name,
        "amount_in": int(case.amount_in),
        "max_legs": int(case.max_legs),
        "pools": [{"pool_id": pid, "x": int(p.x), "y": int(p.y), "fee_bps": int(p.fee_bps)} for pid, p in case.pools],
        "tags": list(case.tags),
        "oracle": brute,
        "staircase_kpool": staircase,
        "adaptive_kpool": adaptive,
        "small_domain_dp": small_dp,
        "greedy_fallback": greedy,
    }


def _summary(case_reports: Sequence[dict[str, Any]]) -> dict[str, Any]:
    summary: dict[str, Any] = {}
    for solver in ("staircase_kpool", "adaptive_kpool", "small_domain_dp", "greedy_fallback"):
        rows = [case[solver] for case in case_reports]
        ok_rows = [row for row in rows if row["status"] == "ok"]
        parity_rows = [row for row in ok_rows if row.get("matches_oracle") is not None]
        summary[solver] = {
            "ok_count": len(ok_rows),
            "reject_count": len(rows) - len(ok_rows),
            "parity_case_count": len(parity_rows),
            "oracle_match_count": sum(1 for row in parity_rows if row.get("matches_oracle") is True),
            "output_match_count": sum(1 for row in parity_rows if row.get("output_matches_oracle") is True),
            "total_quote_count": sum(int(row["quote_count"]) for row in rows),
            "max_quote_count": max((int(row["quote_count"]) for row in rows), default=0),
        }
    return summary


def build_kpool_staircase_report(
    *,
    cases: Sequence[KPoolBenchmarkCase] | None = None,
    include_performance: bool = False,
) -> dict[str, Any]:
    if cases is not None:
        selected_cases = tuple(cases)
    elif include_performance:
        selected_cases = all_benchmark_cases()
    else:
        selected_cases = default_benchmark_cases()
    case_reports = [_case_report(case) for case in selected_cases]
    return {
        "schema": "zenodex/kpool_staircase_benchmark/v1",
        "case_count": len(case_reports),
        "cases": case_reports,
        "summary": _summary(case_reports),
        "claim_scope": (
            "advisory quote-count and brute-force parity report for the "
            "experimental k-pool staircase optimizer; does not change the live "
            "route selector"
        ),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument(
        "--include-performance",
        action="store_true",
        help="include large-domain performance cases; may be slow",
    )
    args = parser.parse_args(argv)
    report = build_kpool_staircase_report(include_performance=args.include_performance)
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    print(encoded)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
