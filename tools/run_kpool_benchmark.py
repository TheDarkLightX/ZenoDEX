#!/usr/bin/env python3
"""Quick benchmark runner for k-pool staircase vs existing solvers."""
from __future__ import annotations
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.benchmark_kpool_staircase import (
    default_benchmark_cases,
    _run_brute,
    _run_staircase,
    _run_adaptive,
    _run_small_domain_dp,
    _run_greedy,
)


def _match(report, brute, is_parity):
    if not is_parity or report["status"] != "ok" or brute["status"] != "ok":
        return "N/A"
    return "OK" if (report["total_out"] == brute["total_out"] and report["legs"] == brute["legs"]) else "FAIL"


def main():
    cases = default_benchmark_cases()
    header = (
        f"{'name':40s} {'D':>5} {'L':>1} | "
        f"{'brute_q':>7} {'stair_q':>7} {'adapt_q':>7} {'dp_q':>7} {'greedy_q':>7} | "
        f"{'stair/dp':>8} {'adapt/dp':>8} | "
        f"{'stair':>5} {'adapt':>5} {'dp':>5} {'greedy':>5} | {'time':>6}"
    )
    print(header)
    print("-" * len(header))
    for c in cases:
        t0 = time.time()
        is_parity = "parity" in c.tags
        brute = _run_brute(c) if is_parity else {"status": "skipped", "quote_count": 0, "total_out": 0, "legs": ()}
        stair = _run_staircase(c)
        adapt = _run_adaptive(c)
        dp = _run_small_domain_dp(c)
        gr = _run_greedy(c)
        elapsed = time.time() - t0
        stair_ratio = f"{stair['quote_count'] / max(dp['quote_count'], 1):.2f}x"
        adapt_ratio = f"{adapt['quote_count'] / max(dp['quote_count'], 1):.2f}x"
        print(
            f"{c.name:40s} {c.amount_in:5d} {c.max_legs:1d} | "
            f"{brute['quote_count']:>7} {stair['quote_count']:>7} {adapt['quote_count']:>7} {dp['quote_count']:>7} {gr['quote_count']:>7} | "
            f"{stair_ratio:>8} {adapt_ratio:>8} | "
            f"{_match(stair, brute, is_parity):>5} {_match(adapt, brute, is_parity):>5} {_match(dp, brute, is_parity):>5} {_match(gr, brute, is_parity):>5} | "
            f"{elapsed:5.1f}s"
        )


if __name__ == "__main__":
    main()
