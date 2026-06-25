"""Benchmark: deadline scheduling vs brute-force vs greedy for batch clearing.

Compares the deadline scheduling algorithm against:
1. Brute-force optimal (O(n!)) - for small n only
2. Greedy limit-price ordering (current production heuristic)

Reports A (total volume), B (total surplus), and runtime for each method.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
import time
from typing import List, Tuple

from src.core.batch_clearing_deadline import deadline_schedule_batch
from src.core.batch_clearing_brute import brute_force_best_subset
from src.kernels.python.settlement_swap_runtime_v1 import quote_cpmm_swap_exact_in


def _quote(reserve_in, reserve_out, amount_in, fee_bps):
    return quote_cpmm_swap_exact_in(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    )


def _greedy_limit_price(
    intents: List[Tuple[str, int, int]],
    *,
    reserve_in_0: int,
    reserve_out_0: int,
    fee_bps: int,
) -> Tuple[Tuple[str, ...], int, int]:
    """Greedy limit-price ordering: sort by effective price (descending)."""
    if not intents:
        return (), 0, 0

    def limit_price(iid, ai, mo):
        return (mo * 10**18) // ai if ai > 0 else 0

    ordered = sorted(intents, key=lambda t: (-limit_price(*t), t[0]))

    r_in, r_out = reserve_in_0, reserve_out_0
    total_a, total_b = 0, 0
    executed = []
    for iid, ai, mo in ordered:
        try:
            q = _quote(r_in, r_out, ai, fee_bps)
            if q.amount_out >= max(mo, 1):
                total_a += ai
                total_b += q.amount_out - mo
                r_in, r_out = q.reserve_in_after, q.reserve_out_after
                executed.append(iid)
        except ValueError:
            continue

    return tuple(executed), total_a, total_b


def _generate_test_corpus(
    n: int, reserve_in: int, reserve_out: int, seed: int
) -> List[Tuple[str, int, int]]:
    """Generate a deterministic test corpus of n intents."""
    rng = random.Random(seed)
    intents = []
    for i in range(n):
        amount_in = rng.randint(1, max(2, reserve_in // 10))
        min_out_choices = [0, 1, rng.randint(1, max(2, reserve_out // 10))]
        min_amount_out = rng.choice(min_out_choices)
        intents.append((f"i{i}", amount_in, min_amount_out))
    return intents


def run_benchmark(
    n_range: range,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    seeds: range,
    brute_max_n: int = 8,
) -> List[dict]:
    """Run benchmark across n values and seeds."""
    results = []
    for n in n_range:
        for seed in seeds:
            intents = _generate_test_corpus(n, reserve_in, reserve_out, seed)

            entry = {"n": n, "seed": seed, "intents": intents}

            # Deadline scheduling
            t0 = time.perf_counter()
            dl_result = deadline_schedule_batch(
                intents,
                reserve_in_0=reserve_in,
                reserve_out_0=reserve_out,
                fee_bps=fee_bps,
                quote_exact_in_fn=_quote,
            )
            dl_time = time.perf_counter() - t0
            entry["deadline_a"] = dl_result.total_a
            entry["deadline_b"] = dl_result.total_b
            entry["deadline_time_ms"] = dl_time * 1000
            entry["deadline_count"] = len(dl_result.ordered_intents)

            # Greedy limit-price
            t0 = time.perf_counter()
            g_ids, g_a, g_b = _greedy_limit_price(
                intents,
                reserve_in_0=reserve_in,
                reserve_out_0=reserve_out,
                fee_bps=fee_bps,
            )
            g_time = time.perf_counter() - t0
            entry["greedy_a"] = g_a
            entry["greedy_b"] = g_b
            entry["greedy_time_ms"] = g_time * 1000
            entry["greedy_count"] = len(g_ids)

            # Brute-force (only for small n)
            if n <= brute_max_n:
                t0 = time.perf_counter()
                b_ids, b_a, b_b = brute_force_best_subset(
                    intents,
                    reserve_in_0=reserve_in,
                    reserve_out_0=reserve_out,
                    fee_bps=fee_bps,
                    quote_exact_in_fn=_quote,
                )
                b_time = time.perf_counter() - t0
                entry["brute_a"] = b_a
                entry["brute_b"] = b_b
                entry["brute_time_ms"] = b_time * 1000
                entry["brute_count"] = len(b_ids)
                entry["deadline_vs_brute_a_gap"] = b_a - dl_result.total_a
                entry["deadline_vs_brute_optimal"] = dl_result.total_a >= b_a
                entry["greedy_vs_brute_a_gap"] = b_a - g_a
            else:
                entry["brute_a"] = None
                entry["brute_b"] = None
                entry["brute_time_ms"] = None
                entry["brute_count"] = None
                entry["deadline_vs_brute_a_gap"] = None
                entry["deadline_vs_brute_optimal"] = None
                entry["greedy_vs_brute_a_gap"] = None

            entry["deadline_vs_greedy_a_gain"] = dl_result.total_a - g_a
            results.append(entry)

    return results


def main():
    parser = argparse.ArgumentParser(
        description="Benchmark deadline scheduling vs brute-force vs greedy"
    )
    parser.add_argument("--reserve-in", type=int, default=10_000)
    parser.add_argument("--reserve-out", type=int, default=10_000)
    parser.add_argument("--fee-bps", type=int, default=30)
    parser.add_argument("--n-min", type=int, default=1)
    parser.add_argument("--n-max", type=int, default=12)
    parser.add_argument("--seeds", type=int, default=10)
    parser.add_argument("--brute-max-n", type=int, default=8)
    parser.add_argument("--json", action="store_true", help="JSON output to stdout")
    args = parser.parse_args()

    results = run_benchmark(
        n_range=range(args.n_min, args.n_max + 1),
        reserve_in=args.reserve_in,
        reserve_out=args.reserve_out,
        fee_bps=args.fee_bps,
        seeds=range(args.seeds),
        brute_max_n=args.brute_max_n,
    )

    if args.json:
        print(json.dumps(results, indent=2))
        return

    # Summary table
    print(f"{'n':>3} {'seed':>4} {'dl_A':>8} {'g_A':>8} {'b_A':>8} "
          f"{'dl_ms':>8} {'g_ms':>8} {'b_ms':>8} {'dl_opt':>6} {'dl_gain':>8}")
    print("-" * 80)

    optimal_count = 0
    brute_count = 0
    total_gain = 0
    for r in results:
        brute_a = r["brute_a"] if r["brute_a"] is not None else "-"
        dl_opt = r["deadline_vs_brute_optimal"]
        dl_opt_str = "YES" if dl_opt else ("NO" if dl_opt is not None else "-")
        gain = r["deadline_vs_greedy_a_gain"]

        if r["brute_a"] is not None:
            brute_count += 1
            if dl_opt:
                optimal_count += 1

        total_gain += gain

        print(f"{r['n']:>3} {r['seed']:>4} {r['deadline_a']:>8} {r['greedy_a']:>8} "
              f"{str(brute_a):>8} {r['deadline_time_ms']:>8.2f} "
              f"{r['greedy_time_ms']:>8.2f} "
              f"{str(r['brute_time_ms'] or '-'):>8} {dl_opt_str:>6} {gain:>+8}")

    print("-" * 80)
    print(f"Deadline optimal vs brute-force: {optimal_count}/{brute_count}")
    print(f"Total A gain over greedy: {total_gain}")
    print(f"Average A gain over greedy: {total_gain / len(results):.1f}")


if __name__ == "__main__":
    main()
