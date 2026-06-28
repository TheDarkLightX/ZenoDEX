#!/usr/bin/env python3
"""Deterministic benchmark for the two-pool subset-DP batch oracle."""

from __future__ import annotations

import argparse
import json
import random
import time
import sys
from pathlib import Path
from statistics import mean

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.cross_pool_subset_dp import (
    SubsetDPLimits,
    TwoPoolCPMM,
    solve_k_pool_cpmm_multiset_dp,
    solve_k_pool_cpmm_subset_dp,
    solve_two_pool_cpmm_subset_dp,
)


def _case(rng: random.Random, *, n_intents: int) -> tuple[TwoPoolCPMM, TwoPoolCPMM, list[int]]:
    reserves = [1, 2, 3, 5, 10, 50, 100, 500, 1000, 10000]
    fees = [0, 1, 10, 30, 50, 100, 500, 1000, 5000, 9999]
    amount_max = max(2, 18 - n_intents)
    return (
        TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees)),
        TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees)),
        [rng.randint(1, amount_max) for _ in range(n_intents)],
    )


def _bench_n(*, seed: int, n_intents: int, trials: int, limits: SubsetDPLimits) -> dict[str, object]:
    rng = random.Random(seed + n_intents * 1009)
    elapsed_ms: list[float] = []
    max_states: list[int] = []
    final_states: list[int] = []
    transitions: list[int] = []
    outputs: list[int] = []
    for _ in range(trials):
        pool0, pool1, intents = _case(rng, n_intents=n_intents)
        start = time.perf_counter()
        result = solve_two_pool_cpmm_subset_dp(pool0, pool1, intents, limits=limits, trace_mode="none")
        elapsed_ms.append((time.perf_counter() - start) * 1000.0)
        max_states.append(int(result.max_states_per_subset))
        final_states.append(int(result.final_state_count))
        transitions.append(int(result.transitions_evaluated))
        outputs.append(int(result.amount_out_total))
    return {
        "n_intents": int(n_intents),
        "trials": int(trials),
        "avg_elapsed_ms": round(mean(elapsed_ms), 3),
        "max_elapsed_ms": round(max(elapsed_ms), 3),
        "avg_max_states_per_subset": round(mean(max_states), 1),
        "max_states_per_subset": max(max_states),
        "avg_final_states": round(mean(final_states), 1),
        "max_final_states": max(final_states),
        "avg_transitions": round(mean(transitions), 1),
        "max_transitions": max(transitions),
        "avg_output": round(mean(outputs), 1),
    }


def _bench_k_pool_multiset_fixtures(*, limits: SubsetDPLimits) -> list[dict[str, object]]:
    pools = (
        TwoPoolCPMM(5, 10, 5000),
        TwoPoolCPMM(2, 1000, 5000),
        TwoPoolCPMM(7, 300, 30),
    )
    fixtures = ([4, 4, 4, 4, 4, 4], [3, 3, 3, 5, 5])
    rows: list[dict[str, object]] = []
    for intents in fixtures:
        subset_started = time.perf_counter()
        subset = solve_k_pool_cpmm_subset_dp(pools, intents, limits=limits, trace_mode="none")
        subset_ms = (time.perf_counter() - subset_started) * 1000.0
        multiset_started = time.perf_counter()
        multiset = solve_k_pool_cpmm_multiset_dp(pools, intents, limits=limits, trace_mode="none")
        multiset_ms = (time.perf_counter() - multiset_started) * 1000.0
        rows.append(
            {
                "intents": list(int(v) for v in intents),
                "pool_count": len(pools),
                "same_output": bool(subset.amount_out_total == multiset.amount_out_total),
                "amount_out_total": int(subset.amount_out_total),
                "subset_states_visited": int(subset.states_visited),
                "multiset_states_visited": int(multiset.states_visited),
                "state_reduction": round(
                    int(subset.states_visited) / max(int(multiset.states_visited), 1),
                    3,
                ),
                "subset_transitions": int(subset.transitions_evaluated),
                "multiset_transitions": int(multiset.transitions_evaluated),
                "transition_reduction": round(
                    int(subset.transitions_evaluated) / max(int(multiset.transitions_evaluated), 1),
                    3,
                ),
                "subset_ordering_upper_bound": int(subset.ordering_count_upper_bound),
                "multiset_ordering_upper_bound": int(multiset.ordering_count_upper_bound),
                "ordering_reduction": round(
                    int(subset.ordering_count_upper_bound) / max(int(multiset.ordering_count_upper_bound), 1),
                    3,
                ),
                "subset_elapsed_ms": round(subset_ms, 3),
                "multiset_elapsed_ms": round(multiset_ms, 3),
                "elapsed_reduction": round(subset_ms / max(multiset_ms, 0.000001), 3),
            }
        )
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260626)
    parser.add_argument("--trials", type=int, default=5)
    parser.add_argument("--n-values", default="3,4,5,6,8")
    parser.add_argument("--max-intents", type=int, default=20)
    parser.add_argument("--max-total-input", type=int, default=100_000)
    parser.add_argument("--max-states-per-subset", type=int, default=250_000)
    parser.add_argument("--include-kpool-multiset", action="store_true")
    args = parser.parse_args()

    n_values = [int(part.strip()) for part in str(args.n_values).split(",") if part.strip()]
    limits = SubsetDPLimits(
        max_intents=int(args.max_intents),
        max_total_input=int(args.max_total_input),
        max_states_per_subset=int(args.max_states_per_subset),
    )
    started = time.perf_counter()
    results = [
        _bench_n(seed=int(args.seed), n_intents=n, trials=int(args.trials), limits=limits)
        for n in n_values
    ]
    payload = {
        "schema": "zenodex/cross_pool_subset_dp_benchmark/v1",
        "seed": int(args.seed),
        "limits": {
            "max_intents": int(limits.max_intents),
            "max_total_input": int(limits.max_total_input),
            "max_states_per_subset": int(limits.max_states_per_subset),
        },
        "results": results,
    }
    if args.include_kpool_multiset:
        payload["k_pool_multiset_fixtures"] = _bench_k_pool_multiset_fixtures(limits=limits)
    payload["elapsed_ms"] = round((time.perf_counter() - started) * 1000.0, 3)
    print(json.dumps(payload, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
