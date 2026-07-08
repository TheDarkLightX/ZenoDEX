#!/usr/bin/env python3
"""Adversarial parity checker for the k-pool multiset DP research oracle."""

from __future__ import annotations

import argparse
import json
import random
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.cross_pool_subset_dp import (  # noqa: E402
    KPoolBatchResult,
    SubsetDPLimits,
    TwoPoolCPMM,
    brute_force_k_pool_cpmm_batch,
    solve_k_pool_cpmm_multiset_dp,
    solve_k_pool_cpmm_subset_dp,
)


@dataclass(frozen=True)
class _CorpusStats:
    case_count: int = 0
    mismatch_count: int = 0
    max_state_reduction: float = 0.0
    max_transition_reduction: float = 0.0
    max_ordering_reduction: float = 0.0


def _ratio(numerator: int, denominator: int) -> float:
    return round(float(int(numerator) / max(int(denominator), 1)), 6)


def _duplicate_intents(rng: random.Random, *, intent_count: int, amount_max: int) -> list[int]:
    alphabet = [rng.randint(1, int(amount_max)) for _ in range(rng.choice([1, 2]))]
    return [rng.choice(alphabet) for _ in range(int(intent_count))]


def _pools(rng: random.Random, *, pool_count: int, reserves: Iterable[int], fees: Iterable[int]) -> tuple[TwoPoolCPMM, ...]:
    reserve_values = tuple(int(v) for v in reserves)
    fee_values = tuple(int(v) for v in fees)
    return tuple(
        TwoPoolCPMM(rng.choice(reserve_values), rng.choice(reserve_values), rng.choice(fee_values))
        for _ in range(int(pool_count))
    )


def _case_summary(*, pools: tuple[TwoPoolCPMM, ...], intents: list[int]) -> dict[str, object]:
    return {
        "pools": [asdict(pool) for pool in pools],
        "intents": [int(v) for v in intents],
    }


def _assert_same_output(
    *,
    label: str,
    pools: tuple[TwoPoolCPMM, ...],
    intents: list[int],
    left_name: str,
    left: KPoolBatchResult,
    right_name: str,
    right: KPoolBatchResult,
) -> dict[str, object] | None:
    if int(left.amount_out_total) == int(right.amount_out_total):
        return None
    return {
        "label": label,
        "left_name": left_name,
        "left_amount_out_total": int(left.amount_out_total),
        "right_name": right_name,
        "right_amount_out_total": int(right.amount_out_total),
        **_case_summary(pools=pools, intents=intents),
    }


def _run_subset_multiset_corpus(*, rng: random.Random, limits: SubsetDPLimits) -> tuple[_CorpusStats, dict[str, object] | None]:
    reserves = [1, 2, 3, 5, 10, 50, 100]
    fees = [0, 1, 10, 30, 100, 1000, 5000, 9999]
    configs = ((3, 4, 12, 4), (3, 5, 8, 3), (4, 3, 10, 3), (4, 4, 6, 2))
    stats = _CorpusStats()
    for pool_count, intent_count, trials, amount_max in configs:
        for trial_index in range(int(trials)):
            intents = _duplicate_intents(rng, intent_count=intent_count, amount_max=int(amount_max))
            pools = _pools(rng, pool_count=int(pool_count), reserves=reserves, fees=fees)
            subset = solve_k_pool_cpmm_subset_dp(pools, intents, limits=limits, trace_mode="none")
            multiset = solve_k_pool_cpmm_multiset_dp(pools, intents, limits=limits, trace_mode="none")
            mismatch = _assert_same_output(
                label=f"subset_multiset:{pool_count}:{intent_count}:{trial_index}",
                pools=pools,
                intents=intents,
                left_name="subset",
                left=subset,
                right_name="multiset",
                right=multiset,
            )
            if mismatch is not None:
                return (
                    _CorpusStats(case_count=stats.case_count + 1, mismatch_count=stats.mismatch_count + 1),
                    mismatch,
                )
            stats = _CorpusStats(
                case_count=stats.case_count + 1,
                mismatch_count=stats.mismatch_count,
                max_state_reduction=max(
                    stats.max_state_reduction,
                    _ratio(subset.states_visited, multiset.states_visited),
                ),
                max_transition_reduction=max(
                    stats.max_transition_reduction,
                    _ratio(subset.transitions_evaluated, multiset.transitions_evaluated),
                ),
                max_ordering_reduction=max(
                    stats.max_ordering_reduction,
                    _ratio(subset.ordering_count_upper_bound, multiset.ordering_count_upper_bound),
                ),
            )
    return stats, None


def _run_bruteforce_corpus(*, rng: random.Random, limits: SubsetDPLimits) -> tuple[_CorpusStats, dict[str, object] | None]:
    reserves = [1, 2, 3, 5, 10]
    fees = [0, 1, 10, 30, 100, 1000, 5000, 9999]
    configs = ((3, 4, 8, 2), (4, 3, 6, 2))
    stats = _CorpusStats()
    for pool_count, intent_count, trials, amount_max in configs:
        for trial_index in range(int(trials)):
            intents = _duplicate_intents(rng, intent_count=intent_count, amount_max=int(amount_max))
            pools = _pools(rng, pool_count=int(pool_count), reserves=reserves, fees=fees)
            multiset = solve_k_pool_cpmm_multiset_dp(pools, intents, limits=limits)
            brute = brute_force_k_pool_cpmm_batch(pools, intents, limits=limits)
            mismatch = _assert_same_output(
                label=f"bruteforce:{pool_count}:{intent_count}:{trial_index}",
                pools=pools,
                intents=intents,
                left_name="multiset",
                left=multiset,
                right_name="bruteforce",
                right=brute,
            )
            if mismatch is not None:
                return (
                    _CorpusStats(case_count=stats.case_count + 1, mismatch_count=stats.mismatch_count + 1),
                    mismatch,
                )
            stats = _CorpusStats(
                case_count=stats.case_count + 1,
                mismatch_count=stats.mismatch_count,
                max_state_reduction=stats.max_state_reduction,
                max_transition_reduction=stats.max_transition_reduction,
                max_ordering_reduction=max(
                    stats.max_ordering_reduction,
                    _ratio(brute.ordering_count_upper_bound, multiset.ordering_count_upper_bound),
                ),
            )
    return stats, None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=2026062803)
    parser.add_argument("--max-intents", type=int, default=20)
    parser.add_argument("--max-total-input", type=int, default=100_000)
    parser.add_argument("--max-states-per-subset", type=int, default=250_000)
    parser.add_argument("--max-pools", type=int, default=5)
    args = parser.parse_args()

    started = time.perf_counter()
    limits = SubsetDPLimits(
        max_intents=int(args.max_intents),
        max_total_input=int(args.max_total_input),
        max_states_per_subset=int(args.max_states_per_subset),
        max_pools=int(args.max_pools),
    )
    rng = random.Random(int(args.seed))
    subset_stats, subset_mismatch = _run_subset_multiset_corpus(rng=rng, limits=limits)
    brute_stats, brute_mismatch = _run_bruteforce_corpus(rng=rng, limits=limits)
    mismatch = subset_mismatch or brute_mismatch
    payload = {
        "schema": "zenodex/kpool_multiset_dp_adversarial_check/v1",
        "ok": mismatch is None,
        "seed": int(args.seed),
        "limits": asdict(limits),
        "subset_multiset": asdict(subset_stats),
        "bruteforce": asdict(brute_stats),
        "first_mismatch": mismatch,
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
        "non_claims": [
            "research oracle only",
            "no settlement authority",
            "no exact-out support",
            "no heterogeneous per-intent constraints",
            "no polynomial-time claim for all-distinct inputs",
        ],
    }
    print(json.dumps(payload, sort_keys=True, indent=2))
    return 0 if mismatch is None else 1


if __name__ == "__main__":
    raise SystemExit(main())
