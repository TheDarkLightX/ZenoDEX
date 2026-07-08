#!/usr/bin/env python3
"""Parity and reduction checker for AB subset-DP dominance pruning.

This is an opt-in research experiment. It compares a dominance-pruned
same-direction exact-in AB subset DP against the unpruned full-state DP and
small brute force. It does not modify production ordering.
"""

from __future__ import annotations

import json
import math
import sys
import time
import argparse
from dataclasses import asdict, dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.batch_clearing_ab_order import _best_order_by_objective_bruteforce  # noqa: E402
from tools.check_ab_subset_dp_dominance_candidate import (  # noqa: E402
    _AbState,
    _apply_intent,
    _case,
    _context,
    _dominates,
    _initial_state,
    _key,
    _sender_index,
)


CASE_SIZES = (4, 5, 6, 7)
VARIANTS_PER_SIZE = 6


@dataclass(frozen=True)
class _DpRun:
    order_ids: tuple[str, ...]
    objective_key: tuple[int, int, tuple[str, ...]]
    transitions_evaluated: int
    states_inserted: int
    states_retained: int
    dominated_insertions_skipped: int
    retained_states_removed: int
    max_bucket_size: int
    elapsed_ms: float


@dataclass
class _Aggregate:
    case_count: int = 0
    mismatch_count: int = 0
    brute_mismatch_count: int = 0
    max_state_insertion_reduction: float = 0.0
    max_retained_state_reduction: float = 0.0
    max_transition_reduction: float = 0.0
    max_bucket_reduction: float = 0.0
    total_full_states_inserted: int = 0
    total_pruned_states_inserted: int = 0
    total_full_transitions: int = 0
    total_pruned_transitions: int = 0
    total_dominated_insertions_skipped: int = 0
    total_retained_states_removed: int = 0


def _ratio(left: int | float, right: int | float) -> float:
    denominator = float(right)
    if denominator <= 0:
        return 0.0
    return float(left) / denominator


def _is_better(candidate: _AbState, incumbent: _AbState | None, context: object) -> bool:
    if incumbent is None:
        return True
    return context.factories.is_better_ab_key_fn(_key(candidate, context), _key(incumbent, context))


def _insert_state_with_pruning(bucket: list[_AbState], state: _AbState) -> tuple[bool, int]:
    for existing in bucket:
        if _dominates(existing, state):
            return False, 0

    retained: list[_AbState] = []
    removed = 0
    for existing in bucket:
        if _dominates(state, existing):
            removed += 1
            continue
        retained.append(existing)
    retained.append(state)
    bucket[:] = retained
    return True, removed


def _run_subset_dp(intents: list[object], context: object, *, prune: bool) -> _DpRun:
    started = time.perf_counter()
    sender_index = _sender_index(context)
    states_by_mask: dict[int, list[_AbState]] = {0: [_initial_state(context)]}
    transitions_evaluated = 0
    states_inserted = 1
    dominated_insertions_skipped = 0
    retained_states_removed = 0
    max_bucket_size = 1
    n = len(intents)

    for mask in range(1 << n):
        states = states_by_mask.get(mask, [])
        max_bucket_size = max(max_bucket_size, len(states))
        for state in list(states):
            for idx, intent in enumerate(intents):
                bit = 1 << idx
                if mask & bit:
                    continue
                transitions_evaluated += 1
                next_mask = mask | bit
                next_state = _apply_intent(state, intent, context, sender_index)
                bucket = states_by_mask.setdefault(next_mask, [])
                if prune:
                    inserted, removed = _insert_state_with_pruning(bucket, next_state)
                    if inserted:
                        states_inserted += 1
                    else:
                        dominated_insertions_skipped += 1
                    retained_states_removed += removed
                else:
                    bucket.append(next_state)
                    states_inserted += 1
                max_bucket_size = max(max_bucket_size, len(bucket))

    final_mask = (1 << n) - 1
    best_state: _AbState | None = None
    for state in states_by_mask.get(final_mask, []):
        if _is_better(state, best_state, context):
            best_state = state
    if best_state is None:
        raise RuntimeError("subset DP produced no final state")

    retained_total = sum(len(bucket) for bucket in states_by_mask.values())
    return _DpRun(
        order_ids=best_state.order_ids,
        objective_key=_key(best_state, context),
        transitions_evaluated=int(transitions_evaluated),
        states_inserted=int(states_inserted),
        states_retained=int(retained_total),
        dominated_insertions_skipped=int(dominated_insertions_skipped),
        retained_states_removed=int(retained_states_removed),
        max_bucket_size=int(max_bucket_size),
        elapsed_ms=round((time.perf_counter() - started) * 1000.0, 3),
    )


def _order_ids(order: object) -> tuple[str, ...]:
    if order is None:
        return ()
    return tuple(intent.intent_id for intent in order)


def _check_case(n: int, variant: int) -> dict[str, object]:
    pool, intents, balances = _case(n, variant)
    context = _context(pool, intents, balances)
    full = _run_subset_dp(intents, context, prune=False)
    pruned = _run_subset_dp(intents, context, prune=True)
    brute = _best_order_by_objective_bruteforce(intents, context)
    brute_ids = _order_ids(brute)

    same_dp_key = full.objective_key == pruned.objective_key
    same_dp_order = full.order_ids == pruned.order_ids
    same_brute = brute_ids == full.order_ids == pruned.order_ids
    return {
        "n": n,
        "variant": variant,
        "ok": bool(same_dp_key and same_dp_order and same_brute),
        "same_dp_key": bool(same_dp_key),
        "same_dp_order": bool(same_dp_order),
        "same_brute_order": bool(same_brute),
        "brute_order_ids": brute_ids,
        "full": asdict(full),
        "pruned": asdict(pruned),
        "reductions": {
            "state_insertion": round(_ratio(full.states_inserted, pruned.states_inserted), 6),
            "states_retained": round(_ratio(full.states_retained, pruned.states_retained), 6),
            "transitions": round(_ratio(full.transitions_evaluated, pruned.transitions_evaluated), 6),
            "max_bucket": round(_ratio(full.max_bucket_size, pruned.max_bucket_size), 6),
        },
    }


def _case_summary(case: dict[str, object]) -> dict[str, object]:
    full = case["full"]
    pruned = case["pruned"]
    return {
        "n": case["n"],
        "variant": case["variant"],
        "ok": case["ok"],
        "same_brute_order": case["same_brute_order"],
        "full_states_inserted": full["states_inserted"],
        "pruned_states_inserted": pruned["states_inserted"],
        "full_transitions": full["transitions_evaluated"],
        "pruned_transitions": pruned["transitions_evaluated"],
        "dominated_insertions_skipped": pruned["dominated_insertions_skipped"],
        "retained_states_removed": pruned["retained_states_removed"],
        "reductions": case["reductions"],
    }


def _summarize(cases: list[dict[str, object]]) -> _Aggregate:
    aggregate = _Aggregate(case_count=len(cases))
    for case in cases:
        full = case["full"]
        pruned = case["pruned"]
        reductions = case["reductions"]
        aggregate.mismatch_count += 0 if case["ok"] else 1
        aggregate.brute_mismatch_count += 0 if case["same_brute_order"] else 1
        aggregate.max_state_insertion_reduction = max(
            aggregate.max_state_insertion_reduction,
            float(reductions["state_insertion"]),
        )
        aggregate.max_retained_state_reduction = max(
            aggregate.max_retained_state_reduction,
            float(reductions["states_retained"]),
        )
        aggregate.max_transition_reduction = max(
            aggregate.max_transition_reduction,
            float(reductions["transitions"]),
        )
        aggregate.max_bucket_reduction = max(
            aggregate.max_bucket_reduction,
            float(reductions["max_bucket"]),
        )
        aggregate.total_full_states_inserted += int(full["states_inserted"])
        aggregate.total_pruned_states_inserted += int(pruned["states_inserted"])
        aggregate.total_full_transitions += int(full["transitions_evaluated"])
        aggregate.total_pruned_transitions += int(pruned["transitions_evaluated"])
        aggregate.total_dominated_insertions_skipped += int(pruned["dominated_insertions_skipped"])
        aggregate.total_retained_states_removed += int(pruned["retained_states_removed"])
    return aggregate


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--include-cases",
        action="store_true",
        help="include full per-case order and objective details in the JSON receipt",
    )
    args = parser.parse_args()
    started = time.perf_counter()
    cases = [
        _check_case(n, variant)
        for n in CASE_SIZES
        for variant in range(VARIANTS_PER_SIZE)
    ]
    aggregate = _summarize(cases)
    payload = {
        "schema": "zenodex/ab_subset_dp_dominance_pruning_check/v1",
        "ok": aggregate.mismatch_count == 0,
        "bounds": {
            "case_sizes": CASE_SIZES,
            "variants_per_size": VARIANTS_PER_SIZE,
            "brute_force": "all permutations for each case",
            "domain": "same-pool, same-direction, exact-in AB ordering research cases",
        },
        "summary": asdict(aggregate),
        "aggregate_reductions": {
            "state_insertion": round(
                _ratio(aggregate.total_full_states_inserted, aggregate.total_pruned_states_inserted),
                6,
            ),
            "transitions": round(
                _ratio(aggregate.total_full_transitions, aggregate.total_pruned_transitions),
                6,
            ),
            "factorial_reference_n7": math.factorial(7),
        },
        "first_mismatch": next((case for case in cases if not case["ok"]), None),
        "case_summaries": [_case_summary(case) for case in cases],
        "non_claims": [
            "This is an opt-in research checker, not a production ordering change.",
            "The dominance rule is only tested for exact-in same-direction AB cases.",
            "Passing this checker is not a machine-checked proof.",
            "No settlement authority is derived from this artifact.",
        ],
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }
    if args.include_cases:
        payload["cases"] = cases
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
