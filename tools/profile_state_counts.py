"""Profile the k-pool staircase DP to collect state-count evidence.

Collects:
- Jump point counts per pool
- Prefix/suffix DP state counts at each step
- Pareto-optimal state counts after indexing
- Combined state space size (prefix x suffix)
- Actual quote counts
- Wall-clock time

This data is used to:
1. Establish the actual resource envelope (not just asymptotic claims)
2. Identify worst-case state-count growth patterns
3. Inform hard resource bound design
"""
from __future__ import annotations

import json
import time
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.split_routing_kpool_staircase import (
    _PoolSpec,
    _build_jump_points,
    _build_prefix_suffix_dps,
    _index_by_spent_pareto,
    _combine_prefix_suffix_by_spent,
    _best_with_residual_from_combined,
    _best_exact_full_from_dp,
    _is_better_state,
    _KPoolStaircaseRequest,
    _KPoolStaircaseContext,
    _validate_pool_ids,
    _estimate_breakpoint_count,
    _State,
    _DPTable,
)
from src.core.split_routing import PoolXY
from src.core.split_routing import exact_out_for_pool_exact_in


@dataclass
class StateCountProfile:
    """Profile of state counts and work through the staircase DP pipeline."""
    k: int
    D: int
    max_legs: int
    jump_point_counts: dict[str, int] = field(default_factory=dict)
    prefix_state_counts: list[int] = field(default_factory=list)
    suffix_state_counts: list[int] = field(default_factory=list)
    pareto_state_counts: list[int] = field(default_factory=list)
    combined_state_counts: list[int] = field(default_factory=list)
    total_quotes: int = 0
    wall_time_ms: float = 0.0
    est_breakpoint_counts: dict[str, int] = field(default_factory=dict)
    est_total: int = 0
    threshold: int = 0
    # Work counts (new)
    transition_attempts: int = 0  # total candidate transitions tried in DP folds
    combine_pairs: int = 0  # total prefix x suffix candidate pairs iterated
    residual_quotes: int = 0  # total residual quote calls
    # Resource bounds (new)
    max_table_states: int = 0
    max_combine_pairs: int = 0
    max_residual_quotes: int = 0
    # Online Pareto pruning stats (new)
    pareto_pruned_transitions: int = 0  # transitions skipped by online Pareto check


def profile_staircase(
    pools: list[tuple[str, PoolXY]],
    amount_in_total: int,
    max_legs: int,
) -> StateCountProfile:
    """Run the staircase DP with full state-count and work-count instrumentation."""
    from src.core.split_routing_kpool_staircase import (
        _MAX_TABLE_STATES_MULTIPLIER,
        _MAX_COMBINE_PAIRS_MULTIPLIER,
        _MAX_RESIDUAL_QUOTES_MULTIPLIER,
    )

    k = len(pools)
    D = int(amount_in_total)
    profile = StateCountProfile(k=k, D=D, max_legs=int(max_legs))

    # Compute resource bounds
    profile.max_table_states = _MAX_TABLE_STATES_MULTIPLIER * (int(max_legs) + 1) * (D + 1)
    profile.max_combine_pairs = _MAX_COMBINE_PAIRS_MULTIPLIER * D * D * int(max_legs) * int(max_legs)
    profile.max_residual_quotes = _MAX_RESIDUAL_QUOTES_MULTIPLIER * D

    # Track quotes
    quote_count = {"n": 0}
    def counted_quote(pool, amount):
        quote_count["n"] += 1
        return int(exact_out_for_pool_exact_in(pool, int(amount)))

    specs = [_PoolSpec(pool_id=pid, pool=p, min_valid=1) for pid, p in pools]

    # Estimate breakpoint counts
    threshold = (k * D) // 4
    profile.threshold = threshold
    for pid, p in pools:
        est = _estimate_breakpoint_count(p, D)
        profile.est_breakpoint_counts[pid] = est
    profile.est_total = sum(profile.est_breakpoint_counts.values())

    t0 = time.perf_counter()

    # Build jump points
    request = _KPoolStaircaseRequest(
        pools=tuple(specs),
        amount_in_total=D,
        max_legs=int(max_legs),
        quote_exact_in=counted_quote,
    )
    context = _KPoolStaircaseContext(request=request)
    context.jump_points = _build_jump_points(request)

    for spec in specs:
        profile.jump_point_counts[spec.pool_id] = len(context.jump_points.get(spec.pool_id, []))

    # Estimate transition attempts: sum over folds of (states * candidates)
    # This is an upper bound on the work done in DP folds.
    ordered = sorted(specs, key=lambda p: p.pool_id)
    transition_attempts = 0
    for i in range(k):
        # Prefix fold i: states=prefix[i] size, candidates=pool[i] jump points
        # We don't have prefix yet, so estimate after building.
        pass

    # Build prefix/suffix DPs (with resource bounds for profiling)
    prefix, suffix = _build_prefix_suffix_dps(
        pools=tuple(specs),
        jump_points=context.jump_points,
        amount_total=D,
        max_legs=int(max_legs),
        max_table_states=profile.max_table_states,
    )

    # Count transition attempts (upper bound: states_before * candidates)
    for i in range(k):
        states_before = len(prefix[i])
        candidates_i = len(context.jump_points.get(ordered[i].pool_id, []))
        transition_attempts += states_before * candidates_i
    for i in range(k - 1, -1, -1):
        states_before = len(suffix[i + 1])
        candidates_i = len(context.jump_points.get(ordered[i].pool_id, []))
        transition_attempts += states_before * candidates_i
    profile.transition_attempts = transition_attempts

    for i in range(k + 1):
        profile.prefix_state_counts.append(len(prefix[i]))
        profile.suffix_state_counts.append(len(suffix[i]))

    # For each interior pool candidate, measure Pareto + combined sizes + work
    def quote_fn(pool_id, amount):
        return context.quote(pool_id, int(amount))

    total_combine_pairs = 0
    total_residual_quotes = 0

    for i in range(k):
        prefix_index = _index_by_spent_pareto(prefix[i], max_legs=int(max_legs))
        suffix_index = _index_by_spent_pareto(suffix[i + 1], max_legs=int(max_legs))

        pareto_size = sum(len(v) for v in prefix_index.values()) + sum(len(v) for v in suffix_index.values())
        profile.pareto_state_counts.append(pareto_size)

        # Count combine pairs (without triggering ResourceLimitExceeded)
        pair_count = 0
        for p_spent, p_candidates in prefix_index.items():
            for s_spent, s_candidates in suffix_index.items():
                if int(p_spent) + int(s_spent) >= D:
                    continue
                for _ in p_candidates:
                    for _ in s_candidates:
                        pair_count += 1
        total_combine_pairs += pair_count

        combined = _combine_prefix_suffix_by_spent(
            prefix_index=prefix_index,
            suffix_index=suffix_index,
            amount_total=D,
            max_legs=int(max_legs),
            max_combine_pairs=profile.max_combine_pairs,
        )
        profile.combined_state_counts.append(len(combined))

        # Count residual quotes
        for spent in combined:
            residual = D - int(spent)
            if residual > 0 and residual >= 1:
                total_residual_quotes += 1

    profile.combine_pairs = total_combine_pairs
    profile.residual_quotes = total_residual_quotes

    t1 = time.perf_counter()
    profile.wall_time_ms = (t1 - t0) * 1000.0
    profile.total_quotes = quote_count["n"]

    return profile


def format_profile(p: StateCountProfile) -> str:
    """Format a profile for human-readable output."""
    lines = []
    lines.append(f"k={p.k}, D={p.D}, max_legs={p.max_legs}")
    lines.append(f"  threshold={p.threshold}, est_total={p.est_total} ({'FALLBACK' if p.est_total >= p.threshold else 'STAIRCASE'})")
    lines.append(f"  est_breakpoints: {p.est_breakpoint_counts}")
    lines.append(f"  jump_points: {p.jump_point_counts}")
    lines.append(f"  total_jump_points: {sum(p.jump_point_counts.values())}")
    lines.append(f"  prefix_state_counts: {p.prefix_state_counts}")
    lines.append(f"  suffix_state_counts: {p.suffix_state_counts}")
    lines.append(f"  max_prefix_states: {max(p.prefix_state_counts) if p.prefix_state_counts else 0}")
    lines.append(f"  max_suffix_states: {max(p.suffix_state_counts) if p.suffix_state_counts else 0}")
    lines.append(f"  pareto_state_counts (per interior): {p.pareto_state_counts}")
    lines.append(f"  max_pareto: {max(p.pareto_state_counts) if p.pareto_state_counts else 0}")
    lines.append(f"  combined_state_counts (per interior): {p.combined_state_counts}")
    lines.append(f"  max_combined: {max(p.combined_state_counts) if p.combined_state_counts else 0}")
    lines.append(f"  --- work counts ---")
    lines.append(f"  transition_attempts: {p.transition_attempts}")
    lines.append(f"  combine_pairs: {p.combine_pairs}")
    lines.append(f"  residual_quotes: {p.residual_quotes}")
    lines.append(f"  --- resource bounds ---")
    lines.append(f"  max_table_states: {p.max_table_states}")
    lines.append(f"  max_combine_pairs: {p.max_combine_pairs}")
    lines.append(f"  max_residual_quotes: {p.max_residual_quotes}")
    lines.append(f"  total_quotes: {p.total_quotes}")
    lines.append(f"  wall_time_ms: {p.wall_time_ms:.2f}")
    return "\n".join(lines)


# Test cases: sparse, moderate, dense, adversarial
TEST_CASES = [
    # Sparse: very skewed reserves, few breakpoints
    ("sparse-k2", [
        ("a", PoolXY(x=100_000, y=10_000, fee_bps=30)),
        ("b", PoolXY(x=80_000, y=12_000, fee_bps=30)),
    ], 8_000, 2),

    ("sparse-k3", [
        ("a", PoolXY(x=100_000, y=10_000, fee_bps=30)),
        ("b", PoolXY(x=80_000, y=12_000, fee_bps=30)),
        ("c", PoolXY(x=50_000, y=20_000, fee_bps=10)),
    ], 8_000, 3),

    ("sparse-k4", [
        ("a", PoolXY(x=100_000, y=10_000, fee_bps=30)),
        ("b", PoolXY(x=80_000, y=12_000, fee_bps=30)),
        ("c", PoolXY(x=50_000, y=20_000, fee_bps=10)),
        ("d", PoolXY(x=200_000, y=5_000, fee_bps=50)),
    ], 8_000, 4),

    # Moderate: balanced reserves
    ("moderate-k2", [
        ("a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("b", PoolXY(x=8_000, y=12_000, fee_bps=30)),
    ], 8_000, 2),

    ("moderate-k3", [
        ("a", PoolXY(x=10_000, y=10_000, fee_bps=30)),
        ("b", PoolXY(x=8_000, y=12_000, fee_bps=30)),
        ("c", PoolXY(x=5_000, y=20_000, fee_bps=10)),
    ], 8_000, 3),

    # Dense: small reserves relative to D
    ("dense-k2", [
        ("a", PoolXY(x=1_000, y=1_000, fee_bps=30)),
        ("b", PoolXY(x=800, y=1_200, fee_bps=30)),
    ], 8_000, 2),

    # Adversarial: one sparse, one dense
    ("adversarial-k2", [
        ("a", PoolXY(x=100_000, y=1_000, fee_bps=0)),
        ("b", PoolXY(x=500, y=500, fee_bps=0)),
    ], 8_000, 2),

    # Large D, sparse
    ("sparse-k2-largeD", [
        ("a", PoolXY(x=1_000_000, y=100_000, fee_bps=30)),
        ("b", PoolXY(x=800_000, y=120_000, fee_bps=30)),
    ], 50_000, 2),

    # Zero fee, very sparse
    ("zerofee-sparse-k3", [
        ("a", PoolXY(x=500_000, y=50_000, fee_bps=0)),
        ("b", PoolXY(x=400_000, y=60_000, fee_bps=0)),
        ("c", PoolXY(x=300_000, y=80_000, fee_bps=0)),
    ], 20_000, 3),
]


def main():
    profiles = []
    for name, pools, D, max_legs in TEST_CASES:
        print(f"\n{'='*60}")
        print(f"Case: {name}")
        print(f"{'='*60}")
        p = profile_staircase(pools, D, max_legs)
        print(format_profile(p))
        profiles.append({"name": name, "profile": {
            "k": p.k, "D": p.D, "max_legs": p.max_legs,
            "threshold": p.threshold, "est_total": p.est_total,
            "est_breakpoint_counts": p.est_breakpoint_counts,
            "jump_point_counts": p.jump_point_counts,
            "total_jump_points": sum(p.jump_point_counts.values()),
            "max_prefix_states": max(p.prefix_state_counts) if p.prefix_state_counts else 0,
            "max_suffix_states": max(p.suffix_state_counts) if p.suffix_state_counts else 0,
            "max_pareto": max(p.pareto_state_counts) if p.pareto_state_counts else 0,
            "max_combined": max(p.combined_state_counts) if p.combined_state_counts else 0,
            "combined_state_counts": p.combined_state_counts,
            "pareto_state_counts": p.pareto_state_counts,
            "prefix_state_counts": p.prefix_state_counts,
            "suffix_state_counts": p.suffix_state_counts,
            "total_quotes": p.total_quotes,
            "wall_time_ms": round(p.wall_time_ms, 2),
            "transition_attempts": p.transition_attempts,
            "combine_pairs": p.combine_pairs,
            "residual_quotes": p.residual_quotes,
            "max_table_states": p.max_table_states,
            "max_combine_pairs": p.max_combine_pairs,
            "max_residual_quotes": p.max_residual_quotes,
        }})

    # Summary table
    print(f"\n{'='*80}")
    print("SUMMARY: State-count envelope")
    print(f"{'='*80}")
    print(f"\n{'='*100}")
    print("SUMMARY: State-count + work-count envelope (with online Pareto pruning)")
    print(f"{'='*100}")
    print(f"{'Case':<25} {'k':>2} {'D':>6} {'JP':>5} {'Pfx':>5} {'Sfx':>5} {'Pareto':>7} {'Combo':>7} {'Xitions':>8} {'Pairs':>8} {'ResQ':>6} {'ms':>7}")
    print("-" * 100)
    for entry in profiles:
        p = entry["profile"]
        print(f"{entry['name']:<25} {p['k']:>2} {p['D']:>6} {p['total_jump_points']:>5} {p['max_prefix_states']:>5} {p['max_suffix_states']:>5} {p['max_pareto']:>7} {p['max_combined']:>7} {p['transition_attempts']:>8} {p['combine_pairs']:>8} {p['residual_quotes']:>6} {p['wall_time_ms']:>7.1f}")

    # Resource bounds vs actual usage
    print(f"\n{'='*100}")
    print("RESOURCE BOUNDS vs ACTUAL USAGE")
    print(f"{'='*100}")
    print(f"{'Case':<25} {'maxTable':>10} {'maxPfx':>8} {'maxCombo':>12} {'actPairs':>10} {'maxResQ':>8} {'actResQ':>8}")
    print("-" * 100)
    for entry in profiles:
        p = entry["profile"]
        print(f"{entry['name']:<25} {p['max_table_states']:>10} {p['max_prefix_states']:>8} {p['max_combine_pairs']:>12} {p['combine_pairs']:>10} {p['max_residual_quotes']:>8} {p['residual_quotes']:>8}")

    # Save JSON for Codex
    with open("/tmp/kpool_state_counts.json", "w", encoding="utf-8") as f:
        json.dump(profiles, f, indent=2)
    print(f"\nJSON saved to /tmp/kpool_state_counts.json")


if __name__ == "__main__":
    main()
