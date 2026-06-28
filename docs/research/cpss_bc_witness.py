"""Reproducible pressure test for CPSS-BC versus two-phase decomposition.

Hermetic: no I/O, no network, no entropy source. Seeded RNG.
Determinism: same seed -> same verdict.

Usage:
    python3 docs/research/cpss_bc_witness.py
"""

from __future__ import annotations

import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.cross_pool_subset_dp import (
    SubsetDPLimits,
    TwoPoolCPMM,
    brute_force_k_pool_cpmm_batch,
    solve_k_pool_cpmm_subset_dp,
    solve_two_pool_cpmm_full_state_dp,
    solve_two_pool_cpmm_multiset_dp,
    solve_two_pool_cpmm_subset_dp,
)


def q(x: int, y: int, a: int, fee_bps: int = 0) -> int:
    """CPMM v8 exact-in output: fee ceil, output floor."""
    if a <= 0:
        return 0
    fee = -(-a * fee_bps // 10000)
    net = a - fee
    if net <= 0:
        return 0
    return (y * net) // (x + net)


def best_split_2pool(
    x0: int, y0: int, x1: int, y1: int, d: int, fee0: int = 0, fee1: int = 0
) -> tuple[int, int]:
    """Brute-force optimal 2-pool split, smallest a tie-break."""
    best_out, best_a = -1, 0
    for a in range(0, d + 1):
        total = q(x0, y0, a, fee0) + q(x1, y1, d - a, fee1)
        if total > best_out or (total == best_out and a < best_a):
            best_out, best_a = total, a
    return best_out, best_a


def decomposition(pools: list[tuple[int, int, int]], intents: list[int]) -> int:
    """Two-phase: split all against initial reserves, clear per-pool in order."""
    k = len(pools)
    splits: list[tuple[int, int]] = []
    for amt in intents:
        _, a = best_split_2pool(
            pools[0][0], pools[0][1], pools[1][0], pools[1][1], amt, pools[0][2], pools[1][2]
        )
        splits.append((a, amt - a))
    reserves = [(p[0], p[1], p[2]) for p in pools]
    total_out = 0
    for split in splits:
        for i in range(k):
            a = split[i]
            if a <= 0:
                continue
            x, y, fee = reserves[i]
            out = q(x, y, a, fee)
            reserves[i] = (x + a, y - out, fee)
            total_out += out
    return total_out


def cpss_bc(pools: list[tuple[int, int, int]], intents: list[int]) -> int:
    """CPSS-BC: process intents in order, split each against current reserves."""
    k = len(pools)
    reserves = [(p[0], p[1], p[2]) for p in pools]
    total_out = 0
    for amt in intents:
        _, a = best_split_2pool(
            reserves[0][0], reserves[0][1], reserves[1][0], reserves[1][1], amt,
            reserves[0][2], reserves[1][2],
        )
        for i, alloc in enumerate([a, amt - a]):
            if alloc <= 0:
                continue
            x, y, fee = reserves[i]
            out = q(x, y, alloc, fee)
            reserves[i] = (x + alloc, y - out, fee)
            total_out += out
    return total_out


def decomp_ab(pools: list[tuple[int, int, int]], intents: list[int]) -> tuple[int, int, int]:
    """Decomposition with AB-greedy per-pool ordering."""
    k = len(pools)
    splits: list[tuple[int, int, int]] = []
    for idx, amt in enumerate(intents):
        _, a = best_split_2pool(
            pools[0][0], pools[0][1], pools[1][0], pools[1][1], amt, pools[0][2], pools[1][2]
        )
        splits.append((idx, a, amt - a))
    reserves = [(p[0], p[1], p[2]) for p in pools]
    total_a, total_b, total_out = 0, 0, 0
    for pool_idx in range(k):
        x, y, fee = reserves[pool_idx]
        pool_legs = [(s[0], s[1 + pool_idx]) for s in splits if s[1 + pool_idx] > 0]
        pool_legs.sort(key=lambda t: (-q(x, y, t[1], fee), t[0]))
        for _intent_idx, amt in pool_legs:
            out = q(x, y, amt, fee)
            if out <= 0:
                continue
            x, y = x + amt, y - out
            reserves[pool_idx] = (x, y, fee)
            total_a += amt
            total_b += out
            total_out += out
    return total_a, total_b, total_out


def cpss_bc_ab(pools: list[tuple[int, int, int]], intents: list[int]) -> tuple[int, int, int]:
    """CPSS-BC with AB-greedy ordering across all intents."""
    k = len(pools)
    reserves = [(p[0], p[1], p[2]) for p in pools]
    remaining = list(enumerate(intents))
    total_a, total_b, total_out = 0, 0, 0
    while remaining:
        best_idx, best_out_i, best_pos = -1, -1, -1
        for pos, (idx, amt) in enumerate(remaining):
            out, _ = best_split_2pool(
                reserves[0][0], reserves[0][1], reserves[1][0], reserves[1][1], amt,
                reserves[0][2], reserves[1][2],
            )
            if out > best_out_i or (out == best_out_i and idx < best_idx):
                best_out_i, best_idx, best_pos = out, idx, pos
        idx, amt = remaining.pop(best_pos)
        _, a = best_split_2pool(
            reserves[0][0], reserves[0][1], reserves[1][0], reserves[1][1], amt,
            reserves[0][2], reserves[1][2],
        )
        for i, alloc in enumerate([a, amt - a]):
            if alloc <= 0:
                continue
            x, y, fee = reserves[i]
            out = q(x, y, alloc, fee)
            if out <= 0:
                continue
            reserves[i] = (x + alloc, y - out, fee)
            total_a += alloc
            total_b += out
            total_out += out
    return total_a, total_b, total_out


def run_fixed_order_suite(seed: int = 42, trials: int = 10000) -> dict[str, int]:
    rng = random.Random(seed)
    strict, tie, violation = 0, 0, 0
    for _ in range(trials):
        x0 = rng.randint(10, 500)
        y0 = rng.randint(10, 500)
        x1 = rng.randint(10, 500)
        y1 = rng.randint(10, 500)
        fee0 = rng.choice([0, 10, 30, 50, 100])
        fee1 = rng.choice([0, 10, 30, 50, 100])
        pools = [(x0, y0, fee0), (x1, y1, fee1)]
        n_intents = rng.randint(2, 4)
        intents = [rng.randint(10, 200) for _ in range(n_intents)]
        d_out = decomposition(pools, intents)
        c_out = cpss_bc(pools, intents)
        if c_out > d_out:
            strict += 1
        elif c_out == d_out:
            tie += 1
        else:
            violation += 1
    return {"strict": strict, "tie": tie, "violation": violation, "total": trials}


def run_ab_order_suite(seed: int = 12345, trials: int = 5000) -> dict[str, int]:
    rng = random.Random(seed)
    strict, tie, violation = 0, 0, 0
    for _ in range(trials):
        x0 = rng.randint(10, 500)
        y0 = rng.randint(10, 500)
        x1 = rng.randint(10, 500)
        y1 = rng.randint(10, 500)
        fee0 = rng.choice([0, 10, 30, 50, 100])
        fee1 = rng.choice([0, 10, 30, 50, 100])
        pools = [(x0, y0, fee0), (x1, y1, fee1)]
        n_intents = rng.randint(2, 5)
        intents = [rng.randint(10, 200) for _ in range(n_intents)]
        _, _, d_out = decomp_ab(pools, intents)
        _, _, c_out = cpss_bc_ab(pools, intents)
        if c_out > d_out:
            strict += 1
        elif c_out == d_out:
            tie += 1
        else:
            violation += 1
    return {"strict": strict, "tie": tie, "violation": violation, "total": trials}


def anticipatory_2(pools: list[tuple[int, int, int]], intents: list[int]) -> int:
    """Anticipatory algorithm for 2 intents: exhaustive split for first, optimal for last.

    Uses Last-Intent Optimality: the last intent is always split optimally
    against current reserves (no future intent to sacrifice for).
    """
    from itertools import permutations
    best = -1
    for perm in permutations(range(2)):
        ordered = [intents[i] for i in perm]
        for a0 in range(0, ordered[0] + 1):
            r = [(p[0], p[1], p[2]) for p in pools]
            t0 = 0
            for i, alloc in enumerate([a0, ordered[0] - a0]):
                if alloc <= 0:
                    continue
                x, y, fee = r[i]
                out = q(x, y, alloc, fee)
                r[i] = (x + alloc, y - out, fee)
                t0 += out
            _, a1 = best_split_2pool(r[0][0], r[0][1], r[1][0], r[1][1], ordered[1], r[0][2], r[1][2])
            t1 = t0
            for i, alloc in enumerate([a1, ordered[1] - a1]):
                if alloc <= 0:
                    continue
                x, y, fee = r[i]
                out = q(x, y, alloc, fee)
                t1 += out
            if t1 > best:
                best = t1
    return best


def true_brute_joint_2(pools: list[tuple[int, int, int]], intents: list[int]) -> int:
    """True joint optimum for 2 intents: all orderings, all splits."""
    from itertools import permutations
    best = -1
    for perm in permutations(range(2)):
        ordered = [intents[i] for i in perm]
        for a0 in range(0, ordered[0] + 1):
            r0 = [(p[0], p[1], p[2]) for p in pools]
            t0 = 0
            for i, alloc in enumerate([a0, ordered[0] - a0]):
                if alloc <= 0:
                    continue
                x, y, fee = r0[i]
                out = q(x, y, alloc, fee)
                r0[i] = (x + alloc, y - out, fee)
                t0 += out
            for a1 in range(0, ordered[1] + 1):
                r1 = [(r[0], r[1], r[2]) for r in r0]
                t1 = t0
                for i, alloc in enumerate([a1, ordered[1] - a1]):
                    if alloc <= 0:
                        continue
                    x, y, fee = r1[i]
                    out = q(x, y, alloc, fee)
                    r1[i] = (x + alloc, y - out, fee)
                    t1 += out
                if t1 > best:
                    best = t1
    return best


def run_anticipatory_vs_brute_suite(seed: int = 42, trials: int = 1000) -> dict[str, int]:
    """Test Anticipatory-2 == true brute joint (Last-Intent Optimality)."""
    rng = random.Random(seed)
    match, mismatch, total = 0, 0, 0
    for _ in range(trials):
        x0 = rng.choice([1, 2, 5, 10, 20, 50, 100, 200, 500])
        y0 = rng.choice([1, 2, 5, 10, 20, 50, 100, 200, 500])
        x1 = rng.choice([1, 2, 5, 10, 20, 50, 100, 200, 500])
        y1 = rng.choice([1, 2, 5, 10, 20, 50, 100, 200, 500])
        fee0 = rng.choice([0, 10, 30, 50, 100])
        fee1 = rng.choice([0, 10, 30, 50, 100])
        pools = [(x0, y0, fee0), (x1, y1, fee1)]
        intents = [rng.randint(1, 25), rng.randint(1, 25)]
        antic = anticipatory_2(pools, intents)
        tbj = true_brute_joint_2(pools, intents)
        total += 1
        if antic == tbj:
            match += 1
        elif tbj > antic:
            mismatch += 1
    return {"match": match, "mismatch": mismatch, "total": total}


def run_anticipatory_vs_decomp_suite(seed: int = 99999, trials: int = 5000) -> dict[str, int]:
    """Test Anticipatory-2 dominates decomposition (adversarial)."""
    rng = random.Random(seed)
    strict, tie, violation, total = 0, 0, 0, 0
    for _ in range(trials):
        x0 = rng.choice([1, 2, 5, 10, 50, 100, 500, 1000])
        y0 = rng.choice([1, 2, 5, 10, 50, 100, 500, 1000])
        x1 = rng.choice([1, 2, 5, 10, 50, 100, 500, 1000])
        y1 = rng.choice([1, 2, 5, 10, 50, 100, 500, 1000])
        fee0 = rng.choice([0, 1, 10, 30, 50, 100, 500, 9999])
        fee1 = rng.choice([0, 1, 10, 30, 50, 100, 500, 9999])
        pools = [(x0, y0, fee0), (x1, y1, fee1)]
        intents = [rng.randint(1, 100), rng.randint(1, 100)]
        d = decomposition(pools, intents)
        a = anticipatory_2(pools, intents)
        total += 1
        if a > d:
            strict += 1
        elif a == d:
            tie += 1
        else:
            violation += 1
    return {"strict": strict, "tie": tie, "violation": violation, "total": total}


def main() -> int:
    print("=== CPSS-BC Pressure Witness ===")
    print()

    fixed_cex_pools = [(1, 2, 0), (2, 2, 0)]
    fixed_cex_intents = [1, 1, 2]
    fixed_d = decomposition(fixed_cex_pools, fixed_cex_intents)
    fixed_c = cpss_bc(fixed_cex_pools, fixed_cex_intents)
    print("Known fixed-order counterexample (refutes universal CPSS-BC dominance)")
    print(f"  Pools:       {fixed_cex_pools}")
    print(f"  Intents:     {fixed_cex_intents}")
    print(f"  Decomp out:  {fixed_d}")
    print(f"  CPSS out:    {fixed_c}")
    print()

    ab_cex_pools = [(1, 2, 0), (1, 6, 0)]
    ab_cex_intents = [1, 2, 4]
    _d_a, _d_b, ab_d = decomp_ab(ab_cex_pools, ab_cex_intents)
    _c_a, _c_b, ab_c = cpss_bc_ab(ab_cex_pools, ab_cex_intents)
    print("Known AB-order counterexample (refutes universal CPSS-BC dominance)")
    print(f"  Pools:       {ab_cex_pools}")
    print(f"  Intents:     {ab_cex_intents}")
    print(f"  Decomp out:  {ab_d}")
    print(f"  CPSS out:    {ab_c}")
    print()

    print("Suite 1: Fixed intent order (moderate params, refutes broad dominance claim)")
    r1 = run_fixed_order_suite(seed=42, trials=10000)
    print(f"  Total:       {r1['total']}")
    print(f"  Strict:      {r1['strict']}")
    print(f"  Tie:         {r1['tie']}")
    print(f"  Violation:   {r1['violation']}")
    rate1 = (r1['strict'] + r1['tie']) / r1['total']
    print(f"  Dominance:   {rate1:.4f}")
    print()

    print("Suite 2: AB-greedy ordering (moderate params)")
    r2 = run_ab_order_suite(seed=12345, trials=5000)
    print(f"  Total:       {r2['total']}")
    print(f"  Strict:      {r2['strict']}")
    print(f"  Tie:         {r2['tie']}")
    print(f"  Violation:   {r2['violation']}")
    rate2 = (r2['strict'] + r2['tie']) / r2['total']
    print(f"  Dominance:   {rate2:.4f}")
    print()

    print("Suite 3: Anticipatory-2 == true brute joint (Last-Intent Optimality)")
    r3 = run_anticipatory_vs_brute_suite(seed=42, trials=1000)
    print(f"  Total:       {r3['total']}")
    print(f"  Match:       {r3['match']}")
    print(f"  Mismatch:    {r3['mismatch']}")
    print()

    print("Suite 4: Anticipatory-2 vs decomposition (adversarial)")
    r4 = run_anticipatory_vs_decomp_suite(seed=99999, trials=5000)
    print(f"  Total:       {r4['total']}")
    print(f"  Strict:      {r4['strict']}")
    print(f"  Tie:         {r4['tie']}")
    print(f"  Violation:   {r4['violation']}")
    rate4 = (r4['strict'] + r4['tie']) / r4['total']
    print(f"  Dominance:   {rate4:.4f}")
    print()

    if fixed_c >= fixed_d or ab_c >= ab_d:
        print("FAIL: expected counterexample no longer refutes CPSS-BC dominance")
        return 1
    if r3['mismatch'] != 0:
        print("FAIL: Anticipatory-2 does not match true brute joint (Last-Intent Optimality broken)")
        return 1
    if r4['violation'] != 0:
        print("FAIL: Anticipatory-2 does not dominate decomposition")
        return 1

    print("Suite 5: Subset DP vs brute force (3 intents, moderate)")
    r5 = run_subset_dp_vs_brute_suite(seed=42, trials=500, n_intents=3, adversarial=False)
    print(f"  Total:       {r5['total']}")
    print(f"  Match:       {r5['match']}")
    print(f"  Mismatch:    {r5['mismatch']}")
    print(f"  Max states:  {r5['max_states']}")
    print(f"  Avg states:  {r5['avg_states']:.1f}")
    print()

    print("Suite 6: Subset DP vs brute force (3 intents, adversarial)")
    r6 = run_subset_dp_vs_brute_suite(seed=99999, trials=2000, n_intents=3, adversarial=True)
    print(f"  Total:       {r6['total']}")
    print(f"  Match:       {r6['match']}")
    print(f"  Mismatch:    {r6['mismatch']}")
    print(f"  Max states:  {r6['max_states']}")
    print(f"  Avg states:  {r6['avg_states']:.1f}")
    print()

    print("Suite 7: Subset DP vs brute force (4 intents, moderate)")
    r7 = run_subset_dp_vs_brute_suite(seed=42, trials=100, n_intents=4, adversarial=False)
    print(f"  Total:       {r7['total']}")
    print(f"  Match:       {r7['match']}")
    print(f"  Mismatch:    {r7['mismatch']}")
    print(f"  Max states:  {r7['max_states']}")
    print(f"  Avg states:  {r7['avg_states']:.1f}")
    print()

    print("Suite 8: Compressed subset DP vs full-reserve subset DP")
    r8 = run_subset_dp_vs_full_state_suite(seed=20260626, trials=75)
    print(f"  Total:       {r8['total']}")
    print(f"  Match:       {r8['match']}")
    print(f"  Mismatch:    {r8['mismatch']}")
    print(f"  Max collision: {r8['max_collision']}")
    print(f"  Max states:  {r8['max_states']}")
    print(f"  Max full states: {r8['max_full_states']}")
    print()

    if r5['mismatch'] != 0 or r6['mismatch'] != 0 or r7['mismatch'] != 0:
        print("FAIL: Subset DP does not match brute force")
        return 1
    if r8['mismatch'] != 0:
        print("FAIL: compressed Subset DP does not match full-reserve Subset DP")
        return 1

    print("Suite 9: k-Pool subset DP vs brute force")
    r9 = suite_8_kpool_subset_dp(seed=20260630, trials=120, max_d=4)
    for name, row in r9.items():
        print(f"  {name}: {row['match']}/{row['total']} match, mismatches={row['mismatches']}")
    print()

    print("Suite 10: Multi-set DP vs subset DP on duplicate-heavy batches")
    r10 = suite_9_multiset_vs_subset(seed=20260628, trials=300)
    for name, row in r10.items():
        print(f"  {name}: {row['match']}/{row['total']} match, mismatches={row['mismatches']}")
    print()

    if any(int(row["mismatches"]) != 0 for row in r9.values()):
        print("FAIL: k-Pool Subset DP does not match brute force")
        return 1
    if any(int(row["mismatches"]) != 0 for row in r10.values()):
        print("FAIL: Multi-set DP does not match Subset DP")
        return 1
    print("PASS: CPSS-BC refuted; Subset DP, k-Pool DP, and Multi-set DP replay checks passed")
    return 0


def dp_subset(
    pools: list[tuple[int, int, int]], intents: list[int]
) -> tuple[int, int]:
    """Subset DP: state = (subset_bitmask, a, y0r) -> max_total_output.

    Returns (best_output, max_state_space_size).
    Complexity O(2^n * n * |S| * D). This is exponential in n and
    pseudo-polynomial in the split domain D, but removes the n! ordering factor.
    """
    result = solve_two_pool_cpmm_subset_dp(
        TwoPoolCPMM(*pools[0]),
        TwoPoolCPMM(*pools[1]),
        intents,
        limits=SubsetDPLimits(max_intents=20, max_total_input=100_000, max_states_per_subset=500_000),
        trace_mode="none",
    )
    return int(result.amount_out_total), int(result.max_states_per_subset)


def dp_subset_full_reserve(
    pools: list[tuple[int, int, int]], intents: list[int]
) -> tuple[int, int, int]:
    """Reference subset DP that keeps y1r in the state.

    This is slower than dp_subset, but useful as a regression oracle for the
    compressed-state dominance rule.
    """
    result = solve_two_pool_cpmm_full_state_dp(
        TwoPoolCPMM(*pools[0]),
        TwoPoolCPMM(*pools[1]),
        intents,
        limits=SubsetDPLimits(max_intents=12, max_total_input=20_000, max_states_per_subset=500_000),
    )
    return int(result.amount_out_total), int(result.max_states_per_subset), int(result.max_compressed_collision)


def true_brute_n(
    pools: list[tuple[int, int, int]], intents: list[int]
) -> int:
    """True joint optimum: all orderings, all per-intent splits."""
    from itertools import permutations
    n = len(intents)
    best = -1
    for perm in permutations(range(n)):
        ordered = [intents[i] for i in perm]
        def search(k: int, reserves: list[list[int]], total: int) -> None:
            nonlocal best
            if k == n:
                if total > best:
                    best = total
                return
            d = ordered[k]
            for b in range(0, d + 1):
                r = [list(reserves[0]), list(reserves[1])]
                t = total
                for i, alloc in enumerate([b, d - b]):
                    if alloc <= 0:
                        continue
                    x, y, fee = r[i]
                    out = q(x, y, alloc, fee)
                    r[i] = [x + alloc, y - out, fee]
                    t += out
                search(k + 1, r, t)
        search(0, [list(pools[0]), list(pools[1])], 0)
    return best


def run_subset_dp_vs_brute_suite(
    seed: int, trials: int, n_intents: int, adversarial: bool
) -> dict[str, int | float]:
    """Suite 5/6/7: Subset DP vs brute force."""
    random.seed(seed)
    match = 0
    mismatch = 0
    total = 0
    state_sizes: list[int] = []
    reserves_mod = [1, 2, 5, 10, 20, 50, 100]
    fees_mod = [0, 10, 30, 50, 100]
    reserves_adv = [1, 2, 3, 5, 10, 50, 100, 500, 1000, 10000]
    fees_adv = [0, 1, 10, 30, 50, 100, 500, 1000, 5000, 9999]
    amt_max = {3: 12, 4: 6}
    for _ in range(trials):
        rv = reserves_adv if adversarial else reserves_mod
        fv = fees_adv if adversarial else fees_mod
        pools = [
            (random.choice(rv), random.choice(rv), random.choice(fv)),
            (random.choice(rv), random.choice(rv), random.choice(fv)),
        ]
        intents = [random.randint(1, amt_max[n_intents]) for _ in range(n_intents)]
        dp_val, ms = dp_subset(pools, intents)
        brute = true_brute_n(pools, intents)
        state_sizes.append(ms)
        total += 1
        if dp_val == brute:
            match += 1
        else:
            mismatch += 1
    return {
        "total": total,
        "match": match,
        "mismatch": mismatch,
        "max_states": max(state_sizes) if state_sizes else 0,
        "avg_states": sum(state_sizes) / len(state_sizes) if state_sizes else 0,
    }


def run_subset_dp_vs_full_state_suite(seed: int, trials: int) -> dict[str, int]:
    """Suite 8: compressed Subset DP vs a full-reserve subset oracle."""
    random.seed(seed)
    match = 0
    mismatch = 0
    state_sizes: list[int] = []
    full_state_sizes: list[int] = []
    collisions: list[int] = []
    reserves = [1, 2, 3, 4, 5, 10, 50, 100, 500, 1000]
    fees = [0, 1, 10, 30, 100, 500, 1000, 5000, 9999]
    amt_max = {3: 14, 4: 9, 5: 6}
    for _ in range(trials):
        n_intents = random.choice([3, 4, 5])
        pools = [
            (random.choice(reserves), random.choice(reserves), random.choice(fees)),
            (random.choice(reserves), random.choice(reserves), random.choice(fees)),
        ]
        intents = [random.randint(1, amt_max[n_intents]) for _ in range(n_intents)]
        compressed, compressed_states = dp_subset(pools, intents)
        full, full_states, max_collision = dp_subset_full_reserve(pools, intents)
        state_sizes.append(compressed_states)
        full_state_sizes.append(full_states)
        collisions.append(max_collision)
        if compressed == full:
            match += 1
        else:
            mismatch += 1
    return {
        "total": trials,
        "match": match,
        "mismatch": mismatch,
        "max_states": max(state_sizes) if state_sizes else 0,
        "max_full_states": max(full_state_sizes) if full_state_sizes else 0,
        "max_collision": max(collisions) if collisions else 0,
    }


# ---------------------------------------------------------------------------
# Suite 8: k-Pool Subset DP vs brute force
# ---------------------------------------------------------------------------

def dp_subset_kpool(
    pools: list[tuple[int, int, int]],
    intents: list[int],
) -> tuple[int, int]:
    """k-pool subset DP. Returns (max_output, max_states)."""
    result = solve_k_pool_cpmm_subset_dp(
        [TwoPoolCPMM(*pool) for pool in pools],
        intents,
        limits=SubsetDPLimits(max_intents=12, max_total_input=20_000, max_states_per_subset=500_000, max_pools=6),
        trace_mode="none",
    )
    return int(result.amount_out_total), int(result.max_states_per_subset)


def brute_kpool(
    pools: list[tuple[int, int, int]], intents: list[int]
) -> int:
    """Brute force k-pool: all orderings, all k-way splits."""
    result = brute_force_k_pool_cpmm_batch(
        [TwoPoolCPMM(*pool) for pool in pools],
        intents,
        limits=SubsetDPLimits(max_intents=7, max_total_input=256, max_states_per_subset=500_000, max_pools=6),
    )
    return int(result.amount_out_total)


def suite_8_kpool_subset_dp(
    seed: int = 99999,
    trials: int = 120,
    max_d: int = 4,
) -> dict:
    """k-pool subset DP vs brute force, adversarial."""
    random.seed(seed)
    configs = [
        (3, 3, max(1, trials // 2)),
        (4, 2, max(1, trials // 3)),
        (5, 2, max(1, trials // 6)),
    ]
    results = {}
    for k_pools, n_intents, n_trials in configs:
        match = 0
        total = 0
        for _ in range(n_trials):
            pools = [
                (
                    random.choice([1, 2, 5, 10, 100, 1000, 10000]),
                    random.choice([1, 2, 5, 10, 100, 1000, 10000]),
                    random.choice([0, 1, 10, 100, 1000, 9999]),
                )
                for _ in range(k_pools)
            ]
            intents = [random.randint(1, max_d) for _ in range(n_intents)]
            dp_val, _ = dp_subset_kpool(pools, intents)
            brute = brute_kpool(pools, intents)
            total += 1
            if dp_val == brute:
                match += 1
        results[f"{k_pools}pool_{n_intents}intent"] = {
            "match": match,
            "total": total,
            "mismatches": total - match,
        }
    return results


# ---------------------------------------------------------------------------
# Suite 9: Multi-set DP vs subset DP
# ---------------------------------------------------------------------------

def dp_multiset(
    pools: list[tuple[int, int, int]], intents: list[int]
) -> int:
    """Multi-set DP: groups intents by amount."""
    result = solve_two_pool_cpmm_multiset_dp(
        TwoPoolCPMM(*pools[0]),
        TwoPoolCPMM(*pools[1]),
        intents,
        limits=SubsetDPLimits(max_intents=20, max_total_input=100_000, max_states_per_subset=500_000),
        trace_mode="none",
    )
    return int(result.amount_out_total)


def suite_9_multiset_vs_subset(
    seed: int = 99999, trials: int = 300
) -> dict:
    """Multi-set DP vs subset DP, adversarial."""
    random.seed(seed)
    results = {}
    for n in [3, 4, 5]:
        match = 0
        total = 0
        n_trials = trials if n == 3 else trials // 2
        if n == 5:
            n_trials = trials // 4
        for _ in range(n_trials):
            pools = [
                (
                    random.choice(
                        [1, 2, 3, 5, 10, 50, 100, 500, 1000, 10000]
                    ),
                    random.choice(
                        [1, 2, 3, 5, 10, 50, 100, 500, 1000, 10000]
                    ),
                    random.choice(
                        [0, 1, 10, 30, 50, 100, 500, 1000, 5000, 9999]
                    ),
                )
                for _ in range(2)
            ]
            alphabet = [random.randint(1, 8) for _ in range(random.choice([1, 2, 3]))]
            intents = [random.choice(alphabet) for _ in range(n)]
            ss_val, _ = dp_subset(pools, intents)
            ms = dp_multiset(pools, intents)
            total += 1
            if ss_val == ms:
                match += 1
        results[f"{n}_intent"] = {
            "match": match,
            "total": total,
            "mismatches": total - match,
        }
    return results


# ---------------------------------------------------------------------------
# Suite 10: Beam search DP with all orderings
# ---------------------------------------------------------------------------

def dp_beam(
    pools: list[tuple[int, int, int]],
    ordered_intents: list[int],
    beam_width: int = 20,
) -> int:
    """Beam search DP: keep top-K states by total_output."""
    x0, y0, fee0 = pools[0]
    x1, y1, fee1 = pools[1]
    n = len(ordered_intents)
    S = [0] * (n + 1)
    for k in range(n):
        S[k + 1] = S[k] + ordered_intents[k]
    dp: dict = {(0, y0): 0}
    for k in range(n):
        d = ordered_intents[k]
        new_dp: dict = {}
        for (a, y0r), t_out in dp.items():
            x0r = x0 + a
            x1r = x1 + (S[k] - a)
            y1r = y1 - t_out + (y0 - y0r)
            for b in range(0, d + 1):
                o0 = q(x0r, y0r, b, fee0)
                o1 = q(x1r, y1r, d - b, fee1)
                key = (a + b, y0r - o0)
                nt = t_out + o0 + o1
                if key not in new_dp or nt > new_dp[key]:
                    new_dp[key] = nt
        if len(new_dp) > beam_width:
            sorted_states = sorted(new_dp.items(), key=lambda x: -x[1])
            new_dp = dict(sorted_states[:beam_width])
        dp = new_dp
    return max(dp.values()) if dp else -1


def suite_10_beam_search_all_orderings(
    seed: int = 99999, trials: int = 1000, beam_width: int = 20
) -> dict:
    """Beam search DP with all n! orderings vs subset DP."""
    from itertools import permutations

    random.seed(seed)
    results = {}
    for n in [3, 4]:
        match = 0
        total = 0
        n_trials = trials if n == 3 else trials // 5
        for _ in range(n_trials):
            pools = [
                (
                    random.choice(
                        [1, 2, 3, 5, 10, 50, 100, 500, 1000, 10000]
                    ),
                    random.choice(
                        [1, 2, 3, 5, 10, 50, 100, 500, 1000, 10000]
                    ),
                    random.choice(
                        [0, 1, 10, 30, 50, 100, 500, 1000, 5000, 9999]
                    ),
                )
                for _ in range(2)
            ]
            max_d = 12 if n == 3 else 10
            intents = [random.randint(1, max_d) for _ in range(n)]
            dp_opt, _ = dp_subset(pools, intents)
            beam_val = max(
                dp_beam(pools, [intents[i] for i in p], beam_width)
                for p in permutations(range(n))
            )
            total += 1
            if beam_val == dp_opt:
                match += 1
        results[f"{n}_intent_beam{beam_width}"] = {
            "match": match,
            "total": total,
            "mismatches": total - match,
        }
    return results


if __name__ == "__main__":
    sys.exit(main())
