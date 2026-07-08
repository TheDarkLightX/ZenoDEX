"""K-pool discrete concavity violation characterization (sampling-based).

Characterizes how floor rounding breaks discrete concavity for k pools.
Uses random sampling instead of exhaustive enumeration for speed.
"""
from __future__ import annotations

import random
import sys
from dataclasses import dataclass
from typing import Sequence


@dataclass(frozen=True)
class Pool:
    reserve_in: int
    reserve_out: int
    fee_bps: int


def cpmm_output_cont(pool: Pool, amount_in: float) -> float:
    """Continuous CPMM: continuous fee, no floor."""
    if amount_in <= 0 or pool.reserve_in <= 0:
        return 0.0
    gamma = 1.0 - pool.fee_bps / 10000.0
    net = amount_in * gamma
    if net <= 0:
        return 0.0
    return pool.reserve_out * net / (pool.reserve_in + net)


def cpmm_output_lean_floor(pool: Pool, amount_in: float) -> int:
    """LEAN model: continuous fee, floor output. Matches Lean cpmmOutputFloor."""
    if amount_in <= 0 or pool.reserve_in <= 0:
        return 0
    gamma = 1.0 - pool.fee_bps / 10000.0
    net = amount_in * gamma
    if net <= 0:
        return 0
    return int(pool.reserve_out * net / (pool.reserve_in + net))


def cpmm_output_prod_floor(pool: Pool, amount_in: int) -> int:
    """PRODUCTION model: ceiling fee, floor output (v8 semantics)."""
    if amount_in <= 0 or pool.reserve_in <= 0:
        return 0
    gamma_num = 10000 - pool.fee_bps
    if gamma_num <= 0:
        return 0
    fee = -(-amount_in * pool.fee_bps // 10000)  # ceil
    net = amount_in - fee
    if net <= 0:
        return 0
    return (pool.reserve_out * net) // (pool.reserve_in + net)


# Use lean model for concavity tests (matches Lean proofs)
cpmm_output_floor = cpmm_output_lean_floor


def k_pool_split_cont(pools: Sequence[Pool], amounts: Sequence[int], D: int) -> float:
    total = 0.0
    for i, pool in enumerate(pools):
        amt = amounts[i] if i < len(amounts) else D - sum(amounts)
        total += cpmm_output_cont(pool, float(amt))
    return total


def k_pool_split_floor(pools: Sequence[Pool], amounts: Sequence[int], D: int) -> int:
    total = 0
    for i, pool in enumerate(pools):
        amt = amounts[i] if i < len(amounts) else D - sum(amounts)
        total += cpmm_output_floor(pool, amt)
    return total


def second_diff_discrete_coord(
    pools: Sequence[Pool], amounts: Sequence[int], D: int, coord: int, h: int
) -> int:
    a = list(amounts)
    def at_offset(offset: int) -> int:
        b = list(a)
        b[coord] += offset
        if sum(b) > D:
            return -(10**18)
        return k_pool_split_floor(pools, b, D)
    return at_offset(2 * h) - 2 * at_offset(h) + at_offset(0)


def sample_max_violation(pools: Sequence[Pool], D: int, n_samples: int = 5000) -> int:
    """Sample random points and find max interior violation."""
    k = len(pools)
    max_viol = 0
    rng = random.Random(hash(tuple(pools)) % 2**32)
    for _ in range(n_samples):
        amounts = [rng.randint(0, max(1, D // k)) for _ in range(k - 1)]
        if sum(amounts) >= D:
            amounts = [a // 3 for a in amounts]
        for coord in range(k - 1):
            for h in [1, 2]:
                if amounts[coord] + 2 * h < D - sum(amounts):
                    sd = second_diff_discrete_coord(pools, amounts, D, coord, h)
                    if sd > 0 and sd > max_viol:
                        max_viol = sd
    return max_viol


def test_2pool_violation_bounded() -> None:
    """2-pool: max interior violation is bounded by O(max spot price).

    Empirically, 2-pool violations can reach ~25 for high-fee, small-reserve
    configurations. The bound is O(L) where L is the Lipschitz constant
    (max spot price), not O(1). Floor rounding creates staircase plateaus
    whose width depends on the slope.
    """
    random.seed(42)
    max_overall = 0
    for _ in range(100):
        p0 = Pool(random.randint(100, 5000), random.randint(100, 5000),
                  random.choice([0, 30, 100, 300]))
        p1 = Pool(random.randint(100, 5000), random.randint(100, 5000),
                  random.choice([0, 30, 100, 300]))
        D = random.randint(20, 100)
        viol = sample_max_violation([p0, p1], D, n_samples=2000)
        max_overall = max(max_overall, viol)
    print(f"2-pool max violation: {max_overall}")
    # Empirically bounded by ~25 for these parameter ranges
    assert max_overall <= 30, f"2-pool violation {max_overall} > 30"


def test_3pool_violation_bounded() -> None:
    """3-pool: max interior violation is bounded by O(k * max spot price)."""
    random.seed(43)
    max_overall = 0
    for _ in range(50):
        pools = [Pool(random.randint(100, 5000), random.randint(100, 5000),
                      random.choice([0, 30, 100])) for _ in range(3)]
        D = random.randint(20, 60)
        viol = sample_max_violation(pools, D, n_samples=2000)
        max_overall = max(max_overall, viol)
    print(f"3-pool max violation: {max_overall}")
    # 3-pool should be at most ~1.5x the 2-pool bound
    assert max_overall <= 40, f"3-pool violation {max_overall} > 40"


def test_violation_scales_linearly() -> None:
    """Violation magnitude scales at most linearly with k."""
    violations_by_k = {}
    for k in [2, 3, 4, 5]:
        random.seed(44 + k)
        max_overall = 0
        for _ in range(30):
            pools = [Pool(random.randint(100, 5000), random.randint(100, 5000),
                          random.choice([0, 30, 100])) for _ in range(k)]
            D = random.randint(20, min(50, 15 * k))
            viol = sample_max_violation(pools, D, n_samples=1500)
            max_overall = max(max_overall, viol)
        violations_by_k[k] = max_overall
        print(f"k={k}: max violation = {max_overall}")
    for k in [3, 4, 5]:
        ratio = violations_by_k[k] / max(1, violations_by_k[2])
        assert ratio <= k * 3, f"k={k}: ratio {ratio:.2f} > 3*k={3*k}"


def test_floor_error_scales_with_k() -> None:
    """Floor error (cont - lean_floor) scales as < k for k pools.

    Uses the LEAN model (continuous fee + floor output) which matches
    the Lean proofs. Each pool contributes < 1 unit of floor error,
    so the total is < k.
    """
    for k in [2, 3, 4, 5]:
        random.seed(46 + k)
        max_err = 0.0
        for _ in range(50):
            pools = [Pool(random.randint(100, 5000), random.randint(100, 5000),
                          random.choice([0, 30, 100])) for _ in range(k)]
            D = random.randint(20, 50)
            for _ in range(10):
                amounts = [random.randint(0, D // k) for _ in range(k - 1)]
                if sum(amounts) >= D:
                    amounts = [a // 2 for a in amounts]
                # Use lean model (continuous fee, floor output)
                cont = k_pool_split_cont(pools, amounts, D)
                floor = k_pool_split_floor(pools, amounts, D)  # uses lean_floor
                max_err = max(max_err, cont - floor)
        print(f"k={k}: max floor error (lean) = {max_err:.4f}")
        # Lean model: each pool < 1, total < k
        assert max_err < k + 0.1, f"k={k}: floor error {max_err} >= {k}"


def test_ternary_search_accuracy_2pool() -> None:
    """2-pool ternary search accuracy (quick check)."""
    random.seed(47)
    exact_count = 0
    total = 50
    for _ in range(total):
        p0 = Pool(random.randint(1000, 5000), random.randint(1000, 5000), 30)
        p1 = Pool(random.randint(1000, 5000), random.randint(1000, 5000), 30)
        D = random.randint(20, 50)
        best_val = max(k_pool_split_floor([p0, p1], [a], D) for a in range(D + 1))
        lo, hi = 0, D
        for _ in range(30):
            if hi - lo < 2: break
            m1 = lo + (hi - lo) // 3
            m2 = hi - (hi - lo) // 3
            if k_pool_split_floor([p0, p1], [m1], D) < k_pool_split_floor([p0, p1], [m2], D):
                lo = m1 + 1
            else:
                hi = m2
        ts_val = max(k_pool_split_floor([p0, p1], [a], D) for a in range(lo, hi + 1))
        if ts_val == best_val:
            exact_count += 1
    accuracy = exact_count / total
    print(f"2-pool ternary search accuracy: {accuracy:.3f}")
    assert accuracy > 0.8, f"2-pool accuracy {accuracy:.3f} too low"


def main() -> int:
    tests = [
        test_2pool_violation_bounded,
        test_3pool_violation_bounded,
        test_violation_scales_linearly,
        test_floor_error_scales_with_k,
        test_ternary_search_accuracy_2pool,
    ]
    passed = 0
    failed = 0
    for test in tests:
        try:
            test()
            print(f"PASS: {test.__name__}")
            passed += 1
        except AssertionError as e:
            print(f"FAIL: {test.__name__}: {e}", file=sys.stderr)
            failed += 1
    print(f"\n{passed}/{passed + failed} tests passed")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
