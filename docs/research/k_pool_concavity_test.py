"""K-pool continuous concavity test.

Tests the hypothesis that the k-pool CPMM split function is strictly concave
in each coordinate direction, generalizing the 2-pool proof from Phase 3A.

Key insight: F(a1, ..., a_{k-1}) = sum_i f_i(c_i * a_i) where the last pool
gets the remainder a_{k-1} = D - sum_{j<k-1} a_j.
f_i(x) = K_i*x/(M_i+x).

The second forward difference of F in direction j is just the second forward
difference of f_j plus f_{k-1} (the remainder pool), which is strictly negative
(proven in CpmmSplitConcavity.lean for 2 pools, extended to 3 in
KPoolSplitConcavity.lean).

This means:
1. F is concave in each coordinate (marginal concavity)
2. The Hessian of F has negative DIAGONAL entries (coordinate concavity)
   NOTE: The Hessian is NOT fully diagonal because the remainder pool couples
   coordinates: pool k-1 depends on all a_j via the sum constraint.
   The off-diagonal entries come from the remainder pool's cross-terms.
   However, the Hessian is still negative definite (jointly concave) because
   the remainder pool is itself concave and the coupling is through a linear
   constraint (simplex).
3. F is jointly concave (separable sum of concave functions under linear
   constraint)

Tests:
1. Coordinate-wise second differences are negative (marginal concavity)
2. Random direction second differences are negative (joint concavity)
3. Hessian eigenvalues are all negative (negative definite)
4. Ternary search in each coordinate finds the same optimum as brute force
"""
from __future__ import annotations

import random
import sys
from dataclasses import dataclass
from typing import Sequence

import numpy as np


@dataclass(frozen=True)
class Pool:
    """CPMM pool parameters."""
    K: float  # R_out (output reserve)
    M: float  # R_in (input reserve)
    c: float  # effective input coefficient (1 - fee)


def cpmm_output_cont(K: float, M: float, x: float) -> float:
    """Continuous CPMM output: K*x/(M+x)."""
    if M + x <= 0:
        return float("-inf")
    return K * x / (M + x)


def k_pool_split_cont(pools: Sequence[Pool], amounts: Sequence[float]) -> float:
    """K-pool continuous split output: sum_i K_i*c_i*a_i / (M_i + c_i*a_i).

    The (k-1) amounts are for pools 0..k-2. Pool k-1 gets the remainder: D - sum(a_i).
    """
    D = sum(amounts)
    total = 0.0
    for i, pool in enumerate(pools):
        if i < len(amounts):
            x = pool.c * amounts[i]
        else:
            # Last pool gets remainder
            x = pool.c * (D - sum(amounts))
        total += cpmm_output_cont(pool.K, pool.M, x)
    return total


def k_pool_split_full(
    pools: Sequence[Pool], amounts: Sequence[float], D: float
) -> float:
    """K-pool split where amounts are for pools 0..k-2, pool k-1 gets D - sum."""
    remainder = D - sum(amounts)
    if remainder < 0:
        return float("-inf")
    total = 0.0
    for i, pool in enumerate(pools):
        if i < len(amounts):
            x = pool.c * amounts[i]
        else:
            x = pool.c * remainder
        total += cpmm_output_cont(pool.K, pool.M, x)
    return total


def second_diff_coordinate(
    pools: Sequence[Pool],
    amounts: Sequence[float],
    D: float,
    coord: int,
    h: float,
) -> float:
    """Second forward difference in coordinate `coord` with step h.

    Δ²F = F(a+2h*e_j) - 2*F(a+h*e_j) + F(a)
    where e_j is the unit vector in coordinate j.
    """
    a = list(amounts)

    def at_offset(offset: float) -> float:
        b = list(a)
        b[coord] += offset
        return k_pool_split_full(pools, b, D)

    return at_offset(2 * h) - 2 * at_offset(h) + at_offset(0.0)


def second_diff_random_direction(
    pools: Sequence[Pool],
    amounts: Sequence[float],
    D: float,
    direction: Sequence[float],
    h: float,
) -> float:
    """Second forward difference in a random direction with step h.

    Δ²F = F(a+2h*d) - 2*F(a+h*d) + F(a)
    where d is a unit direction vector.
    """
    a = list(amounts)
    d = list(direction)

    def at_offset(offset: float) -> float:
        b = [a[i] + offset * d[i] for i in range(len(a))]
        return k_pool_split_full(pools, b, D)

    return at_offset(2 * h) - 2 * at_offset(h) + at_offset(0.0)


def test_coordinate_wise_concavity_3pool() -> None:
    """3-pool: second differences in each coordinate are negative."""
    pools = [
        Pool(K=1_000_000, M=500_000, c=0.997),
        Pool(K=2_000_000, M=800_000, c=0.995),
        Pool(K=1_500_000, M=600_000, c=0.999),
    ]
    D = 100_000.0
    amounts = [30_000.0, 30_000.0]  # pool 2 gets 40_000

    for coord in range(2):
        for h in [1.0, 10.0, 100.0, 1000.0]:
            sd = second_diff_coordinate(pools, amounts, D, coord, h)
            assert sd < 0, (
                f"3-pool coord {coord} h={h}: second diff = {sd} >= 0"
            )


def test_coordinate_wise_concavity_5pool() -> None:
    """5-pool: second differences in each coordinate are negative."""
    pools = [
        Pool(K=1_000_000, M=500_000, c=0.997),
        Pool(K=2_000_000, M=800_000, c=0.995),
        Pool(K=1_500_000, M=600_000, c=0.999),
        Pool(K=3_000_000, M=1_000_000, c=0.998),
        Pool(K=800_000, M=400_000, c=0.996),
    ]
    D = 200_000.0
    amounts = [40_000.0, 40_000.0, 40_000.0, 40_000.0]  # pool 4 gets 40_000

    for coord in range(4):
        for h in [1.0, 10.0, 100.0, 1000.0]:
            sd = second_diff_coordinate(pools, amounts, D, coord, h)
            assert sd < 0, (
                f"5-pool coord {coord} h={h}: second diff = {sd} >= 0"
            )


def test_random_direction_concavity_3pool() -> None:
    """3-pool: second differences in random directions are negative."""
    pools = [
        Pool(K=1_000_000, M=500_000, c=0.997),
        Pool(K=2_000_000, M=800_000, c=0.995),
        Pool(K=1_500_000, M=600_000, c=0.999),
    ]
    D = 100_000.0
    amounts = [30_000.0, 30_000.0]

    random.seed(42)
    for _ in range(50):
        # Random direction (unit vector in 2D)
        angle = random.uniform(0, 2 * np.pi)
        direction = [np.cos(angle), np.sin(angle)]
        for h in [1.0, 10.0, 100.0]:
            sd = second_diff_random_direction(pools, amounts, D, direction, h)
            assert sd < 0, (
                f"3-pool random dir {direction} h={h}: second diff = {sd} >= 0"
            )


def test_random_direction_concavity_5pool() -> None:
    """5-pool: second differences in random directions are negative."""
    pools = [
        Pool(K=1_000_000, M=500_000, c=0.997),
        Pool(K=2_000_000, M=800_000, c=0.995),
        Pool(K=1_500_000, M=600_000, c=0.999),
        Pool(K=3_000_000, M=1_000_000, c=0.998),
        Pool(K=800_000, M=400_000, c=0.996),
    ]
    D = 200_000.0
    amounts = [40_000.0, 40_000.0, 40_000.0, 40_000.0]

    random.seed(123)
    for _ in range(50):
        # Random direction (unit vector in 4D)
        d = np.random.randn(4)
        d = d / np.linalg.norm(d)
        direction = list(d)
        for h in [1.0, 10.0, 100.0]:
            sd = second_diff_random_direction(pools, amounts, D, direction, h)
            assert sd < 0, (
                f"5-pool random dir h={h}: second diff = {sd} >= 0"
            )


def test_hessian_negative_definite_3pool() -> None:
    """3-pool: Hessian is negative definite (jointly concave).

    NOTE: The Hessian is NOT diagonal because the remainder pool (pool 2)
    couples coordinates 1 and 2 through the sum constraint a1 + a2 <= D.
    The off-diagonal entries come from pool 2's cross-terms.
    However, the Hessian is still negative definite (all eigenvalues < 0).
    """
    pools = [
        Pool(K=1_000_000, M=500_000, c=0.997),
        Pool(K=2_000_000, M=800_000, c=0.995),
        Pool(K=1_500_000, M=600_000, c=0.999),
    ]
    D = 100_000.0
    amounts = [30_000.0, 30_000.0]

    # For F(a1, a2) = f_0(c0*a1) + f_1(c1*a2) + f_2(c2*(D-a1-a2))
    # The Hessian is:
    # H = [[d²f_0/d a1² + d²f_2/d a1²,  d²f_2/d a1 d a2],
    #      [d²f_2/d a2 d a1,           d²f_1/d a2² + d²f_2/d a2²]]
    #
    # For f_i(x) = K_i*x/(M_i+x), f_i''(x) = -2*K_i*M_i/(M_i+x)^3
    # With the chain rule: d²/d a_j² f_j(c_j*a_j) = c_j² * f_j''(c_j*a_j)
    # And for pool 2: d²/d a1² f_2(c2*(D-a1-a2)) = c2² * f_2''(c2*(D-a1-a2))

    h = 0.01  # small step for numerical Hessian

    # Numerical Hessian
    def F(a1: float, a2: float) -> float:
        return k_pool_split_full(pools, [a1, a2], D)

    H = np.zeros((2, 2))
    f0 = F(amounts[0], amounts[1])
    # Diagonal
    H[0, 0] = (F(amounts[0] + h, amounts[1]) - 2 * f0 + F(amounts[0] - h, amounts[1])) / h**2
    H[1, 1] = (F(amounts[0], amounts[1] + h) - 2 * f0 + F(amounts[0], amounts[1] - h)) / h**2
    # Off-diagonal
    H[0, 1] = (
        F(amounts[0] + h, amounts[1] + h) - F(amounts[0] + h, amounts[1] - h)
        - F(amounts[0] - h, amounts[1] + h) + F(amounts[0] - h, amounts[1] - h)
    ) / (4 * h**2)
    H[1, 0] = H[0, 1]

    eigenvalues = np.linalg.eigvalsh(H)
    print(f"3-pool Hessian eigenvalues: {eigenvalues}")
    for ev in eigenvalues:
        assert ev < 0, f"3-pool Hessian eigenvalue {ev} >= 0 (not negative definite)"


def test_coordinate_wise_concavity_stress() -> None:
    """Stress test: random k-pool configs, all second differences negative.

    Ensures the amounts stay within the simplex (sum <= D - 2*h buffer)
    so that the remainder pool always has positive input.
    """
    random.seed(42)
    for k in [3, 4, 5, 6]:
        for trial in range(100):
            pools = [
                Pool(
                    K=random.uniform(100_000, 5_000_000),
                    M=random.uniform(50_000, 2_000_000),
                    c=random.uniform(0.99, 0.999),
                )
                for _ in range(k)
            ]
            D = random.uniform(10_000, 500_000)
            h = D * 0.001  # 0.1% of D

            # Generate amounts within simplex with buffer for 2*h step
            # Each coord can move by +2h, so need a_i + 2h <= D - sum(a_j, j!=i) - 2h
            # Simplest: use equal split with margin
            base = D / k
            amounts = [base * random.uniform(0.5, 1.0) for _ in range(k - 1)]
            # Ensure sum + 2*h < D (remainder stays positive after +2h step in any coord)
            max_sum = D - 3 * h  # leave room for +2h in one coord + remainder > h
            if sum(amounts) >= max_sum:
                scale = max_sum / sum(amounts) * 0.9
                amounts = [a * scale for a in amounts]

            # Also ensure each coord has room for +2h
            for coord in range(k - 1):
                # After +2h in coord, remainder = D - sum - 2h must be > 0
                if D - sum(amounts) - 2 * h <= 0:
                    continue  # skip this configuration
                sd = second_diff_coordinate(pools, amounts, D, coord, h)
                if sd != sd:  # NaN check
                    continue  # skip NaN (shouldn't happen with valid amounts)
                assert sd < 0, (
                    f"k={k} trial={trial} coord={coord}: second diff = {sd} >= 0"
                )


def test_ternary_search_finds_optimum_3pool() -> None:
    """3-pool: coordinate-wise ternary search finds near-optimal split."""
    pools = [
        Pool(K=1_000_000, M=500_000, c=0.997),
        Pool(K=2_000_000, M=800_000, c=0.995),
        Pool(K=1_500_000, M=600_000, c=0.999),
    ]
    D = 100_000.0

    # Brute force: enumerate a1, a2 with a1 + a2 <= D
    best_val = float("-inf")
    best_split = (0, 0)
    step = 1000
    for a1 in range(0, int(D) + 1, step):
        for a2 in range(0, int(D) - a1 + 1, step):
            val = k_pool_split_full(pools, [float(a1), float(a2)], D)
            if val > best_val:
                best_val = val
                best_split = (a1, a2)

    # Coordinate-wise ternary search
    # Optimize a1 (with a2 fixed at D/3), then a2 (with a1 fixed)
    def F_a1(a1: float, a2: float) -> float:
        return k_pool_split_full(pools, [a1, a2], D)

    # Ternary search on a1 with a2 = D/3
    lo, hi = 0.0, D * 0.9
    for _ in range(50):
        if hi - lo < 1:
            break
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        if F_a1(m1, D / 3) < F_a1(m2, D / 3):
            lo = m1
        else:
            hi = m2
    a1_opt = (lo + hi) / 2

    # Ternary search on a2 with a1 = a1_opt
    lo, hi = 0.0, D - a1_opt
    for _ in range(50):
        if hi - lo < 1:
            break
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        if F_a1(a1_opt, m1) < F_a1(a1_opt, m2):
            lo = m1
        else:
            hi = m2
    a2_opt = (lo + hi) / 2

    ts_val = F_a1(a1_opt, a2_opt)

    # Ternary search should get within 0.1% of brute force
    gap = best_val - ts_val
    rel_gap = gap / best_val if best_val > 0 else 0
    print(f"3-pool: brute={best_val:.2f} at {best_split}, "
          f"ternary={ts_val:.2f} at ({a1_opt:.0f}, {a2_opt:.0f}), "
          f"rel_gap={rel_gap:.6f}")
    assert rel_gap < 0.001, f"3-pool ternary search gap too large: {rel_gap}"


def test_separable_concavity_formula() -> None:
    """Verify: the k-pool second difference equals sum of individual pool second differences.

    For F = sum_i f_i, Δ²F = sum_i Δ²f_i.
    Each Δ²f_i < 0 (from Phase 3A), so Δ²F < 0.
    """
    pools = [
        Pool(K=1_000_000, M=500_000, c=0.997),
        Pool(K=2_000_000, M=800_000, c=0.995),
        Pool(K=1_500_000, M=600_000, c=0.999),
    ]
    D = 100_000.0
    amounts = [30_000.0, 30_000.0]
    h = 100.0

    # Full second difference in coordinate 0
    full_sd = second_diff_coordinate(pools, amounts, D, 0, h)

    # Individual contributions
    # Pool 0: f_0(c0*a1) changes by a1 -> a1+h -> a1+2h
    x0 = pools[0].c * amounts[0]
    sd0 = (cpmm_output_cont(pools[0].K, pools[0].M, x0 + 2 * pools[0].c * h)
           - 2 * cpmm_output_cont(pools[0].K, pools[0].M, x0 + pools[0].c * h)
           + cpmm_output_cont(pools[0].K, pools[0].M, x0))

    # Pool 1: f_1(c1*a2) unchanged (a2 fixed)
    sd1 = 0.0

    # Pool 2: f_2(c2*(D-a1-a2)) changes by D-a1 -> D-a1-h -> D-a1-2h
    x2 = pools[2].c * (D - amounts[0] - amounts[1])
    sd2 = (cpmm_output_cont(pools[2].K, pools[2].M, x2 - 2 * pools[2].c * h)
           - 2 * cpmm_output_cont(pools[2].K, pools[2].M, x2 - pools[2].c * h)
           + cpmm_output_cont(pools[2].K, pools[2].M, x2))

    sum_sd = sd0 + sd1 + sd2
    print(f"Full SD: {full_sd:.6f}, Sum of individual: {sum_sd:.6f}, "
          f"sd0={sd0:.6f}, sd2={sd2:.6f}")
    assert abs(full_sd - sum_sd) < 1e-6, (
        f"Separability violated: full={full_sd}, sum={sum_sd}"
    )
    assert full_sd < 0, f"Second difference not negative: {full_sd}"


def test_edge_case_equal_pools() -> None:
    """Edge case: all pools identical. Concavity should still hold."""
    pools = [Pool(K=1_000_000, M=500_000, c=0.997) for _ in range(4)]
    D = 100_000.0
    amounts = [25_000.0, 25_000.0, 25_000.0]

    for coord in range(3):
        for h in [1.0, 10.0, 100.0]:
            sd = second_diff_coordinate(pools, amounts, D, coord, h)
            assert sd < 0, (
                f"Equal pools coord {coord} h={h}: second diff = {sd} >= 0"
            )


def test_edge_case_extreme_fees() -> None:
    """Edge case: very high fees (c close to 0). Concavity should still hold."""
    pools = [
        Pool(K=1_000_000, M=500_000, c=0.01),  # 99% fee
        Pool(K=2_000_000, M=800_000, c=0.01),
        Pool(K=1_500_000, M=600_000, c=0.01),
    ]
    D = 100_000.0
    amounts = [33_000.0, 33_000.0]

    for coord in range(2):
        for h in [1.0, 10.0, 100.0]:
            sd = second_diff_coordinate(pools, amounts, D, coord, h)
            assert sd < 0, (
                f"Extreme fee coord {coord} h={h}: second diff = {sd} >= 0"
            )


def main() -> int:
    """Run all tests."""
    tests = [
        test_coordinate_wise_concavity_3pool,
        test_coordinate_wise_concavity_5pool,
        test_random_direction_concavity_3pool,
        test_random_direction_concavity_5pool,
        test_hessian_negative_definite_3pool,
        test_coordinate_wise_concavity_stress,
        test_ternary_search_finds_optimum_3pool,
        test_separable_concavity_formula,
        test_edge_case_equal_pools,
        test_edge_case_extreme_fees,
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
