"""Local strong concavity bound: W_local = ceil(sqrt(2L/m*)) + 1.

Breakthrough 26 showed the global strong concavity bound
W_theory = ceil(sqrt(2L/m_min)) + 1 is correct but impractical (130-632
vs empirical 1-3). The root cause is that m_min (global minimum of |f''|)
is dominated by nearly-linear boundary regions.

This script tests whether the LOCAL strong concavity parameter
m* = |f''(b*)| at the optimum gives a tighter bound that matches
the empirical W = ceil(1/L).

The hypothesis is that sqrt(2L/m*) ≈ 1/L, i.e., m* ≈ 2L³.
If true, this would bridge the abstract proof and the empirical bound.
"""
from __future__ import annotations

import math
import random
from dataclasses import dataclass


@dataclass(frozen=True)
class Pool:
    x: float
    y: float
    fee_bps: int


def q_float(x: float, y: float, a: float, fee_bps: int) -> float:
    if a <= 0:
        return 0.0
    c = 1.0 - fee_bps / 10000.0
    net = a * c
    if net <= 0:
        return 0.0
    return y * net / (x + net)


def cpmm_split_f(b: float, p0: Pool, p1: Pool, D: float) -> float:
    return q_float(p0.x, p0.y, b, p0.fee_bps) + q_float(p1.x, p1.y, D - b, p1.fee_bps)


def cpmm_split_f_second_deriv(b: float, p0: Pool, p1: Pool, D: float) -> float:
    c0 = 1.0 - p0.fee_bps / 10000.0
    c1 = 1.0 - p1.fee_bps / 10000.0
    term0 = -2.0 * p0.y * c0**2 * p0.x / (p0.x + c0 * b) ** 3
    term1 = -2.0 * p1.y * c1**2 * p1.x / (p1.x + c1 * (D - b)) ** 3
    return term0 + term1


def find_continuous_optimum(p0: Pool, p1: Pool, D: float) -> float:
    lo, hi = 0.0, D
    for _ in range(200):
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        if cpmm_split_f(m1, p0, p1, D) < cpmm_split_f(m2, p0, p1, D):
            lo = m1
        else:
            hi = m2
    return (lo + hi) / 2


def compute_lipschitz_constant(p0: Pool, p1: Pool) -> float:
    c0 = 1.0 - p0.fee_bps / 10000.0
    c1 = 1.0 - p1.fee_bps / 10000.0
    return max(p0.y * c0 / p0.x, p1.y * c1 / p1.x)


def find_integer_optimum(p0: Pool, p1: Pool, D: int) -> int:
    best_b = 0
    best_f = cpmm_split_f(0, p0, p1, float(D))
    for b in range(D + 1):
        f_val = cpmm_split_f(float(b), p0, p1, float(D))
        if f_val > best_f:
            best_f = f_val
            best_b = b
    return best_b


def main() -> None:
    print("Local Strong Concavity Window Bound")
    print("=" * 130)
    print()
    print("Hypothesis: W_local = ceil(sqrt(2L/m*)) + 1 matches W_emp = ceil(1/L)")
    print("where m* = |f''(b*)| is the strong concavity at the optimum")
    print()
    print(f"{'L':>10} {'m_min':>12} {'m*':>12} {'2L/m_min':>10} {'2L/m*':>10} "
          f"{'sqrt(2L/m*)':>12} {'1/L':>10} {'W_global':>8} {'W_local':>7} "
          f"{'W_emp':>5} {'|b-b*|':>8} {'m*/2L^3':>10}")
    print("-" * 130)

    rng = random.Random(20260627)
    w_local_matches_emp = 0
    w_local_satisfied = 0
    total = 0
    m_star_over_2L3_values = []

    for _ in range(50):
        x0 = rng.randint(10000, 500000)
        y0 = rng.randint(10000, 500000)
        fee0 = rng.choice([0, 10, 30, 100, 300])
        p0 = Pool(float(x0), float(y0), fee0)

        x1 = rng.randint(10000, 500000)
        y1 = rng.randint(10000, 500000)
        fee1 = rng.choice([0, 10, 30, 100, 300])
        p1 = Pool(float(x1), float(y1), fee1)

        D = rng.randint(50, 500)

        L = compute_lipschitz_constant(p0, p1)
        b_star = find_continuous_optimum(p0, p1, float(D))
        m_star = abs(cpmm_split_f_second_deriv(b_star, p0, p1, float(D)))

        # Global min |f''|
        m_min = float('inf')
        for i in range(1001):
            b = D * i / 1000
            m_min = min(m_min, abs(cpmm_split_f_second_deriv(b, p0, p1, float(D))))

        # Bounds
        W_global = math.ceil(math.sqrt(2 * L / m_min)) + 1 if m_min > 0 else -1
        W_local = math.ceil(math.sqrt(2 * L / m_star)) + 1 if m_star > 0 else -1
        W_emp = math.ceil(1 / L) if L > 0 else -1

        # Actual distance
        b_int_star = find_integer_optimum(p0, p1, D)
        actual_dist = abs(b_int_star - b_star)

        # Check if m* ≈ 2L^3
        ratio = m_star / (2 * L**3) if L > 0 else 0
        m_star_over_2L3_values.append(ratio)

        total += 1
        if W_local >= actual_dist:
            w_local_satisfied += 1
        if W_local == W_emp:
            w_local_matches_emp += 1

        print(f"{L:>10.6f} {m_min:>12.6f} {m_star:>12.6f} {2*L/m_min:>10.2f} "
              f"{2*L/m_star:>10.2f} {math.sqrt(2*L/m_star) if m_star > 0 else 0:>12.4f} "
              f"{1/L if L > 0 else 0:>10.4f} {W_global:>8} {W_local:>7} "
              f"{W_emp:>5} {actual_dist:>8.2f} {ratio:>10.4f}")

    print()
    print(f"Summary: {w_local_satisfied}/{total} W_local satisfied actual distance")
    print(f"         {w_local_matches_emp}/{total} W_local matches W_emp exactly")
    print()

    # Statistics on m* / (2L^3)
    ratios = m_star_over_2L3_values
    mean_ratio = sum(ratios) / len(ratios)
    min_ratio = min(ratios)
    max_ratio = max(ratios)
    median_ratio = sorted(ratios)[len(ratios)//2]
    print(f"m* / (2L^3) statistics:")
    print(f"  min:    {min_ratio:.6f}")
    print(f"  median: {median_ratio:.6f}")
    print(f"  mean:   {mean_ratio:.6f}")
    print(f"  max:    {max_ratio:.6f}")
    print()

    if w_local_satisfied == total:
        print("VERIFIED: W_local = ceil(sqrt(2L/m*)) + 1 is satisfied in all cases.")
    else:
        print(f"WARNING: {total - w_local_satisfied} cases failed W_local!")

    if abs(mean_ratio - 1.0) < 0.5:
        print(f"m* ≈ 2L^3 (mean ratio = {mean_ratio:.4f})")
        print("This confirms the hypothesis: sqrt(2L/m*) ≈ sqrt(2L/(2L^3)) = sqrt(1/L^2) = 1/L")
        print("So W_local = ceil(sqrt(2L/m*)) + 1 ≈ ceil(1/L) + 1 ≈ W_emp + 1")
        print("The local strong concavity bound bridges the abstract proof and the empirical bound!")
    else:
        print(f"m* / (2L^3) = {mean_ratio:.4f} (not close to 1)")
        print("The relationship m* ≈ 2L^3 does not hold. The bound structure is different.")


if __name__ == "__main__":
    main()
