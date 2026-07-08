"""Compute the CPMM-specific strong concavity parameter m and verify
the theoretical window bound W = ceil(sqrt(2L/m)) + 1 matches the
empirical W = ceil(1/L).

The abstract tightness proof (StrongConcavityWindowBound.lean) shows the
bound |b - b*| <= sqrt(2L/m) + 1 is tight for f(b) = -(m/2)b^2. This script
computes m for the actual CPMM split function and checks the bound.

CPMM split function:
  f(b) = q(x0, y0, b, fee) + q(x1, y1, D-b, fee)

where q(x, y, a, fee) = y * (a * (1 - fee/10000)) / (x + a * (1 - fee/10000))

Second derivative:
  f''(b) = -2 * y0 * c^2 * x0 / (x0 + c*b)^3 - 2 * y1 * c^2 * x1 / (x1 + c*(D-b))^3

where c = 1 - fee/10000.

Strong concavity parameter: m = -max_b f''(b) = min_b |f''(b)|
(the minimum of |f''| over the feasible range, since f'' is always negative).

Lipschitz constant: L = max(y0*c/x0, y1*c/x1) (the maximum slope).

Window bound: W_theoretical = ceil(sqrt(2L/m)) + 1
Empirical bound: W_empirical = ceil(1/L)
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
    """Second derivative of f(b) = q(x0,y0,b,fee0) + q(x1,y1,D-b,fee1).

    f''(b) = -2*y0*c0^2*x0/(x0+c0*b)^3 - 2*y1*c1^2*x1/(x1+c1*(D-b))^3

    Both terms are strictly negative, so f'' < 0 everywhere (strong concavity).
    """
    c0 = 1.0 - p0.fee_bps / 10000.0
    c1 = 1.0 - p1.fee_bps / 10000.0
    term0 = -2.0 * p0.y * c0**2 * p0.x / (p0.x + c0 * b) ** 3
    term1 = -2.0 * p1.y * c1**2 * p1.x / (p1.x + c1 * (D - b)) ** 3
    return term0 + term1


def cpmm_split_f_deriv(b: float, p0: Pool, p1: Pool, D: float) -> float:
    """First derivative of f(b).

    f'(b) = y0*c0*x0/(x0+c0*b)^2 - y1*c1*x1/(x1+c1*(D-b))^2
    """
    c0 = 1.0 - p0.fee_bps / 10000.0
    c1 = 1.0 - p1.fee_bps / 10000.0
    term0 = p0.y * c0 * p0.x / (p0.x + c0 * b) ** 2
    term1 = -p1.y * c1 * p1.x / (p1.x + c1 * (D - b)) ** 2
    return term0 + term1


def find_continuous_optimum(p0: Pool, p1: Pool, D: float) -> float:
    """Find b* that maximizes f(b) via ternary search."""
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
    """L = max(y0*c0/x0, y1*c1/x1)."""
    c0 = 1.0 - p0.fee_bps / 10000.0
    c1 = 1.0 - p1.fee_bps / 10000.0
    return max(p0.y * c0 / p0.x, p1.y * c1 / p1.x)


def compute_strong_concavity_param(p0: Pool, p1: Pool, D: float, b_star: float) -> float:
    """m = min_{b in [0,D]} |f''(b)|.

    Since f'' < 0 everywhere, |f''(b)| = -f''(b).
    The minimum of |f''| gives the weakest strong concavity bound.
    """
    # Sample f'' at many points and find the minimum |f''|
    min_abs_fpp = float('inf')
    for i in range(1001):
        b = D * i / 1000
        fpp = cpmm_split_f_second_deriv(b, p0, p1, D)
        abs_fpp = abs(fpp)
        if abs_fpp < min_abs_fpp:
            min_abs_fpp = abs_fpp
    return min_abs_fpp


def compute_strong_concavity_at_optimum(p0: Pool, p1: Pool, D: float, b_star: float) -> float:
    """m* = |f''(b*)|, the strong concavity at the optimum."""
    return abs(cpmm_split_f_second_deriv(b_star, p0, p1, D))


def find_integer_optimum(p0: Pool, p1: Pool, D: int) -> int:
    """Find the integer b that maximizes f(b)."""
    best_b = 0
    best_f = cpmm_split_f(0, p0, p1, float(D))
    for b in range(D + 1):
        f_val = cpmm_split_f(float(b), p0, p1, float(D))
        if f_val > best_f:
            best_f = f_val
            best_b = b
    return best_b


def main() -> None:
    print("CPMM Strong Concavity Parameter and Window Bound Verification")
    print("=" * 130)
    print()
    print("Theoretical bound: W_theory = ceil(sqrt(2L/m)) + 1")
    print("Empirical bound:   W_emp = ceil(1/L)")
    print("Actual distance:   |b_int* - b*|")
    print()
    print(f"{'Pool0 (x,y,fee)':>30} {'Pool1 (x,y,fee)':>30} {'D':>6} {'L':>10} "
          f"{'m_min':>12} {'m*':>12} {'W_theory':>8} {'W_emp':>6} {'|b-b*|':>8} {'Match':>6}")
    print("-" * 130)

    rng = random.Random(20260627)
    match_count = 0
    total_count = 0
    theory_tighter_count = 0

    for _ in range(50):
        # Generate random pools
        x0 = rng.randint(10000, 500000)
        y0 = rng.randint(10000, 500000)
        fee0 = rng.choice([0, 10, 30, 100, 300])
        p0 = Pool(float(x0), float(y0), fee0)

        x1 = rng.randint(10000, 500000)
        y1 = rng.randint(10000, 500000)
        fee1 = rng.choice([0, 10, 30, 100, 300])
        p1 = Pool(float(x1), float(y1), fee1)

        D = rng.randint(50, 500)

        # Compute parameters
        L = compute_lipschitz_constant(p0, p1)
        b_star = find_continuous_optimum(p0, p1, float(D))
        m_min = compute_strong_concavity_param(p0, p1, float(D), b_star)
        m_star = compute_strong_concavity_at_optimum(p0, p1, float(D), b_star)

        # Theoretical bound
        if m_min > 0 and L > 0:
            W_theory = math.ceil(math.sqrt(2 * L / m_min)) + 1
        else:
            W_theory = -1

        # Empirical bound
        W_emp = math.ceil(1 / L) if L > 0 else -1

        # Actual distance
        b_int_star = find_integer_optimum(p0, p1, D)
        actual_dist = abs(b_int_star - b_star)

        # Check if bounds are satisfied
        theory_ok = W_theory >= actual_dist if W_theory > 0 else False
        emp_ok = W_emp >= actual_dist if W_emp > 0 else False
        match = "OK" if (theory_ok and emp_ok) else "FAIL"

        # Check if theory is tighter
        theory_tighter = W_theory < W_emp if (W_theory > 0 and W_emp > 0) else False

        total_count += 1
        if theory_ok and emp_ok:
            match_count += 1
        if theory_tighter:
            theory_tighter_count += 1

        p0_str = f"({x0},{y0},{fee0})"
        p1_str = f"({x1},{y1},{fee1})"
        print(f"{p0_str:>30} {p1_str:>30} {D:>6} {L:>10.6f} {m_min:>12.6f} "
              f"{m_star:>12.6f} {W_theory:>8} {W_emp:>6} {actual_dist:>8.2f} {match:>6}")

    print()
    print(f"Summary: {match_count}/{total_count} cases both bounds satisfied")
    print(f"         {theory_tighter_count}/{total_count} cases theoretical bound is tighter")
    print()
    if match_count == total_count:
        print("VERIFIED: Both theoretical and empirical bounds are satisfied in all cases.")
    else:
        print(f"WARNING: {total_count - match_count} cases failed!")
    print()
    if theory_tighter_count > total_count * 0.3:
        print(f"Theoretical bound is tighter in {theory_tighter_count}/{total_count} cases.")
        print("The strong concavity bound provides a significant improvement over the Lipschitz-only bound.")
    else:
        print(f"Theoretical bound is tighter in {theory_tighter_count}/{total_count} cases.")
        print("The empirical bound ceil(1/L) is typically tighter than the theoretical ceil(sqrt(2L/m)) + 1.")
        print("This is because the empirical bound uses CPMM-specific structure more directly.")


if __name__ == "__main__":
    main()
