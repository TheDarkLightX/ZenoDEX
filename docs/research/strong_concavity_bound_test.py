#!/usr/bin/env python3
"""Empirical verification of the strong concavity lower bound (P2).

Verifies the Lean theorems in `CpmmSplitConcavity.lean`:

1. `inv_cube_antitone_mul`: For positive x <= y and c >= 0, c/x^3 >= c/y^3.
2. `T0_decreasing_bound`: T0(a) = 2*c0^2*K0*M0/(M0+c0*a)^3 is decreasing.
3. `T1_increasing_bound`: T1(a) = 2*c1^2*K1*M1/(M1+c1*(D-a))^3 is increasing.
4. `strong_concavity_lower_bound`:
   m >= 2*c0^2*K0*M0/(M0+c0*D)^3 + 2*c1^2*K1*M1/(M1+c1*D)^3

Key insight: |F''(a)| = T0(a) + T1(a) where T0 is decreasing (inf at a=D)
and T1 is increasing (inf at a=0). So inf(T0+T1) >= inf T0 + inf T1.

This removes the external hypothesis on m: the window bound sqrt(2*eps/m)
is now fully determined by pool parameters.

Determinism: All tests use fixed seeds. No real time, RNG, network, or fs.
"""

import math
import random
from dataclasses import dataclass


@dataclass(frozen=True)
class Pool:
    reserve_in: float   # M
    reserve_out: float  # K
    fee_bps: int        # fee in basis points


def cpmm_output_cont(K: float, M: float, x: float) -> float:
    """cpmmOutputCont K M x = K * x / (M + x)."""
    if M + x <= 0.0:
        return 0.0
    return K * x / (M + x)


def split_function_cont(p0: Pool, p1: Pool, D: float, a: float) -> float:
    """splitFunctionCont: continuous fee split."""
    c0 = 1.0 - p0.fee_bps / 10000.0
    c1 = 1.0 - p1.fee_bps / 10000.0
    return cpmm_output_cont(p0.reserve_out, p0.reserve_in, c0 * a) + \
           cpmm_output_cont(p1.reserve_out, p1.reserve_in, c1 * (D - a))


def T0(p0: Pool, a: float) -> float:
    """T0(a) = 2*c0^2*K0*M0/(M0+c0*a)^3. Decreasing in a."""
    c0 = 1.0 - p0.fee_bps / 10000.0
    K0, M0 = p0.reserve_out, p0.reserve_in
    denom = (M0 + c0 * a) ** 3
    if denom <= 0:
        return 0.0
    return 2 * c0**2 * K0 * M0 / denom


def T1(p1: Pool, D: float, a: float) -> float:
    """T1(a) = 2*c1^2*K1*M1/(M1+c1*(D-a))^3. Increasing in a."""
    c1 = 1.0 - p1.fee_bps / 10000.0
    K1, M1 = p1.reserve_out, p1.reserve_in
    denom = (M1 + c1 * (D - a)) ** 3
    if denom <= 0:
        return 0.0
    return 2 * c1**2 * K1 * M1 / denom


def second_derivative_numerical(p0: Pool, p1: Pool, D: float, a: float, h: float = 0.01) -> float:
    """Numerical second derivative of split function at a.
    Uses h=0.01 to avoid catastrophic cancellation with float64."""
    f_pp = split_function_cont(p0, p1, D, a + h)
    f_0 = split_function_cont(p0, p1, D, a)
    f_mm = split_function_cont(p0, p1, D, a - h)
    return (f_pp - 2 * f_0 + f_mm) / (h * h)


def lower_bound(p0: Pool, p1: Pool, D: float) -> float:
    """Lower bound on m: T0(D) + T1(0)."""
    return T0(p0, D) + T1(p1, D, 0.0)


# ---------------------------------------------------------------------------
# Test 1: inv_cube_antitone_mul (c/x^3 >= c/y^3 for x <= y, c >= 0)
# ---------------------------------------------------------------------------

def test_inv_cube_antitone():
    """Verify c/x^3 >= c/y^3 for x <= y, c >= 0."""
    rng = random.Random(42)
    violations = 0
    for _ in range(10000):
        x = float(rng.randint(1, 10000))
        y = x + float(rng.randint(0, 10000))  # y >= x
        c = float(rng.randint(0, 10000))
        lhs = c / x**3
        rhs = c / y**3
        if lhs < rhs - 1e-9:
            violations += 1
            print(f"  VIOLATION: c/x^3={lhs} < c/y^3={rhs} x={x} y={y} c={c}")
    assert violations == 0, f"{violations} antitone violations"
    print(f"  PASS: 10000 random trials, c/x^3 >= c/y^3 always")


# ---------------------------------------------------------------------------
# Test 2: T0 is decreasing (T0(a) >= T0(D) for a <= D)
# ---------------------------------------------------------------------------

def test_T0_decreasing():
    """Verify T0(a) >= T0(D) for a in [0, D]."""
    rng = random.Random(42)
    violations = 0
    for _ in range(10000):
        K0 = float(rng.randint(100, 10000))
        M0 = float(rng.randint(100, 10000))
        fee0 = rng.randint(0, 500)
        D = float(rng.randint(10, 1000))
        a = float(rng.randint(0, int(D)))
        p0 = Pool(M0, K0, fee0)
        t0_a = T0(p0, a)
        t0_D = T0(p0, D)
        if t0_a < t0_D - 1e-9:
            violations += 1
            print(f"  VIOLATION: T0(a)={t0_a} < T0(D)={t0_D} "
                  f"K0={K0} M0={M0} a={a} D={D}")
    assert violations == 0, f"{violations} T0 decreasing violations"
    print(f"  PASS: 10000 random trials, T0(a) >= T0(D) always")


# ---------------------------------------------------------------------------
# Test 3: T1 is increasing (T1(a) >= T1(0) for a >= 0)
# ---------------------------------------------------------------------------

def test_T1_increasing():
    """Verify T1(a) >= T1(0) for a in [0, D]."""
    rng = random.Random(42)
    violations = 0
    for _ in range(10000):
        K1 = float(rng.randint(100, 10000))
        M1 = float(rng.randint(100, 10000))
        fee1 = rng.randint(0, 500)
        D = float(rng.randint(10, 1000))
        a = float(rng.randint(0, int(D)))
        p1 = Pool(M1, K1, fee1)
        t1_a = T1(p1, D, a)
        t1_0 = T1(p1, D, 0.0)
        if t1_a < t1_0 - 1e-9:
            violations += 1
            print(f"  VIOLATION: T1(a)={t1_a} < T1(0)={t1_0} "
                  f"K1={K1} M1={M1} a={a} D={D}")
    assert violations == 0, f"{violations} T1 increasing violations"
    print(f"  PASS: 10000 random trials, T1(a) >= T1(0) always")


# ---------------------------------------------------------------------------
# Test 4: Strong concavity lower bound holds
# T0(a) + T1(a) >= T0(D) + T1(0) for all a in [0, D]
# ---------------------------------------------------------------------------

def test_strong_concavity_lower_bound():
    """Verify T0(a) + T1(a) >= T0(D) + T1(0) for all a in [0, D]."""
    rng = random.Random(42)
    violations = 0
    max_ratio = 0.0  # (T0(a)+T1(a)) / (T0(D)+T1(0))
    for _ in range(10000):
        K0 = float(rng.randint(100, 10000))
        M0 = float(rng.randint(100, 10000))
        K1 = float(rng.randint(100, 10000))
        M1 = float(rng.randint(100, 10000))
        fee0 = rng.randint(0, 500)
        fee1 = rng.randint(0, 500)
        D = float(rng.randint(10, 1000))
        a = float(rng.randint(0, int(D)))
        p0 = Pool(M0, K0, fee0)
        p1 = Pool(M1, K1, fee1)
        actual = T0(p0, a) + T1(p1, D, a)
        bound = lower_bound(p0, p1, D)
        if bound > 0:
            max_ratio = max(max_ratio, actual / bound)
        if actual < bound - 1e-9:
            violations += 1
            print(f"  VIOLATION: T0+T1={actual} < bound={bound} "
                  f"K0={K0} M0={M0} K1={K1} M1={M1} a={a} D={D}")
    assert violations == 0, f"{violations} lower bound violations"
    print(f"  PASS: 10000 random trials, 0 violations, "
          f"max actual/bound ratio = {max_ratio:.6f}")


# ---------------------------------------------------------------------------
# Test 5: Numerical second derivative matches T0 + T1
# F''(a) = -(T0(a) + T1(a))
# ---------------------------------------------------------------------------

def test_second_derivative_matches():
    """Verify numerical F''(a) matches -(T0(a) + T1(a))."""
    rng = random.Random(42)
    violations = 0
    max_rel_error = 0.0
    for _ in range(1000):
        K0 = float(rng.randint(100, 10000))
        M0 = float(rng.randint(100, 10000))
        K1 = float(rng.randint(100, 10000))
        M1 = float(rng.randint(100, 10000))
        fee0 = rng.randint(0, 500)
        fee1 = rng.randint(0, 500)
        D = float(rng.randint(10, 1000))
        a = float(rng.randint(1, int(D) - 1))  # interior point
        p0 = Pool(M0, K0, fee0)
        p1 = Pool(M1, K1, fee1)
        numerical = second_derivative_numerical(p0, p1, D, a)
        analytical = -(T0(p0, a) + T1(p1, D, a))
        if abs(analytical) > 1e-10:
            rel_error = abs(numerical - analytical) / abs(analytical)
            max_rel_error = max(max_rel_error, rel_error)
        if abs(numerical - analytical) > 0.05 * max(abs(analytical), 1.0):
            violations += 1
            print(f"  VIOLATION: numerical={numerical} analytical={analytical} "
                  f"K0={K0} M0={M0} K1={K1} M1={M1} a={a} D={D}")
    assert violations == 0, f"{violations} second derivative mismatches"
    print(f"  PASS: 1000 random trials, F''(a) = -(T0+T1), "
          f"max rel error = {max_rel_error:.8f}")


# ---------------------------------------------------------------------------
# Test 6: Bound is positive (non-vacuous) and degenerates with D
# ---------------------------------------------------------------------------

def test_bound_positive_and_degenerates():
    """Verify bound is positive and decreases as D increases."""
    rng = random.Random(42)
    p0 = Pool(1000, 1000, 99)
    p1 = Pool(1000, 2000, 99)
    D_small = 10.0
    D_large = 10000.0
    bound_small = lower_bound(p0, p1, D_small)
    bound_large = lower_bound(p0, p1, D_large)
    assert bound_small > 0, f"bound(D=10)={bound_small} <= 0"
    assert bound_large > 0, f"bound(D=10000)={bound_large} <= 0"
    assert bound_large < bound_small, \
        f"bound(D=10000)={bound_large} >= bound(D=10)={bound_small}"
    print(f"  PASS: bound(D=10)={bound_small:.6f}, "
          f"bound(D=10000)={bound_large:.10f}")
    print(f"  Bound degenerates as D increases (correct behavior)")


# ---------------------------------------------------------------------------
# Test 7: Witness non-vacuity
# ---------------------------------------------------------------------------

def test_witness_non_vacuity():
    """Verify the concrete witness case from Lean."""
    p0 = Pool(1000, 1000, 99)   # c0 = 0.99
    p1 = Pool(1000, 2000, 99)   # c1 = 0.99
    D = 100.0
    a = 50.0
    bound = lower_bound(p0, p1, D)
    actual = T0(p0, a) + T1(p1, D, a)
    assert bound > 0, f"bound={bound} <= 0"
    assert actual >= bound - 1e-9, f"actual={actual} < bound={bound}"
    print(f"  PASS: bound={bound:.6f}, actual(T0+T1 at a=50)={actual:.6f}")
    print(f"  Bound is {bound/actual:.1%} of actual at midpoint")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("=== P2: Strong Concavity Lower Bound Empirical Verification ===\n")

    print("Test 1: inv_cube_antitone_mul (c/x^3 >= c/y^3 for x <= y)")
    test_inv_cube_antitone()
    print()

    print("Test 2: T0 decreasing (T0(a) >= T0(D) for a <= D)")
    test_T0_decreasing()
    print()

    print("Test 3: T1 increasing (T1(a) >= T1(0) for a >= 0)")
    test_T1_increasing()
    print()

    print("Test 4: Strong concavity lower bound holds")
    test_strong_concavity_lower_bound()
    print()

    print("Test 5: Numerical F''(a) matches -(T0+T1)")
    test_second_derivative_matches()
    print()

    print("Test 6: Bound positive and degenerates with D")
    test_bound_positive_and_degenerates()
    print()

    print("Test 7: Witness non-vacuity")
    test_witness_non_vacuity()
    print()

    print("=== All tests passed ===")
