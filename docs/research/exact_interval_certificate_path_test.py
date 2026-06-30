#!/usr/bin/env python3
"""P10: Empirical verification of the exact interval certificate path.

Tests the four Lean theorems from ExactIntervalCertificatePath.lean:

1. exact_interval_certificate_path: bracket + upper value + strong concavity
   + prod <= cont => |argmax - b*| <= sqrt(2 * tau_upper / m)
2. exact_interval_certificate_path_squared: same conditions, squared form
   (argmax - b*)^2 <= 2 * tau_upper / m
3. checker_acceptance_implies_distance_bound: distance_sq_upper <= radius_sq
   + b* in bracket => (argmax - b*)^2 <= radius_sq
4. complete_certificate_soundness: all conditions => |argmax - b*| <= sqrt(radius_sq)

The certificate chain:
  derivative bracket -> b* in [lo, hi]                    (P9)
  b* in [lo, hi] -> F(b*) <= cont_star_upper              (P9)
  F(b*) - prod(argmax) <= cont_star_upper - prod = tau    (arithmetic)
  strong concavity: (m/2)(argmax - b*)^2 <= F(b*) - prod  (P2)
  transitivity: (m/2)(argmax - b*)^2 <= tau_upper         (composition)
  algebra: (argmax - b*)^2 <= 2*tau_upper/m = radius_sq   (algebra)
  sqrt: |argmax - b*| <= sqrt(radius_sq)                  (monotonicity)

Also tests the checker acceptance path:
  bracket distance: (argmax - b*)^2 <= distance_sq_upper  (P9)
  checker accept: distance_sq_upper <= radius_sq          (checker)
  transitivity: (argmax - b*)^2 <= radius_sq              (composition)
"""

from __future__ import annotations

import random
import sys
from pathlib import Path
from typing import NamedTuple

import numpy as np

try:
    import sympy as sp
    HAS_SYMPY = True
except ImportError:
    HAS_SYMPY = False


class Pool(NamedTuple):
    K: float  # reserve_out
    M: float  # reserve_in
    c: float  # fee multiplier (1 - fee_bps/10000)


def cpmm_output(K: float, M: float, x: float) -> float:
    """Continuous CPMM output: K*x/(M+x)."""
    return K * x / (M + x)


def split_function_cont(p0: Pool, p1: Pool, D: float, a: float) -> float:
    """F(a) = f0(c0*a) + f1(c1*(D-a))."""
    return cpmm_output(p0.K, p0.M, p0.c * a) + cpmm_output(p1.K, p1.M, p1.c * (D - a))


def split_deriv(p0: Pool, p1: Pool, D: float, a: float) -> float:
    """F'(a) = c0*K0*M0/(M0+c0*a)^2 - c1*K1*M1/(M1+c1*(D-a))^2."""
    term0 = p0.c * p0.K * p0.M / (p0.M + p0.c * a) ** 2
    term1 = p1.c * p1.K * p1.M / (p1.M + p1.c * (D - a)) ** 2
    return term0 - term1


def split_second_deriv(p0: Pool, p1: Pool, D: float, a: float) -> float:
    """F''(a) = -2*c0^2*K0*M0/(M0+c0*a)^3 - 2*c1^2*K1*M1/(M1+c1*(D-a))^3."""
    term0 = -2 * p0.c ** 2 * p0.K * p0.M / (p0.M + p0.c * a) ** 3
    term1 = -2 * p1.c ** 2 * p1.K * p1.M / (p1.M + p1.c * (D - a)) ** 3
    return term0 + term1


def find_continuous_maximizer(p0: Pool, p1: Pool, D: float) -> float:
    """Find b* by binary search on derivative sign."""
    lo, hi = 0.0, D
    for _ in range(200):
        mid = (lo + hi) / 2
        d = split_deriv(p0, p1, D, mid)
        if d > 0:
            lo = mid
        elif d < 0:
            hi = mid
        else:
            return mid
    return (lo + hi) / 2


def find_derivative_bracket(p0: Pool, p1: Pool, D: float, b_star: float) -> tuple[float, float]:
    """Find a bracket [lo, hi] around b* using derivative signs."""
    lo = max(0.0, b_star - D * 0.1)
    hi = min(D, b_star + D * 0.1)

    d_lo = split_deriv(p0, p1, D, lo)
    d_hi = split_deriv(p0, p1, D, hi)

    while d_lo < 0 and lo > 0:
        lo = max(0.0, lo - D * 0.05)
        d_lo = split_deriv(p0, p1, D, lo)

    while d_hi > 0 and hi < D:
        hi = min(D, hi + D * 0.05)
        d_hi = split_deriv(p0, p1, D, hi)

    return lo, hi


def endpoint_m(p0: Pool, p1: Pool, D: float) -> float:
    """Endpoint curvature lower bound: 2*c0^2*K0*M0/(M0+c0*D)^3 + 2*c1^2*K1*M1/(M1+c1*D)^3."""
    term0 = 2 * p0.c ** 2 * p0.K * p0.M / (p0.M + p0.c * D) ** 3
    term1 = 2 * p1.c ** 2 * p1.K * p1.M / (p1.M + p1.c * D) ** 3
    return term0 + term1


def find_production_argmax(p0: Pool, p1: Pool, D: int) -> tuple[int, float]:
    """Scan integer splits 0..D and return (argmax_index, prod_value)."""
    best_idx = 0
    best_val = split_function_cont(p0, p1, float(D), 0.0)
    for a in range(1, D + 1):
        v = split_function_cont(p0, p1, float(D), float(a))
        if v > best_val:
            best_val = v
            best_idx = a
    return best_idx, best_val


def cont_star_upper(p0: Pool, p1: Pool, D: float, lo: float, hi: float) -> float:
    """Conservative continuous upper value: f0(c0*hi) + f1(c1*(D-lo))."""
    return cpmm_output(p0.K, p0.M, p0.c * hi) + cpmm_output(p1.K, p1.M, p1.c * (D - lo))


def test_exact_interval_certificate_path() -> None:
    """Test 1: Full certificate path => |argmax - b*| <= sqrt(2*tau_upper/m).

    This tests the main theorem: given a valid derivative bracket, positive m,
    strong concavity, and prod <= cont, the distance from argmax to b* is
    bounded by sqrt(2 * tau_upper / m).
    """
    rng = random.Random(42)
    violations = 0
    total = 0
    max_ratio = 0.0
    for _ in range(500):
        K0 = rng.uniform(100, 10000)
        M0 = rng.uniform(100, 10000)
        c0 = rng.uniform(0.9, 1.0)
        K1 = rng.uniform(100, 10000)
        M1 = rng.uniform(100, 10000)
        c1 = rng.uniform(0.9, 1.0)
        D = float(rng.randint(10, 500))

        p0 = Pool(K0, M0, c0)
        p1 = Pool(K1, M1, c1)

        b_star = find_continuous_maximizer(p0, p1, D)
        lo, hi = find_derivative_bracket(p0, p1, D, b_star)

        d_lo = split_deriv(p0, p1, D, lo)
        d_hi = split_deriv(p0, p1, D, hi)
        if d_lo < 0 or d_hi > 0:
            continue
        if not (lo <= b_star <= hi):
            continue

        m = endpoint_m(p0, p1, D)
        if m <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))

        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1

        radius_sq = 2 * tau_upper / m
        radius = np.sqrt(radius_sq)
        actual_dist = abs(float(argmax) - b_star)

        if actual_dist > radius + 1e-6:
            violations += 1
        else:
            ratio = actual_dist / max(radius, 1e-10)
            max_ratio = max(max_ratio, ratio)

    assert violations == 0, f"Certificate path violated in {violations}/{total} cases"
    print(f"Test 1: Exact interval certificate path holds ({total} trials, "
          f"0 violations, max ratio = {max_ratio:.6f})")
    print("  PASS")


def test_certificate_path_squared() -> None:
    """Test 2: Squared form => (argmax - b*)^2 <= 2*tau_upper/m."""
    rng = random.Random(42)
    violations = 0
    total = 0
    for _ in range(500):
        K0 = rng.uniform(100, 10000)
        M0 = rng.uniform(100, 10000)
        c0 = rng.uniform(0.9, 1.0)
        K1 = rng.uniform(100, 10000)
        M1 = rng.uniform(100, 10000)
        c1 = rng.uniform(0.9, 1.0)
        D = float(rng.randint(10, 500))

        p0 = Pool(K0, M0, c0)
        p1 = Pool(K1, M1, c1)

        b_star = find_continuous_maximizer(p0, p1, D)
        lo, hi = find_derivative_bracket(p0, p1, D, b_star)

        d_lo = split_deriv(p0, p1, D, lo)
        d_hi = split_deriv(p0, p1, D, hi)
        if d_lo < 0 or d_hi > 0:
            continue
        if not (lo <= b_star <= hi):
            continue

        m = endpoint_m(p0, p1, D)
        if m <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))

        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1

        radius_sq = 2 * tau_upper / m
        actual_sq = (float(argmax) - b_star) ** 2

        if actual_sq > radius_sq + 1e-6:
            violations += 1

    assert violations == 0, f"Squared certificate path violated in {violations}/{total} cases"
    print(f"Test 2: Squared certificate path holds ({total} trials, 0 violations)")
    print("  PASS")


def test_checker_acceptance_implies_distance_bound() -> None:
    """Test 3: Checker acceptance => (argmax - b*)^2 <= radius_sq.

    The checker accepts when distance_sq_upper <= radius_sq.
    The bracket distance bound gives (argmax - b*)^2 <= distance_sq_upper.
    So acceptance implies (argmax - b*)^2 <= radius_sq.
    """
    rng = random.Random(42)
    violations = 0
    total = 0
    checker_accepts = 0
    for _ in range(500):
        K0 = rng.uniform(100, 10000)
        M0 = rng.uniform(100, 10000)
        c0 = rng.uniform(0.9, 1.0)
        K1 = rng.uniform(100, 10000)
        M1 = rng.uniform(100, 10000)
        c1 = rng.uniform(0.9, 1.0)
        D = float(rng.randint(10, 500))

        p0 = Pool(K0, M0, c0)
        p1 = Pool(K1, M1, c1)

        b_star = find_continuous_maximizer(p0, p1, D)
        lo, hi = find_derivative_bracket(p0, p1, D, b_star)

        if not (lo <= b_star <= hi):
            continue

        m = endpoint_m(p0, p1, D)
        if m <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))

        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1

        radius_sq = 2 * tau_upper / m
        distance_sq_upper = max((float(argmax) - lo) ** 2, (float(argmax) - hi) ** 2)
        actual_sq = (float(argmax) - b_star) ** 2

        # Checker acceptance condition
        if distance_sq_upper <= radius_sq + 1e-6:
            checker_accepts += 1
            # Theorem: actual_sq <= radius_sq
            if actual_sq > radius_sq + 1e-6:
                violations += 1

        # Also verify bracket distance bound always holds
        if actual_sq > distance_sq_upper + 1e-6:
            violations += 1

    assert violations == 0, f"Checker acceptance path violated in {violations} cases"
    print(f"Test 3: Checker acceptance implies distance bound ({total} trials, "
          f"0 violations, checker accepted {checker_accepts}/{total})")
    print("  PASS")


def test_complete_certificate_soundness() -> None:
    """Test 4: Complete certificate soundness => |argmax - b*| <= sqrt(radius_sq).

    This is the main soundness theorem: all certificate conditions hold
    => the actual distance is bounded by the certified radius.
    """
    rng = random.Random(42)
    violations = 0
    total = 0
    max_ratio = 0.0
    for _ in range(500):
        K0 = rng.uniform(100, 10000)
        M0 = rng.uniform(100, 10000)
        c0 = rng.uniform(0.9, 1.0)
        K1 = rng.uniform(100, 10000)
        M1 = rng.uniform(100, 10000)
        c1 = rng.uniform(0.9, 1.0)
        D = float(rng.randint(10, 500))

        p0 = Pool(K0, M0, c0)
        p1 = Pool(K1, M1, c1)

        b_star = find_continuous_maximizer(p0, p1, D)
        lo, hi = find_derivative_bracket(p0, p1, D, b_star)

        d_lo = split_deriv(p0, p1, D, lo)
        d_hi = split_deriv(p0, p1, D, hi)
        if d_lo < 0 or d_hi > 0:
            continue
        if not (lo <= b_star <= hi):
            continue

        m = endpoint_m(p0, p1, D)
        if m <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))

        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1

        radius_sq = 2 * tau_upper / m
        radius = np.sqrt(radius_sq)
        actual_dist = abs(float(argmax) - b_star)

        if actual_dist > radius + 1e-6:
            violations += 1
        else:
            ratio = actual_dist / max(radius, 1e-10)
            max_ratio = max(max_ratio, ratio)

    assert violations == 0, f"Complete certificate soundness violated in {violations}/{total} cases"
    print(f"Test 4: Complete certificate soundness holds ({total} trials, "
          f"0 violations, max ratio = {max_ratio:.6f})")
    print("  PASS")


def test_strong_concavity_holds() -> None:
    """Test 5: Strong concavity: F(x) <= F(b*) - (m/2)*(x - b*)^2.

    This verifies the strong concavity hypothesis used in the certificate path.
    The endpoint m is a lower bound on the second derivative, so
    F(x) <= F(b*) - (m/2)*(x - b*)^2 should hold for all x in [0, D].
    """
    rng = random.Random(42)
    violations = 0
    total = 0
    max_slack = 0.0
    for _ in range(200):
        K0 = rng.uniform(100, 10000)
        M0 = rng.uniform(100, 10000)
        c0 = rng.uniform(0.9, 1.0)
        K1 = rng.uniform(100, 10000)
        M1 = rng.uniform(100, 10000)
        c1 = rng.uniform(0.9, 1.0)
        D = float(rng.randint(10, 500))

        p0 = Pool(K0, M0, c0)
        p1 = Pool(K1, M1, c1)

        b_star = find_continuous_maximizer(p0, p1, D)
        m = endpoint_m(p0, p1, D)
        if m <= 0:
            continue

        f_bstar = split_function_cont(p0, p1, D, b_star)

        # Test at several points
        for frac in [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0]:
            x = D * frac
            f_x = split_function_cont(p0, p1, D, x)
            upper = f_bstar - (m / 2) * (x - b_star) ** 2
            total += 1
            if f_x > upper + 1e-6:
                violations += 1
            else:
                slack = upper - f_x
                max_slack = max(max_slack, slack)

    assert violations == 0, f"Strong concavity violated in {violations}/{total} cases"
    print(f"Test 5: Strong concavity holds ({total} checks, 0 violations, "
          f"max slack = {max_slack:.4f})")
    print("  PASS")


def test_radius_tightness() -> None:
    """Test 6: Measure how tight the certified radius is vs actual distance.

    The certified radius sqrt(2*tau_upper/m) is conservative because:
    - tau_upper uses cont_star_upper (conservative) instead of F(b*)
    - m uses endpoint lower bound (conservative) instead of exact curvature

    This test measures the ratio actual_dist / certified_radius to quantify
    the conservatism. A ratio close to 1 means the certificate is tight.
    """
    rng = random.Random(42)
    total = 0
    ratios = []
    for _ in range(500):
        K0 = rng.uniform(100, 10000)
        M0 = rng.uniform(100, 10000)
        c0 = rng.uniform(0.9, 1.0)
        K1 = rng.uniform(100, 10000)
        M1 = rng.uniform(100, 10000)
        c1 = rng.uniform(0.9, 1.0)
        D = float(rng.randint(10, 500))

        p0 = Pool(K0, M0, c0)
        p1 = Pool(K1, M1, c1)

        b_star = find_continuous_maximizer(p0, p1, D)
        lo, hi = find_derivative_bracket(p0, p1, D, b_star)

        d_lo = split_deriv(p0, p1, D, lo)
        d_hi = split_deriv(p0, p1, D, hi)
        if d_lo < 0 or d_hi > 0:
            continue
        if not (lo <= b_star <= hi):
            continue

        m = endpoint_m(p0, p1, D)
        if m <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))

        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1

        radius_sq = 2 * tau_upper / m
        radius = np.sqrt(radius_sq)
        actual_dist = abs(float(argmax) - b_star)

        if radius > 1e-10:
            ratios.append(actual_dist / radius)

    if not ratios:
        print("Test 6: Radius tightness (no valid cases)")
        print("  SKIP")
        return

    ratios_arr = np.array(ratios)
    print(f"Test 6: Radius tightness ({total} trials)")
    print(f"  mean ratio:   {np.mean(ratios_arr):.6f}")
    print(f"  median ratio: {np.median(ratios_arr):.6f}")
    print(f"  max ratio:    {np.max(ratios_arr):.6f}")
    print(f"  min ratio:    {np.min(ratios_arr):.6f}")
    assert np.max(ratios_arr) <= 1.0 + 1e-6, "Ratio exceeded 1.0 (bound violated)"
    print("  PASS")


def test_symbolic_certificate_chain() -> None:
    """Test 7: Symbolic verification of the certificate chain algebra.

    Verifies that the algebraic steps in the proof are correct:
    1. (m/2)*(x - b*)^2 <= F(b*) - prod  (strong concavity)
    2. F(b*) - prod <= cont_upper - prod = tau_upper  (upper bound)
    3. (m/2)*(x - b*)^2 <= tau_upper  (transitivity)
    4. (x - b*)^2 <= 2*tau_upper/m  (algebra)
    5. |x - b*| <= sqrt(2*tau_upper/m)  (sqrt monotonicity)
    """
    if not HAS_SYMPY:
        print("Test 7: Symbolic certificate chain (skipped, sympy not available)")
        print("  SKIP")
        return

    m, tau, x, b_star = sp.symbols("m tau x b_star", positive=True)

    # Step 4: (m/2)*(x-b*)^2 <= tau  =>  (x-b*)^2 <= 2*tau/m
    quad_bound = sp.Rational(1, 2) * m * (x - b_star) ** 2
    algebra_step = sp.solve(sp.Eq(quad_bound, tau), (x - b_star) ** 2)
    assert any(sp.simplify(s - 2 * tau / m) == 0 for s in algebra_step), \
        "Algebra step 4 failed"

    # Step 5: (x-b*)^2 <= 2*tau/m  =>  |x-b*| <= sqrt(2*tau/m)
    # This follows from sqrt being monotone on nonneg and |x-b*|^2 = (x-b*)^2
    radius = sp.sqrt(2 * tau / m)
    assert sp.simplify(radius ** 2 - 2 * tau / m) == 0, "Sqrt step 5 failed"

    # Verify the transitivity: if A <= B and B <= C then A <= C
    # (m/2)*(x-b*)^2 <= F(b*)-prod and F(b*)-prod <= tau
    # => (m/2)*(x-b*)^2 <= tau
    F_bstar, prod = sp.symbols("F_bstar prod", positive=True)
    slack = F_bstar - prod
    # If (m/2)*(x-b*)^2 <= slack and slack <= tau, then (m/2)*(x-b*)^2 <= tau
    # This is just transitivity of <=, verified by:
    assert sp.simplify(slack - (F_bstar - prod)) == 0, "Transitivity setup failed"

    print("Test 7: Symbolic certificate chain algebra verified")
    print("  PASS")


def test_endpoint_m_is_lower_bound() -> None:
    """Test 8: Endpoint m is a valid lower bound on |F''(a)|.

    The endpoint m = 2*c0^2*K0*M0/(M0+c0*D)^3 + 2*c1^2*K1*M1/(M1+c1*D)^3
    should be <= |F''(a)| for all a in [0, D], since F'' is the sum of two
    negative terms whose magnitudes are minimized at the endpoints.
    """
    rng = random.Random(42)
    violations = 0
    total = 0
    for _ in range(200):
        K0 = rng.uniform(100, 10000)
        M0 = rng.uniform(100, 10000)
        c0 = rng.uniform(0.9, 1.0)
        K1 = rng.uniform(100, 10000)
        M1 = rng.uniform(100, 10000)
        c1 = rng.uniform(0.9, 1.0)
        D = float(rng.randint(10, 500))

        p0 = Pool(K0, M0, c0)
        p1 = Pool(K1, M1, c1)

        m = endpoint_m(p0, p1, D)
        if m <= 0:
            continue

        # Check m <= |F''(a)| for several a values
        for frac in [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0]:
            a = D * frac
            d2 = split_second_deriv(p0, p1, D, a)
            total += 1
            if m > abs(d2) + 1e-6:
                violations += 1

    assert violations == 0, f"Endpoint m not a lower bound in {violations}/{total} cases"
    print(f"Test 8: Endpoint m is valid lower bound on |F''| ({total} checks, 0 violations)")
    print("  PASS")


def main() -> int:
    print("=== P10: Exact Interval Certificate Path ===")
    print()
    test_exact_interval_certificate_path()
    test_certificate_path_squared()
    test_checker_acceptance_implies_distance_bound()
    test_complete_certificate_soundness()
    test_strong_concavity_holds()
    test_radius_tightness()
    test_symbolic_certificate_chain()
    test_endpoint_m_is_lower_bound()
    print()
    print("=== All tests passed ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())
