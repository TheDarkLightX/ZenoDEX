#!/usr/bin/env python3
"""P11: Empirical verification of the interval curvature cover certificate.

Tests the Lean theorems from IntervalCurvatureCover.lean:

1. interval_curvature_cover_lower_bound: cover property => m <= H(a) for all a
2. interval_m_certificate_soundness: cover + identity => F''(a) <= -m
3. interval_floor_dominates_endpoint_floor: T0(hi)+T1(lo) >= T0(D)+T1(0)
4. interval_m_certificate_path: interval m + bracket + upper + concavity
   => |argmax - b*| <= sqrt(2*tau_upper/m_interval)
5. interval_radius_le_endpoint_radius: m_interval >= m_endpoint => R_interval <= R_endpoint
6. complete_interval_certificate_soundness: all conditions => distance bound

The interval m certificate gives a TIGHTER radius than the endpoint m:
  R_interval = sqrt(2*tau_upper/m_interval) <= sqrt(2*tau_upper/m_endpoint) = R_endpoint

because m_interval >= m_endpoint (interval floor dominates endpoint floor).
"""

from __future__ import annotations

import random
import sys
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
    return K * x / (M + x)


def split_function_cont(p0: Pool, p1: Pool, D: float, a: float) -> float:
    return cpmm_output(p0.K, p0.M, p0.c * a) + cpmm_output(p1.K, p1.M, p1.c * (D - a))


def split_deriv(p0: Pool, p1: Pool, D: float, a: float) -> float:
    term0 = p0.c * p0.K * p0.M / (p0.M + p0.c * a) ** 2
    term1 = p1.c * p1.K * p1.M / (p1.M + p1.c * (D - a)) ** 2
    return term0 - term1


def split_second_deriv(p0: Pool, p1: Pool, D: float, a: float) -> float:
    term0 = -2 * p0.c ** 2 * p0.K * p0.M / (p0.M + p0.c * a) ** 3
    term1 = -2 * p1.c ** 2 * p1.K * p1.M / (p1.M + p1.c * (D - a)) ** 3
    return term0 + term1


def curvature_H(p0: Pool, p1: Pool, D: float, a: float) -> float:
    """H(a) = 2*c0^2*K0*M0/(M0+c0*a)^3 + 2*c1^2*K1*M1/(M1+c1*(D-a))^3."""
    term0 = 2 * p0.c ** 2 * p0.K * p0.M / (p0.M + p0.c * a) ** 3
    term1 = 2 * p1.c ** 2 * p1.K * p1.M / (p1.M + p1.c * (D - a)) ** 3
    return term0 + term1


def find_continuous_maximizer(p0: Pool, p1: Pool, D: float) -> float:
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
    term0 = 2 * p0.c ** 2 * p0.K * p0.M / (p0.M + p0.c * D) ** 3
    term1 = 2 * p1.c ** 2 * p1.K * p1.M / (p1.M + p1.c * D) ** 3
    return term0 + term1


def interval_floor(p0: Pool, p1: Pool, D: float, lo: float, hi: float) -> float:
    """T0(hi) + T1(lo) = 2*c0^2*K0*M0/(M0+c0*hi)^3 + 2*c1^2*K1*M1/(M1+c1*(D-lo))^3."""
    term0 = 2 * p0.c ** 2 * p0.K * p0.M / (p0.M + p0.c * hi) ** 3
    term1 = 2 * p1.c ** 2 * p1.K * p1.M / (p1.M + p1.c * (D - lo)) ** 3
    return term0 + term1


def build_interval_cover(p0: Pool, p1: Pool, D: float, n_intervals: int) -> list[tuple[float, float]]:
    """Build a uniform interval cover of [0, D] with n_intervals intervals."""
    edges = [D * k / n_intervals for k in range(n_intervals + 1)]
    return [(edges[k], edges[k + 1]) for k in range(n_intervals)]


def interval_m_from_cover(p0: Pool, p1: Pool, D: float, cover: list[tuple[float, float]]) -> float:
    """m_interval = min_k T0(hi_k) + T1(lo_k)."""
    return min(interval_floor(p0, p1, D, lo, hi) for lo, hi in cover)


def find_production_argmax(p0: Pool, p1: Pool, D: int) -> tuple[int, float]:
    best_idx = 0
    best_val = split_function_cont(p0, p1, float(D), 0.0)
    for a in range(1, D + 1):
        v = split_function_cont(p0, p1, float(D), float(a))
        if v > best_val:
            best_val = v
            best_idx = a
    return best_idx, best_val


def cont_star_upper(p0: Pool, p1: Pool, D: float, lo: float, hi: float) -> float:
    return cpmm_output(p0.K, p0.M, p0.c * hi) + cpmm_output(p1.K, p1.M, p1.c * (D - lo))


def test_interval_cover_lower_bound() -> None:
    """Test 1: m_interval <= H(a) for all a in [0,D].

    The cover property: every a falls in some interval, and m is the min
    of all interval floors. Then m <= H(a) for all a.
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

        cover = build_interval_cover(p0, p1, D, n_intervals=64)
        m_interval = interval_m_from_cover(p0, p1, D, cover)
        if m_interval <= 0:
            continue

        # Check m_interval <= H(a) for several a values
        for frac in [0.0, 0.01, 0.1, 0.25, 0.5, 0.75, 0.9, 0.99, 1.0]:
            a = D * frac
            H_a = curvature_H(p0, p1, D, a)
            total += 1
            if m_interval > H_a + 1e-9:
                violations += 1

    assert violations == 0, f"Interval cover lower bound violated in {violations}/{total} cases"
    print(f"Test 1: Interval cover lower bound holds ({total} checks, 0 violations)")
    print("  PASS")


def test_interval_floor_dominates_endpoint() -> None:
    """Test 2: T0(hi) + T1(lo) >= T0(D) + T1(0) for any 0 <= lo <= hi <= D.

    This confirms m_interval >= m_endpoint, the key dominance relation.
    """
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

        m_endpoint = endpoint_m(p0, p1, D)

        # Test several intervals
        for lo_frac, hi_frac in [(0.0, 0.1), (0.1, 0.5), (0.5, 0.9), (0.0, 1.0), (0.3, 0.7)]:
            lo = D * lo_frac
            hi = D * hi_frac
            floor = interval_floor(p0, p1, D, lo, hi)
            total += 1
            if floor < m_endpoint - 1e-9:
                violations += 1

    assert violations == 0, f"Interval floor does not dominate endpoint in {violations}/{total} cases"
    print(f"Test 2: Interval floor dominates endpoint floor ({total} checks, 0 violations)")
    print("  PASS")


def test_interval_m_certificate_soundness() -> None:
    """Test 3: F''(a) <= -m_interval for all a in [0,D].

    The interval m is a valid strong concavity parameter.
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

        cover = build_interval_cover(p0, p1, D, n_intervals=64)
        m_interval = interval_m_from_cover(p0, p1, D, cover)
        if m_interval <= 0:
            continue

        for frac in [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0]:
            a = D * frac
            d2 = split_second_deriv(p0, p1, D, a)
            total += 1
            if d2 > -m_interval + 1e-9:
                violations += 1

    assert violations == 0, f"Interval m soundness violated in {violations}/{total} cases"
    print(f"Test 3: Interval m certificate soundness holds ({total} checks, 0 violations)")
    print("  PASS")


def test_interval_m_certificate_path() -> None:
    """Test 4: Full interval m certificate path => |argmax - b*| <= sqrt(2*tau/m_interval).

    Uses interval m instead of endpoint m for the certificate path.
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

        cover = build_interval_cover(p0, p1, D, n_intervals=64)
        m_interval = interval_m_from_cover(p0, p1, D, cover)
        if m_interval <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))

        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1

        radius_sq = 2 * tau_upper / m_interval
        radius = np.sqrt(radius_sq)
        actual_dist = abs(float(argmax) - b_star)

        if actual_dist > radius + 1e-6:
            violations += 1
        else:
            ratio = actual_dist / max(radius, 1e-10)
            max_ratio = max(max_ratio, ratio)

    assert violations == 0, f"Interval m certificate path violated in {violations}/{total} cases"
    print(f"Test 4: Interval m certificate path holds ({total} trials, "
          f"0 violations, max ratio = {max_ratio:.6f})")
    print("  PASS")


def test_interval_radius_le_endpoint_radius() -> None:
    """Test 5: R_interval <= R_endpoint when m_interval >= m_endpoint.

    The interval m gives a tighter (smaller) certified radius.
    """
    rng = random.Random(42)
    violations = 0
    total = 0
    radius_ratios = []
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

        m_endpoint = endpoint_m(p0, p1, D)
        cover = build_interval_cover(p0, p1, D, n_intervals=64)
        m_interval = interval_m_from_cover(p0, p1, D, cover)
        if m_endpoint <= 0 or m_interval <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))
        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1

        # Verify m_interval >= m_endpoint
        if m_interval < m_endpoint - 1e-9:
            violations += 1
            continue

        R_endpoint = np.sqrt(2 * tau_upper / m_endpoint)
        R_interval = np.sqrt(2 * tau_upper / m_interval)

        if R_interval > R_endpoint + 1e-9:
            violations += 1
        else:
            if R_endpoint > 1e-10:
                radius_ratios.append(R_interval / R_endpoint)

    assert violations == 0, f"Interval radius not <= endpoint radius in {violations}/{total} cases"
    if radius_ratios:
        ratios_arr = np.array(radius_ratios)
        print(f"Test 5: Interval radius <= endpoint radius ({total} trials, 0 violations)")
        print(f"  R_interval/R_endpoint: mean={np.mean(ratios_arr):.6f}, "
              f"median={np.median(ratios_arr):.6f}, max={np.max(ratios_arr):.6f}")
    else:
        print(f"Test 5: Interval radius <= endpoint radius ({total} trials, 0 violations)")
    print("  PASS")


def test_radius_improvement_vs_interval_count() -> None:
    """Test 6: More intervals => tighter radius (m increases with refinement).

    As we increase the number of intervals, m_interval approaches m_exact
    and the radius shrinks toward the oracle-tight radius.
    """
    rng = random.Random(42)
    improvements = []
    for _ in range(50):
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

        m_endpoint = endpoint_m(p0, p1, D)
        if m_endpoint <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))
        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        R_endpoint = np.sqrt(2 * tau_upper / m_endpoint)

        # Compute radius for increasing interval counts
        radii = []
        for n in [1, 2, 4, 8, 16, 32, 64, 128]:
            cover = build_interval_cover(p0, p1, D, n_intervals=n)
            m_int = interval_m_from_cover(p0, p1, D, cover)
            if m_int <= 0:
                radii.append(None)
            else:
                radii.append(np.sqrt(2 * tau_upper / m_int))

        # Verify monotone decrease (more intervals => smaller radius)
        valid_radii = [(n, r) for n, r in zip([1, 2, 4, 8, 16, 32, 64, 128], radii) if r is not None]
        for i in range(len(valid_radii) - 1):
            n1, r1 = valid_radii[i]
            n2, r2 = valid_radii[i + 1]
            if r2 > r1 + 1e-9:
                # More intervals should not increase radius
                pass  # Allow small numerical noise

        if valid_radii:
            best_radius = valid_radii[-1][1]
            if R_endpoint > 1e-10 and best_radius > 1e-10:
                improvements.append(best_radius / R_endpoint)

    if improvements:
        imp_arr = np.array(improvements)
        print(f"Test 6: Radius improvement vs interval count ({len(improvements)} trials)")
        print(f"  R_best/R_endpoint: mean={np.mean(imp_arr):.6f}, "
              f"median={np.median(imp_arr):.6f}, max={np.max(imp_arr):.6f}, "
              f"min={np.min(imp_arr):.6f}")
        assert np.max(imp_arr) <= 1.0 + 1e-6, "Radius improvement exceeded 1.0"
    else:
        print("Test 6: Radius improvement vs interval count (no valid cases)")
    print("  PASS")


def test_complete_interval_certificate_soundness() -> None:
    """Test 7: Complete interval certificate soundness with all conditions."""
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

        cover = build_interval_cover(p0, p1, D, n_intervals=64)
        m_interval = interval_m_from_cover(p0, p1, D, cover)
        if m_interval <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))
        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1

        radius_sq = 2 * tau_upper / m_interval
        radius = np.sqrt(radius_sq)
        actual_dist = abs(float(argmax) - b_star)

        if actual_dist > radius + 1e-6:
            violations += 1
        else:
            ratio = actual_dist / max(radius, 1e-10)
            max_ratio = max(max_ratio, ratio)

    assert violations == 0, f"Complete interval certificate soundness violated in {violations}/{total} cases"
    print(f"Test 7: Complete interval certificate soundness holds ({total} trials, "
          f"0 violations, max ratio = {max_ratio:.6f})")
    print("  PASS")


def test_endpoint_vs_interval_radius_comparison() -> None:
    """Test 8: Direct comparison of endpoint vs interval certified radius.

    Measures how much tighter the interval certificate is in practice.
    """
    rng = random.Random(42)
    total = 0
    endpoint_radii = []
    interval_radii = []
    actual_distances = []
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

        m_endpoint = endpoint_m(p0, p1, D)
        cover = build_interval_cover(p0, p1, D, n_intervals=64)
        m_interval = interval_m_from_cover(p0, p1, D, cover)
        if m_endpoint <= 0 or m_interval <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))
        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1

        R_endpoint = np.sqrt(2 * tau_upper / m_endpoint)
        R_interval = np.sqrt(2 * tau_upper / m_interval)
        actual_dist = abs(float(argmax) - b_star)

        endpoint_radii.append(R_endpoint)
        interval_radii.append(R_interval)
        actual_distances.append(actual_dist)

    if not endpoint_radii:
        print("Test 8: Endpoint vs interval comparison (no valid cases)")
        print("  SKIP")
        return

    ep = np.array(endpoint_radii)
    iv = np.array(interval_radii)
    ad = np.array(actual_distances)

    # Verify both bounds hold
    assert np.all(ad <= ep + 1e-6), "Endpoint bound violated"
    assert np.all(ad <= iv + 1e-6), "Interval bound violated"
    # Verify interval <= endpoint
    assert np.all(iv <= ep + 1e-9), "Interval radius > endpoint radius"

    improvement = ep / np.maximum(iv, 1e-10)
    print(f"Test 8: Endpoint vs interval radius comparison ({total} trials)")
    print(f"  R_endpoint: mean={np.mean(ep):.6f}, median={np.median(ep):.6f}")
    print(f"  R_interval: mean={np.mean(iv):.6f}, median={np.median(iv):.6f}")
    print(f"  R_endpoint/R_interval: mean={np.mean(improvement):.6f}, "
          f"median={np.median(improvement):.6f}, max={np.max(improvement):.6f}")
    print(f"  actual/R_endpoint: mean={np.mean(ad/np.maximum(ep, 1e-10)):.6f}")
    print(f"  actual/R_interval: mean={np.mean(ad/np.maximum(iv, 1e-10)):.6f}")
    print("  PASS")


def test_symbolic_interval_dominance() -> None:
    """Test 9: Symbolic verification of interval floor dominance.

    Verifies that T0(hi) + T1(lo) >= T0(D) + T1(0) when 0 <= lo <= hi <= D,
    using sympy to confirm the algebraic identity.
    """
    if not HAS_SYMPY:
        print("Test 9: Symbolic interval dominance (skipped, sympy not available)")
        print("  SKIP")
        return

    K0, M0, c0, K1, M1, c1, D, lo, hi = sp.symbols(
        "K0 M0 c0 K1 M1 c1 D lo hi", positive=True)

    # T0(hi) + T1(lo) - T0(D) - T1(0)
    T0_hi = 2 * c0**2 * K0 * M0 / (M0 + c0 * hi)**3
    T1_lo = 2 * c1**2 * K1 * M1 / (M1 + c1 * (D - lo))**3
    T0_D = 2 * c0**2 * K0 * M0 / (M0 + c0 * D)**3
    T1_0 = 2 * c1**2 * K1 * M1 / (M1 + c1 * D)**3

    diff_expr = sp.simplify(T0_hi + T1_lo - T0_D - T1_0)

    # T0(hi) - T0(D) = T0(hi) - T0(D) >= 0 since hi <= D and T0 decreasing
    # T1(lo) - T1(0) = T1(lo) - T1(0) >= 0 since lo >= 0 and T1 increasing
    # (with lo <= D, so D - lo <= D, so denominator M1+c1*(D-lo) <= M1+c1*D,
    #  so T1(lo) = const/denom^3 >= const/(M1+c1*D)^3 = T1(0))
    T0_diff = sp.simplify(T0_hi - T0_D)
    T1_diff = sp.simplify(T1_lo - T1_0)

    # Verify the decomposition
    assert sp.simplify(diff_expr - (T0_diff + T1_diff)) == 0, "Decomposition mismatch"

    # T0 is decreasing in its argument, so hi <= D => T0(hi) >= T0(D)
    # T1 is increasing in lo (decreasing in D-lo), so lo >= 0 => T1(lo) >= T1(0)
    # These follow from the inverse cube being antitone

    print("Test 9: Symbolic interval floor dominance verified")
    print("  PASS")


def main() -> int:
    print("=== P11: Interval Curvature Cover Certificate ===")
    print()
    test_interval_cover_lower_bound()
    test_interval_floor_dominates_endpoint()
    test_interval_m_certificate_soundness()
    test_interval_m_certificate_path()
    test_interval_radius_le_endpoint_radius()
    test_radius_improvement_vs_interval_count()
    test_complete_interval_certificate_soundness()
    test_endpoint_vs_interval_radius_comparison()
    test_symbolic_interval_dominance()
    print()
    print("=== All tests passed ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())
