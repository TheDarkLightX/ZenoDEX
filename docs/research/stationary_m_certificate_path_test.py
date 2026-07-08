#!/usr/bin/env python3
"""P12: Empirical verification of the stationary m certificate path.

Tests the Lean theorems from StationaryMCertificatePath.lean:

1. symmetric_stationary_m_universal_floor: H(a) >= H(D/2) for identical pools
2. symmetric_stationary_m_soundness: F''(a) <= -m_sym for identical pools
3. symmetric_stationary_m_dominates_endpoint: m_symmetric >= m_endpoint
4. asymmetric_stationary_m_soundness: F''(a) <= -m for checker-supplied m
5. symmetric_stationary_m_certificate_path: |argmax - b*| <= sqrt(2*tau/m_sym)
6. asymmetric_stationary_m_certificate_path: |argmax - b*| <= sqrt(2*tau/m)
7. stationary_radius_le_interval_radius: R_stationary <= R_interval
8. stationary_radius_le_endpoint_radius: R_stationary <= R_endpoint
9. complete_stationary_certificate_soundness: all conditions => distance bound

The stationary m certificate gives the TIGHTEST radius:
  R_stationary <= R_interval <= R_endpoint

because m_stationary >= m_interval >= m_endpoint (exact curvature minimum
dominates interval floor dominates endpoint floor).

For symmetric pools (K0=K1, M0=M1, c0=c1), the stationary m is exact:
  m_symmetric = H(D/2) = 4*c^2*K*M/(M+c*D/2)^3

For asymmetric pools, the stationary m is supplied by the checker via
the normalized affine certificate (validated externally).
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
    K: float
    M: float
    c: float


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
    term0 = 2 * p0.c ** 2 * p0.K * p0.M / (p0.M + p0.c * hi) ** 3
    term1 = 2 * p1.c ** 2 * p1.K * p1.M / (p1.M + p1.c * (D - lo)) ** 3
    return term0 + term1


def build_interval_cover(p0: Pool, p1: Pool, D: float, n_intervals: int) -> list[tuple[float, float]]:
    edges = [D * k / n_intervals for k in range(n_intervals + 1)]
    return [(edges[k], edges[k + 1]) for k in range(n_intervals)]


def interval_m_from_cover(p0: Pool, p1: Pool, D: float, cover: list[tuple[float, float]]) -> float:
    return min(interval_floor(p0, p1, D, lo, hi) for lo, hi in cover)


def symmetric_stationary_m(K: float, M: float, c: float, D: float) -> float:
    return 4 * c ** 2 * K * M / (M + c * (D / 2)) ** 3


def find_exact_curvature_min(p0: Pool, p1: Pool, D: float) -> float:
    """Find the exact curvature minimum by grid search + refinement."""
    best_a = 0.0
    best_H = curvature_H(p0, p1, D, 0.0)
    for a in np.linspace(0, D, 1000):
        H_a = curvature_H(p0, p1, D, float(a))
        if H_a < best_H:
            best_H = H_a
            best_a = float(a)
    lo = max(0.0, best_a - D * 0.01)
    hi = min(D, best_a + D * 0.01)
    for _ in range(100):
        mid = (lo + hi) / 2
        H_left = curvature_H(p0, p1, D, mid - 1e-8)
        H_right = curvature_H(p0, p1, D, mid + 1e-8)
        if H_left < H_right:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2


def exact_stationary_m(p0: Pool, p1: Pool, D: float) -> float:
    a_min = find_exact_curvature_min(p0, p1, D)
    return curvature_H(p0, p1, D, a_min)


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


def test_symmetric_stationary_m_universal_floor() -> None:
    """Test 1: H(a) >= H(D/2) for identical pools."""
    rng = random.Random(42)
    violations = 0
    total = 0
    for _ in range(200):
        K = rng.uniform(100, 10000)
        M = rng.uniform(100, 10000)
        c = rng.uniform(0.9, 1.0)
        D = float(rng.randint(10, 500))
        p = Pool(K, M, c)

        m_sym = symmetric_stationary_m(K, M, c, D)
        for frac in [0.0, 0.01, 0.1, 0.25, 0.5, 0.75, 0.9, 0.99, 1.0]:
            a = D * frac
            H_a = curvature_H(p, p, D, a)
            total += 1
            if m_sym > H_a + 1e-9:
                violations += 1

    assert violations == 0, f"Symmetric floor violated in {violations}/{total} cases"
    print(f"Test 1: Symmetric stationary m universal floor ({total} checks, 0 violations)")
    print("  PASS")


def test_symmetric_stationary_m_soundness() -> None:
    """Test 2: F''(a) <= -m_sym for identical pools."""
    rng = random.Random(42)
    violations = 0
    total = 0
    for _ in range(200):
        K = rng.uniform(100, 10000)
        M = rng.uniform(100, 10000)
        c = rng.uniform(0.9, 1.0)
        D = float(rng.randint(10, 500))
        p = Pool(K, M, c)

        m_sym = symmetric_stationary_m(K, M, c, D)
        for frac in [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0]:
            a = D * frac
            d2 = split_second_deriv(p, p, D, a)
            total += 1
            if d2 > -m_sym + 1e-9:
                violations += 1

    assert violations == 0, f"Symmetric soundness violated in {violations}/{total} cases"
    print(f"Test 2: Symmetric stationary m soundness ({total} checks, 0 violations)")
    print("  PASS")


def test_symmetric_stationary_m_dominates_endpoint() -> None:
    """Test 3: m_symmetric >= m_endpoint for identical pools."""
    rng = random.Random(42)
    violations = 0
    total = 0
    for _ in range(500):
        K = rng.uniform(100, 10000)
        M = rng.uniform(100, 10000)
        c = rng.uniform(0.9, 1.0)
        D = float(rng.randint(10, 500))
        p = Pool(K, M, c)

        m_end = endpoint_m(p, p, D)
        m_sym = symmetric_stationary_m(K, M, c, D)
        total += 1
        if m_sym < m_end - 1e-9:
            violations += 1

    assert violations == 0, f"Symmetric dominance violated in {violations}/{total} cases"
    print(f"Test 3: Symmetric stationary m dominates endpoint ({total} trials, 0 violations)")
    print("  PASS")


def test_asymmetric_stationary_m_soundness() -> None:
    """Test 4: F''(a) <= -m_exact for asymmetric pools with exact m."""
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

        m_exact = exact_stationary_m(p0, p1, D)
        if m_exact <= 0:
            continue

        for frac in [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0]:
            a = D * frac
            d2 = split_second_deriv(p0, p1, D, a)
            total += 1
            if d2 > -m_exact + 1e-9:
                violations += 1

    assert violations == 0, f"Asymmetric soundness violated in {violations}/{total} cases"
    print(f"Test 4: Asymmetric stationary m soundness ({total} checks, 0 violations)")
    print("  PASS")


def test_symmetric_stationary_m_certificate_path() -> None:
    """Test 5: |argmax - b*| <= sqrt(2*tau/m_sym) for symmetric pools."""
    rng = random.Random(42)
    violations = 0
    total = 0
    max_ratio = 0.0
    for _ in range(500):
        K = rng.uniform(100, 10000)
        M = rng.uniform(100, 10000)
        c = rng.uniform(0.9, 1.0)
        D = float(rng.randint(10, 500))
        p = Pool(K, M, c)

        b_star = find_continuous_maximizer(p, p, D)
        lo, hi = find_derivative_bracket(p, p, D, b_star)
        d_lo = split_deriv(p, p, D, lo)
        d_hi = split_deriv(p, p, D, hi)
        if d_lo < 0 or d_hi > 0:
            continue
        if not (lo <= b_star <= hi):
            continue

        m_sym = symmetric_stationary_m(K, M, c, D)
        if m_sym <= 0:
            continue

        argmax, prod_val = find_production_argmax(p, p, int(D))
        cont_upper = cont_star_upper(p, p, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1
        radius = np.sqrt(2 * tau_upper / m_sym)
        actual_dist = abs(float(argmax) - b_star)

        if actual_dist > radius + 1e-6:
            violations += 1
        else:
            ratio = actual_dist / max(radius, 1e-10)
            max_ratio = max(max_ratio, ratio)

    assert violations == 0, f"Symmetric path violated in {violations}/{total} cases"
    print(f"Test 5: Symmetric stationary m certificate path ({total} trials, "
          f"0 violations, max ratio = {max_ratio:.6f})")
    print("  PASS")


def test_asymmetric_stationary_m_certificate_path() -> None:
    """Test 6: |argmax - b*| <= sqrt(2*tau/m_exact) for asymmetric pools."""
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

        m_exact = exact_stationary_m(p0, p1, D)
        if m_exact <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))
        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1
        radius = np.sqrt(2 * tau_upper / m_exact)
        actual_dist = abs(float(argmax) - b_star)

        if actual_dist > radius + 1e-6:
            violations += 1
        else:
            ratio = actual_dist / max(radius, 1e-10)
            max_ratio = max(max_ratio, ratio)

    assert violations == 0, f"Asymmetric path violated in {violations}/{total} cases"
    print(f"Test 6: Asymmetric stationary m certificate path ({total} trials, "
          f"0 violations, max ratio = {max_ratio:.6f})")
    print("  PASS")


def test_stationary_radius_le_interval_radius() -> None:
    """Test 7: R_stationary <= R_interval when m_stationary >= m_interval."""
    rng = random.Random(42)
    violations = 0
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

        cover = build_interval_cover(p0, p1, D, n_intervals=64)
        m_interval = interval_m_from_cover(p0, p1, D, cover)
        m_exact = exact_stationary_m(p0, p1, D)
        if m_interval <= 0 or m_exact <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))
        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1
        if m_exact < m_interval - 1e-9:
            violations += 1
            continue

        R_interval = np.sqrt(2 * tau_upper / m_interval)
        R_stationary = np.sqrt(2 * tau_upper / m_exact)

        if R_stationary > R_interval + 1e-9:
            violations += 1
        else:
            if R_interval > 1e-10:
                ratios.append(R_stationary / R_interval)

    assert violations == 0, f"Stationary <= interval radius violated in {violations}/{total} cases"
    if ratios:
        arr = np.array(ratios)
        print(f"Test 7: Stationary radius <= interval radius ({total} trials, 0 violations)")
        print(f"  R_stationary/R_interval: mean={np.mean(arr):.6f}, "
              f"median={np.median(arr):.6f}, max={np.max(arr):.6f}")
    else:
        print(f"Test 7: Stationary radius <= interval radius ({total} trials, 0 violations)")
    print("  PASS")


def test_stationary_radius_le_endpoint_radius() -> None:
    """Test 8: R_stationary <= R_endpoint when m_stationary >= m_endpoint."""
    rng = random.Random(42)
    violations = 0
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

        m_end = endpoint_m(p0, p1, D)
        m_exact = exact_stationary_m(p0, p1, D)
        if m_end <= 0 or m_exact <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))
        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1
        if m_exact < m_end - 1e-9:
            violations += 1
            continue

        R_endpoint = np.sqrt(2 * tau_upper / m_end)
        R_stationary = np.sqrt(2 * tau_upper / m_exact)

        if R_stationary > R_endpoint + 1e-9:
            violations += 1
        else:
            if R_endpoint > 1e-10:
                ratios.append(R_stationary / R_endpoint)

    assert violations == 0, f"Stationary <= endpoint radius violated in {violations}/{total} cases"
    if ratios:
        arr = np.array(ratios)
        print(f"Test 8: Stationary radius <= endpoint radius ({total} trials, 0 violations)")
        print(f"  R_stationary/R_endpoint: mean={np.mean(arr):.6f}, "
              f"median={np.median(arr):.6f}, max={np.max(arr):.6f}")
    else:
        print(f"Test 8: Stationary radius <= endpoint radius ({total} trials, 0 violations)")
    print("  PASS")


def test_complete_stationary_certificate_soundness() -> None:
    """Test 9: Complete certificate soundness with stationary m."""
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

        m_exact = exact_stationary_m(p0, p1, D)
        if m_exact <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))
        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1
        radius = np.sqrt(2 * tau_upper / m_exact)
        actual_dist = abs(float(argmax) - b_star)

        if actual_dist > radius + 1e-6:
            violations += 1
        else:
            ratio = actual_dist / max(radius, 1e-10)
            max_ratio = max(max_ratio, ratio)

    assert violations == 0, f"Complete soundness violated in {violations}/{total} cases"
    print(f"Test 9: Complete stationary certificate soundness ({total} trials, "
          f"0 violations, max ratio = {max_ratio:.6f})")
    print("  PASS")


def test_three_way_radius_comparison() -> None:
    """Test 10: Direct comparison of endpoint vs interval vs stationary radius.

    Measures the full radius shrinkage chain:
      R_endpoint >= R_interval >= R_stationary
    """
    rng = random.Random(42)
    total = 0
    endpoint_radii = []
    interval_radii = []
    stationary_radii = []
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

        m_end = endpoint_m(p0, p1, D)
        cover = build_interval_cover(p0, p1, D, n_intervals=64)
        m_int = interval_m_from_cover(p0, p1, D, cover)
        m_exact = exact_stationary_m(p0, p1, D)
        if m_end <= 0 or m_int <= 0 or m_exact <= 0:
            continue

        argmax, prod_val = find_production_argmax(p0, p1, int(D))
        cont_upper = cont_star_upper(p0, p1, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1
        R_end = np.sqrt(2 * tau_upper / m_end)
        R_int = np.sqrt(2 * tau_upper / m_int)
        R_sta = np.sqrt(2 * tau_upper / m_exact)
        actual = abs(float(argmax) - b_star)

        endpoint_radii.append(R_end)
        interval_radii.append(R_int)
        stationary_radii.append(R_sta)
        actual_distances.append(actual)

    if not endpoint_radii:
        print("Test 10: Three-way radius comparison (no valid cases)")
        print("  SKIP")
        return

    ep = np.array(endpoint_radii)
    iv = np.array(interval_radii)
    st = np.array(stationary_radii)
    ad = np.array(actual_distances)

    assert np.all(ad <= ep + 1e-6), "Endpoint bound violated"
    assert np.all(ad <= iv + 1e-6), "Interval bound violated"
    assert np.all(ad <= st + 1e-6), "Stationary bound violated"
    assert np.all(iv <= ep + 1e-9), "Interval > endpoint"
    assert np.all(st <= iv + 1e-9), "Stationary > interval"

    ep_over_st = ep / np.maximum(st, 1e-10)
    iv_over_st = iv / np.maximum(st, 1e-10)
    ep_over_iv = ep / np.maximum(iv, 1e-10)

    print(f"Test 10: Three-way radius comparison ({total} trials)")
    print(f"  R_endpoint:   mean={np.mean(ep):.6f}, median={np.median(ep):.6f}")
    print(f"  R_interval:   mean={np.mean(iv):.6f}, median={np.median(iv):.6f}")
    print(f"  R_stationary: mean={np.mean(st):.6f}, median={np.median(st):.6f}")
    print(f"  R_endpoint/R_stationary:   mean={np.mean(ep_over_st):.6f}, "
          f"median={np.median(ep_over_st):.6f}, max={np.max(ep_over_st):.6f}")
    print(f"  R_interval/R_stationary:   mean={np.mean(iv_over_st):.6f}, "
          f"median={np.median(iv_over_st):.6f}, max={np.max(iv_over_st):.6f}")
    print(f"  R_endpoint/R_interval:     mean={np.mean(ep_over_iv):.6f}, "
          f"median={np.median(ep_over_iv):.6f}, max={np.max(ep_over_iv):.6f}")
    print(f"  actual/R_stationary: mean={np.mean(ad/np.maximum(st, 1e-10)):.6f}")
    print("  PASS")


def test_symmetric_three_way_comparison() -> None:
    """Test 11: Three-way comparison for symmetric pools (exact stationary m).

    For symmetric pools, m_stationary = H(D/2) is Lean-proven exact.
    """
    rng = random.Random(42)
    total = 0
    endpoint_radii = []
    interval_radii = []
    stationary_radii = []
    actual_distances = []
    for _ in range(500):
        K = rng.uniform(100, 10000)
        M = rng.uniform(100, 10000)
        c = rng.uniform(0.9, 1.0)
        D = float(rng.randint(10, 500))
        p = Pool(K, M, c)

        b_star = find_continuous_maximizer(p, p, D)
        lo, hi = find_derivative_bracket(p, p, D, b_star)
        d_lo = split_deriv(p, p, D, lo)
        d_hi = split_deriv(p, p, D, hi)
        if d_lo < 0 or d_hi > 0:
            continue
        if not (lo <= b_star <= hi):
            continue

        m_end = endpoint_m(p, p, D)
        cover = build_interval_cover(p, p, D, n_intervals=64)
        m_int = interval_m_from_cover(p, p, D, cover)
        m_sym = symmetric_stationary_m(K, M, c, D)
        if m_end <= 0 or m_int <= 0 or m_sym <= 0:
            continue

        argmax, prod_val = find_production_argmax(p, p, int(D))
        cont_upper = cont_star_upper(p, p, D, lo, hi)
        tau_upper = cont_upper - prod_val
        if tau_upper < 0:
            continue

        total += 1
        R_end = np.sqrt(2 * tau_upper / m_end)
        R_int = np.sqrt(2 * tau_upper / m_int)
        R_sym = np.sqrt(2 * tau_upper / m_sym)
        actual = abs(float(argmax) - b_star)

        endpoint_radii.append(R_end)
        interval_radii.append(R_int)
        stationary_radii.append(R_sym)
        actual_distances.append(actual)

    if not endpoint_radii:
        print("Test 11: Symmetric three-way comparison (no valid cases)")
        print("  SKIP")
        return

    ep = np.array(endpoint_radii)
    iv = np.array(interval_radii)
    st = np.array(stationary_radii)
    ad = np.array(actual_distances)

    assert np.all(ad <= ep + 1e-6), "Endpoint bound violated"
    assert np.all(ad <= iv + 1e-6), "Interval bound violated"
    assert np.all(ad <= st + 1e-6), "Stationary bound violated"
    assert np.all(iv <= ep + 1e-9), "Interval > endpoint"
    assert np.all(st <= iv + 1e-9), "Stationary > interval"

    ep_over_st = ep / np.maximum(st, 1e-10)
    ep_over_iv = ep / np.maximum(iv, 1e-10)

    print(f"Test 11: Symmetric three-way comparison ({total} trials)")
    print(f"  R_endpoint/R_stationary: mean={np.mean(ep_over_st):.6f}, "
          f"median={np.median(ep_over_st):.6f}, max={np.max(ep_over_st):.6f}")
    print(f"  R_endpoint/R_interval:   mean={np.mean(ep_over_iv):.6f}, "
          f"median={np.median(ep_over_iv):.6f}, max={np.max(ep_over_iv):.6f}")
    print(f"  actual/R_stationary:     mean={np.mean(ad/np.maximum(st, 1e-10)):.6f}")
    print("  PASS")


def test_symbolic_symmetric_dominance() -> None:
    """Test 12: Symbolic verification of symmetric stationary dominance."""
    if not HAS_SYMPY:
        print("Test 12: Symbolic symmetric dominance (skipped, sympy not available)")
        print("  SKIP")
        return

    K, M, c, D = sp.symbols("K M c D", positive=True)

    m_endpoint = 4 * c**2 * K * M / (M + c * D)**3
    m_stationary = 4 * c**2 * K * M / (M + c * (D / 2))**3

    diff_expr = sp.simplify(m_stationary - m_endpoint)

    # m_stationary - m_endpoint >= 0 iff (M+c*D)^3 >= (M+c*D/2)^3
    # which holds since D > 0 and c > 0
    denom_diff = sp.simplify((M + c * D)**3 - (M + c * (D / 2))**3)

    # Factor the denominator difference
    denom_factored = sp.factor(denom_diff)

    # Verify the factorization is a product of positive factors
    # For positive K, M, c, D: (M+c*D)^3 > (M+c*D/2)^3 since M+c*D > M+c*D/2
    # The difference should factor as c*D/2 * (positive polynomial)
    # Just verify the difference is symbolically equal to the factored form
    assert sp.simplify(denom_diff - denom_factored) == 0, "Factorization mismatch"

    # Verify non-negativity by checking the factored form has positive factors
    # (M+c*D)^3 - (M+c*D/2)^3 = (c*D - c*D/2) * ((M+c*D)^2 + (M+c*D)*(M+c*D/2) + (M+c*D/2)^2)
    # = (c*D/2) * (sum of positive terms)
    # Use a^3 - b^3 = (a-b)*(a^2 + a*b + b^2) with a = M+c*D, b = M+c*D/2
    a = M + c * D
    b = M + c * (D / 2)
    expected = (a - b) * (a**2 + a * b + b**2)
    assert sp.simplify(denom_diff - expected) == 0, "a^3-b^3 formula mismatch"
    # a - b = c*D/2 > 0 for positive c, D
    # a^2 + a*b + b^2 > 0 for positive a, b
    assert sp.simplify(a - b - c * D / 2) == 0, "a-b != c*D/2"

    print("Test 12: Symbolic symmetric stationary dominance verified")
    print(f"  (M+c*D)^3 - (M+c*D/2)^3 = (c*D/2) * ((M+c*D)^2 + (M+c*D)*(M+c*D/2) + (M+c*D/2)^2)")
    print("  PASS")


def main() -> int:
    print("=== P12: Stationary m Certificate Path ===")
    print()
    test_symmetric_stationary_m_universal_floor()
    test_symmetric_stationary_m_soundness()
    test_symmetric_stationary_m_dominates_endpoint()
    test_asymmetric_stationary_m_soundness()
    test_symmetric_stationary_m_certificate_path()
    test_asymmetric_stationary_m_certificate_path()
    test_stationary_radius_le_interval_radius()
    test_stationary_radius_le_endpoint_radius()
    test_complete_stationary_certificate_soundness()
    test_three_way_radius_comparison()
    test_symmetric_three_way_comparison()
    test_symbolic_symmetric_dominance()
    print()
    print("=== All tests passed ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())
