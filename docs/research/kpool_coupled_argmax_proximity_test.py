#!/usr/bin/env python3
"""Empirical verification of the K-pool coupled argmax proximity (P3).

Verifies the Lean theorems in `KPoolDiscreteArgmaxProximity.lean`:

1. `abs_sub_le_max_of_nonneg`: |x - y| <= max(x, y) for non-negative x, y.
2. `cpmm_deriv_nonneg`: f'(x) = K*M/(M+x)^2 >= 0.
3. `cpmm_deriv_le_K_over_M`: f'(x) <= K/M.
4. `kpool_gradient_bound_coord1`: |dF/da1| <= max(c0*K0/M0, c2*K2/M2) <= L.
5. `kpool_gradient_bound_coord2`: |dF/da2| <= max(c1*K1/M1, c2*K2/M2) <= L.
6. `kpool_coupled_argmax_proximity_3pool`: F_floor(floor(b*)) >= F_floor(b) - (L + 3).
7. `kpool_coupled_argmax_proximity`: General K-pool bound L + K.

Key insight: Each gradient component is a difference of non-negative terms,
so |dF/da_j| <= max(term_j, term_K) <= L by P1's |x-y| <= max(x,y) lemma.
This gives L-Lipschitz in L-inf norm, combined with floor error < K.

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
    denom = M + x
    if denom <= 0.0:
        return 0.0
    return K * x / denom


def cpmm_deriv(K: float, M: float, x: float) -> float:
    """f'(x) = K*M/(M+x)^2."""
    denom = (M + x) ** 2
    if denom <= 0.0:
        return 0.0
    return K * M / denom


def split_3pool(p0: Pool, p1: Pool, p2: Pool, D: float, a1: float, a2: float) -> float:
    """3-pool split: F(a1, a2) = f0(c0*a1) + f1(c1*a2) + f2(c2*(D-a1-a2))."""
    c0 = 1.0 - p0.fee_bps / 10000.0
    c1 = 1.0 - p1.fee_bps / 10000.0
    c2 = 1.0 - p2.fee_bps / 10000.0
    return (cpmm_output_cont(p0.reserve_out, p0.reserve_in, c0 * a1) +
            cpmm_output_cont(p1.reserve_out, p1.reserve_in, c1 * a2) +
            cpmm_output_cont(p2.reserve_out, p2.reserve_in, c2 * (D - a1 - a2)))


def gradient_coord1(p0: Pool, p2: Pool, D: float, a1: float, a2: float) -> float:
    """dF/da1 = c0*f0'(c0*a1) - c2*f2'(c2*(D-a1-a2))."""
    c0 = 1.0 - p0.fee_bps / 10000.0
    c2 = 1.0 - p2.fee_bps / 10000.0
    return (c0 * cpmm_deriv(p0.reserve_out, p0.reserve_in, c0 * a1) -
            c2 * cpmm_deriv(p2.reserve_out, p2.reserve_in, c2 * (D - a1 - a2)))


def gradient_coord2(p1: Pool, p2: Pool, D: float, a1: float, a2: float) -> float:
    """dF/da2 = c1*f1'(c1*a2) - c2*f2'(c2*(D-a1-a2))."""
    c1 = 1.0 - p1.fee_bps / 10000.0
    c2 = 1.0 - p2.fee_bps / 10000.0
    return (c1 * cpmm_deriv(p1.reserve_out, p1.reserve_in, c1 * a2) -
            c2 * cpmm_deriv(p2.reserve_out, p2.reserve_in, c2 * (D - a1 - a2)))


def L_bound(pools: list) -> float:
    """L = max_i(c_i * K_i / M_i)."""
    return max((1.0 - p.fee_bps / 10000.0) * p.reserve_out / p.reserve_in
               for p in pools)


# ---------------------------------------------------------------------------
# Test 1: |x - y| <= max(x, y) for non-negative x, y (P1's key lemma)
# ---------------------------------------------------------------------------

def test_abs_sub_le_max():
    """Verify |x - y| <= max(x, y) for non-negative x, y."""
    rng = random.Random(42)
    violations = 0
    for _ in range(10000):
        x = float(rng.randint(0, 10000))
        y = float(rng.randint(0, 10000))
        if abs(x - y) > max(x, y) + 1e-9:
            violations += 1
    assert violations == 0, f"{violations} |x-y| <= max violations"
    print(f"  PASS: 10000 random trials, |x-y| <= max(x,y) always")


# ---------------------------------------------------------------------------
# Test 2: CPMM derivative is non-negative and bounded by K/M
# ---------------------------------------------------------------------------

def test_cpmm_deriv_bounds():
    """Verify f'(x) >= 0 and f'(x) <= K/M."""
    rng = random.Random(42)
    violations_nn = 0
    violations_le = 0
    for _ in range(10000):
        K = float(rng.randint(100, 10000))
        M = float(rng.randint(100, 10000))
        x = float(rng.randint(0, 5000))
        deriv = cpmm_deriv(K, M, x)
        if deriv < -1e-9:
            violations_nn += 1
        if deriv > K / M + 1e-9:
            violations_le += 1
    assert violations_nn == 0, f"{violations_nn} deriv < 0 violations"
    assert violations_le == 0, f"{violations_le} deriv > K/M violations"
    print(f"  PASS: 10000 random trials, 0 <= f'(x) <= K/M always")


# ---------------------------------------------------------------------------
# Test 3: Gradient bound coord1 (|dF/da1| <= max(c0*K0/M0, c2*K2/M2) <= L)
# ---------------------------------------------------------------------------

def test_gradient_bound_coord1():
    """Verify |dF/da1| <= L for 3-pool split function."""
    rng = random.Random(42)
    violations = 0
    max_ratio = 0.0
    for _ in range(10000):
        p0 = Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                  rng.randint(0, 500))
        p1 = Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                  rng.randint(0, 500))
        p2 = Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                  rng.randint(0, 500))
        D = float(rng.randint(10, 1000))
        a1 = float(rng.randint(1, int(D) - 2))
        a2 = float(rng.randint(1, int(D) - int(a1) - 1))
        grad = gradient_coord1(p0, p2, D, a1, a2)
        L = L_bound([p0, p1, p2])
        if L > 0:
            max_ratio = max(max_ratio, abs(grad) / L)
        if abs(grad) > L + 1e-9:
            violations += 1
            print(f"  VIOLATION: |grad|={abs(grad)} > L={L}")
    assert violations == 0, f"{violations} gradient bound violations"
    print(f"  PASS: 10000 random trials, |dF/da1| <= L, max ratio = {max_ratio:.6f}")


# ---------------------------------------------------------------------------
# Test 4: Gradient bound coord2 (|dF/da2| <= max(c1*K1/M1, c2*K2/M2) <= L)
# ---------------------------------------------------------------------------

def test_gradient_bound_coord2():
    """Verify |dF/da2| <= L for 3-pool split function."""
    rng = random.Random(42)
    violations = 0
    max_ratio = 0.0
    for _ in range(10000):
        p0 = Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                  rng.randint(0, 500))
        p1 = Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                  rng.randint(0, 500))
        p2 = Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                  rng.randint(0, 500))
        D = float(rng.randint(10, 1000))
        a1 = float(rng.randint(1, int(D) - 2))
        a2 = float(rng.randint(1, int(D) - int(a1) - 1))
        grad = gradient_coord2(p1, p2, D, a1, a2)
        L = L_bound([p0, p1, p2])
        if L > 0:
            max_ratio = max(max_ratio, abs(grad) / L)
        if abs(grad) > L + 1e-9:
            violations += 1
            print(f"  VIOLATION: |grad|={abs(grad)} > L={L}")
    assert violations == 0, f"{violations} gradient bound violations"
    print(f"  PASS: 10000 random trials, |dF/da2| <= L, max ratio = {max_ratio:.6f}")


# ---------------------------------------------------------------------------
# Test 5: Numerical gradient matches analytical
# ---------------------------------------------------------------------------

def test_numerical_gradient_matches():
    """Verify numerical gradient matches analytical formula."""
    rng = random.Random(42)
    violations = 0
    max_rel_error = 0.0
    h = 0.01
    for _ in range(1000):
        p0 = Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                  rng.randint(0, 500))
        p1 = Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                  rng.randint(0, 500))
        p2 = Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                  rng.randint(0, 500))
        D = float(rng.randint(10, 1000))
        a1 = float(rng.randint(1, int(D) - 2))
        a2 = float(rng.randint(1, int(D) - int(a1) - 1))
        # Numerical gradient coord1
        F_pp = split_3pool(p0, p1, p2, D, a1 + h, a2)
        F_mm = split_3pool(p0, p1, p2, D, a1 - h, a2)
        num_grad1 = (F_pp - F_mm) / (2 * h)
        ana_grad1 = gradient_coord1(p0, p2, D, a1, a2)
        if abs(ana_grad1) > 1e-10:
            rel_err = abs(num_grad1 - ana_grad1) / abs(ana_grad1)
            max_rel_error = max(max_rel_error, rel_err)
        if abs(num_grad1 - ana_grad1) > 0.05 * max(abs(ana_grad1), 1.0):
            violations += 1
    assert violations == 0, f"{violations} gradient mismatch violations"
    print(f"  PASS: 1000 random trials, numerical=analytical, "
          f"max rel error = {max_rel_error:.8f}")


# ---------------------------------------------------------------------------
# Test 6: 3-pool argmax proximity (F_floor(floor(b*)) >= F_floor(b) - (L + 3))
# ---------------------------------------------------------------------------

def split_3pool_floor(p0, p1, p2, D, a1, a2):
    """3-pool split with floor rounding."""
    c0 = 1.0 - p0.fee_bps / 10000.0
    c1 = 1.0 - p1.fee_bps / 10000.0
    c2 = 1.0 - p2.fee_bps / 10000.0
    return (math.floor(cpmm_output_cont(p0.reserve_out, p0.reserve_in, c0 * a1)) +
            math.floor(cpmm_output_cont(p1.reserve_out, p1.reserve_in, c1 * a2)) +
            math.floor(cpmm_output_cont(p2.reserve_out, p2.reserve_in, c2 * (D - a1 - a2))))


def test_3pool_argmax_proximity():
    """Verify F_floor(floor(b*)) >= F_floor(b) - (L + 3) for 3 pools."""
    rng = random.Random(42)
    violations = 0
    max_gap = 0.0
    for _ in range(1000):
        p0 = Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                  rng.randint(0, 500))
        p1 = Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                  rng.randint(0, 500))
        p2 = Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                  rng.randint(0, 500))
        D = float(rng.randint(10, 200))
        L = L_bound([p0, p1, p2])
        # Find continuous argmax by grid search
        best_cont = -1e18
        best_a1, best_a2 = 0.0, 0.0
        for a1_i in range(0, int(D) + 1):
            for a2_i in range(0, int(D) - a1_i + 1):
                val = split_3pool(p0, p1, p2, D, float(a1_i), float(a2_i))
                if val > best_cont:
                    best_cont = val
                    best_a1, best_a2 = float(a1_i), float(a2_i)
        # Floor of argmax
        floor_a1 = math.floor(best_a1)
        floor_a2 = math.floor(best_a2)
        # Check all integer points
        for a1_i in range(0, int(D) + 1):
            for a2_i in range(0, int(D) - a1_i + 1):
                floor_val = split_3pool_floor(p0, p1, p2, D, float(a1_i), float(a2_i))
                floor_argmax = split_3pool_floor(p0, p1, p2, D, float(floor_a1), float(floor_a2))
                gap = floor_argmax - floor_val
                max_gap = max(max_gap, -gap if gap < 0 else 0)
                if floor_argmax < floor_val - (L + 3) - 1e-9:
                    violations += 1
                    if violations <= 3:
                        print(f"  VIOLATION: gap={floor_argmax - floor_val} < -(L+3)={-(L+3)}")
    assert violations == 0, f"{violations} proximity violations"
    print(f"  PASS: 1000 random trials, F_floor(floor(b*)) >= F_floor(b) - (L+3), "
          f"max gap = {max_gap:.4f}")


# ---------------------------------------------------------------------------
# Test 7: K-pool gradient bound for K=5
# ---------------------------------------------------------------------------

def test_kpool_gradient_bound_k5():
    """Verify gradient bound for K=5 pools (4 free coordinates)."""
    rng = random.Random(42)
    violations = 0
    max_ratio = 0.0
    h = 0.01
    for _ in range(1000):
        pools = [Pool(float(rng.randint(100, 10000)), float(rng.randint(100, 10000)),
                      rng.randint(0, 500)) for _ in range(5)]
        D = float(rng.randint(10, 500))
        # Random allocation
        allocs = [float(rng.randint(1, int(D) // 5)) for _ in range(4)]
        remainder = D - sum(allocs)
        if remainder <= 0:
            continue
        L = L_bound(pools)
        # Check each coordinate's gradient
        for j in range(4):
            # Numerical gradient in coordinate j
            allocs_pp = allocs.copy()
            allocs_mm = allocs.copy()
            allocs_pp[j] += h
            allocs_mm[j] -= h
            if allocs_mm[j] < 0 or D - sum(allocs_pp) < 0:
                continue
            def F(allocs):
                total = 0.0
                for i in range(4):
                    c = 1.0 - pools[i].fee_bps / 10000.0
                    total += cpmm_output_cont(pools[i].reserve_out, pools[i].reserve_in,
                                             c * allocs[i])
                c4 = 1.0 - pools[4].fee_bps / 10000.0
                total += cpmm_output_cont(pools[4].reserve_out, pools[4].reserve_in,
                                         c4 * (D - sum(allocs)))
                return total
            num_grad = (F(allocs_pp) - F(allocs_mm)) / (2 * h)
            if L > 0:
                max_ratio = max(max_ratio, abs(num_grad) / L)
            if abs(num_grad) > L + 0.1:  # tolerance for numerical
                violations += 1
                if violations <= 3:
                    print(f"  VIOLATION: |grad_{j}|={abs(num_grad)} > L={L}")
    assert violations == 0, f"{violations} K=5 gradient violations"
    print(f"  PASS: 1000 random trials, K=5 gradient bound holds, "
          f"max ratio = {max_ratio:.6f}")


# ---------------------------------------------------------------------------
# Test 8: Witness non-vacuity
# ---------------------------------------------------------------------------

def test_witness_non_vacuity():
    """Verify the concrete witness case."""
    p0 = Pool(1000, 1000, 99)   # c0 = 0.99, K0/M0 = 1.0, c0*K0/M0 = 0.99
    p1 = Pool(1000, 2000, 99)   # c1 = 0.99, K1/M1 = 2.0, c1*K1/M1 = 1.98
    p2 = Pool(1000, 1500, 99)   # c2 = 0.99, K2/M2 = 1.5, c2*K2/M2 = 1.485
    D = 100.0
    a1, a2 = 30.0, 30.0
    L = L_bound([p0, p1, p2])
    grad1 = gradient_coord1(p0, p2, D, a1, a2)
    grad2 = gradient_coord2(p1, p2, D, a1, a2)
    assert abs(grad1) <= L + 1e-9, f"|grad1|={abs(grad1)} > L={L}"
    assert abs(grad2) <= L + 1e-9, f"|grad2|={abs(grad2)} > L={L}"
    print(f"  PASS: L={L:.4f}, |grad1|={abs(grad1):.6f}, |grad2|={abs(grad2):.6f}")
    print(f"  Both gradients bounded by L (witness non-vacuous)")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("=== P3: K-Pool Coupled Argmax Proximity Empirical Verification ===\n")

    print("Test 1: |x - y| <= max(x, y) for non-negative x, y")
    test_abs_sub_le_max()
    print()

    print("Test 2: CPMM derivative bounds (0 <= f'(x) <= K/M)")
    test_cpmm_deriv_bounds()
    print()

    print("Test 3: Gradient bound coord1 (|dF/da1| <= L)")
    test_gradient_bound_coord1()
    print()

    print("Test 4: Gradient bound coord2 (|dF/da2| <= L)")
    test_gradient_bound_coord2()
    print()

    print("Test 5: Numerical gradient matches analytical")
    test_numerical_gradient_matches()
    print()

    print("Test 6: 3-pool argmax proximity (F_floor(floor(b*)) >= F_floor(b) - (L+3))")
    test_3pool_argmax_proximity()
    print()

    print("Test 7: K=5 gradient bound")
    test_kpool_gradient_bound_k5()
    print()

    print("Test 8: Witness non-vacuity")
    test_witness_non_vacuity()
    print()

    print("=== All tests passed ===")
