#!/usr/bin/env python3
"""Empirical verification of the coupled Lipschitz bound (P1).

Verifies the Lean theorem `split_lipschitz_coupled` in
`lean-mathlib/Proofs/CeilingFeeRounding.lean`:

    |splitCont(x) - splitCont(y)| <= max(c0*K0/M0, c1*K1/M1) * |x - y|

This is tighter than the triangle-inequality bound:

    |splitCont(x) - splitCont(y)| <= (K0/M0 + K1/M1) * |x - y|

Key insight: the split difference b0 + b1 has opposite-sign components
(pool 0 increases with the split variable, pool 1 decreases), so
|b0 + b1| <= max(|b0|, |b1|) instead of |b0| + |b1|.

Tests:
1. Coupled bound holds (L = max(c0*K0/M0, c1*K1/M1))
2. Coupled bound is tighter than sum bound (K0/M0 + K1/M1)
3. Opposite-sign property (b0 * b1 <= 0)
4. Exact Lipschitz constant <= L (L is an upper bound, not exact)
5. Witness non-vacuity

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
    """cpmmOutputCont K M x = K * x / (M + x). Matches Lean."""
    if M + x <= 0.0:
        return 0.0
    return K * x / (M + x)


def split_function_cont(p0: Pool, p1: Pool, D: float, a: float) -> float:
    """splitFunctionCont: continuous fee split. Matches Lean."""
    c0 = 1.0 - p0.fee_bps / 10000.0
    c1 = 1.0 - p1.fee_bps / 10000.0
    return cpmm_output_cont(p0.reserve_out, p0.reserve_in, c0 * a) + \
           cpmm_output_cont(p1.reserve_out, p1.reserve_in, c1 * (D - a))


def per_pool_lipschitz(K: float, M: float) -> float:
    """K/M: per-pool output Lipschitz constant at x=0."""
    if M <= 0:
        return 0.0
    return K / M


def coupled_lipschitz(p0: Pool, p1: Pool) -> float:
    """L = max(c0*K0/M0, c1*K1/M1): coupled split Lipschitz."""
    c0 = 1.0 - p0.fee_bps / 10000.0
    c1 = 1.0 - p1.fee_bps / 10000.0
    return max(c0 * p0.reserve_out / p0.reserve_in,
               c1 * p1.reserve_out / p1.reserve_in)


def sum_lipschitz(p0: Pool, p1: Pool) -> float:
    """K0/M0 + K1/M1: triangle-inequality (sum) Lipschitz."""
    return p0.reserve_out / p0.reserve_in + p1.reserve_out / p1.reserve_in


def split_diff_components(p0: Pool, p1: Pool, D: float, x: float, y: float):
    """Return (b0, b1) where split(x) - split(y) = b0 + b1."""
    c0 = 1.0 - p0.fee_bps / 10000.0
    c1 = 1.0 - p1.fee_bps / 10000.0
    b0 = cpmm_output_cont(p0.reserve_out, p0.reserve_in, c0 * x) - \
         cpmm_output_cont(p0.reserve_out, p0.reserve_in, c0 * y)
    b1 = cpmm_output_cont(p1.reserve_out, p1.reserve_in, c1 * (D - x)) - \
         cpmm_output_cont(p1.reserve_out, p1.reserve_in, c1 * (D - y))
    return b0, b1


# ---------------------------------------------------------------------------
# Test 1: Coupled bound holds
# |split(x) - split(y)| <= L * |x - y|
# ---------------------------------------------------------------------------

def test_coupled_bound_holds():
    """Verify coupled Lipschitz bound holds for all random trials."""
    rng = random.Random(42)
    violations = 0
    max_ratio = 0.0  # actual / coupled_bound
    for _ in range(10000):
        K0 = float(rng.randint(100, 10000))
        M0 = float(rng.randint(100, 10000))
        K1 = float(rng.randint(100, 10000))
        M1 = float(rng.randint(100, 10000))
        fee0 = rng.randint(0, 500)
        fee1 = rng.randint(0, 500)
        D = float(rng.randint(10, 1000))
        x = float(rng.randint(0, int(D)))
        y = float(rng.randint(0, int(D)))
        p0 = Pool(M0, K0, fee0)
        p1 = Pool(M1, K1, fee1)
        actual = abs(split_function_cont(p0, p1, D, x) -
                     split_function_cont(p0, p1, D, y))
        L = coupled_lipschitz(p0, p1)
        bound = L * abs(x - y)
        if bound > 0:
            max_ratio = max(max_ratio, actual / bound)
        if actual > bound + 1e-9:
            violations += 1
            print(f"  VIOLATION: actual={actual} bound={bound} "
                  f"K0={K0} M0={M0} K1={K1} M1={M1} x={x} y={y}")
    assert violations == 0, f"{violations} coupled bound violations"
    print(f"  PASS: 10000 random trials, 0 violations, "
          f"max actual/bound ratio = {max_ratio:.6f}")


# ---------------------------------------------------------------------------
# Test 2: Coupled bound is tighter than sum bound
# L = max(c0*K0/M0, c1*K1/M1) <= K0/M0 + K1/M1 = sum
# ---------------------------------------------------------------------------

def test_coupled_tighter_than_sum():
    """Verify coupled bound is always <= sum bound."""
    rng = random.Random(42)
    coupled_tighter = 0
    equal = 0
    max_tightness = 0.0  # coupled / sum (lower is tighter)
    for _ in range(10000):
        K0 = float(rng.randint(100, 10000))
        M0 = float(rng.randint(100, 10000))
        K1 = float(rng.randint(100, 10000))
        M1 = float(rng.randint(100, 10000))
        fee0 = rng.randint(0, 500)
        fee1 = rng.randint(0, 500)
        p0 = Pool(M0, K0, fee0)
        p1 = Pool(M1, K1, fee1)
        L = coupled_lipschitz(p0, p1)
        S = sum_lipschitz(p0, p1)
        ratio = L / S if S > 0 else 1.0
        max_tightness = min(max_tightness, ratio) if max_tightness > 0 else ratio
        if L < S - 1e-9:
            coupled_tighter += 1
        elif abs(L - S) < 1e-9:
            equal += 1
    assert coupled_tighter + equal == 10000
    print(f"  PASS: {coupled_tighter} cases coupled < sum, {equal} equal")
    print(f"  Coupled bound is always <= sum bound (tightness ratio <= 1.0)")


# ---------------------------------------------------------------------------
# Test 3: Opposite-sign property
# b0 * b1 <= 0 (pool 0 increases, pool 1 decreases with split variable)
# ---------------------------------------------------------------------------

def test_opposite_sign_property():
    """Verify b0 * b1 <= 0 for all random trials."""
    rng = random.Random(42)
    violations = 0
    for _ in range(10000):
        K0 = float(rng.randint(100, 10000))
        M0 = float(rng.randint(100, 10000))
        K1 = float(rng.randint(100, 10000))
        M1 = float(rng.randint(100, 10000))
        fee0 = rng.randint(0, 500)
        fee1 = rng.randint(0, 500)
        D = float(rng.randint(10, 1000))
        x = float(rng.randint(0, int(D)))
        y = float(rng.randint(0, int(D)))
        p0 = Pool(M0, K0, fee0)
        p1 = Pool(M1, K1, fee1)
        b0, b1 = split_diff_components(p0, p1, D, x, y)
        product = b0 * b1
        if product > 1e-9:
            violations += 1
            print(f"  VIOLATION: b0*b1={product} b0={b0} b1={b1} "
                  f"K0={K0} M0={M0} K1={K1} M1={M1} x={x} y={y}")
    assert violations == 0, f"{violations} opposite-sign violations"
    print(f"  PASS: 10000 random trials, b0*b1 <= 0 always (opposite signs)")


# ---------------------------------------------------------------------------
# Test 4: Exact Lipschitz constant <= L
# L is an upper bound, not the exact constant
# ---------------------------------------------------------------------------

def test_exact_lipschitz_le_coupled():
    """Verify exact sup|f'(a)| <= L for random pool configs."""
    rng = random.Random(42)
    violations = 0
    max_ratio = 0.0  # exact / coupled
    for _ in range(1000):
        K0 = float(rng.randint(100, 10000))
        M0 = float(rng.randint(100, 10000))
        K1 = float(rng.randint(100, 10000))
        M1 = float(rng.randint(100, 10000))
        fee0 = rng.randint(0, 500)
        fee1 = rng.randint(0, 500)
        D = float(rng.randint(10, 1000))
        p0 = Pool(M0, K0, fee0)
        p1 = Pool(M1, K1, fee1)
        c0 = 1.0 - fee0 / 10000.0
        c1 = 1.0 - fee1 / 10000.0
        # Compute sup |f'(a)| by sampling
        max_deriv = 0.0
        for i in range(1000):
            a = D * i / 999.0
            t0 = c0 * K0 * M0 / (M0 + c0 * a) ** 2
            t1 = c1 * K1 * M1 / (M1 + c1 * (D - a)) ** 2
            deriv = abs(t0 - t1)
            max_deriv = max(max_deriv, deriv)
        L = coupled_lipschitz(p0, p1)
        if L > 0:
            max_ratio = max(max_ratio, max_deriv / L)
        if max_deriv > L + 1e-9:
            violations += 1
            print(f"  VIOLATION: exact={max_deriv} L={L} "
                  f"K0={K0} M0={M0} K1={K1} M1={M1}")
    assert violations == 0, f"{violations} exact > coupled violations"
    print(f"  PASS: 1000 random trials, exact sup|f'| <= L always, "
          f"max exact/L ratio = {max_ratio:.6f}")


# ---------------------------------------------------------------------------
# Test 5: Witness non-vacuity
# Concrete case showing coupled bound is strictly tighter
# ---------------------------------------------------------------------------

def test_witness_non_vacuity():
    """Verify the concrete witness case from Lean."""
    p0 = Pool(1000, 1000, 99)   # c0 = 0.99
    p1 = Pool(1000, 2000, 99)   # c1 = 0.99
    D = 100.0
    x, y = 50.0, 49.0
    actual = abs(split_function_cont(p0, p1, D, x) -
                 split_function_cont(p0, p1, D, y))
    L = coupled_lipschitz(p0, p1)
    S = sum_lipschitz(p0, p1)
    diff = abs(x - y)
    coupled_bound = L * diff
    sum_bound = S * diff
    assert actual <= coupled_bound + 1e-9, \
        f"actual={actual} > coupled={coupled_bound}"
    assert coupled_bound < sum_bound, \
        f"coupled={coupled_bound} >= sum={sum_bound}"
    assert coupled_bound < 2.0, \
        f"coupled={coupled_bound} >= 2.0"
    print(f"  PASS: actual={actual:.6f}, coupled={coupled_bound:.4f}, "
          f"sum={sum_bound:.4f}")
    print(f"  Coupled bound is {coupled_bound/sum_bound:.1%} of sum bound")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("=== P1: Coupled Lipschitz Bound Empirical Verification ===\n")

    print("Test 1: Coupled bound holds (split_lipschitz_coupled)")
    test_coupled_bound_holds()
    print()

    print("Test 2: Coupled bound tighter than sum bound")
    test_coupled_tighter_than_sum()
    print()

    print("Test 3: Opposite-sign property (b0 * b1 <= 0)")
    test_opposite_sign_property()
    print()

    print("Test 4: Exact Lipschitz <= L (L is upper bound)")
    test_exact_lipschitz_le_coupled()
    print()

    print("Test 5: Witness non-vacuity")
    test_witness_non_vacuity()
    print()

    print("=== All tests passed ===")
