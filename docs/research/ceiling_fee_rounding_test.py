#!/usr/bin/env python3
"""Empirical verification of CeilingFeeRounding.lean Lean theorems.

This file empirically verifies the formal theorems proven in
lean-mathlib/Proofs/CeilingFeeRounding.lean:

1. cpmm_output_lipschitz_wrt_net:
   |f(x1) - f(x2)| <= (K/M) * |x1 - x2|  for K >= 0, M > 0, x >= 0

2. cpmm_prod_floor_error_bound_directed:
   0 <= cont(clean) - prodFloor(prod) < K/M + 1
   when net_prod <= net_cont and net_cont - net_prod < 1

3. split_prod_floor_error_bound:
   0 <= splitCont - splitProdFloor < K0/M0 + K1/M1 + 2

4. cpmm_prod_discrete_argmax_proximity:
   splitProdFloor(floor(b*)) >= splitProdFloor(b) - (L + K0/M0 + K1/M1 + 2)

5. split_lipschitz_coupled:
   |splitCont(x) - splitCont(y)| <= L * |x - y|
   where L = max(c0*K0/M0, c1*K1/M1)

The Lean bounds use K/M (per-pool output Lipschitz at x=0), which is the
worst case. The empirical bounds in discrete_argmax_proximity_test.py use
L = max(c0*K0/M0, c1*K1/M1) (split Lipschitz with continuous fee), which
is a formal coupled upper bound for the continuous split objective.

Relationship:
  gross_bound = L + K0/M0 + K1/M1 + 2     (Lean)
  low_fee_bound = 3L + 2                  (discrete_argmax_proximity_test.py)

Neither bound is universally tighter under fees. The gross bound is the
universal production lane; the low-fee bound is an empirical regression.

Non-claims:
- The ceiling fee perturbation bound (net_cont - net_prod < 1) is an external
  hypothesis in Lean, verified empirically here.
- The effective-L constants are not universal production theorems.
- The coupled L is an upper bound, not the exact split Lipschitz constant.
- Strong concavity parameter m is an external hypothesis.

Determinism: All tests use fixed seeds. No real time, RNG, network, or fs.
"""

import math
import random
from dataclasses import dataclass


@dataclass(frozen=True)
class Pool:
    """CPMM pool: (reserve_in=M, reserve_out=K, fee_bps)."""
    reserve_in: int
    reserve_out: int
    fee_bps: int


# ---------------------------------------------------------------------------
# Lean model functions (match CeilingFeeRounding.lean definitions)
# ---------------------------------------------------------------------------

def cpmm_output_cont(K: float, M: float, x: float) -> float:
    """cpmmOutputCont K M x = K * x / (M + x). Matches Lean definition."""
    if x <= 0.0:
        return 0.0
    if M + x <= 0.0:
        return 0.0
    return K * x / (M + x)


def cpmm_output_prod_floor(K: float, M: float, x_net: float) -> float:
    """cpmmOutputProdFloor K M x = floor(K * x / (M + x)). Matches Lean."""
    cont = cpmm_output_cont(K, M, x_net)
    return float(math.floor(cont))


def split_function_cont(K0, M0, c0, K1, M1, c1, D, a):
    """splitFunctionCont: continuous fee split. Matches Lean."""
    return cpmm_output_cont(K0, M0, c0 * a) + cpmm_output_cont(K1, M1, c1 * (D - a))


def split_derivative(K0, M0, c0, K1, M1, c1, D, a):
    """Derivative of splitFunctionCont with respect to the split a."""
    t0 = c0 * K0 * M0 / ((M0 + c0 * a) ** 2)
    t1 = c1 * K1 * M1 / ((M1 + c1 * (D - a)) ** 2)
    return t0 - t1


def exact_boundary_split_lipschitz(K0, M0, c0, K1, M1, c1, D):
    """Exact Lipschitz for this concave split is attained at an interval end."""
    return max(abs(split_derivative(K0, M0, c0, K1, M1, c1, D, 0.0)),
               abs(split_derivative(K0, M0, c0, K1, M1, c1, D, D)))


def split_function_prod_floor(K0, M0, net0, K1, M1, net1):
    """splitFunctionProdFloor: production floored split. Matches Lean."""
    return cpmm_output_prod_floor(K0, M0, net0) + cpmm_output_prod_floor(K1, M1, net1)


# ---------------------------------------------------------------------------
# Production ceiling-fee model (matches src/core/cpmm.py v8)
# ---------------------------------------------------------------------------

def ceil_fee(amount_in: int, fee_bps: int) -> int:
    """Ceiling fee: ceil(amount_in * fee_bps / 10000)."""
    if amount_in <= 0:
        return 0
    return (amount_in * fee_bps + 9999) // 10000


def prod_net(amount_in: int, fee_bps: int) -> int:
    """Production net input after ceiling fee."""
    return amount_in - ceil_fee(amount_in, fee_bps)


def cont_net(amount_in: float, fee_bps: int) -> float:
    """Continuous net input: amount_in * (1 - fee_bps/10000)."""
    return amount_in * (1.0 - fee_bps / 10000.0)


# ---------------------------------------------------------------------------
# Lipschitz constants
# ---------------------------------------------------------------------------

def per_pool_lipschitz(K: float, M: float) -> float:
    """K/M: per-pool output Lipschitz constant (worst case at x=0)."""
    if M <= 0:
        return 0.0
    return K / M


def split_lipschitz(K0, M0, c0, K1, M1, c1) -> float:
    """L = max(c0*K0/M0, c1*K1/M1): split Lipschitz with continuous fee."""
    return max(c0 * K0 / M0 if M0 > 0 else 0.0,
               c1 * K1 / M1 if M1 > 0 else 0.0)


# ---------------------------------------------------------------------------
# Test 1: Per-pool output Lipschitz (cpmm_output_lipschitz_wrt_net)
#          |f(x1) - f(x2)| <= (K/M) * |x1 - x2|
# ---------------------------------------------------------------------------

def test_per_pool_lipschitz():
    """Verify |cpmmOutputCont(K,M,x1) - cpmmOutputCont(K,M,x2)| <= (K/M)*|x1-x2|."""
    rng = random.Random(42)
    violations = 0
    for _ in range(10000):
        K = float(rng.randint(0, 10000))
        M = float(rng.randint(1, 10000))
        x1 = float(rng.randint(0, 10000))
        x2 = float(rng.randint(0, 10000))
        f1 = cpmm_output_cont(K, M, x1)
        f2 = cpmm_output_cont(K, M, x2)
        lip = per_pool_lipschitz(K, M)
        actual = abs(f1 - f2)
        bound = lip * abs(x1 - x2)
        if actual > bound + 1e-9:
            violations += 1
            print(f"  VIOLATION: K={K} M={M} x1={x1} x2={x2} "
                  f"actual={actual} bound={bound}")
    assert violations == 0, f"{violations} Lipschitz violations"
    print(f"  PASS: 10000 random trials, 0 violations")


# ---------------------------------------------------------------------------
# Test 1b: Coupled split Lipschitz bound (split_lipschitz_coupled)
#          |splitCont(x) - splitCont(y)| <= L * |x - y|
# ---------------------------------------------------------------------------

def test_coupled_split_lipschitz_max_bound():
    """Verify the formal max-bound and compare it to the exact boundary slope."""
    rng = random.Random(20260711)
    violations = 0
    exact_over_l = 0
    strict_sum_improvements = 0
    max_ratio = 0.0
    max_exact_ratio = 0.0
    worst = None
    for _ in range(1000):
        K0 = float(rng.randint(1, 10000))
        M0 = float(rng.randint(1, 10000))
        K1 = float(rng.randint(1, 10000))
        M1 = float(rng.randint(1, 10000))
        fee0 = rng.randint(0, 3000)
        fee1 = rng.randint(0, 3000)
        c0 = 1.0 - fee0 / 10000.0
        c1 = 1.0 - fee1 / 10000.0
        D = float(rng.randint(1, 10000))
        L = split_lipschitz(K0, M0, c0, K1, M1, c1)
        sum_L = c0 * K0 / M0 + c1 * K1 / M1
        exact_L = exact_boundary_split_lipschitz(K0, M0, c0, K1, M1, c1, D)
        if exact_L > L + 1e-9:
            exact_over_l += 1
        if L + 1e-12 < sum_L:
            strict_sum_improvements += 1
        if L > 0:
            max_exact_ratio = max(max_exact_ratio, exact_L / L)
        for _pair in range(20):
            x = rng.random() * D
            y = rng.random() * D
            actual = abs(split_function_cont(K0, M0, c0, K1, M1, c1, D, x) -
                         split_function_cont(K0, M0, c0, K1, M1, c1, D, y))
            bound = L * abs(x - y)
            ratio = actual / bound if bound > 0 else 0.0
            if ratio > max_ratio:
                max_ratio = ratio
                worst = (K0, M0, c0, K1, M1, c1, D, x, y, actual, bound)
            if actual > bound + 1e-8:
                violations += 1
                print(f"  VIOLATION: actual={actual} bound={bound} "
                      f"case={(K0, M0, c0, K1, M1, c1, D, x, y)}")
    assert violations == 0, f"{violations} coupled Lipschitz violations"
    assert exact_over_l == 0, f"{exact_over_l} exact boundary constants exceed L"
    assert strict_sum_improvements > 0, "No case showed max-bound improvement over sum-bound"
    print("  PASS: 1000 configs, 20000 split pairs, 0 violations, "
          f"strict_sum_improvements={strict_sum_improvements}, "
          f"max_pair_ratio={max_ratio:.6f}, max_exact_ratio={max_exact_ratio:.6f}, "
          f"worst={worst}")


# ---------------------------------------------------------------------------
# Test 2: Ceiling fee perturbation bound (external hypothesis)
#          net_cont - net_prod < 1
# ---------------------------------------------------------------------------

def test_ceil_fee_perturbation():
    """Verify cont_net(a) - prod_net(a) < 1 for all integer a."""
    rng = random.Random(42)
    violations = 0
    max_pert = 0.0
    for _ in range(10000):
        a = rng.randint(1, 1000000)
        fee_bps = rng.randint(0, 1000)
        nc = cont_net(float(a), fee_bps)
        np_ = float(prod_net(a, fee_bps))
        pert = nc - np_
        max_pert = max(max_pert, pert)
        if pert >= 1.0 + 1e-12:
            violations += 1
            print(f"  VIOLATION: a={a} fee_bps={fee_bps} pert={pert}")
    assert violations == 0, f"{violations} perturbation violations"
    assert max_pert < 1.0, f"max perturbation {max_pert} >= 1.0"
    print(f"  PASS: 10000 random trials, max perturbation = {max_pert:.6f} < 1.0")


# ---------------------------------------------------------------------------
# Test 3: Per-pool production floor error (cpmm_prod_floor_error_bound_directed)
#          0 <= cont(clean) - prodFloor(prod) < K/M + 1
# ---------------------------------------------------------------------------

def test_per_pool_floor_error():
    """Verify 0 <= cont(clean) - prodFloor(prod) < K/M + 1."""
    rng = random.Random(42)
    violations = 0
    max_err = 0.0
    max_bound = 0.0
    for _ in range(10000):
        K = float(rng.randint(0, 10000))
        M = float(rng.randint(1, 10000))
        fee_bps = rng.randint(0, 1000)
        a = rng.randint(1, 100000)
        net_cont = cont_net(float(a), fee_bps)
        net_prod = float(prod_net(a, fee_bps))
        if net_prod < 0:
            continue
        cont_val = cpmm_output_cont(K, M, net_cont)
        floor_val = cpmm_output_prod_floor(K, M, net_prod)
        err = cont_val - floor_val
        bound = per_pool_lipschitz(K, M) + 1.0
        max_err = max(max_err, err)
        max_bound = max(max_bound, bound)
        if err < -1e-9:
            violations += 1
            print(f"  LOWER VIOLATION: K={K} M={M} err={err}")
        if err >= bound + 1e-9:
            violations += 1
            print(f"  UPPER VIOLATION: K={K} M={M} err={err} bound={bound}")
    assert violations == 0, f"{violations} floor error violations"
    print(f"  PASS: 10000 random trials, max error = {max_err:.4f}, "
          f"max bound = {max_bound:.4f}")


# ---------------------------------------------------------------------------
# Test 4: Split production floor error (split_prod_floor_error_bound)
#          0 <= splitCont - splitProdFloor < K0/M0 + K1/M1 + 2
# ---------------------------------------------------------------------------

def test_split_floor_error():
    """Verify 0 <= splitCont - splitProdFloor < K0/M0 + K1/M1 + 2."""
    rng = random.Random(42)
    violations = 0
    max_err = 0.0
    max_bound = 0.0
    for _ in range(10000):
        K0 = float(rng.randint(0, 10000))
        M0 = float(rng.randint(1, 10000))
        K1 = float(rng.randint(0, 10000))
        M1 = float(rng.randint(1, 10000))
        fee0 = rng.randint(0, 1000)
        fee1 = rng.randint(0, 1000)
        D = rng.randint(1, 10000)
        a = rng.randint(0, D)
        c0 = 1.0 - fee0 / 10000.0
        c1 = 1.0 - fee1 / 10000.0
        net_cont0 = c0 * float(a)
        net_cont1 = c1 * float(D - a)
        net_prod0 = float(prod_net(a, fee0))
        net_prod1 = float(prod_net(D - a, fee1))
        if net_prod0 < 0 or net_prod1 < 0:
            continue
        split_cont = (cpmm_output_cont(K0, M0, net_cont0) +
                      cpmm_output_cont(K1, M1, net_cont1))
        split_floor = (cpmm_output_prod_floor(K0, M0, net_prod0) +
                       cpmm_output_prod_floor(K1, M1, net_prod1))
        err = split_cont - split_floor
        bound = K0 / M0 + K1 / M1 + 2.0
        max_err = max(max_err, err)
        max_bound = max(max_bound, bound)
        if err < -1e-9:
            violations += 1
            print(f"  LOWER VIOLATION: err={err}")
        if err >= bound + 1e-9:
            violations += 1
            print(f"  UPPER VIOLATION: err={err} bound={bound}")
    assert violations == 0, f"{violations} split floor error violations"
    print(f"  PASS: 10000 random trials, max error = {max_err:.4f}, "
          f"max bound = {max_bound:.4f}")


# ---------------------------------------------------------------------------
# Test 5: Production argmax proximity (cpmm_prod_discrete_argmax_proximity)
#          splitProdFloor(floor(b*)) >= splitProdFloor(b) - (L + K0/M0 + K1/M1 + 2)
# ---------------------------------------------------------------------------

def test_prod_argmax_proximity():
    """Verify production argmax proximity bound."""
    rng = random.Random(42)
    violations = 0
    max_gap = 0.0
    max_bound = 0.0
    for _ in range(1000):
        K0 = float(rng.randint(100, 10000))
        M0 = float(rng.randint(100, 10000))
        K1 = float(rng.randint(100, 10000))
        M1 = float(rng.randint(100, 10000))
        fee0 = rng.randint(0, 300)
        fee1 = rng.randint(0, 300)
        D = rng.randint(10, 500)
        c0 = 1.0 - fee0 / 10000.0
        c1 = 1.0 - fee1 / 10000.0

        # Find continuous optimum b* via ternary search
        lo, hi = 0.0, float(D)
        for _ in range(200):
            if hi - lo < 1e-10:
                break
            m1 = lo + (hi - lo) / 3.0
            m2 = hi - (hi - lo) / 3.0
            if split_function_cont(K0, M0, c0, K1, M1, c1, float(D), m1) < \
               split_function_cont(K0, M0, c0, K1, M1, c1, float(D), m2):
                lo = m1
            else:
                hi = m2
        b_star = (lo + hi) / 2.0

        # Compute L (split Lipschitz)
        L = split_lipschitz(K0, M0, c0, K1, M1, c1)

        # Production net inputs at floor(b*) and at a random b
        b_star_floor = int(math.floor(b_star))
        b = rng.randint(0, D)

        net_prod0_star = float(prod_net(b_star_floor, fee0))
        net_prod1_star = float(prod_net(D - b_star_floor, fee1))
        net_prod0_b = float(prod_net(b, fee0))
        net_prod1_b = float(prod_net(D - b, fee1))

        if net_prod0_star < 0 or net_prod1_star < 0:
            continue
        if net_prod0_b < 0 or net_prod1_b < 0:
            continue

        split_floor_star = split_function_prod_floor(
            K0, M0, net_prod0_star, K1, M1, net_prod1_star)
        split_floor_b = split_function_prod_floor(
            K0, M0, net_prod0_b, K1, M1, net_prod1_b)

        gap = split_floor_b - split_floor_star
        bound = L + K0 / M0 + K1 / M1 + 2.0
        max_gap = max(max_gap, gap)
        max_bound = max(max_bound, bound)
        if gap > bound + 1e-9:
            violations += 1
            print(f"  VIOLATION: gap={gap} bound={bound} "
                  f"K0={K0} M0={M0} K1={K1} M1={M1} D={D} b*={b_star:.2f} b={b}")

    assert violations == 0, f"{violations} argmax proximity violations"
    print(f"  PASS: 1000 random trials, max gap = {max_gap:.4f}, "
          f"max bound = {max_bound:.4f}")


# ---------------------------------------------------------------------------
# Test 6: Gross formal bound vs low-fee empirical bound relationship
#          gross = L + K0/M0 + K1/M1 + 2
#          low_fee = 3L + 2
#          Neither is universally tighter; relationship depends on pool params.
# ---------------------------------------------------------------------------

def test_formal_vs_empirical_bound():
    """Document the relationship between formal and empirical bounds.

    gross - low_fee = K0/M0 + K1/M1 - 2L
    where L = max(c0*K0/M0, c1*K1/M1) and c = 1 - fee_bps/10000.

    When c = 1 (no fee): L = max(K0/M0, K1/M1), so formal - empirical
    = K0/M0 + K1/M1 - 2*max(K0/M0, K1/M1) = min - max <= 0.
    So formal <= empirical when no fee.

    When c < 1 (fee): L < max(K0/M0, K1/M1), so the relationship depends
    on the specific values.
    """
    rng = random.Random(20260712)
    gross_stronger = 0
    low_fee_stronger = 0
    equal = 0
    for _ in range(10000):
        K0 = float(rng.randint(100, 10000))
        M0 = float(rng.randint(100, 10000))
        K1 = float(rng.randint(100, 10000))
        M1 = float(rng.randint(100, 10000))
        fee0 = rng.randint(0, 1000)
        fee1 = rng.randint(0, 1000)
        c0 = 1.0 - fee0 / 10000.0
        c1 = 1.0 - fee1 / 10000.0
        L = split_lipschitz(K0, M0, c0, K1, M1, c1)
        gross = L + K0 / M0 + K1 / M1 + 2.0
        low_fee = 3.0 * L + 2.0
        diff = gross - low_fee
        if abs(diff) < 1e-9:
            equal += 1
        elif diff < 0:
            gross_stronger += 1
        else:
            low_fee_stronger += 1
    total = gross_stronger + low_fee_stronger + equal
    assert total == 10000
    assert gross_stronger > 0 and low_fee_stronger > 0
    print(f"  PASS: {gross_stronger} cases gross < low_fee (gross tighter), "
          f"{low_fee_stronger} cases gross > low_fee (low_fee tighter), "
          f"{equal} equal")
    print("  Neither bound is universally tighter; the low-fee lane remains empirical.")


# ---------------------------------------------------------------------------
# Test 7: Witness non-vacuity (witness_per_pool_error_bound)
# ---------------------------------------------------------------------------

def test_witness_non_vacuity():
    """Verify the concrete witness case from Lean."""
    K, M = 1000.0, 1000.0
    net_cont = 50.0
    net_prod = 49.5
    cont_val = cpmm_output_cont(K, M, net_cont)
    floor_val = cpmm_output_prod_floor(K, M, net_prod)
    err = cont_val - floor_val
    bound = K / M + 1.0
    assert err < bound, f"witness err={err} >= bound={bound}"
    assert err >= 0.0, f"witness err={err} < 0"
    print(f"  PASS: witness err={err:.6f} < bound={bound:.1f}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("=== CeilingFeeRounding.lean Empirical Verification ===\n")

    print("Test 1: Per-pool output Lipschitz (cpmm_output_lipschitz_wrt_net)")
    test_per_pool_lipschitz()
    print()

    print("Test 1b: Coupled split Lipschitz (split_lipschitz_coupled)")
    test_coupled_split_lipschitz_max_bound()
    print()

    print("Test 2: Ceiling fee perturbation < 1 (external hypothesis)")
    test_ceil_fee_perturbation()
    print()

    print("Test 3: Per-pool floor error (cpmm_prod_floor_error_bound_directed)")
    test_per_pool_floor_error()
    print()

    print("Test 4: Split floor error (split_prod_floor_error_bound)")
    test_split_floor_error()
    print()

    print("Test 5: Production argmax proximity (cpmm_prod_discrete_argmax_proximity)")
    test_prod_argmax_proximity()
    print()

    print("Test 6: Gross formal bound vs low-fee empirical bound")
    test_formal_vs_empirical_bound()
    print()

    print("Test 7: Witness non-vacuity (witness_per_pool_error_bound)")
    test_witness_non_vacuity()
    print()

    print("=== All tests passed ===")
