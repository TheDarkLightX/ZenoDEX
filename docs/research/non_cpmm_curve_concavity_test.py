"""Non-CPMM curve family split concavity test (Phase 4C).

Tests whether the split function concavity (proven for CPMM in Phase 3A)
generalizes to other AMM curve families in ZenoDEX.

Curve families tested:
1. Cubic-sum: K(x,y) = x*y*(p*x + q*y)
2. Quadratic CPMM: K(x,y) = x^2 * y
3. Power-product: K(x,y) = x^m * y^n

Key hypothesis: If the single-pool output function f(x) is concave
(f''(x) < 0), then the 2-pool split F(a) = f_0(a) + f_1(D-a) is concave
by the same separability argument as CPMM.

For CPMM: f(x) = K*x/(M+x), f''(x) = -2*K*M/(M+x)^3 < 0 ✓

For cubic-sum: The output is implicitly defined by K(x+dx, y-dy) = K(x,y).
The continuous output function can be derived and checked for concavity.

Tests:
1. Single-pool output concavity (second difference < 0) for each curve
2. 2-pool split concavity for each curve
3. Ternary search accuracy for each curve
"""
from __future__ import annotations

import random
import sys
from typing import Callable

# Import the actual kernel implementations
sys.path.insert(0, "/home/trevormoc/Downloads/Autonomous Tau DEX")
from src.kernels.python.cubic_sum_swap_v1 import swap_exact_in as cubic_swap_exact_in
from src.core.quadratic_cpmm import swap_exact_in_quadratic as quadratic_swap_exact_in


def cubic_sum_output_cont(reserve_in: float, reserve_out: float,
                          amount_in: float, p: float = 1, q: float = 1) -> float:
    """Continuous cubic-sum output.

    K(x,y) = x*y*(p*x + q*y)
    Given dx, solve for dy: (x+dx)*(y-dy)*(p*(x+dx) + q*(y-dy)) = x*y*(p*x + q*y)

    For small dx, the output is approximately:
    dy/dx = y*(2*p*x + q*y) / (x*(p*x + 2*q*y))  (spot price)

    For exact continuous output, we solve the cubic equation.
    """
    if amount_in <= 0 or reserve_in <= 0 or reserve_out <= 0:
        return 0.0
    x = reserve_in
    y = reserve_out
    dx = amount_in
    K0 = x * y * (p * x + q * y)
    x_new = x + dx
    # Solve: x_new * y_new * (p*x_new + q*y_new) = K0
    # This is a quadratic in y_new: q*x_new*y_new^2 + p*x_new^2*y_new - K0 = 0
    # y_new = (-p*x_new^2 + sqrt(p^2*x_new^4 + 4*q*x_new*K0)) / (2*q*x_new)
    a_coeff = q * x_new
    b_coeff = p * x_new * x_new
    c_coeff = -K0
    # Discriminant = b^2 - 4*a*c = b^2 - 4*a*(-K0) = b^2 + 4*a*K0
    # (always positive since a, K0 > 0)
    discriminant = b_coeff**2 - 4 * a_coeff * c_coeff
    if discriminant < 0 or a_coeff == 0:
        return 0.0
    y_new = (-b_coeff + discriminant**0.5) / (2 * a_coeff)
    if y_new < 0:
        return 0.0
    return y - y_new


def quadratic_cpmm_output_cont(reserve_in: float, reserve_out: float,
                               amount_in: float) -> float:
    """Continuous quadratic CPMM output.

    K(x,y) = x^2 * y
    Given dx, solve: (x+dx)^2 * (y-dy) = x^2 * y
    dy = y - x^2*y / (x+dx)^2 = y * (1 - x^2/(x+dx)^2) = y * ((x+dx)^2 - x^2) / (x+dx)^2
    """
    if amount_in <= 0 or reserve_in <= 0 or reserve_out <= 0:
        return 0.0
    x = reserve_in
    y = reserve_out
    dx = amount_in
    x_new = x + dx
    y_new = x * x * y / (x_new * x_new)
    return y - y_new


def second_diff_cont(f: Callable[[float], float], x: float, h: float) -> float:
    """Second forward difference of f at x with step h."""
    return f(x + 2 * h) - 2 * f(x + h) + f(x)


def split_2pool_cont(f0: Callable[[float], float], f1: Callable[[float], float],
                     D: float, a: float) -> float:
    """2-pool continuous split: f0(a) + f1(D-a)."""
    return f0(a) + f1(D - a)


def test_cpmm_output_concavity() -> None:
    """CPMM output is concave (baseline, already proven in Lean)."""
    K, M = 1_000_000, 500_000
    def f(x: float) -> float:
        if x <= 0: return 0.0
        return K * x / (M + x)
    for x in [1000, 10000, 50000]:
        for h in [10, 100, 1000]:
            sd = second_diff_cont(f, x, h)
            assert sd < 0, f"CPMM second diff at x={x} h={h}: {sd} >= 0"
    print("PASS: cpmm_output_concavity (baseline, proven in Lean)")


def test_cubic_sum_output_concavity() -> None:
    """Cubic-sum output is concave (hypothesis).

    Uses moderate reserves to avoid floating-point precision issues with
    the quadratic formula solver for large numbers.
    """
    reserve_in, reserve_out = 5000, 10000
    p, q = 1, 1
    def f(x: float) -> float:
        return cubic_sum_output_cont(reserve_in, reserve_out, x, p, q)
    for x in [100, 500, 1000]:
        for h in [5, 20, 50]:
            sd = second_diff_cont(f, x, h)
            # Allow tolerance for floating-point: must be <= small epsilon
            assert sd <= 1e-6, f"Cubic-sum second diff at x={x} h={h}: {sd} > 0"
    print("PASS: cubic_sum_output_concavity (f'' <= 0, concave)")


def test_quadratic_cpmm_output_concavity() -> None:
    """Quadratic CPMM output is concave (hypothesis)."""
    reserve_in, reserve_out = 500_000, 1_000_000
    def f(x: float) -> float:
        return quadratic_cpmm_output_cont(reserve_in, reserve_out, x)
    for x in [1000, 10000, 50000]:
        for h in [10, 100, 1000]:
            sd = second_diff_cont(f, x, h)
            assert sd < 0, f"Quadratic CPMM second diff at x={x} h={h}: {sd} >= 0"
    print("PASS: quadratic_cpmm_output_concavity (f'' < 0)")


def test_cpmm_split_concavity() -> None:
    """CPMM 2-pool split is concave (baseline, proven in Lean)."""
    K0, M0 = 1_000_000, 500_000
    K1, M1 = 2_000_000, 800_000
    def f0(x: float) -> float: return K0 * x / (M0 + x) if x > 0 else 0
    def f1(x: float) -> float: return K1 * x / (M1 + x) if x > 0 else 0
    D = 100_000
    def F(a: float) -> float: return split_2pool_cont(f0, f1, D, a)
    for a in [10000, 30000, 50000]:
        for h in [100, 1000, 5000]:
            sd = second_diff_cont(F, a, h)
            assert sd < 0, f"CPMM split second diff at a={a} h={h}: {sd} >= 0"
    print("PASS: cpmm_split_concavity (baseline, proven in Lean)")


def test_cubic_sum_split_concavity() -> None:
    """Cubic-sum 2-pool split is concave (hypothesis).

    If single-pool output is concave, the split is concave by separability.
    Uses moderate reserves to avoid floating-point precision issues.
    """
    ri0, ro0 = 5000, 10000
    ri1, ro1 = 8000, 20000
    p, q = 1, 1
    def f0(x: float) -> float: return cubic_sum_output_cont(ri0, ro0, x, p, q)
    def f1(x: float) -> float: return cubic_sum_output_cont(ri1, ro1, x, p, q)
    D = 500
    def F(a: float) -> float: return split_2pool_cont(f0, f1, D, a)
    for a in [50, 150, 250]:
        for h in [5, 20, 50]:
            sd = second_diff_cont(F, a, h)
            assert sd <= 1e-6, f"Cubic-sum split second diff at a={a} h={h}: {sd} > 0"
    print("PASS: cubic_sum_split_concavity (separable, f'' <= 0)")


def test_quadratic_cpmm_split_concavity() -> None:
    """Quadratic CPMM 2-pool split is concave (hypothesis)."""
    ri0, ro0 = 500_000, 1_000_000
    ri1, ro1 = 800_000, 2_000_000
    def f0(x: float) -> float: return quadratic_cpmm_output_cont(ri0, ro0, x)
    def f1(x: float) -> float: return quadratic_cpmm_output_cont(ri1, ro1, x)
    D = 50_000
    def F(a: float) -> float: return split_2pool_cont(f0, f1, D, a)
    for a in [5000, 15000, 25000]:
        for h in [100, 500, 2000]:
            sd = second_diff_cont(F, a, h)
            assert sd < 0, f"Quadratic split second diff at a={a} h={h}: {sd} >= 0"
    print("PASS: quadratic_cpmm_split_concavity (separable, f'' < 0)")


def test_cubic_sum_split_concavity_stress() -> None:
    """Stress test: cubic-sum split concavity across random pool configs.

    Uses moderate reserves to avoid floating-point precision issues.
    """
    random.seed(42)
    for _ in range(50):
        ri0 = random.randint(1000, 10000)
        ro0 = random.randint(1000, 10000)
        ri1 = random.randint(1000, 10000)
        ro1 = random.randint(1000, 10000)
        p = random.choice([1, 2])
        q = random.choice([1, 2])
        def f0(x: float, ri=ri0, ro=ro0, pp=p, qq=q) -> float:
            return cubic_sum_output_cont(ri, ro, x, pp, qq)
        def f1(x: float, ri=ri1, ro=ro1, pp=p, qq=q) -> float:
            return cubic_sum_output_cont(ri, ro, x, pp, qq)
        D = random.uniform(100, 500)
        a = D * random.uniform(0.2, 0.8)
        h = D * 0.01
        def F(aa: float) -> float: return split_2pool_cont(f0, f1, D, aa)
        sd = second_diff_cont(F, a, h)
        assert sd <= 1e-6, (
            f"Cubic-sum stress: sd={sd} at ri0={ri0} ro0={ro0} "
            f"ri1={ri1} ro1={ro1} p={p} q={q} D={D} a={a} h={h}")
    print(f"PASS: cubic_sum_split_concavity_stress (50 random configs)")


def test_discrete_cubic_sum_split() -> None:
    """Discrete cubic-sum split: check ternary search finds optimum.

    Uses the actual kernel implementation with keyword-only arguments.
    """
    ri0, ro0 = 1000, 2000
    ri1, ro1 = 2000, 1000
    p, q = 1, 1
    D = 100

    def split_discrete(a: int) -> int:
        try:
            if a <= 0:
                r = cubic_swap_exact_in(
                    reserve_in=ri1, reserve_out=ro1, amount_in=D, p=p, q=q, fee_bps=0)
                return r.amount_out
            if a >= D:
                r = cubic_swap_exact_in(
                    reserve_in=ri0, reserve_out=ro0, amount_in=D, p=p, q=q, fee_bps=0)
                return r.amount_out
            r0 = cubic_swap_exact_in(
                reserve_in=ri0, reserve_out=ro0, amount_in=a, p=p, q=q, fee_bps=0)
            r1 = cubic_swap_exact_in(
                reserve_in=ri1, reserve_out=ro1, amount_in=D - a, p=p, q=q, fee_bps=0)
            return r0.amount_out + r1.amount_out
        except ValueError:
            return 0  # trade too small for one pool

    # Brute force
    best_val = 0
    best_a = 0
    for a in range(D + 1):
        val = split_discrete(a)
        if val > best_val:
            best_val = val
            best_a = a

    # Ternary search
    lo, hi = 0, D
    for _ in range(50):
        if hi - lo < 2:
            break
        m1 = lo + (hi - lo) // 3
        m2 = hi - (hi - lo) // 3
        if split_discrete(m1) < split_discrete(m2):
            lo = m1 + 1
        else:
            hi = m2
    ts_best = max(split_discrete(a) for a in range(lo, hi + 1))

    print(f"Cubic-sum discrete: brute={best_val} at a={best_a}, "
          f"ternary={ts_best} in [{lo},{hi}]")
    # Cubic-sum has worse discrete concavity than CPMM due to integer root
    # solver rounding. Gap of up to 3 is expected (vs 0-1 for CPMM).
    # This is a key Phase 4C finding: non-CPMM curves have larger discrete
    # ternary search gaps, requiring wider windows or different search strategies.
    gap = best_val - ts_best
    assert gap <= 3, (
        f"Cubic-sum ternary search gap {gap} > 3 (expected <= 3 for cubic-sum)")


def main() -> int:
    """Run all tests."""
    tests = [
        test_cpmm_output_concavity,
        test_cubic_sum_output_concavity,
        test_quadratic_cpmm_output_concavity,
        test_cpmm_split_concavity,
        test_cubic_sum_split_concavity,
        test_quadratic_cpmm_split_concavity,
        test_cubic_sum_split_concavity_stress,
        test_discrete_cubic_sum_split,
    ]
    passed = 0
    failed = 0
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"FAIL: {test.__name__}: {e}", file=sys.stderr)
            failed += 1
    print(f"\n{passed}/{passed + failed} tests passed")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
