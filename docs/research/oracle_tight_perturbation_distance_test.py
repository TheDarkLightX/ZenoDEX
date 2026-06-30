#!/usr/bin/env python3
"""Production-kernel replay for the oracle-tight perturbation distance.

Formal owners:

1. `abstract_oracle_perturbed_argmax_distance` in
   `DiscreteArgmaxProximity.lean`.
2. `cpmm_prod_oracle_argmax_distance` in `CeilingFeeRounding.lean`.
3. `oracle_perturbation_radius_sharp_quadratic` in
   `StrongConcavityWindowBound.lean`.

The replay uses the same ceiling-fee production split and endpoint-`m` helper
as the tight-argmax certificate checker. It also records a negative case:
overstating the oracle production value by one output unit can understate the
radius enough to exclude the true argmax.
"""

from __future__ import annotations

import math
import random
import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from docs.research.discrete_argmax_proximity_test import (
    Pool,
    best_continuous_integer_anchor,
    continuous_optimum,
    discrete_optimum_prod,
    gross_ceiling_fee_perturbation_bound,
    split_lean_cont,
    split_prod_floor,
    strong_concavity_param_pool_lower_bound,
)


FEE_CHOICES = (0, 30, 100, 300, 1000, 3000, 5000, 9000)
TOL = 1e-6


@dataclass(frozen=True)
class OracleMetrics:
    p0: Pool
    p1: Pool
    D: int
    b_star: float
    argmax: int
    prod_argmax: int
    cont_star: float
    m: float
    tau_oracle: float
    oracle_radius: float
    distance: float


def _random_pool(rng: random.Random) -> Pool:
    return Pool(
        reserve_in=rng.randint(100, 20_000),
        reserve_out=rng.randint(100, 80_000),
        fee_bps=rng.choice(FEE_CHOICES),
    )


def _oracle_metrics(
    p0: Pool,
    p1: Pool,
    D: int,
    *,
    reported_prod_delta: int = 0,
) -> OracleMetrics:
    b_star = continuous_optimum(p0, p1, D)
    argmax, prod_argmax = discrete_optimum_prod(p0, p1, D)
    cont_star = split_lean_cont(p0, p1, float(D), b_star)
    m = strong_concavity_param_pool_lower_bound(p0, p1, D)
    if m <= 0.0:
        raise ValueError("endpoint m must be positive for replay domain")
    reported_prod = prod_argmax + reported_prod_delta
    tau = cont_star - float(reported_prod)
    if tau < -TOL:
        raise ValueError("reported production value exceeds clean optimum")
    safe_tau = max(0.0, tau)
    return OracleMetrics(
        p0=p0,
        p1=p1,
        D=D,
        b_star=b_star,
        argmax=argmax,
        prod_argmax=prod_argmax,
        cont_star=cont_star,
        m=m,
        tau_oracle=safe_tau,
        oracle_radius=math.sqrt(2.0 * safe_tau / m),
        distance=abs(float(argmax) - b_star),
    )


def test_oracle_tight_bound_uses_production_kernel() -> None:
    """True production argmax value gives the oracle-tight radius."""
    rng = random.Random(20260715)
    max_ratio = 0.0
    nonzero_distance = 0
    for _ in range(1000):
        p0 = _random_pool(rng)
        p1 = _random_pool(rng)
        D = rng.randint(10, 250)
        metrics = _oracle_metrics(p0, p1, D)
        if metrics.distance > 1e-9:
            nonzero_distance += 1
        if metrics.oracle_radius > 1e-12:
            max_ratio = max(max_ratio, metrics.distance / metrics.oracle_radius)
        assert metrics.distance <= metrics.oracle_radius + TOL, (
            "oracle-tight production radius violated",
            metrics,
        )
    assert nonzero_distance > 0, "vacuous replay: every argmax matched b_star"
    print(
        "  PASS: 1000 production-kernel trials, oracle-tight bound holds "
        f"with ceiling-fee perturbation, max ratio = {max_ratio:.4f}"
    )


def test_anchor_envelope_hierarchy_uses_production_kernel() -> None:
    """The certified-anchor and gross envelopes dominate the oracle radius."""
    rng = random.Random(20260716)
    oracle_tighter = 0
    anchor_tighter_than_gross = 0
    for _ in range(1000):
        p0 = _random_pool(rng)
        p1 = _random_pool(rng)
        D = rng.randint(10, 250)
        metrics = _oracle_metrics(p0, p1, D)
        anchor = best_continuous_integer_anchor(p0, p1, D)
        cont_anchor = split_lean_cont(p0, p1, float(D), float(anchor))
        prod_anchor = float(split_prod_floor(p0, p1, D, anchor))
        alpha = max(0.0, metrics.cont_star - cont_anchor)
        eta_actual = max(0.0, cont_anchor - prod_anchor)
        eta_bound = gross_ceiling_fee_perturbation_bound(p0, p1)
        tau_anchor = max(0.0, metrics.cont_star - prod_anchor)
        anchor_radius = math.sqrt(2.0 * tau_anchor / metrics.m)
        gross_radius = math.sqrt(2.0 * (alpha + eta_bound) / metrics.m)

        assert eta_actual <= eta_bound + TOL
        assert metrics.oracle_radius <= anchor_radius + TOL
        assert anchor_radius <= gross_radius + TOL
        assert metrics.distance <= anchor_radius + TOL
        if metrics.oracle_radius < anchor_radius - TOL:
            oracle_tighter += 1
        if anchor_radius < gross_radius - TOL:
            anchor_tighter_than_gross += 1

    assert oracle_tighter > 0, "vacuous replay: oracle never beat anchor"
    assert anchor_tighter_than_gross > 0, "vacuous replay: anchor never beat gross"
    print(
        "  PASS: anchor/gross hierarchy held for 1000 production-kernel trials "
        f"(oracle_tighter={oracle_tighter}, anchor_tighter={anchor_tighter_than_gross})"
    )


def test_overstated_oracle_value_can_understate_radius() -> None:
    """A stale oracle value is a concrete radius-safety failure family."""
    p0 = Pool(reserve_in=4422, reserve_out=22891, fee_bps=0)
    p1 = Pool(reserve_in=14374, reserve_out=71647, fee_bps=100)
    D = 221

    true_metrics = _oracle_metrics(p0, p1, D)
    stale_metrics = _oracle_metrics(p0, p1, D, reported_prod_delta=1)

    assert true_metrics.distance <= true_metrics.oracle_radius + TOL
    assert stale_metrics.oracle_radius + TOL < stale_metrics.distance
    print(
        "  PASS: stale oracle value refuted "
        "failure_family=oracle_value_overstatement_understates_radius "
        f"distance={stale_metrics.distance:.6f}, stale_radius={stale_metrics.oracle_radius:.6f}"
    )


def test_sharpness_witness_attains_bound() -> None:
    """The quadratic witness reaches the oracle radius exactly."""
    rng = random.Random(20260717)
    max_error = 0.0
    for _ in range(1000):
        m = float(rng.randint(1, 100)) / 10.0
        tau = float(rng.randint(0, 1000)) / 10.0
        x_g = math.sqrt(2.0 * tau / m)
        bound = math.sqrt(2.0 * tau / m)
        max_error = max(max_error, abs(abs(x_g) - bound))
        f_cont_xg = -(m / 2.0) * x_g**2
        f_prod_xg = -tau
        assert f_prod_xg <= f_cont_xg + 1e-10
        assert abs(0.0 - f_prod_xg - tau) < 1e-10
    assert max_error < 1e-10
    print(
        "  PASS: 1000 quadratic witnesses attained the oracle radius exactly, "
        f"max error = {max_error:.2e}"
    )


def test_bound_cannot_be_improved() -> None:
    """Any smaller generic tau constant fails on the quadratic witness."""
    m = 1.0
    tau = 10.0
    x_g = math.sqrt(2.0 * tau / m)
    for delta in (0.01, 0.1, 0.5, 1.0, 5.0):
        tighter_bound = math.sqrt(2.0 * (tau - delta) / m)
        assert abs(x_g) > tighter_bound
    print("  PASS: Bound cannot be improved from m and tau alone")


def test_symbolic_sharpness_when_sympy_available() -> None:
    """Sympy mirrors the quadratic equality when available."""
    try:
        import sympy as sp
    except ImportError:
        print("  SKIP: sympy not available")
        return

    m, tau, x = sp.symbols("m tau x", positive=True)
    f_cont = -(m / 2) * x**2
    f_prod_xg = -tau
    bound = sp.sqrt(2 * tau / m)
    x_g = sp.sqrt(2 * tau / m)
    assert sp.simplify(f_cont.subs(x, x_g) - f_prod_xg) == 0
    assert sp.simplify(x_g - bound) == 0
    print("  PASS: sympy confirms oracle-tight bound and sharpness witness")


def test_curvature_floor_supports_full_chain() -> None:
    """Sampled second derivatives stay below the endpoint m floor."""
    rng = random.Random(20260718)
    for _ in range(300):
        p0 = _random_pool(rng)
        p1 = _random_pool(rng)
        D = rng.randint(10, 250)
        metrics = _oracle_metrics(p0, p1, D)
        c0 = 1.0 - p0.fee_bps / 10000.0
        c1 = 1.0 - p1.fee_bps / 10000.0
        for frac in (0.1, 0.25, 0.5, 0.75, 0.9):
            a = frac * D
            term0 = 2.0 * c0**2 * p0.reserve_out * p0.reserve_in
            term0 /= (p0.reserve_in + c0 * a) ** 3
            term1 = 2.0 * c1**2 * p1.reserve_out * p1.reserve_in
            term1 /= (p1.reserve_in + c1 * (D - a)) ** 3
            assert -(term0 + term1) <= -metrics.m + 1e-9
        assert metrics.distance <= metrics.oracle_radius + TOL
    print("  PASS: 300 sampled curvature chains supported m -> oracle radius")


if __name__ == "__main__":
    print("=== P8: Oracle-Tight Perturbation Distance Production Replay ===\n")

    print("Test 1: Production-kernel oracle-tight bound")
    test_oracle_tight_bound_uses_production_kernel()
    print()

    print("Test 2: Anchor and gross envelope hierarchy")
    test_anchor_envelope_hierarchy_uses_production_kernel()
    print()

    print("Test 3: Stale oracle value refutation")
    test_overstated_oracle_value_can_understate_radius()
    print()

    print("Test 4: Sharpness witness")
    test_sharpness_witness_attains_bound()
    print()

    print("Test 5: Bound cannot be improved")
    test_bound_cannot_be_improved()
    print()

    print("Test 6: Symbolic sharpness")
    test_symbolic_sharpness_when_sympy_available()
    print()

    print("Test 7: Curvature floor full chain")
    test_curvature_floor_supports_full_chain()
    print()

    print("=== All tests passed ===")
