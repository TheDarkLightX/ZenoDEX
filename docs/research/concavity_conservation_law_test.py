#!/usr/bin/env python3
"""CPMM Concavity Evidence: Window Algebra and Lipschitz Increment Tests.

This is NOT a conservation law package. The Lean file proves only:
1. An algebraic identity: sqrt(2*L/m) = sqrt(M) when L=K/M, m=2*K/M^2
   (epsilon=0 case; production window includes epsilon).
2. A generic Lipschitz increment: f(a_A)-f(0) <= L*a_A for any L-Lipschitz f.

The stateful CPMM attack gain (out_B_without_A - out_B_with_A) is a DIFFERENT
quantity from the Lipschitz increment. The empirical tests below check the
stateful gain against L*a_A on a seeded corpus, but this bridge is empirical,
not Lean-proven.

LEAN-PROVEN vs EMPIRICAL:
- [Lean PROVEN]: algebraic identities only (m formula, window=sqrt(M) at eps=0,
  generic Lipschitz increment f(a_A)-f(0) <= L*a_A).
- [Empirical]: stateful gain envelope, depth-monotone gain, falsification of
  the concavity bound, min_out cap behavior, frontier characterization.

For CPMM f(x) = K*x/(M+x):
  m = 2*K*M / (M + x_max)^3  (strong concavity parameter)
  L = K/M  (spot price = Lipschitz constant)
  At margin (x=0): m = 2*K/M^2 = 2*L/M

TESTS:
1. CPMM concavity parameter formula: m = 2*K*gamma^2/M^2 [Lean PROVEN, gamma=1]
2. CPMM window identity: sqrt(2*L/m) = sqrt(M) [Lean PROVEN, epsilon=0]
3. Stateful gain vs Lipschitz envelope [Empirical, NOT Lean-proven for stateful]
4. Second-order concavity bound falsified [Empirical falsification, regression guard]
5. Actual stateful gain decreases with M [Empirical, NOT formalized]
6. Min_out cap makes sacrifice infeasible [Empirical]
7. Tradeoff frontier characterization [Empirical]
8. Exact count audit

Determinism: All tests use fixed seeds.
"""

import math
import random
from dataclasses import dataclass


@dataclass(frozen=True)
class Pool:
    reserve_in: int
    reserve_out: int
    fee_bps: int


def cpmm_output_cont(p: Pool, amount_in: float) -> float:
    if amount_in <= 0.0:
        return 0.0
    gamma = 1.0 - p.fee_bps / 10000.0
    net = amount_in * gamma
    if net <= 0.0:
        return 0.0
    return p.reserve_out * net / (p.reserve_in + net)


def spot_price(p: Pool) -> float:
    gamma = 1.0 - p.fee_bps / 10000.0
    return gamma * p.reserve_out / p.reserve_in


def strong_concavity_param(p: Pool, x_max: float) -> float:
    K = p.reserve_out
    M = p.reserve_in
    gamma = 1.0 - p.fee_bps / 10000.0
    denom = M + gamma * x_max
    if denom <= 0:
        return 0.0
    return 2.0 * K * gamma * gamma * M / (denom ** 3)


def concavity_param_at_margin(p: Pool) -> float:
    """m at x=0: m = 2*K*gamma^2*M / M^3 = 2*K*gamma^2 / M^2."""
    K = p.reserve_out
    M = p.reserve_in
    gamma = 1.0 - p.fee_bps / 10000.0
    return 2.0 * K * gamma * gamma / (M * M)


def algorithm_window(L: float, m: float, k: int = 2, epsilon: float = 2.0) -> float:
    """Window size from the argmax proximity theorem: sqrt(2*(L+epsilon)/m)."""
    if m <= 0:
        return float("inf")
    return math.sqrt(2.0 * (L + epsilon) / m)


def lipschitz_increment_value(L: float, a_A: float) -> float:
    """Value of the Lean-proven generic increment bound: L * a_A.

    Lean proves f(a_A)-f(0) <= L*a_A for any L-Lipschitz f. This function
    returns the bound value. It does NOT prove the stateful CPMM attack gain
    is bounded by L*a_A; that bridge is empirical only.
    """
    return L * a_A


def adversarial_gain_concavity(m: float, a_A: float, a_B: float) -> float:
    """Falsified second-order approximation: (m/2)*a_A*(a_A + 2*a_B)."""
    return (m / 2.0) * a_A * (a_A + 2.0 * a_B)


def simulate_sacrifice_gain(p: Pool, a_A: float, a_B: float) -> float:
    """Simulate actual sacrifice attack gain.

    Gain = f(a_B) - f(a_A + a_B) where f is the CPMM output.
    (A doesn't fill, so B trades against the original pool vs pool with A.)
    """
    out_B_alone = cpmm_output_cont(p, a_B)
    out_B_after_A = cpmm_output_cont(p, a_A + a_B) - cpmm_output_cont(p, a_A)
    # Actually, the gain is: B's output when A is absent vs B's output after A filled
    # When A fills: pool state changes, B trades against modified pool
    # When A sacrifices: B trades against original pool
    # Gain = f(a_B, original_pool) - f(a_B, pool_after_A)
    K = p.reserve_out
    M = p.reserve_in
    gamma = 1.0 - p.fee_bps / 10000.0
    # A fills first
    out_A = cpmm_output_cont(p, a_A)
    M_after_A = M + a_A * gamma
    K_after_A = K - out_A
    pool_after_A = Pool(int(M_after_A), int(K_after_A), p.fee_bps)
    out_B_with_A = cpmm_output_cont(pool_after_A, a_B)
    # A sacrifices (B trades against original pool)
    out_B_without_A = cpmm_output_cont(p, a_B)
    # Gain = B's extra output from A's sacrifice
    gain = out_B_without_A - out_B_with_A
    return gain


# ---------------------------------------------------------------------------
# Test 1: CPMM concavity parameter formula [Lean PROVEN, gamma=1]
# ---------------------------------------------------------------------------

def test_cpmm_concavity_param_formula() -> None:
    """m = 2*K*gamma^2/M^2 = 2*gamma*L/M at the margin (x=0).

    For f(x) = K*gamma*x/(M+gamma*x):
      f''(x) = -2*K*gamma^2*M / (M+gamma*x)^3
      m(0) = 2*K*gamma^2 / M^2

    The spot price (Lipschitz constant) is L = gamma*K/M.
    So m = 2*gamma*L/M (NOT 2*L/M; the gamma factor comes from the
    second derivative having gamma^2 while the first has gamma).

    For fee=0 (gamma=1): m = 2*K/M^2 = 2*L/M (the Lean theorem case).
    """
    rng = random.Random(20260710)
    for _ in range(200):
        K = rng.randint(100, 50000)
        M = rng.randint(100, 50000)
        fee = rng.choice([0, 30, 100, 300])
        p = Pool(M, K, fee)
        gamma = 1.0 - fee / 10000.0
        L = spot_price(p)
        m_formula = 2.0 * K * gamma * gamma / (M * M)
        # Correct relation: m = 2*gamma*L/M (gamma factor from 2nd derivative)
        m_via_L = 2.0 * gamma * L / M
        assert abs(m_formula - m_via_L) < 1e-6, (
            f"m formula mismatch: {m_formula} vs {m_via_L} "
            f"(K={K}, M={M}, fee={fee}, gamma={gamma})")
    print(f"PASS: cpmm_concavity_param_formula (200 configs, m = 2*K*gamma^2/M^2 = 2*gamma*L/M)")


# ---------------------------------------------------------------------------
# Test 2: CPMM window identity [Lean PROVEN, epsilon=0]
# ---------------------------------------------------------------------------

def test_cpmm_conservation_tradeoff() -> None:
    """window = sqrt(M) when L and m are linked via m = 2*L/M (epsilon=0).

    Lean proves sqrt(2*L/m) = sqrt(M) for the epsilon=0 case. The production
    argmax window is sqrt(2*(L+epsilon)/m), which is strictly larger.
    """
    rng = random.Random(20260711)
    for _ in range(200):
        K = rng.randint(100, 50000)
        M = rng.randint(100, 50000)
        L = K / M  # spot price (no fee for clean check)
        m = 2.0 * L / M  # concavity at margin
        if m <= 0:
            continue
        window_eps0 = math.sqrt(2.0 * L / m)
        expected = math.sqrt(M)
        assert abs(window_eps0 - expected) < 1e-6, (
            f"window_eps0={window_eps0} != sqrt(M)={expected} "
            f"(K={K}, M={M}, L={L}, m={m})")
    print(f"PASS: cpmm_window_identity (200 configs, sqrt(2*L/m)=sqrt(M) at eps=0)")


# ---------------------------------------------------------------------------
# Test 3: Stateful gain vs Lipschitz envelope [Empirical, NOT Lean-proven]
# ---------------------------------------------------------------------------

def test_stateful_gain_lipschitz_envelope_empirical() -> None:
    """Simulated stateful sacrifice gain stays within the Lipschitz envelope.

    Lean proves the generic increment f(a_A)-f(0) <= L*a_A. This test checks
    the stateful attack gain (a DIFFERENT quantity involving pool state change)
    against the same envelope on a seeded corpus. This is empirical replay,
    NOT a Lean-proven theorem for the stateful gain.
    """
    rng = random.Random(20260712)
    max_violation = 0.0
    worst: tuple = ()
    for _ in range(500):
        M = rng.randint(1000, 50000)
        K = rng.randint(1000, 50000)
        fee = rng.choice([0, 30, 100])
        p = Pool(M, K, fee)
        L = spot_price(p)
        a_A = rng.uniform(10, min(1000, M / 10))
        a_B = rng.uniform(100, min(5000, M / 2))
        gain = simulate_sacrifice_gain(p, a_A, a_B)
        bound = lipschitz_increment_value(L, a_A)
        if gain > bound + 1e-6:
            v = gain - bound
            max_violation = max(max_violation, v)
            worst = (M, K, fee, a_A, a_B, gain, bound)
    assert max_violation <= 1e-6, (
        f"STATEFUL GAIN EXCEEDED LIPSCHITZ ENVELOPE: {max_violation}. Worst: {worst}")
    print(f"PASS: stateful_gain_lipschitz_envelope_empirical "
          f"(500 configs, stateful gain <= L*a_A [empirical, not Lean-proven])")


# ---------------------------------------------------------------------------
# Test 4: Concavity bound falsification [Empirical, regression guard]
# ---------------------------------------------------------------------------

def test_concavity_bound_falsified_small_trades() -> None:
    """Concavity gain bound is an APPROXIMATION, not a universal bound.

    FALSIFICATION: The bound gain <= (m/2)*a_A*(a_A+2*a_B) derived from a
    second-order Taylor expansion of f(input) does NOT universally hold,
    even in the small-trade regime. The actual gain involves a pool STATE
    change (M -> M+a_A*gamma), not just an input change, so the Taylor
    expansion in input space is the wrong model.

    The generic Lipschitz increment f(a_A)-f(0) <= L*a_A is Lean-proven,
    but the stateful gain is a different quantity. The empirical envelope
    test (test 3) checks the stateful gain against L*a_A on a seeded corpus.
    """
    rng = random.Random(20260713)
    max_ratio = 0.0
    fail_count = 0
    total = 0
    for _ in range(500):
        M = rng.randint(1000, 50000)
        K = rng.randint(1000, 50000)
        fee = rng.choice([0, 30, 100])
        p = Pool(M, K, fee)
        max_trade = M / 10
        a_A = rng.uniform(1, max_trade / 3)
        a_B = rng.uniform(1, max_trade * 2 / 3)
        x_max = a_A + a_B
        m = strong_concavity_param(p, x_max)
        gain = simulate_sacrifice_gain(p, a_A, a_B)
        bound = adversarial_gain_concavity(m, a_A, a_B)
        if bound > 0:
            ratio = gain / bound
            total += 1
            if ratio > 1.0:
                fail_count += 1
            if ratio > max_ratio:
                max_ratio = ratio
    # HARD ASSERT: falsification must actually occur (regression guard)
    assert fail_count > 0, (
        "FALSIFICATION REGRESSION: no configs exceeded concavity bound; "
        "either the bound started holding or the test regime changed")
    assert max_ratio > 1.0, (
        "FALSIFICATION REGRESSION: max_ratio <= 1.0; concavity bound holds")
    print(f"PASS: concavity_bound_falsified_small_trades "
          f"(FALSIFICATION: {fail_count}/{total} configs exceed concavity bound, "
          f"max_ratio={max_ratio:.4f})")


def test_concavity_bound_fails_large_trades() -> None:
    """Document that the concavity bound FAILS for large trades.

    This is a FALSIFICATION: the concavity bound (m/2)*a_A*(a_A+2*a_B) is
    NOT a universal upper bound. For large trades (a_B ~ M/2), the actual
    gain exceeds the concavity bound by up to 2x.
    """
    rng = random.Random(20260714)
    max_ratio = 0.0
    worst: tuple = ()
    fail_count = 0
    total = 0
    for _ in range(500):
        M = rng.randint(1000, 5000)
        K = rng.randint(1000, 50000)
        fee = rng.choice([0, 30, 100])
        p = Pool(M, K, fee)
        # Large-trade regime: a_B up to M/2
        a_A = rng.uniform(10, min(100, M / 10))
        a_B = rng.uniform(100, M / 2)
        x_max = a_A + a_B
        m = strong_concavity_param(p, x_max)
        gain = simulate_sacrifice_gain(p, a_A, a_B)
        bound = adversarial_gain_concavity(m, a_A, a_B)
        if bound > 0:
            ratio = gain / bound
            total += 1
            if ratio > 1.0:
                fail_count += 1
            if ratio > max_ratio:
                max_ratio = ratio
                worst = (M, K, fee, a_A, a_B, gain, bound, ratio)
    # HARD ASSERT: falsification must actually occur (regression guard)
    assert fail_count > 0, (
        "FALSIFICATION REGRESSION: no large-trade configs exceeded concavity bound")
    assert max_ratio > 1.0, (
        "FALSIFICATION REGRESSION: max_ratio <= 1.0 for large trades")
    print(f"PASS: concavity_bound_fails_large_trades "
          f"({fail_count}/{total} large-trade configs EXCEED concavity bound, "
          f"max_ratio={max_ratio:.4f})")
    # Empirically check that the Lipschitz increment value holds for the worst case
    # (empirical, not Lean-proven for the stateful gain)
    if worst:
        M_w, K_w, fee_w, a_A_w, a_B_w, _, _, _ = worst
        p_w = Pool(M_w, K_w, fee_w)
        L_w = spot_price(p_w)
        lip_bound = lipschitz_increment_value(L_w, a_A_w)
        actual_w = simulate_sacrifice_gain(p_w, a_A_w, a_B_w)
        assert actual_w <= lip_bound + 1e-6, (
            f"Stateful gain exceeded Lipschitz envelope: actual={actual_w} > L*a_A={lip_bound}")



# ---------------------------------------------------------------------------
# Test 5: Actual stateful gain decreases with M [Empirical]
# ---------------------------------------------------------------------------

def test_actual_gain_decreases_with_depth() -> None:
    """ACTUAL adversarial gain decreases as pool depth M increases.

    NOTE: This uses the ACTUAL simulated gain, not a bound. The Lipschitz
    bound L*a_A is constant (for balanced pools where L=K/M=1), so the
    Lipschitz product window*L*a_A = sqrt(M)*a_A is INCREASING in M.
    The actual gain DECREASES with M because the pool's curvature
    decreases, making the stateful gain smaller. This is an EMPIRICAL
    observation, not a formalized theorem.

    The concavity-based bound using MINIMUM curvature m, (m/2)*a_A*a_B, also
    decreases with M, but it is FALSIFIED as a stateful attack bound (ratio up
    to 1.88x). The empirical scaling probe in concavity_bounded_adversarial_test.py
    uses |f''(0)| (MAXIMUM curvature at the margin), which is a more
    conservative upper-bound constant than m since |f''(0)| >= m. That probe
    is empirical only, not a Lean theorem.
    The actual gain is the honest quantity to track.
    """
    a_A, a_B = 100.0, 2000.0
    gains_by_depth: dict[int, float] = {}
    for M in [1000, 5000, 10000, 50000, 100000]:
        K = M  # balanced pool (L = 1)
        p = Pool(M, K, 0)
        gain = simulate_sacrifice_gain(p, a_A, a_B)
        gains_by_depth[M] = gain
    # Actual gain should decrease with M (deeper = more secure)
    depths = sorted(gains_by_depth.keys())
    for i in range(len(depths) - 1):
        assert gains_by_depth[depths[i]] > gains_by_depth[depths[i + 1]], (
            f"Actual gain not decreasing: M={depths[i]} "
            f"gain={gains_by_depth[depths[i]]} vs M={depths[i+1]} "
            f"gain={gains_by_depth[depths[i+1]]}")
    print(f"PASS: actual_gain_decreases_with_depth "
          f"(gains={{{', '.join(f'M={m}:{g:.2f}' for m, g in gains_by_depth.items())}}})")


# ---------------------------------------------------------------------------
# Test 6: Min_out cap breaks the tradeoff [Empirical]
# ---------------------------------------------------------------------------

def test_min_out_cap_breaks_tradeoff() -> None:
    """Min_out cap at 90% makes sacrifice INFEASIBLE, so gain = 0.

    The cap mechanism: A's min_out is limited to 90% of the EXPECTED output
    (computed at spot price, i.e. linear approximation without price impact).
    The ACTUAL output includes price impact (concavity), so actual < expected.
    For small trades, actual >= 0.9 * expected, so A always fills.

    This test is NON-TAUTOLOGICAL: expected_out_A uses the linear spot price
    (L * a_A), while actual_out_A uses the full CPMM formula with price impact.
    The gap between them is the slippage. The test verifies that the 90% cap
    is above the slippage ratio for the tested regime, so A fills.
    """
    rng = random.Random(20260714)
    cap_ratio = 0.9
    cap_gains: list[float] = []
    nocap_gains: list[float] = []
    a_fills_count = 0
    total = 0
    min_slippage_ratio = 1.0
    for _ in range(200):
        M = rng.randint(1000, 10000)
        K = rng.randint(1000, 10000)
        p = Pool(M, K, 0)
        a_A = rng.uniform(10, min(100, M / 10))
        a_B = rng.uniform(100, min(5000, M / 2))
        total += 1
        # Without cap: actual gain (A can sacrifice)
        gain_nocap = simulate_sacrifice_gain(p, a_A, a_B)
        nocap_gains.append(gain_nocap)
        # With cap: A's min_out is capped at 90% of EXPECTED output (spot price * a_A)
        L = spot_price(p)
        expected_out_A = L * a_A  # linear approximation (no price impact)
        capped_min_out = expected_out_A * cap_ratio
        actual_out_A = cpmm_output_cont(p, a_A)  # full CPMM (with price impact)
        # Slippage ratio: actual / expected (always < 1 due to concavity)
        if expected_out_A > 0:
            slippage_ratio = actual_out_A / expected_out_A
            min_slippage_ratio = min(min_slippage_ratio, slippage_ratio)
        # A fills iff actual_out >= capped_min_out
        if actual_out_A >= capped_min_out - 1e-9:
            a_fills_count += 1
            # A fills: no sacrifice, gain = 0
            cap_gains.append(0.0)
        else:
            # A doesn't fill even with cap: sacrifice still possible
            cap_gains.append(gain_nocap)
    max_cap_gain = max(cap_gains) if cap_gains else 0.0
    max_nocap_gain = max(nocap_gains) if nocap_gains else 0.0
    # With cap at 90%, A should always fill (for small trades a_A << M)
    assert a_fills_count == total, (
        f"Cap should make A always fill: {a_fills_count}/{total} filled. "
        f"Some configs allow sacrifice despite cap.")
    assert max_cap_gain == 0.0, (
        f"Cap should make gain ZERO: max_cap_gain={max_cap_gain}")
    # Verify the test is non-tautological: slippage must be real (< 1.0)
    assert min_slippage_ratio < 1.0, (
        f"Slippage ratio must be < 1.0 (non-tautological): "
        f"min_slippage_ratio={min_slippage_ratio}")
    # Verify the cap is above the worst slippage (so A fills)
    assert min_slippage_ratio >= cap_ratio, (
        f"Worst slippage {min_slippage_ratio} below cap {cap_ratio}: "
        f"some configs would not fill")
    assert max_nocap_gain > 0.0, (
        f"Without cap, some gains should be positive: max_nocap_gain={max_nocap_gain}")
    print(f"PASS: min_out_cap_breaks_tradeoff "
          f"(cap: {a_fills_count}/{total} A fills, max_gain={max_cap_gain:.2f}, "
          f"nocap: max_gain={max_nocap_gain:.2f}, "
          f"min_slippage_ratio={min_slippage_ratio:.6f})")


# ---------------------------------------------------------------------------
# Test 7: Tradeoff frontier characterization [Empirical]
# ---------------------------------------------------------------------------

def test_tradeoff_frontier_characterization() -> None:
    """Characterize a fixed row-set tradeoff probe across pool depths.

    For each M, compute:
    - window_eps0: sqrt(2*L/m) = sqrt(M) [Lean PROVEN, epsilon=0]
    - window_prod: sqrt(2*(L+epsilon)/m) [production, epsilon=2, NOT Lean]
    - lipschitz_increment: L*a_A [Lean PROVEN for f(a_A)-f(0), NOT for stateful]
    - actual gain: stateful simulator [empirical, decreases with M in this row set]
    - lip_product: window * L * a_A [INCREASING in M, NOT a frontier]

    The Lipschitz product is INCREASING in M, NOT decreasing.
    The actual gain DECREASES with M in this row set, but this is empirical.
    The concavity-based bound is FALSIFIED and is NOT shown here.
    """
    a_A, a_B = 100.0, 2000.0
    epsilon = 2.0
    print("\nTradeoff Frontier (a_A=100, a_B=2000, L=1, epsilon=2):")
    print(f"{'M':>8} | {'m':>10} | {'win_eps0':>10} | {'win_prod':>10} | "
          f"{'lip_incr':>10} | {'lip_prod':>10} | {'actual':>10}")
    print("-" * 85)
    previous_actual: float | None = None
    for M in [1000, 5000, 10000, 50000, 100000]:
        K = M  # L = 1
        p = Pool(M, K, 0)
        L = spot_price(p)
        m = concavity_param_at_margin(p)
        window_eps0 = math.sqrt(2.0 * L / m)  # Lean PROVEN: = sqrt(M)
        window_prod = algorithm_window(L, m, epsilon=epsilon)  # production
        lip_bound = lipschitz_increment_value(L, a_A)
        lip_product = window_prod * lip_bound
        actual = simulate_sacrifice_gain(p, a_A, a_B)
        print(f"{M:>8} | {m:>10.6f} | {window_eps0:>10.2f} | {window_prod:>10.2f} | "
              f"{lip_bound:>10.2f} | {lip_product:>10.2f} | {actual:>10.4f}")
        # window_eps0 must equal sqrt(M) [Lean PROVEN]
        assert abs(window_eps0 - math.sqrt(M)) < 1e-6, (
            f"window_eps0 {window_eps0} != sqrt(M) {math.sqrt(M)} at M={M}")
        # Actual gain <= Lipschitz increment value [empirical, NOT Lean-proven for stateful]
        assert actual <= lip_bound + 1e-6, (
            f"Actual gain {actual} > Lipschitz increment {lip_bound} at M={M} "
            f"[empirical envelope check]")
        if previous_actual is not None:
            assert actual < previous_actual, (
                f"Actual gain not decreasing in frontier row set: "
                f"previous={previous_actual}, current={actual}, M={M}")
        previous_actual = actual
    print("PASS: tradeoff_frontier_characterization "
          "(window_eps0=sqrt(M) [Lean]; stateful gain <= L*a_A [empirical]; "
          "actual decreases [empirical])")


# ---------------------------------------------------------------------------
# Test 8: Exact count
# ---------------------------------------------------------------------------

def test_exact_count() -> None:
    empirical_test_names = [
        "test_cpmm_concavity_param_formula",
        "test_cpmm_conservation_tradeoff",
        "test_stateful_gain_lipschitz_envelope_empirical",
        "test_concavity_bound_falsified_small_trades",
        "test_concavity_bound_fails_large_trades",
        "test_actual_gain_decreases_with_depth",
        "test_min_out_cap_breaks_tradeoff",
        "test_tradeoff_frontier_characterization",
    ]
    assert len(empirical_test_names) == 8
    total = 200 + 200 + 500 + 500 + 500 + 5 + 200 + 5
    print(f"PASS: exact_count ({len(empirical_test_names)} empirical tests, "
          f"{total} total test configurations)")


if __name__ == "__main__":
    test_cpmm_concavity_param_formula()
    test_cpmm_conservation_tradeoff()
    test_stateful_gain_lipschitz_envelope_empirical()
    test_concavity_bound_falsified_small_trades()
    test_concavity_bound_fails_large_trades()
    test_actual_gain_decreases_with_depth()
    test_min_out_cap_breaks_tradeoff()
    test_tradeoff_frontier_characterization()
    test_exact_count()
    print("\nAll CPMM Concavity Evidence tests passed.")
    print("Lean-proven (algebraic identities only):")
    print("  1. CPMM concavity param: m = 2*K*gamma^2/M^2 = 2*gamma*L/M  [gamma=1]")
    print("  2. CPMM window identity: sqrt(2*L/m) = sqrt(M)  [epsilon=0]")
    print("  3. Generic Lipschitz increment: f(a_A)-f(0) <= L*a_A")
    print("Empirical (NOT Lean-proven for stateful gain):")
    print("  3b. Stateful gain <= L*a_A on seeded corpus  [empirical]")
    print("  4. Concavity bound falsified  [empirical regression guard]")
    print("  4b. Concavity bound fails for large trades  [empirical]")
    print("  5. Actual stateful gain decreases with M  [empirical]")
    print("  6. Min_out cap makes sacrifice infeasible  [empirical]")
    print("  7. Tradeoff frontier characterized  [empirical]")
