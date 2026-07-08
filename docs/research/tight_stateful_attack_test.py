#!/usr/bin/env python3
"""Empirical verification of the tight stateful attack bound (P5).

Verifies the Lean theorems in `ConcavityConservationLaw.lean`:

1. `cpmm_stateful_gain_bound_tight`:
   gain <= K*a_A/(M+a_A)  (tight, depth-dependent)

2. `cpmm_stateful_gain_bound` (existing):
   gain <= K*a_A/M  (Lipschitz, depth-independent in form)

3. `tight_bound_stricter_than_lipschitz`:
   K*a_A/(M+a_A) < K*a_A/M  for a_A > 0

4. `tight_bound_decreases_with_M`:
   M1 < M2 => K*a_A/(M2+a_A) < K*a_A/(M1+a_A)

Key insight: the tight bound K*a_A/(M+a_A) is exactly the output of the
sacrificial trade. The attacker's maximum gain is bounded by what the
sacrificial trade itself produces. This is depth-dependent: deeper pools
reduce the bound.

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


def stateful_attack_gain(K: float, M: float, a_A: float, a_B: float) -> float:
    """Stateful sacrifice attack gain (fee-free).

    gain = out_B_without_A - out_B_with_A
         = K*a_B/(M+a_B) - K*M*a_B/((M+a_A)*(M+a_A+a_B))

    Matches Lean `cpmm_stateful_gain_bound_tight`.
    """
    out_without = K * a_B / (M + a_B)
    out_with = K * M * a_B / ((M + a_A) * (M + a_A + a_B))
    return out_without - out_with


def stateful_attack_gain_with_fee(
    K: float, M: float, a_A: float, a_B: float, gamma: float
) -> float:
    """Stateful attack gain with fee factor gamma in [0, 1]."""
    out_without = K * gamma * a_B / (M + gamma * a_B)
    out_with = K * M * gamma * a_B / (
        (M + gamma * a_A) * (M + gamma * a_A + gamma * a_B)
    )
    return out_without - out_with


def lipschitz_bound(K: float, M: float, a_A: float) -> float:
    """Lipschitz bound: K*a_A/M."""
    return K * a_A / M


def tight_bound(K: float, M: float, a_A: float) -> float:
    """Tight bound: K*a_A/(M+a_A) = output of sacrificial trade."""
    return K * a_A / (M + a_A)


def tight_bound_with_fee(K: float, M: float, a_A: float, gamma: float) -> float:
    """Tight bound with fee: gamma*K*a_A/(M+gamma*a_A)."""
    return gamma * K * a_A / (M + gamma * a_A)


# ---------------------------------------------------------------------------
# Test 1: Tight bound holds (gain <= K*a_A/(M+a_A))
# ---------------------------------------------------------------------------

def test_tight_bound_holds():
    """Verify gain <= tight_bound for all random trials."""
    rng = random.Random(42)
    violations = 0
    max_ratio = 0.0  # gain / tight_bound
    for _ in range(10000):
        K = float(rng.randint(100, 10000))
        M = float(rng.randint(100, 10000))
        a_A = float(rng.randint(1, 500))
        a_B = float(rng.randint(1, 500))
        gain = stateful_attack_gain(K, M, a_A, a_B)
        bound = tight_bound(K, M, a_A)
        if bound > 0:
            max_ratio = max(max_ratio, gain / bound)
        if gain > bound + 1e-9:
            violations += 1
            print(f"  VIOLATION: gain={gain} bound={bound} "
                  f"K={K} M={M} a_A={a_A} a_B={a_B}")
    assert violations == 0, f"{violations} tight bound violations"
    print(f"  PASS: 10000 random trials, 0 violations, "
          f"max gain/bound ratio = {max_ratio:.6f}")


# ---------------------------------------------------------------------------
# Test 2: Tight bound is stricter than Lipschitz
# K*a_A/(M+a_A) < K*a_A/M for a_A > 0
# ---------------------------------------------------------------------------

def test_tight_stricter_than_lipschitz():
    """Verify tight bound is always strictly less than Lipschitz bound."""
    rng = random.Random(42)
    violations = 0
    max_ratio = 0.0  # tight / lipschitz (lower is tighter)
    for _ in range(10000):
        K = float(rng.randint(100, 10000))
        M = float(rng.randint(100, 10000))
        a_A = float(rng.randint(1, 500))
        tight = tight_bound(K, M, a_A)
        lip = lipschitz_bound(K, M, a_A)
        ratio = tight / lip if lip > 0 else 1.0
        max_ratio = max(max_ratio, ratio)
        if tight >= lip:
            violations += 1
            print(f"  VIOLATION: tight={tight} >= lipschitz={lip} "
                  f"K={K} M={M} a_A={a_A}")
    assert violations == 0, f"{violations} tight >= lipschitz violations"
    print(f"  PASS: 10000 random trials, tight < lipschitz always, "
          f"max tight/lipschitz ratio = {max_ratio:.6f}")


# ---------------------------------------------------------------------------
# Test 3: Tight bound decreases with pool depth M
# M1 < M2 => K*a_A/(M2+a_A) < K*a_A/(M1+a_A)
# ---------------------------------------------------------------------------

def test_decreases_with_M():
    """Verify tight bound decreases as M increases."""
    rng = random.Random(42)
    violations = 0
    for _ in range(10000):
        K = float(rng.randint(100, 10000))
        a_A = float(rng.randint(1, 500))
        M1 = float(rng.randint(100, 5000))
        M2 = M1 + float(rng.randint(1, 5000))  # M2 > M1
        b1 = tight_bound(K, M1, a_A)
        b2 = tight_bound(K, M2, a_A)
        if b2 >= b1:
            violations += 1
            print(f"  VIOLATION: b(M2)={b2} >= b(M1)={b1} "
                  f"K={K} M1={M1} M2={M2} a_A={a_A}")
    assert violations == 0, f"{violations} monotonicity violations"
    print(f"  PASS: 10000 random trials, bound decreases with M always")


# ---------------------------------------------------------------------------
# Test 4: Tight bound with fee holds
# gain_fee <= gamma*K*a_A/(M+gamma*a_A)
# ---------------------------------------------------------------------------

def test_tight_bound_with_fee_holds():
    """Verify fee-bearing tight bound holds."""
    rng = random.Random(42)
    violations = 0
    max_ratio = 0.0
    for _ in range(10000):
        K = float(rng.randint(100, 10000))
        M = float(rng.randint(100, 10000))
        a_A = float(rng.randint(1, 500))
        a_B = float(rng.randint(1, 500))
        gamma = rng.randint(0, 100) / 100.0  # gamma in [0, 1]
        gain = stateful_attack_gain_with_fee(K, M, a_A, a_B, gamma)
        bound = tight_bound_with_fee(K, M, a_A, gamma)
        if bound > 0:
            max_ratio = max(max_ratio, gain / bound)
        if gain > bound + 1e-9:
            violations += 1
            print(f"  VIOLATION: gain={gain} bound={bound} "
                  f"K={K} M={M} a_A={a_A} a_B={a_B} gamma={gamma}")
    assert violations == 0, f"{violations} fee tight bound violations"
    print(f"  PASS: 10000 random trials, 0 violations, "
          f"max gain/bound ratio = {max_ratio:.6f}")


# ---------------------------------------------------------------------------
# Test 5: Tight bound equals sacrificial output
# K*a_A/(M+a_A) = cpmm_output_cont(K, M, a_A)
# ---------------------------------------------------------------------------

def test_tight_equals_sacrificial_output():
    """Verify the tight bound is exactly the sacrificial trade output."""
    rng = random.Random(42)
    violations = 0
    for _ in range(1000):
        K = float(rng.randint(100, 10000))
        M = float(rng.randint(100, 10000))
        a_A = float(rng.randint(1, 500))
        bound = tight_bound(K, M, a_A)
        sacrificial = cpmm_output_cont(K, M, a_A)
        if abs(bound - sacrificial) > 1e-9:
            violations += 1
            print(f"  VIOLATION: bound={bound} != sacrificial={sacrificial} "
                  f"K={K} M={M} a_A={a_A}")
    assert violations == 0, f"{violations} bound != sacrificial violations"
    print(f"  PASS: 1000 random trials, tight bound = sacrificial output")


# ---------------------------------------------------------------------------
# Test 6: Witness non-vacuity
# Concrete case showing tight < lipschitz and gain <= tight
# ---------------------------------------------------------------------------

def test_witness_non_vacuity():
    """Verify the concrete witness case."""
    K, M, a_A, a_B = 1000.0, 1000.0, 100.0, 100.0
    gain = stateful_attack_gain(K, M, a_A, a_B)
    tight = tight_bound(K, M, a_A)
    lip = lipschitz_bound(K, M, a_A)
    assert gain <= tight + 1e-9, f"gain={gain} > tight={tight}"
    assert tight < lip, f"tight={tight} >= lipschitz={lip}"
    print(f"  PASS: gain={gain:.6f}, tight={tight:.4f}, lipschitz={lip:.4f}")
    print(f"  Tight is {tight/lip:.1%} of lipschitz, "
          f"gain is {gain/tight:.1%} of tight")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("=== P5: Tight Stateful Attack Bound Empirical Verification ===\n")

    print("Test 1: Tight bound holds (gain <= K*a_A/(M+a_A))")
    test_tight_bound_holds()
    print()

    print("Test 2: Tight stricter than Lipschitz (K*a_A/(M+a_A) < K*a_A/M)")
    test_tight_stricter_than_lipschitz()
    print()

    print("Test 3: Tight bound decreases with pool depth M")
    test_decreases_with_M()
    print()

    print("Test 4: Tight bound with fee holds")
    test_tight_bound_with_fee_holds()
    print()

    print("Test 5: Tight bound equals sacrificial output")
    test_tight_equals_sacrificial_output()
    print()

    print("Test 6: Witness non-vacuity")
    test_witness_non_vacuity()
    print()

    print("=== All tests passed ===")
