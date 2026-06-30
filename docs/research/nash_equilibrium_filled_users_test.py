#!/usr/bin/env python3
"""Empirical verification of the restricted Nash equilibrium (P4).

Verifies the Lean theorems in `MinOutCapGameTheory.lean`:

1. `filled_user_lower_min_out_still_fills`: Lowering min_out preserves fill.
2. `filled_user_no_profitable_deviation`: Lowering min_out gives same utility.
3. `filled_user_raise_min_out_becomes_unfilled`: Raising min_out above output
   makes the user unfilled.
4. `filled_user_no_profitable_min_out_deviation`: Filled users have no
   profitable min_out deviation in either direction (restricted equilibrium).
5. `unfilled_user_profitable_deviation`: Unfilled users CAN profitably deviate
   by lowering min_out (falsifies full Nash equilibrium).
6. `batch_state_invariant_after_filled_deviation`: Batch state unchanged
   after filled user's min_out deviation.

Key insight: The broad claim "full Nash equilibrium" is FALSE. Unfilled users
can profitably deviate. The corrected claim restricts to filled users and
min_out deviations only.

Determinism: All tests use fixed seeds. No real time, RNG, network, or fs.
"""

import random
from dataclasses import dataclass


@dataclass(frozen=True)
class UserSubmission:
    amount_in: float
    min_out: float


def cpmm_output(K: float, M: float, gamma: float, x: float) -> float:
    """cpmmOutput K M gamma x = K*gamma*x / (M + gamma*x). Matches Lean."""
    denom = M + gamma * x
    if denom <= 0.0:
        return 0.0
    return K * gamma * x / denom


def fills_at(K: float, M: float, gamma: float, u: UserSubmission) -> bool:
    """fillsAt: user fills iff output >= min_out."""
    return cpmm_output(K, M, gamma, u.amount_in) >= u.min_out


def utility(K: float, M: float, gamma: float, u: UserSubmission) -> float:
    """utility = if filled then output else 0. Matches Lean."""
    output = cpmm_output(K, M, gamma, u.amount_in)
    if output >= u.min_out:
        return output
    return 0.0


def batch_transition(K: float, M: float, gamma: float, u: UserSubmission):
    """batchTransition: (M', K') after processing user.
    If filled: (M + gamma*amt, K - output)
    If not filled: (M, K) unchanged."""
    output = cpmm_output(K, M, gamma, u.amount_in)
    if output >= u.min_out:
        return (M + gamma * u.amount_in, K - output)
    return (M, K)


# ---------------------------------------------------------------------------
# Test 1: Lowering min_out preserves fill status
# ---------------------------------------------------------------------------

def test_lower_min_out_preserves_fill():
    """Verify filled_user_lower_min_out_still_fills."""
    rng = random.Random(42)
    violations = 0
    for _ in range(10000):
        K = float(rng.randint(100, 10000))
        M = float(rng.randint(100, 10000))
        gamma = rng.randint(50, 100) / 100.0
        amt = float(rng.randint(1, 500))
        min_out_t = float(rng.randint(0, 500))
        min_out_d = float(rng.randint(0, int(max(min_out_t, 1))))
        u_t = UserSubmission(amt, min_out_t)
        u_d = UserSubmission(amt, min_out_d)
        if fills_at(K, M, gamma, u_t) and not fills_at(K, M, gamma, u_d):
            violations += 1
            print(f"  VIOLATION: t fills but d doesn't "
                  f"K={K} M={M} gamma={gamma} amt={amt} "
                  f"min_t={min_out_t} min_d={min_out_d}")
    assert violations == 0, f"{violations} fill preservation violations"
    print(f"  PASS: 10000 random trials, lowering min_out preserves fill")


# ---------------------------------------------------------------------------
# Test 2: Lowering min_out gives same utility (no profitable deviation)
# ---------------------------------------------------------------------------

def test_lower_min_out_same_utility():
    """Verify filled_user_no_profitable_deviation (lowering direction)."""
    rng = random.Random(42)
    violations = 0
    max_util_change = 0.0
    for _ in range(10000):
        K = float(rng.randint(100, 10000))
        M = float(rng.randint(100, 10000))
        gamma = rng.randint(50, 100) / 100.0
        amt = float(rng.randint(1, 500))
        min_out_t = float(rng.randint(0, 500))
        min_out_d = float(rng.randint(0, int(max(min_out_t, 1))))
        u_t = UserSubmission(amt, min_out_t)
        u_d = UserSubmission(amt, min_out_d)
        if fills_at(K, M, gamma, u_t):
            util_t = utility(K, M, gamma, u_t)
            util_d = utility(K, M, gamma, u_d)
            change = util_d - util_t
            max_util_change = max(max_util_change, abs(change))
            if util_d > util_t + 1e-9:
                violations += 1
                print(f"  VIOLATION: util_d={util_d} > util_t={util_t} "
                      f"K={K} M={M} gamma={gamma} amt={amt} "
                      f"min_t={min_out_t} min_d={min_out_d}")
    assert violations == 0, f"{violations} profitable deviation violations"
    print(f"  PASS: 10000 random trials, max utility change = {max_util_change:.9f}")


# ---------------------------------------------------------------------------
# Test 3: Raising min_out above output makes user unfilled
# ---------------------------------------------------------------------------

def test_raise_min_out_unfilled():
    """Verify filled_user_raise_min_out_becomes_unfilled."""
    rng = random.Random(42)
    violations = 0
    for _ in range(10000):
        K = float(rng.randint(100, 10000))
        M = float(rng.randint(100, 10000))
        gamma = rng.randint(50, 100) / 100.0
        amt = float(rng.randint(1, 500))
        output = cpmm_output(K, M, gamma, amt)
        # Raise min_out above output
        min_out_d = output + float(rng.randint(1, 100))
        u_d = UserSubmission(amt, min_out_d)
        if fills_at(K, M, gamma, u_d):
            violations += 1
            print(f"  VIOLATION: user fills with min_out > output "
                  f"K={K} M={M} gamma={gamma} amt={amt} "
                  f"output={output:.4f} min_d={min_out_d:.4f}")
    assert violations == 0, f"{violations} raise min_out violations"
    print(f"  PASS: 10000 random trials, raising min_out above output unfills")


# ---------------------------------------------------------------------------
# Test 4: Filled users have no profitable min_out deviation (both directions)
# ---------------------------------------------------------------------------

def test_filled_user_no_profitable_deviation_both_directions():
    """Verify filled_user_no_profitable_min_out_deviation."""
    rng = random.Random(42)
    violations = 0
    for _ in range(10000):
        K = float(rng.randint(100, 10000))
        M = float(rng.randint(100, 10000))
        gamma = rng.randint(50, 100) / 100.0
        amt = float(rng.randint(1, 500))
        output = cpmm_output(K, M, gamma, amt)
        if output <= 0:
            continue
        # Truthful min_out: user fills
        min_out_t = float(rng.randint(0, int(max(output, 1))))
        u_t = UserSubmission(amt, min_out_t)
        if not fills_at(K, M, gamma, u_t):
            continue
        # Deviate to any min_out (both directions)
        min_out_d = float(rng.randint(0, int(max(output, 1)) + 100))
        u_d = UserSubmission(amt, min_out_d)
        util_t = utility(K, M, gamma, u_t)
        util_d = utility(K, M, gamma, u_d)
        if util_d > util_t + 1e-9:
            violations += 1
            print(f"  VIOLATION: util_d={util_d} > util_t={util_t} "
                  f"K={K} M={M} gamma={gamma} amt={amt} "
                  f"output={output:.4f} min_t={min_out_t} min_d={min_out_d}")
    assert violations == 0, f"{violations} restricted equilibrium violations"
    print(f"  PASS: 10000 random trials, filled users have no profitable deviation")


# ---------------------------------------------------------------------------
# Test 5: Unfilled users CAN profitably deviate (falsifies full Nash)
# ---------------------------------------------------------------------------

def test_unfilled_user_profitable_deviation():
    """Verify unfilled_user_profitable_deviation (falsification of full Nash)."""
    rng = random.Random(42)
    profitable_count = 0
    total_unfilled = 0
    for _ in range(10000):
        K = float(rng.randint(100, 10000))
        M = float(rng.randint(100, 10000))
        gamma = rng.randint(50, 100) / 100.0
        amt = float(rng.randint(1, 500))
        output = cpmm_output(K, M, gamma, amt)
        if output <= 0:
            continue
        # Truthful min_out: user does NOT fill (min_out > output)
        min_out_t = output + float(rng.randint(1, 100))
        u_t = UserSubmission(amt, min_out_t)
        if fills_at(K, M, gamma, u_t):
            continue
        total_unfilled += 1
        # Deviate: lower min_out to 0 (becomes filled)
        u_d = UserSubmission(amt, 0.0)
        util_t = utility(K, M, gamma, u_t)
        util_d = utility(K, M, gamma, u_d)
        if util_d > util_t + 1e-9:
            profitable_count += 1
    assert profitable_count == total_unfilled, \
        f"Only {profitable_count}/{total_unfilled} unfilled users profit"
    print(f"  PASS: {profitable_count}/{total_unfilled} unfilled users "
          f"profitably deviate (full Nash is FALSE)")


# ---------------------------------------------------------------------------
# Test 6: Batch state invariant after filled deviation
# ---------------------------------------------------------------------------

def test_batch_state_invariant():
    """Verify batch_state_invariant_after_filled_deviation."""
    rng = random.Random(42)
    violations = 0
    for _ in range(10000):
        K = float(rng.randint(100, 10000))
        M = float(rng.randint(100, 10000))
        gamma = rng.randint(50, 100) / 100.0
        amt = float(rng.randint(1, 500))
        min_out_t = float(rng.randint(0, 500))
        min_out_d = float(rng.randint(0, int(max(min_out_t, 1))))
        u_t = UserSubmission(amt, min_out_t)
        u_d = UserSubmission(amt, min_out_d)
        if fills_at(K, M, gamma, u_t):
            state_t = batch_transition(K, M, gamma, u_t)
            state_d = batch_transition(K, M, gamma, u_d)
            if abs(state_t[0] - state_d[0]) > 1e-9 or \
               abs(state_t[1] - state_d[1]) > 1e-9:
                violations += 1
                print(f"  VIOLATION: state_t={state_t} != state_d={state_d} "
                      f"K={K} M={M} gamma={gamma} amt={amt} "
                      f"min_t={min_out_t} min_d={min_out_d}")
    assert violations == 0, f"{violations} batch state invariant violations"
    print(f"  PASS: 10000 random trials, batch state invariant after deviation")


# ---------------------------------------------------------------------------
# Test 7: Witness cases
# ---------------------------------------------------------------------------

def test_witness_filled_no_deviation():
    """Verify the concrete witness case for filled user no deviation."""
    K, M, gamma = 1000.0, 1000.0, 1.0
    amt = 50.0
    output = cpmm_output(K, M, gamma, amt)
    # Filled user: min_out = 40 (output ~47.6 >= 40)
    u_t = UserSubmission(amt, 40.0)
    # Deviate lower: min_out = 20
    u_d_lower = UserSubmission(amt, 20.0)
    # Deviate higher (still fills): min_out = 45
    u_d_higher_fill = UserSubmission(amt, 45.0)
    # Deviate higher (becomes unfilled): min_out = 60
    u_d_higher_unfill = UserSubmission(amt, 60.0)
    util_t = utility(K, M, gamma, u_t)
    util_lower = utility(K, M, gamma, u_d_lower)
    util_higher_fill = utility(K, M, gamma, u_d_higher_fill)
    util_higher_unfill = utility(K, M, gamma, u_d_higher_unfill)
    assert util_lower <= util_t + 1e-9, f"lower: {util_lower} > {util_t}"
    assert util_higher_fill <= util_t + 1e-9, f"higher_fill: {util_higher_fill} > {util_t}"
    assert util_higher_unfill <= util_t + 1e-9, f"higher_unfill: {util_higher_unfill} > {util_t}"
    print(f"  PASS: output={output:.4f}, util_t={util_t:.4f}")
    print(f"  Lower: util={util_lower:.4f} (same, still fills)")
    print(f"  Higher (fill): util={util_higher_fill:.4f} (same, still fills)")
    print(f"  Higher (unfill): util={util_higher_unfill:.4f} (0, unfilled)")


def test_witness_unfilled_profitable():
    """Verify the concrete witness case for unfilled user profitable deviation."""
    K, M, gamma = 1000.0, 1000.0, 1.0
    amt = 50.0
    output = cpmm_output(K, M, gamma, amt)
    # Unfilled user: min_out = 60 (output ~47.6 < 60)
    u_t = UserSubmission(amt, 60.0)
    # Deviate: min_out = 0 (becomes filled)
    u_d = UserSubmission(amt, 0.0)
    util_t = utility(K, M, gamma, u_t)
    util_d = utility(K, M, gamma, u_d)
    assert util_t == 0.0, f"unfilled util should be 0, got {util_t}"
    assert util_d > util_t, f"deviation should be profitable: {util_d} <= {util_t}"
    print(f"  PASS: output={output:.4f}, util_t={util_t:.4f}, util_d={util_d:.4f}")
    print(f"  Unfilled user profits by lowering min_out (full Nash is FALSE)")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("=== P4: Restricted Nash Equilibrium Empirical Verification ===\n")

    print("Test 1: Lowering min_out preserves fill status")
    test_lower_min_out_preserves_fill()
    print()

    print("Test 2: Lowering min_out gives same utility (no gain)")
    test_lower_min_out_same_utility()
    print()

    print("Test 3: Raising min_out above output makes user unfilled")
    test_raise_min_out_unfilled()
    print()

    print("Test 4: Filled users no profitable deviation (both directions)")
    test_filled_user_no_profitable_deviation_both_directions()
    print()

    print("Test 5: Unfilled users CAN profitably deviate (falsifies full Nash)")
    test_unfilled_user_profitable_deviation()
    print()

    print("Test 6: Batch state invariant after filled deviation")
    test_batch_state_invariant()
    print()

    print("Test 7: Witness - filled user no deviation")
    test_witness_filled_no_deviation()
    print()

    print("Test 8: Witness - unfilled user profitable deviation")
    test_witness_unfilled_profitable()
    print()

    print("=== All tests passed ===")
