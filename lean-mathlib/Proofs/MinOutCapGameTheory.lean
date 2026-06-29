/-
# Min-Out Cap Game Theory: Fixed-Order Filled-User No-Gain

This file formalizes the precise game-theoretic property behind the empirical
min_out cap evidence in `nash_equilibrium_min_out_cap_test.py`.

## What Is Proven Here

1. `cpmm_output_independent_of_min_out`: The CPMM output function
   `f(x) = K*gamma*x/(M+gamma*x)` does not depend on min_out. This is
   trivially true by definition but is the key structural fact.

2. `filled_user_lower_min_out_still_fills`: If a user fills at min_out_t
   (output >= min_out_t) and deviates to min_out_d <= min_out_t, then the
   user still fills at min_out_d (output >= min_out_d). This is the fill
   invariance lemma.

3. `filled_user_lower_min_out_same_output`: Under the above conditions,
   the user's output is identical (since output depends only on pool state
   and amount_in, not min_out).

4. `filled_user_no_profitable_deviation`: Under fixed ordering, a filled
   user cannot increase their output by lowering min_out. This is the
   no-gain property. It is NOT a full Nash equilibrium for the (A,B)
   optimal ordering game.

## What Is NOT Proven Here

- No full Nash equilibrium for the (A,B) optimal ordering game. The
  (A,B) game involves strategic ordering changes, which are not modeled.
- No claim that unfilled users can't benefit from lowering min_out. They
  CAN benefit (by becoming filled), which is welfare-improving, not
  strategic manipulation.
- No claim about the (A,B) batch clearing mechanism with optimal ordering.
  The theorem applies to FIXED ordering only.
- No monotonicity of welfare or collusion resistance with respect to the
  cap ratio alpha. Those are empirical observations.

## Game Definition

The game is:
- Players: n users, each submitting (amount_in_i, min_out_i)
- Strategy: choice of min_out_i (capped at alpha * expected_output_i)
- Ordering: FIXED by user_id (NOT strategic)
- Utility: output_i (tokens received), NOT surplus (output - min_out)
- Fill rule: user i fills iff cpmm_output(pool_state, amount_in_i) >= min_out_i
- State transition: if filled, pool updates (M += gamma*amount_in, K -= output)

The no-gain property: for a FILLED user under fixed ordering, no deviation
to a lower min_out increases utility (output). This is because:
1. Output depends only on pool state and amount_in, not min_out.
2. Lowering min_out preserves fill status (output >= min_out_t >= min_out_d).
3. Same fill status → same pool state transition → same downstream outcomes.

## Verification

Compile: `cd lean-mathlib && lake env lean Proofs/MinOutCapGameTheory.lean`
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic

open Real

/-- CPMM output function: f(x) = K*gamma*x / (M + gamma*x).
    This is the standard constant-product market maker output with fee gamma. -/
noncomputable def cpmmOutput (K M gamma x : ℝ) : ℝ :=
  K * gamma * x / (M + gamma * x)

/-- A user submission: (amount_in, min_out). The user fills iff
    cpmm_output(pool, amount_in) >= min_out. -/
structure UserSubmission where
  amount_in : ℝ
  min_out : ℝ

/-- The fill decision: user fills iff output >= min_out. -/
noncomputable def fillsAt (K M gamma : ℝ) (u : UserSubmission) : Bool :=
  cpmmOutput K M gamma u.amount_in ≥ u.min_out

/-- **CPMM Output Independent of Min-Out**: The CPMM output function
    does not depend on min_out. This is trivially true by definition
    but is the key structural fact behind the no-gain property. -/
theorem cpmm_output_independent_of_min_out
    (K M gamma : ℝ) (u₁ u₂ : UserSubmission)
    (h_amt : u₁.amount_in = u₂.amount_in)
    : cpmmOutput K M gamma u₁.amount_in = cpmmOutput K M gamma u₂.amount_in := by
  rw [h_amt]

/-- **Filled User Lower Min-Out Still Fills**: If a user fills at
    min_out_t (output >= min_out_t) and deviates to min_out_d <= min_out_t,
    then the user still fills at min_out_d.

    Proof: output >= min_out_t >= min_out_d, so output >= min_out_d. -/
theorem filled_user_lower_min_out_still_fills
    (K M gamma : ℝ) (u_t u_d : UserSubmission)
    (h_amt : u_t.amount_in = u_d.amount_in)
    (h_filled : cpmmOutput K M gamma u_t.amount_in ≥ u_t.min_out)
    (h_lower : u_d.min_out ≤ u_t.min_out)
    : cpmmOutput K M gamma u_d.amount_in ≥ u_d.min_out := by
  have h_output_eq : cpmmOutput K M gamma u_d.amount_in = cpmmOutput K M gamma u_t.amount_in := by
    rw [h_amt]
  rw [h_output_eq]
  exact le_trans h_lower h_filled

/-- **Filled User Lower Min-Out Same Output**: Under the conditions of
    `filled_user_lower_min_out_still_fills`, the user's output is identical
    at min_out_t and min_out_d, since output depends only on pool state
    and amount_in, not min_out. -/
theorem filled_user_lower_min_out_same_output
    (K M gamma : ℝ) (u_t u_d : UserSubmission)
    (h_amt : u_t.amount_in = u_d.amount_in)
    : cpmmOutput K M gamma u_t.amount_in = cpmmOutput K M gamma u_d.amount_in := by
  rw [h_amt]

/-- **Filled User No Profitable Deviation**: Under fixed ordering, a filled
    user cannot increase their output by lowering min_out.

    This is the no-gain property. It is NOT a full Nash equilibrium for the
    (A,B) optimal ordering game. It applies to FILLED users under FIXED
    ordering only.

    Proof: output at min_out_t = output at min_out_d (by output independence),
    so deviation_output <= truthful_output is trivially output = output. -/
theorem filled_user_no_profitable_deviation
    (K M gamma : ℝ) (u_t u_d : UserSubmission)
    (h_amt : u_t.amount_in = u_d.amount_in)
    (_h_filled : cpmmOutput K M gamma u_t.amount_in ≥ u_t.min_out)
    (_h_lower : u_d.min_out ≤ u_t.min_out)
    : cpmmOutput K M gamma u_d.amount_in ≤ cpmmOutput K M gamma u_t.amount_in := by
  rw [h_amt]

/-- **Batch State Invariance**: If a filled user deviates to a lower min_out,
    the pool state after processing that user is identical. This is because:
    1. The user still fills (by `filled_user_lower_min_out_still_fills`)
    2. The output is the same (by `filled_user_lower_min_out_same_output`)
    3. Same fill status + same output → same state transition

    The pool state after a filled user is:
    M' = M + gamma * amount_in
    K' = K - output

    Both M' and K' are unchanged by the min_out deviation. -/
theorem batch_state_invariant_after_filled_deviation
    (K M gamma : ℝ) (u_t u_d : UserSubmission)
    (h_amt : u_t.amount_in = u_d.amount_in)
    (_h_filled : cpmmOutput K M gamma u_t.amount_in ≥ u_t.min_out)
    (_h_lower : u_d.min_out ≤ u_t.min_out)
    : (M + gamma * u_d.amount_in, K - cpmmOutput K M gamma u_d.amount_in)
      = (M + gamma * u_t.amount_in, K - cpmmOutput K M gamma u_t.amount_in) := by
  rw [h_amt]

/-- **No-Gain is NOT Nash Equilibrium**: This is a documentation theorem
    that explicitly states the scope limitation. The no-gain property holds
    only for FILLED users under FIXED ordering. It does NOT constitute a
    Nash equilibrium for the full (A,B) optimal ordering game.

    A full Nash equilibrium would require:
    1. Modeling strategic ordering (users choose position, not just min_out)
    2. Analyzing unfilled users (who CAN benefit from lowering min_out)
    3. Analyzing cross-user effects (one user's deviation affecting others)

    The fixed-order no-gain property is a NECESSARY condition for Nash
    equilibrium but NOT SUFFICIENT. -/
theorem no_gain_not_nash_scope_note
    (K M gamma : ℝ) (u_t u_d : UserSubmission)
    (h_amt : u_t.amount_in = u_d.amount_in)
    (_h_filled : cpmmOutput K M gamma u_t.amount_in ≥ u_t.min_out)
    (_h_lower : u_d.min_out ≤ u_t.min_out)
    : cpmmOutput K M gamma u_d.amount_in = cpmmOutput K M gamma u_t.amount_in := by
  rw [h_amt]
