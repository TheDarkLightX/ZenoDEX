/-
# Min-Out Cap Game Theory: Fixed-Order Filled-User No-Gain

This file formalizes the precise game-theoretic property behind the empirical
min_out cap evidence in `nash_equilibrium_min_out_cap_test.py`.

## Formal Definitions

- `cpmmOutput`: CPMM output function `f(x) = K*gamma*x/(M+gamma*x)`.
- `UserSubmission`: a user's (amount_in, min_out) pair.
- `fillsAt`: fill decision (output >= min_out).
- `utility`: game-theoretic payoff `if filled then output else 0`.
- `batchTransition`: conditional pool state transition
  `if filled then (M+gamma*amt, K-output) else (M, K)`.

## What Is Proven Here

1. `cpmm_output_independent_of_min_out`: The CPMM output function
   does not depend on min_out. Key structural fact.

2. `filled_user_lower_min_out_still_fills`: If a user fills at min_out_t
   and deviates to min_out_d <= min_out_t, the user still fills.
   Proof: output >= min_out_t >= min_out_d by le_trans.

3. `filled_user_lower_min_out_same_output`: Under the above conditions,
   the user's output is identical (output depends only on pool state
   and amount_in, not min_out).

4. `filled_user_no_profitable_deviation`: Under fixed ordering, a filled
   user cannot increase their UTILITY by lowering min_out. Uses the
   formal `utility` function (`if filled then output else 0`).

5. `batch_state_invariant_after_filled_deviation`: The conditional
   `batchTransition` produces the same pool state after a filled user's
   min_out deviation. Uses the formal `batchTransition` function, not
   raw algebraic equality.

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
- Utility: `utility` function = if filled then output else 0 (NOT surplus)
- Fill rule: user i fills iff cpmm_output(pool_state, amount_in_i) >= min_out_i
- State transition: `batchTransition` = if filled then (M+gamma*amt, K-out) else (M, K)

The no-gain property: for a FILLED user under fixed ordering, no deviation
to a lower min_out increases utility. This is because:
1. Output depends only on pool state and amount_in, not min_out.
2. Lowering min_out preserves fill status (output >= min_out_t >= min_out_d).
3. Same fill status → same utility → same conditional state transition.

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

/-- **Utility function**: a user's utility is their output if they fill,
    and 0 if they don't fill. This is the game-theoretic payoff function.

    Utility = if filled then output else 0
    This is NOT surplus (output - min_out); min_out is a fill threshold. -/
noncomputable def utility (K M gamma : ℝ) (u : UserSubmission) : ℝ :=
  if cpmmOutput K M gamma u.amount_in ≥ u.min_out then
    cpmmOutput K M gamma u.amount_in
  else 0

/-- **Conditional batch state transition**: after processing a user,
    the pool state is (M', K') where:
    - If filled: M' = M + gamma*amount_in, K' = K - output
    - If not filled: M' = M, K' = K (unchanged)

    Returns (M', K') as a pair. -/
noncomputable def batchTransition (K M gamma : ℝ) (u : UserSubmission) : ℝ × ℝ :=
  if cpmmOutput K M gamma u.amount_in ≥ u.min_out then
    (M + gamma * u.amount_in, K - cpmmOutput K M gamma u.amount_in)
  else
    (M, K)

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
    user cannot increase their utility by lowering min_out.

    This is the no-gain property. It is NOT a full Nash equilibrium for the
    (A,B) optimal ordering game. It applies to FILLED users under FIXED
    ordering only.

    The utility function is `if filled then output else 0`. For a filled user
    at truthful min_out, utility = output. After lowering min_out, the user
    still fills (by `filled_user_lower_min_out_still_fills`) with the same
    output (by `filled_user_lower_min_out_same_output`), so utility is
    unchanged. -/
theorem filled_user_no_profitable_deviation
    (K M gamma : ℝ) (u_t u_d : UserSubmission)
    (h_amt : u_t.amount_in = u_d.amount_in)
    (h_filled : cpmmOutput K M gamma u_t.amount_in ≥ u_t.min_out)
    (h_lower : u_d.min_out ≤ u_t.min_out)
    : utility K M gamma u_d ≤ utility K M gamma u_t := by
  -- User still fills at deviated min_out
  have h_d_fills : cpmmOutput K M gamma u_d.amount_in ≥ u_d.min_out :=
    filled_user_lower_min_out_still_fills K M gamma u_t u_d h_amt h_filled h_lower
  -- Utility at truthful = output (since filled)
  have h_util_t : utility K M gamma u_t = cpmmOutput K M gamma u_t.amount_in := by
    unfold utility
    rw [if_pos h_filled]
  -- Utility at deviated = output (since still filled)
  have h_util_d : utility K M gamma u_d = cpmmOutput K M gamma u_d.amount_in := by
    unfold utility
    rw [if_pos h_d_fills]
  -- Output is the same (depends only on amount_in, not min_out)
  rw [h_util_t, h_util_d]
  exact le_of_eq (Eq.symm (filled_user_lower_min_out_same_output K M gamma u_t u_d h_amt))

/-- **Batch State Invariance**: If a filled user deviates to a lower min_out,
    the conditional batch state transition is identical. This is because:
    1. The user still fills at deviated min_out (by `filled_user_lower_min_out_still_fills`)
    2. The output is the same (by `filled_user_lower_min_out_same_output`)
    3. Same fill status + same output → same conditional state transition

    The `batchTransition` function returns:
    - If filled: (M + gamma*amount_in, K - output)
    - If not filled: (M, K) unchanged

    Since both truthful and deviated users fill with the same output and
    amount_in, the conditional transition produces the same result. -/
theorem batch_state_invariant_after_filled_deviation
    (K M gamma : ℝ) (u_t u_d : UserSubmission)
    (h_amt : u_t.amount_in = u_d.amount_in)
    (h_filled : cpmmOutput K M gamma u_t.amount_in ≥ u_t.min_out)
    (h_lower : u_d.min_out ≤ u_t.min_out)
    : batchTransition K M gamma u_d = batchTransition K M gamma u_t := by
  -- User still fills at deviated min_out
  have h_d_fills : cpmmOutput K M gamma u_d.amount_in ≥ u_d.min_out :=
    filled_user_lower_min_out_still_fills K M gamma u_t u_d h_amt h_filled h_lower
  -- Both transitions take the filled branch
  unfold batchTransition
  rw [if_pos h_d_fills, if_pos h_filled]
  -- Now both sides are (M + gamma*amount_in, K - output)
  -- amount_in is the same, output is the same
  rw [h_amt]

/-! ## Scope Limitation: No-Gain is NOT Nash Equilibrium

   The no-gain property (`filled_user_no_profitable_deviation`) holds only
   for FILLED users under FIXED ordering. It does NOT constitute a Nash
   equilibrium for the full (A,B) optimal ordering game.

   A full Nash equilibrium would require:
   1. Modeling strategic ordering (users choose position, not just min_out)
   2. Analyzing unfilled users (who CAN benefit from lowering min_out)
   3. Analyzing cross-user effects (one user's deviation affecting others)

   The fixed-order no-gain property is a NECESSARY condition for Nash
   equilibrium but NOT SUFFICIENT. This scope note is prose, not a formal
   theorem about Nash equilibrium. -/

