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

/-! ## P4: Restricted Nash Equilibrium Among Filled Users

The broad claim "full Nash equilibrium in the min-out cap game" is FALSE.
Unfilled users can profitably deviate by lowering min_out (they go from 0
output to some output > 0). The corrected claim restricts to FILLED users
and min_out deviations only.

A filled user has two deviation directions:
1. Lower min_out: still fills, same output, same utility (no gain).
   Proven in `filled_user_no_profitable_deviation` above.
2. Raise min_out: risks becoming unfilled, utility drops to 0.

This section formalizes both directions and the restricted equilibrium.
-/

/-- **Filled User Raising Min-Out May Become Unfilled**: If a user fills
    at min_out_t and raises to min_out_d > output, the user becomes unfilled.
    Utility drops from output to 0.

    This is the key risk that prevents filled users from profitably
    raising min_out. -/
theorem filled_user_raise_min_out_becomes_unfilled
    (K M gamma : ℝ) (u_t u_d : UserSubmission)
    (h_amt : u_t.amount_in = u_d.amount_in)
    (h_raised : u_d.min_out > cpmmOutput K M gamma u_t.amount_in)
    : ¬ (cpmmOutput K M gamma u_d.amount_in ≥ u_d.min_out) := by
  have h_output_eq : cpmmOutput K M gamma u_d.amount_in = cpmmOutput K M gamma u_t.amount_in := by
    rw [h_amt]
  rw [h_output_eq]
  intro h_ge
  exact not_lt_of_ge h_ge h_raised

/-- **Restricted Equilibrium (Filled Users, Min-Out Deviations)**: Under
    fixed ordering, a filled user has no profitable min_out deviation in
    either direction:

    1. Lower min_out: utility unchanged (still fills, same output).
    2. Raise min_out: utility drops to 0 (becomes unfilled).

    This is a RESTRICTED equilibrium: it applies only to filled users and
    only to min_out deviations (not ordering or amount_in deviations).

    Non-claims:
    - NOT a full Nash equilibrium (unfilled users can profitably deviate).
    - NOT an equilibrium over input amounts (only min_out).
    - NOT a Bayesian or correlated equilibrium.
    - Unfilled user deviations are welfare-improving, not strategic manipulation. -/
theorem filled_user_no_profitable_min_out_deviation
    (K M gamma : ℝ) (u_t u_d : UserSubmission)
    (h_amt : u_t.amount_in = u_d.amount_in)
    (h_filled : cpmmOutput K M gamma u_t.amount_in ≥ u_t.min_out)
    (h_output_pos : 0 < cpmmOutput K M gamma u_t.amount_in)
    : utility K M gamma u_d ≤ utility K M gamma u_t := by
  by_cases h_lower : u_d.min_out ≤ u_t.min_out
  · -- Lower min_out: still fills, same utility
    exact filled_user_no_profitable_deviation K M gamma u_t u_d h_amt h_filled h_lower
  · -- Higher min_out: two sub-cases
    push_neg at h_lower
    by_cases h_still_fills : cpmmOutput K M gamma u_d.amount_in ≥ u_d.min_out
    · -- Still fills even with higher min_out: same output, same utility
      have h_output_eq : cpmmOutput K M gamma u_d.amount_in = cpmmOutput K M gamma u_t.amount_in := by
        rw [h_amt]
      have h_util_t : utility K M gamma u_t = cpmmOutput K M gamma u_t.amount_in := by
        unfold utility; rw [if_pos h_filled]
      have h_util_d : utility K M gamma u_d = cpmmOutput K M gamma u_d.amount_in := by
        unfold utility; rw [if_pos h_still_fills]
      rw [h_util_t, h_util_d, h_output_eq]
    · -- Becomes unfilled: utility drops to 0
      have h_util_d : utility K M gamma u_d = 0 := by
        unfold utility; rw [if_neg h_still_fills]
      have h_util_t : utility K M gamma u_t = cpmmOutput K M gamma u_t.amount_in := by
        unfold utility; rw [if_pos h_filled]
      rw [h_util_d, h_util_t]
      exact le_of_lt h_output_pos

/-- **Unfilled User Can Profitably Deviate**: An unfilled user (output <
    min_out_t) can profitably deviate by lowering min_out to 0, becoming
    filled with positive output.

    This FALSIFIES the broad claim of full Nash equilibrium. The restricted
    equilibrium applies only to filled users. -/
theorem unfilled_user_profitable_deviation
    (K M gamma : ℝ) (u_t u_d : UserSubmission)
    (h_amt : u_t.amount_in = u_d.amount_in)
    (h_unfilled : cpmmOutput K M gamma u_t.amount_in < u_t.min_out)
    (h_output_pos : 0 < cpmmOutput K M gamma u_t.amount_in)
    (h_dev_fills : cpmmOutput K M gamma u_d.amount_in ≥ u_d.min_out)
    : utility K M gamma u_t < utility K M gamma u_d := by
  have h_util_t : utility K M gamma u_t = 0 := by
    unfold utility
    rw [if_neg]
    intro h_ge
    exact not_lt_of_ge h_ge h_unfilled
  have h_util_d : utility K M gamma u_d = cpmmOutput K M gamma u_d.amount_in := by
    unfold utility
    rw [if_pos h_dev_fills]
  rw [h_util_t, h_util_d]
  have h_output_eq : cpmmOutput K M gamma u_d.amount_in = cpmmOutput K M gamma u_t.amount_in := by
    rw [h_amt]
  rw [h_output_eq]
  exact h_output_pos

/-- **Witness: Unfilled User Profitable Deviation**: Concrete case showing
    an unfilled user can profit by lowering min_out.

    K=1000, M=1000, gamma=1, amount_in=50, min_out_t=60 (unfilled, output=47.6),
    min_out_d=0 (filled, utility=47.6 > 0). -/
theorem witness_unfilled_profitable_deviation :
    utility 1000 1000 1 { amount_in := 50, min_out := 60 } <
    utility 1000 1000 1 { amount_in := 50, min_out := 0 } := by
  have h_output : cpmmOutput 1000 1000 1 50 = 1000 * 1 * 50 / (1000 + 1 * 50) := by rfl
  have h_output_val : cpmmOutput 1000 1000 1 50 = 50000 / 1050 := by
    rw [h_output]; ring_nf
  have h_unfilled : cpmmOutput 1000 1000 1 50 < 60 := by
    rw [h_output_val]; norm_num
  have h_filled : cpmmOutput 1000 1000 1 50 ≥ 0 := by
    rw [h_output_val]; norm_num
  have h_util_t : utility 1000 1000 1 { amount_in := 50, min_out := 60 } = 0 := by
    unfold utility
    rw [if_neg]
    intro h_ge
    exact not_lt_of_ge h_ge h_unfilled
  have h_util_d : utility 1000 1000 1 { amount_in := 50, min_out := 0 } =
      cpmmOutput 1000 1000 1 50 := by
    unfold utility
    rw [if_pos h_filled]
  rw [h_util_t, h_util_d, h_output_val]
  norm_num

/-! ## Surplus-Based Utility Variant

The main theorems use a binary utility (output if filled, 0 otherwise).
A more natural game-theoretic payoff is **surplus**: `output - min_out`
if filled, 0 otherwise. Under surplus utility, the result changes:

- **Binary utility**: filled users have no profitable min_out deviation
  (restricted equilibrium — `filled_user_no_profitable_min_out_deviation`).
- **Surplus utility**: lowering min_out strictly *increases* surplus
  (preference revelation improvement, not a no-gain result). The best
  response is `min_out = 0`, which is a *truthful revelation* result
  rather than a no-deviation equilibrium.

The key insight: under surplus utility, a filled user lowering min_out
strictly increases surplus (surplus = output - min_out, and min_out
decreases while output stays fixed). This is beneficial to the user
but is a preference revelation improvement, not a strategic manipulation
of the mechanism.

Raising min_out still risks becoming unfilled (surplus drops to 0).

The surplus variant shows that the mechanism incentivizes truthful
preference revelation (min_out = 0) under surplus utility, complementing
the no-gain result under binary utility.
-/

/-- **Surplus utility function**: a user's surplus is `output - min_out`
    if they fill, and 0 if they don't fill.

    This is the natural game-theoretic payoff: the user gets the surplus
    over their minimum threshold if their order executes. -/
noncomputable def surplusUtility (K M gamma : ℝ) (u : UserSubmission) : ℝ :=
  if cpmmOutput K M gamma u.amount_in ≥ u.min_out then
    cpmmOutput K M gamma u.amount_in - u.min_out
  else 0

/-- **Filled user lowering min_out increases surplus**: if a filled user
    deviates to a lower min_out (and still fills), their surplus strictly
    increases.

    This is NOT a strategic manipulation — it is a preference revelation
    improvement. The user truthfully reports a lower reservation price and
    captures more surplus. The mechanism's fill guarantee is what makes
    this safe. -/
theorem filled_user_lower_min_out_surplus_increases
    (K M gamma : ℝ) (u_t u_d : UserSubmission)
    (h_amt : u_t.amount_in = u_d.amount_in)
    (h_filled : cpmmOutput K M gamma u_t.amount_in ≥ u_t.min_out)
    (h_lower : u_d.min_out < u_t.min_out)
    (h_dev_fills : cpmmOutput K M gamma u_d.amount_in ≥ u_d.min_out) :
    surplusUtility K M gamma u_t < surplusUtility K M gamma u_d := by
  have h_output_eq : cpmmOutput K M gamma u_d.amount_in = cpmmOutput K M gamma u_t.amount_in := by
    rw [h_amt]
  have h_util_t : surplusUtility K M gamma u_t =
      cpmmOutput K M gamma u_t.amount_in - u_t.min_out := by
    unfold surplusUtility; rw [if_pos h_filled]
  have h_util_d : surplusUtility K M gamma u_d =
      cpmmOutput K M gamma u_d.amount_in - u_d.min_out := by
    unfold surplusUtility; rw [if_pos h_dev_fills]
  rw [h_util_t, h_util_d, h_output_eq]
  have h_key : cpmmOutput K M gamma u_t.amount_in - u_d.min_out >
      cpmmOutput K M gamma u_t.amount_in - u_t.min_out := by
    linarith
  exact h_key

/-- **Filled user raising min_out to unfilled drops surplus to 0**: if a
    filled user raises min_out above their output, they become unfilled
    and surplus drops to 0, which is less than or equal to their current
    surplus (equality when `output = min_out_t`). -/
theorem filled_user_raise_min_out_surplus_drops
    (K M gamma : ℝ) (u_t u_d : UserSubmission)
    (h_amt : u_t.amount_in = u_d.amount_in)
    (h_filled : cpmmOutput K M gamma u_t.amount_in ≥ u_t.min_out)
    (h_raised : u_d.min_out > cpmmOutput K M gamma u_t.amount_in) :
    surplusUtility K M gamma u_d ≤ surplusUtility K M gamma u_t := by
  have h_output_eq : cpmmOutput K M gamma u_d.amount_in = cpmmOutput K M gamma u_t.amount_in := by
    rw [h_amt]
  have h_unfilled_d : ¬ (cpmmOutput K M gamma u_d.amount_in ≥ u_d.min_out) := by
    rw [h_output_eq]
    intro h_ge
    exact not_lt_of_ge h_ge h_raised
  have h_util_d : surplusUtility K M gamma u_d = 0 := by
    unfold surplusUtility; rw [if_neg h_unfilled_d]
  have h_util_t : surplusUtility K M gamma u_t =
      cpmmOutput K M gamma u_t.amount_in - u_t.min_out := by
    unfold surplusUtility; rw [if_pos h_filled]
  rw [h_util_d, h_util_t]
  have h_surplus_nonneg : 0 ≤ cpmmOutput K M gamma u_t.amount_in - u_t.min_out := by
    linarith [h_filled]
  exact h_surplus_nonneg

/-- **Surplus-based restricted equilibrium (filled users, min_out deviations)**:
    Under fixed ordering, a filled user's surplus is bounded above by the
    surplus they would get by deviating to the *lowest* feasible min_out (0).

    This means the user's *best response* in the min_out dimension is to
    report min_out = 0 (truthful preference revelation), and any higher
    min_out is weakly dominated. The mechanism incentivizes truthful
    preference revelation among filled users.

    Non-claims:
    - NOT a Nash equilibrium (lowering min_out IS profitable under surplus).
    - The result shows that min_out = 0 is the dominant strategy for filled
      users under surplus utility, which is a *truthful revelation* result.
    - Unfilled users can still profitably deviate by lowering min_out. -/
theorem filled_user_surplus_best_response_zero_min_out
    (K M gamma : ℝ) (u_t : UserSubmission)
    (_h_filled : cpmmOutput K M gamma u_t.amount_in ≥ u_t.min_out)
    (h_output_pos : 0 < cpmmOutput K M gamma u_t.amount_in) :
    ∀ u_d : UserSubmission,
      u_d.amount_in = u_t.amount_in →
      0 ≤ u_d.min_out →
      surplusUtility K M gamma u_d ≤
        surplusUtility K M gamma { amount_in := u_t.amount_in, min_out := 0 } := by
  intro u_d h_amt h_min_out_nn
  have h_output_eq : cpmmOutput K M gamma u_d.amount_in = cpmmOutput K M gamma u_t.amount_in := by
    rw [h_amt]
  by_cases h_fills : cpmmOutput K M gamma u_d.amount_in ≥ u_d.min_out
  · -- Deviation fills: surplus = output - min_out_d <= output = surplus at min_out=0
    have h_util_d : surplusUtility K M gamma u_d =
        cpmmOutput K M gamma u_d.amount_in - u_d.min_out := by
      unfold surplusUtility; rw [if_pos h_fills]
    have h_util_zero : surplusUtility K M gamma { amount_in := u_t.amount_in, min_out := 0 } =
        cpmmOutput K M gamma u_t.amount_in := by
      unfold surplusUtility
      rw [if_pos (le_of_lt h_output_pos)]
      simp
    rw [h_util_d, h_util_zero, h_output_eq]
    linarith
  · -- Deviation doesn't fill: surplus = 0 <= output = surplus at min_out=0
    have h_util_d : surplusUtility K M gamma u_d = 0 := by
      unfold surplusUtility; rw [if_neg h_fills]
    have h_util_zero : surplusUtility K M gamma { amount_in := u_t.amount_in, min_out := 0 } =
        cpmmOutput K M gamma u_t.amount_in := by
      unfold surplusUtility
      rw [if_pos (le_of_lt h_output_pos)]
      simp
    rw [h_util_d, h_util_zero]
    exact le_of_lt h_output_pos

