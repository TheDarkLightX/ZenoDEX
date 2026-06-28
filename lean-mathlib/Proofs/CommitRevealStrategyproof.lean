/-
# Strategyproofness of Commit-Reveal + Fixed Ordering

This file proves that the commit-reveal + fixed ordering mechanism is
strategyproof when `amount_in` is binding (committed before the batch).

## Theorem

With fixed execution order and binding `amount_in`, misreporting `min_out`
can never strictly increase a user's quasilinear utility.

## Proof sketch

With fixed ordering, the user's position in the batch is independent of their
reported `min_out`. The only effect of changing `min_out` is whether the trade
fills or not:

1. **Raising `min_out`**: can only cause a filled trade to become unfilled.
   Utility goes from `out - min_out_true ≥ 0` to `0`. Strictly harmful.

2. **Lowering `min_out`**: can only cause an unfilled trade to fill.
   If the trade was unfilled at `min_out_true`, then `out < min_out_true`.
   Utility becomes `out - min_out_true < 0`, which is worse than `0` (not filling).
   Strictly harmful.

Both directions are strictly harmful or neutral, so no misreport helps.
-/

import Mathlib.Tactic

/-- Main theorem: No misreport of min_out can strictly increase utility.
    With fixed ordering and binding amount_in, the output `out` is independent
    of the reported `min_out`. The outcome is:
    - if `out ≥ min_out_reported`: utility = `out - min_out_true`
    - else: utility = `0`
    Truthful reporting uses `min_out_reported = min_out_true`. -/
theorem commit_reveal_fixed_order_strategyproof :
    ∀ (out min_out_true min_out_reported : ℤ),
      (if out ≥ min_out_true then out - min_out_true else 0) ≥
      (if out ≥ min_out_reported then out - min_out_true else 0)
  := by
  intro out min_out_true min_out_reported
  -- Case 1: trade fills at true min_out (out ≥ min_out_true)
  by_cases h_true : out ≥ min_out_true
  · -- True: filled, utility_true = out - min_out_true
    by_cases h_rep : out ≥ min_out_reported
    · -- Both fill: same utility
      simp [h_true, h_rep]
    · -- True fills, reported doesn't: true utility ≥ 0 > 0 = reported utility
      simp [h_true, h_rep]
  · -- True: not filled, utility_true = 0
    by_cases h_rep : out ≥ min_out_reported
    · -- True doesn't fill, reported does: reported utility < 0 ≤ 0 = true utility
      simp [h_true, h_rep]
      omega
    · -- Neither fills: both 0
      simp [h_true, h_rep]

/-- Corollary: The commit-reveal + fixed ordering mechanism is strategyproof.
    No user can strictly increase their utility by misreporting min_out,
    given that amount_in is binding (commit-reveal) and the execution order
    is fixed (submission order). -/
theorem commit_reveal_fixed_order_SP :
    ∀ (out min_out_true min_out_reported : ℤ),
      ¬ ((if out ≥ min_out_reported then out - min_out_true else 0) >
         if out ≥ min_out_true then out - min_out_true else 0)
  := by
  intro out min_out_true min_out_reported h_violation
  have h_sp :=
    commit_reveal_fixed_order_strategyproof out min_out_true min_out_reported
  -- h_sp: true ≥ reported, h_violation: reported > true → contradiction
  by_cases h_true : out ≥ min_out_true
  · by_cases h_rep : out ≥ min_out_reported
    · -- Both fill: same utility, can't have a > a
      simp [h_true, h_rep] at h_violation
    · -- True fills, reported doesn't: reported = 0, true = out - min_out_true ≥ 0
      simp [h_true, h_rep] at h_violation h_sp
      omega
  · by_cases h_rep : out ≥ min_out_reported
    · -- True doesn't fill, reported does: reported = out - min_out_true < 0, true = 0
      simp [h_true, h_rep] at h_violation h_sp
      omega
    · -- Neither fills: both 0, can't have 0 > 0
      simp [h_true, h_rep] at h_violation
