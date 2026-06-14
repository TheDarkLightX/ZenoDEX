import Mathlib

/-!
# N-party clearinghouse: ADL winner-budget covers bad debt (no-insolvency core)

This is the N-party generalization of the budget bound that the runtime ADL relies
on (`src/core/perp_np_clearinghouse.py::_apply_liquidation_adl`), and it upgrades the
empirical "SettleInsolvent is not reachable from deposit->match states" observation
in `tests/core/test_perp_np_clearinghouse_adl_invariants.py` to a machine-checked
theorem for the no-funding / zero-penalty core.

Model. Each open account contributes a pair `(c, p)`:
* `c` = pre-settle collateral, assumed `0 ≤ c` (the matcher enforces initial margin,
  so every reachable open is funded);
* `p` = mark-to-market PnL for the epoch.

The book is net-zero, and MTM is zero-sum, so `∑ p = 0` (this is exactly
`pnl_e8 (position, s, mark)` summed over a net-zero book in the runtime).

Quantities (arithmetic abstraction of the runtime):
* `gain` = `∑ max 0 p`            -- total positive MTM PnL. This equals the runtime
                                     ADL haircut budget only under the additional
                                     reachable-path assumptions that positive-PnL
                                     accounts are not liquidated and the runtime
                                     winner cap `min(pnl, collateral)` is a no-op;
* `badDebt` = `∑ max 0 (-(c+p))`  -- collateral driven below zero, summed as a positive
                                     deficit (underwater accounts; they pay zero penalty,
                                     so the penalty term drops out of this core bound).

THE THEOREM: `badDebt ≤ gain`. Hence `residual = badDebt - min(badDebt, insurance) ≤
badDebt ≤ gain`. To instantiate this as `residual ≤ runtimeBudget`, the runtime-binding
tests must also show that `runtimeBudget = gain` on the scoped reachable path. This file
therefore proves the core arithmetic inequality. Runtime ADL equivalence requires the
additional runtime-binding checks above. It is a machine-checked counterpart to the
test-level corroboration and a strict generalization of the 2-leg witness in
`PerpADLSybilBankruptcyClosure.lean` to arbitrary N.

Proof idea (two clean steps):
1. Pointwise, `0 ≤ c` makes `max 0 (-(c+p)) ≤ max 0 (-p)` (the deficit can only shrink
   when collateral is added), so `badDebt ≤ ∑ max 0 (-p)`.
2. The identity `max 0 (-p) = max 0 p - p` plus `∑ p = 0` gives `∑ max 0 (-p) = gain`.
-/

namespace Internal
namespace PerpNpNoInsolvencyBudget

/-- Total positive MTM PnL. This is the ADL haircut budget only under the runtime
reachability/cap assumptions stated in the module comment. -/
def gain (book : List (ℤ × ℤ)) : ℤ := (book.map (fun cp => max 0 cp.2)).sum

/-- Bad debt: collateral driven below zero by MTM, summed as a positive deficit. -/
def badDebt (book : List (ℤ × ℤ)) : ℤ := (book.map (fun cp => max 0 (-(cp.1 + cp.2)))).sum

/-- Total mark-to-market PnL (zero on a net-zero book). -/
def pnlSum (book : List (ℤ × ℤ)) : ℤ := (book.map (fun cp => cp.2)).sum

/-- Pointwise: with non-negative collateral the deficit can only shrink. -/
theorem deficit_le_of_collateral_nonneg {c p : ℤ} (hc : 0 ≤ c) :
    max 0 (-(c + p)) ≤ max 0 (-p) := by
  have h : -(c + p) ≤ -p := by linarith
  exact max_le_max (le_refl 0) h

/-- The negative-part identity over `ℤ`: `max 0 (-p) = max 0 p - p`. -/
theorem negPart_eq (p : ℤ) : max 0 (-p) = max 0 p - p := by
  omega

/-- `badDebt ≤ ∑ max 0 (-p)` (step 1: pointwise collateral bound, lifted to the sum). -/
theorem badDebt_le_negPartSum (book : List (ℤ × ℤ))
    (hc : ∀ cp ∈ book, 0 ≤ cp.1) :
    badDebt book ≤ (book.map (fun cp => max 0 (-cp.2))).sum := by
  unfold badDebt
  induction book with
  | nil => simp
  | cons cp rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have hhead : max 0 (-(cp.1 + cp.2)) ≤ max 0 (-cp.2) :=
        deficit_le_of_collateral_nonneg (hc cp (List.mem_cons.mpr (Or.inl rfl)))
      have htail := ih (fun c hc' => hc c (List.mem_cons.mpr (Or.inr hc')))
      linarith [hhead, htail]

/-- General negative-part / positive-part decomposition over a list (no zero-sum yet):
`∑ max 0 (-p) = ∑ max 0 p - ∑ p`. -/
theorem negPartSum_eq_gain_sub_pnl (book : List (ℤ × ℤ)) :
    (book.map (fun cp => max 0 (-cp.2))).sum = gain book - pnlSum book := by
  unfold gain pnlSum
  induction book with
  | nil => simp
  | cons cp rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [negPart_eq cp.2, ih]
      ring

/-- `∑ max 0 (-p) = gain` (step 2: the decomposition above + zero-sum MTM). -/
theorem negPartSum_eq_gain (book : List (ℤ × ℤ)) (hzero : pnlSum book = 0) :
    (book.map (fun cp => max 0 (-cp.2))).sum = gain book := by
  rw [negPartSum_eq_gain_sub_pnl, hzero, sub_zero]

/-- **Main theorem**: the ADL winner budget covers the bad debt on a net-zero book
with non-negative collateral. -/
theorem badDebt_le_gain (book : List (ℤ × ℤ))
    (hc : ∀ cp ∈ book, 0 ≤ cp.1) (hzero : pnlSum book = 0) :
    badDebt book ≤ gain book := by
  calc badDebt book ≤ (book.map (fun cp => max 0 (-cp.2))).sum :=
        badDebt_le_negPartSum book hc
    _ = gain book := negPartSum_eq_gain book hzero

/-- Non-vacuity witness for `badDebt_le_gain`: a GENUINE net-zero instance -- a winner
with PnL +1000 and a bankrupt leg with PnL -1000, both posting zero collateral. The
hypotheses actually HOLD here (`pnlSum = 0`, every collateral `≥ 0`), the bad debt is
POSITIVE (1000, so the conclusion is not the trivial `0 ≤ gain`), and the budget
covers it. The 2-leg shape mirrors the runtime
`test_two_leg_offsetting_witness_matches_lean_adl_closure`. -/
theorem witness_two_leg :
    pnlSum [((0 : ℤ), (1000 : ℤ)), (0, -1000)] = 0
      ∧ (∀ cp ∈ [((0 : ℤ), (1000 : ℤ)), (0, -1000)], 0 ≤ cp.1)
      ∧ 0 < badDebt [((0 : ℤ), (1000 : ℤ)), (0, -1000)]
      ∧ badDebt [((0 : ℤ), (1000 : ℤ)), (0, -1000)]
          ≤ gain [((0 : ℤ), (1000 : ℤ)), (0, -1000)] := by
  -- the final conjunct follows from the general theorem, not just evaluation
  exact ⟨by decide, by decide, by decide, badDebt_le_gain _ (by decide) (by decide)⟩

-- Axiom audit (verified via `#print axioms`): both `badDebt_le_gain` and
-- `witness_two_leg` depend only on [propext, Classical.choice, Quot.sound] -- the
-- standard Mathlib trust base. No `sorryAx`, no `native_decide` / `ofReduceBool`.

end PerpNpNoInsolvencyBudget
end Internal
