import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Funding Imbalance EV

Manual Lean proofs for a core game-theoretic finding from the funding-rate market:
under positive long/short stake sizes, the canonical imbalance expression

`(L - S)^2 / (2 * L * S)`

is non-negative, and it is zero iff the market is perfectly balanced (`L = S`).

This formalizes the structural shape of the EV term observed in wave analysis.
-/

namespace Proofs
namespace FundingImbalanceEV

/-- Canonical imbalance expression (in rational arithmetic). -/
def dualEV (L S : ℚ) : ℚ := (L - S) ^ 2 / (2 * L * S)

/-- The imbalance EV term is always non-negative for positive long/short stakes. -/
theorem dualEV_nonneg {L S : ℚ} (hL : 0 < L) (hS : 0 < S) :
    0 ≤ dualEV L S := by
  unfold dualEV
  apply div_nonneg
  · exact sq_nonneg (L - S)
  · nlinarith

/-- The imbalance EV term is zero exactly at perfect balance (`L = S`). -/
theorem dualEV_eq_zero_iff {L S : ℚ} (hL : 0 < L) (hS : 0 < S) :
    dualEV L S = 0 ↔ L = S := by
  have h2L_ne : (2 * L) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (ne_of_gt hL)
  have hden_ne : (2 * L * S) ≠ 0 := by
    exact mul_ne_zero h2L_ne (ne_of_gt hS)
  unfold dualEV
  constructor
  · intro hzero
    have hsq : (L - S) ^ 2 = 0 := by
      field_simp [hden_ne] at hzero
      nlinarith
    have hdiff : L - S = 0 := sq_eq_zero_iff.mp hsq
    linarith
  · intro hEq
    subst hEq
    simp

/-- Strict positivity holds exactly when the imbalance is non-zero (`L ≠ S`). -/
theorem dualEV_pos_iff {L S : ℚ} (hL : 0 < L) (hS : 0 < S) :
    0 < dualEV L S ↔ L ≠ S := by
  constructor
  · intro hpos hEq
    subst hEq
    simp [dualEV] at hpos
  · intro hneq
    have hnonneg : 0 ≤ dualEV L S := dualEV_nonneg hL hS
    have hne0 : dualEV L S ≠ 0 := by
      intro hzero
      exact hneq ((dualEV_eq_zero_iff hL hS).mp hzero)
    have h0ne : (0 : ℚ) ≠ dualEV L S := by
      intro hz
      exact hne0 hz.symm
    exact lt_of_le_of_ne hnonneg h0ne

/-- Non-vacuity witness: imbalance EV is strictly positive when `L ≠ S`. -/
theorem witness_dualEV_positive :
    0 < dualEV 7 3 := by
  have hL : (0 : ℚ) < 7 := by norm_num
  have hS : (0 : ℚ) < 3 := by norm_num
  have hneq : (7 : ℚ) ≠ 3 := by norm_num
  exact (dualEV_pos_iff hL hS).2 hneq

end FundingImbalanceEV
end Proofs
