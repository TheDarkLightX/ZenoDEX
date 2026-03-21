import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# zUSD Stability Pool Whole-Vault Liquidation Algebra

This file models the liquidation step that the shipped runtime actually performs:
- the vault's debt is set to zero
- the vault's collateral is set to zero
- the stability pool debt decreases by the liquidated debt
- the stability pool collateral increases by the liquidated collateral

So for pre-state `(sp_coll, sp_debt)` and liquidated vault `(v_coll, v_debt)`,
the post-state is:

- `sp_coll' = sp_coll + v_coll`
- `sp_debt' = sp_debt - v_debt`

This is not a convex combination. When `0 < v_debt < sp_debt`, the post ratio
`sp_coll' / sp_debt'` weakly improves over `sp_coll / sp_debt`, and it improves
strictly whenever the liquidation moves positive collateral mass.
-/

namespace Proofs
namespace ZUSDSPWholeVaultLiquidation

noncomputable def spCollAfter (sp_coll v_coll : ℚ) : ℚ :=
  sp_coll + v_coll

noncomputable def spDebtAfter (sp_debt v_debt : ℚ) : ℚ :=
  sp_debt - v_debt

noncomputable def spRatioAfter (sp_coll sp_debt v_coll v_debt : ℚ) : ℚ :=
  spCollAfter sp_coll v_coll / spDebtAfter sp_debt v_debt

/-- Cross-multiplied lower bound preservation under the runtime whole-vault step. -/
theorem whole_vault_lower_bound_preserved
    (sp_coll sp_debt v_coll v_debt m : ℚ)
    (hpre : m * sp_debt ≤ sp_coll)
    (hm : 0 ≤ m)
    (hcoll : 0 ≤ v_coll)
    (hdebt : 0 ≤ v_debt) :
    m * spDebtAfter sp_debt v_debt ≤ spCollAfter sp_coll v_coll := by
  unfold spDebtAfter spCollAfter
  nlinarith

/-- If the post debt remains positive, the preserved linear bound yields a post-ratio bound. -/
theorem whole_vault_ratio_lower_bound
    (sp_coll sp_debt v_coll v_debt m : ℚ)
    (hpre : m * sp_debt ≤ sp_coll)
    (hm : 0 ≤ m)
    (hcoll : 0 ≤ v_coll)
    (hdebt : 0 ≤ v_debt)
    (hpost : 0 < spDebtAfter sp_debt v_debt) :
    m ≤ spRatioAfter sp_coll sp_debt v_coll v_debt := by
  unfold spRatioAfter
  rw [le_div_iff₀ hpost]
  simpa [spDebtAfter, spCollAfter] using
    whole_vault_lower_bound_preserved sp_coll sp_debt v_coll v_debt m hpre hm hcoll hdebt

/-- Whole-vault liquidation weakly improves the SP ratio whenever the post debt is still positive. -/
theorem whole_vault_ratio_weakly_improves
    (sp_coll sp_debt v_coll v_debt : ℚ)
    (hsp_debt : 0 < sp_debt)
    (hpost : 0 < spDebtAfter sp_debt v_debt)
    (hsp_coll : 0 ≤ sp_coll)
    (hv_coll : 0 ≤ v_coll)
    (hv_debt : 0 ≤ v_debt) :
    sp_coll / sp_debt ≤ spRatioAfter sp_coll sp_debt v_coll v_debt := by
  have hpost' : 0 < sp_debt - v_debt := by
    simpa [spDebtAfter] using hpost
  have hsp_debt_ne : sp_debt ≠ 0 := by linarith
  have hpost_ne : sp_debt - v_debt ≠ 0 := by linarith
  unfold spRatioAfter spCollAfter spDebtAfter
  field_simp [hsp_debt_ne, hpost_ne]
  nlinarith

/-- Strict improvement once the liquidation moves positive collateral mass. -/
theorem whole_vault_ratio_strictly_improves
    (sp_coll sp_debt v_coll v_debt : ℚ)
    (hsp_debt : 0 < sp_debt)
    (hpost : 0 < spDebtAfter sp_debt v_debt)
    (hsp_coll : 0 ≤ sp_coll)
    (hv_coll : 0 ≤ v_coll)
    (hv_debt : 0 < v_debt)
    (hpos : 0 < sp_coll ∨ 0 < v_coll) :
    sp_coll / sp_debt < spRatioAfter sp_coll sp_debt v_coll v_debt := by
  have hpost' : 0 < sp_debt - v_debt := by
    simpa [spDebtAfter] using hpost
  have hsp_debt_ne : sp_debt ≠ 0 := by linarith
  have hpost_ne : sp_debt - v_debt ≠ 0 := by linarith
  unfold spRatioAfter spCollAfter spDebtAfter
  field_simp [hsp_debt_ne, hpost_ne]
  cases hpos with
  | inl hsc =>
      have hterm : 0 < sp_coll * v_debt := by positivity
      nlinarith
  | inr hvc =>
      have hterm : 0 < sp_debt * v_coll := by positivity
      nlinarith

/-- Runtime edge case: liquidation may consume all SP debt, so ratio statements need strict post-debt scope. -/
theorem whole_vault_can_zero_out_sp_debt :
    spDebtAfter 100 100 = 0 := by
  norm_num [spDebtAfter]

/-- Witness: a weakly-improving liquidation with positive residual SP debt. -/
theorem witness_weak_improvement :
    let sp_c : ℚ := 1000
    let sp_d : ℚ := 1000
    let v_c : ℚ := 100
    let v_d : ℚ := 200
    spRatioAfter sp_c sp_d v_c v_d = 11 / 8 ∧
    sp_c / sp_d = 1 ∧
    sp_c / sp_d ≤ spRatioAfter sp_c sp_d v_c v_d := by
  norm_num [spRatioAfter, spCollAfter, spDebtAfter]

/-- Witness: strict improvement under positive collateral movement. -/
theorem witness_strict_improvement :
    let sp_c : ℚ := 500
    let sp_d : ℚ := 1000
    let v_c : ℚ := 50
    let v_d : ℚ := 200
    sp_c / sp_d = 1 / 2 ∧
    spRatioAfter sp_c sp_d v_c v_d = 11 / 16 ∧
    sp_c / sp_d < spRatioAfter sp_c sp_d v_c v_d := by
  norm_num [spRatioAfter, spCollAfter, spDebtAfter]

/-- Witness: lower bounds survive the whole-vault transition. -/
theorem witness_lower_bound_preserved :
    let sp_c : ℚ := 1200
    let sp_d : ℚ := 1000
    let v_c : ℚ := 60
    let v_d : ℚ := 200
    let m : ℚ := 1
    m * sp_d ≤ sp_c ∧
    m * spDebtAfter sp_d v_d ≤ spCollAfter sp_c v_c := by
  norm_num [spDebtAfter, spCollAfter]

end ZUSDSPWholeVaultLiquidation
end Proofs
