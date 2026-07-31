import Proofs.FCISFeeApportionmentSRGD
import Proofs.FCISFeeApportionmentAGQESRGDRefinement

namespace FCISFeeApportionmentSRGDTrace

open FCISFeeApportionmentSRGD

/-- Euclidean quotient and remainder are bounded when the denominator is positive. -/
theorem safe_euclidean_floor (A D : Int) (hD : 0 < D) :
    A = D * (A / D) + A % D ∧ 0 ≤ A % D ∧ A % D < D := by
  have hDecomp := Int.emod_add_mul_ediv A D
  have hRemLo := Int.emod_nonneg A (by omega : D ≠ 0)
  have hRemHi := Int.emod_lt_of_pos A hD
  constructor
  · omega
  · exact ⟨hRemLo, hRemHi⟩

/-- A residual sum represented as a multiple of the denominator is divisible by it. -/
theorem residual_sum_divisible
    (D f0 f1 f2 k : Int)
    (hSum : f0 + f1 + f2 = D * k) :
    D ∣ f0 + f1 + f2 := by
  exact ⟨k, hSum⟩

/-- Three bounded residual fractions can contain zero, one, or two residual atoms. -/
theorem residual_count_zero_one_two
    (D f0 f1 f2 : Int)
    (hD : 0 < D)
    (hf0 : 0 ≤ f0 ∧ f0 < D)
    (hf1 : 0 ≤ f1 ∧ f1 < D)
    (hf2 : 0 ≤ f2 ∧ f2 < D)
    (hDiv : D ∣ f0 + f1 + f2) :
    f0 + f1 + f2 = 0 ∨
      f0 + f1 + f2 = D ∨
      f0 + f1 + f2 = 2 * D := by
  rcases hDiv with ⟨k, hSum⟩
  have hSumLo : 0 ≤ f0 + f1 + f2 := by omega
  have hSumHi : f0 + f1 + f2 < 3 * D := by omega
  have hkLo : 0 ≤ k := by
    apply Classical.byContradiction
    intro hNotLo
    have hkNeg : k < 0 := by omega
    have hProdNeg : D * k < 0 := Int.mul_neg_of_pos_of_neg hD hkNeg
    omega
  have hkHi : k < 3 := by
    apply Classical.byContradiction
    intro hNotHi
    have hkThree : 3 ≤ k := by omega
    have hMul : D * 3 ≤ D * k :=
      Int.mul_le_mul_of_nonneg_left hkThree (Int.le_of_lt hD)
    omega
  have hkCases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hkCases with rfl | rfl | rfl <;> omega

/-- A valid SRGD occurrence conserves the signed-deficit sum. -/
theorem one_step_conservation
    (D d0 d1 d2 f0 f1 f2 b0 b1 b2 : Int)
    (hdSum : d0 + d1 + d2 = 0)
    (hCount : f0 + f1 + f2 = D * (b0 + b1 + b2)) :
    updateDeficit D d0 f0 b0 +
        updateDeficit D d1 f1 b1 +
        updateDeficit D d2 f2 b2 = 0 := by
  simp only [updateDeficit]
  rw [Int.mul_add, Int.mul_add] at hCount
  omega

/-- A zero-weight role receives zero base and residual allocation. -/
theorem zero_weight_zero_allocation (A D w : Int) :
    w = 0 → (A / D) * w + ((A % D) * w) / D = 0 := by
  intro hw
  simp [hw]

/-- A valid SRGD occurrence keeps each updated coordinate inside its local quota. -/
theorem one_step_local_quota
    (D d0 d1 d2 f0 f1 f2 b0 b1 b2 : Int)
    (hD : 0 < D)
    (hdSum : d0 + d1 + d2 = 0)
    (hd0Lo : -D < d0) (hd0Hi : d0 < D)
    (hd1Lo : -D < d1) (hd1Hi : d1 < D)
    (hd2Lo : -D < d2) (hd2Hi : d2 < D)
    (hf0Lo : 0 ≤ f0) (hf0Hi : f0 < D)
    (hf1Lo : 0 ≤ f1) (hf1Hi : f1 < D)
    (hf2Lo : 0 ≤ f2) (hf2Hi : f2 < D)
    (hBonus : SRGDBonusRel D d0 d1 d2 f0 f1 f2 b0 b1 b2) :
    -D < updateDeficit D d0 f0 b0 ∧
      updateDeficit D d0 f0 b0 < D ∧
      -D < updateDeficit D d1 f1 b1 ∧
      updateDeficit D d1 f1 b1 < D ∧
      -D < updateDeficit D d2 f2 b2 ∧
      updateDeficit D d2 f2 b2 < D := by
  have h := step_preserves_strict_deficit D d0 d1 d2 f0 f1 f2 b0 b1 b2
    hD hdSum hd0Lo hd0Hi hd1Lo hd1Hi hd2Lo hd2Hi
    hf0Lo hf0Hi hf1Lo hf1Hi hf2Lo hf2Hi hBonus
  rcases h with ⟨_, h0Lo, h0Hi, h1Lo, h1Hi, h2Lo, h2Hi⟩
  exact ⟨h0Lo, h0Hi, h1Lo, h1Hi, h2Lo, h2Hi⟩

end FCISFeeApportionmentSRGDTrace
