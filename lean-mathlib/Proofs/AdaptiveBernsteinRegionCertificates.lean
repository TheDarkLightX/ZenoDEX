import Mathlib.Analysis.SpecialFunctions.Bernstein
import Proofs.TauFragmentCertificates

/-!
# Adaptive Bernstein Region Certificates

This module states the arbitrary-degree acceptance theorem used by the
critical-region dispatcher experiment. Region selection is outside the theorem:
once a checker binds the target to a Bernstein combination with nonnegative
coefficients, the target is nonnegative on the normalized interval.
-/

namespace AdaptiveBernsteinRegionCertificates

open scoped BigOperators unitInterval

noncomputable section

/-- An arbitrary-degree Bernstein combination on the unit interval. -/
def bernsteinCombination
    (n : ℕ) (coeff : Fin (n + 1) → ℝ) (x : Set.Icc (0 : ℝ) 1) : ℝ :=
  ∑ k, coeff k * bernstein n k x

/-- One exact de Casteljau reduction of adjacent Bernstein coefficients. -/
def deCasteljauStep
    (n : ℕ) (coeff : Fin (n + 2) → ℝ) (t : ℝ) : Fin (n + 1) → ℝ :=
  fun k ↦ (1 - t) * coeff k.castSucc + t * coeff k.succ

private def bernsteinNatBasis (n k : ℕ) (x : ℝ) : ℝ :=
  x ^ k * (1 - x) ^ (n - k) * n.choose k

private theorem bernsteinNatBasis_succ_succ
    (n k : ℕ) (hk : k ≤ n) (x : ℝ) :
    bernsteinNatBasis (n + 1) (k + 1) x =
      x * bernsteinNatBasis n k x +
        (1 - x) * bernsteinNatBasis n (k + 1) x := by
  unfold bernsteinNatBasis
  rw [Nat.choose_succ_succ, Nat.cast_add, mul_add]
  congr 1
  · rw [pow_succ' x, Nat.succ_sub_succ, mul_assoc, mul_assoc, mul_assoc]
  · rw [← mul_assoc (1 - x), ← mul_assoc (1 - x)]
    by_cases hkn : k = n
    · subst hkn
      simp
    · rw [Nat.succ_sub (lt_of_le_of_ne hk hkn)]
      simp only [Nat.succ_eq_add_one, pow_succ]
      ring

private theorem bernsteinRange_deCasteljauStep
    (n : ℕ) (coeff : ℕ → ℝ) (x : ℝ) :
    (∑ k ∈ Finset.range (n + 2), coeff k * bernsteinNatBasis (n + 1) k x) =
      ∑ k ∈ Finset.range (n + 1),
        ((1 - x) * coeff k + x * coeff (k + 1)) * bernsteinNatBasis n k x := by
  rw [Finset.sum_range_succ']
  have hmiddle : ∀ k ∈ Finset.range (n + 1),
      coeff (k + 1) * bernsteinNatBasis (n + 1) (k + 1) x =
        x * (coeff (k + 1) * bernsteinNatBasis n k x) +
          (1 - x) * (coeff (k + 1) * bernsteinNatBasis n (k + 1) x) := by
    intro k hk
    rw [bernsteinNatBasis_succ_succ n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) x]
    ring
  rw [Finset.sum_congr rfl hmiddle, Finset.sum_add_distrib]
  have hshift :
      coeff 0 * bernsteinNatBasis (n + 1) 0 x +
          ∑ k ∈ Finset.range (n + 1),
            (1 - x) * (coeff (k + 1) * bernsteinNatBasis n (k + 1) x) =
        ∑ k ∈ Finset.range (n + 1),
          (1 - x) * (coeff k * bernsteinNatBasis n k x) := by
    rw [Finset.sum_range_succ
      (fun k ↦ (1 - x) * (coeff (k + 1) * bernsteinNatBasis n (k + 1) x)) n]
    rw [Finset.sum_range_succ'
      (fun k ↦ (1 - x) * (coeff k * bernsteinNatBasis n k x)) n]
    simp [bernsteinNatBasis, pow_succ']
    ring
  have hrhs :
      (∑ k ∈ Finset.range (n + 1),
          ((1 - x) * coeff k + x * coeff (k + 1)) * bernsteinNatBasis n k x) =
        (∑ k ∈ Finset.range (n + 1),
          (1 - x) * (coeff k * bernsteinNatBasis n k x)) +
        ∑ k ∈ Finset.range (n + 1),
          x * (coeff (k + 1) * bernsteinNatBasis n k x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  rw [hrhs, ← hshift]
  ring

/--
One de Casteljau reduction preserves evaluation when its interpolation
parameter is the evaluation point.
-/
theorem bernsteinCombination_deCasteljauStep
    (n : ℕ) (coeff : Fin (n + 2) → ℝ) (x : Set.Icc (0 : ℝ) 1) :
    bernsteinCombination (n + 1) coeff x =
      bernsteinCombination n (deCasteljauStep n coeff x) x := by
  let extendedCoeff : ℕ → ℝ := fun k ↦
    if hk : k < n + 2 then coeff ⟨k, hk⟩ else 0
  have hstep := bernsteinRange_deCasteljauStep n extendedCoeff (x : ℝ)
  have hleft :
      bernsteinCombination (n + 1) coeff x =
        ∑ k ∈ Finset.range (n + 2),
          extendedCoeff k * bernsteinNatBasis (n + 1) k x := by
    unfold bernsteinCombination
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr (by simp [Nat.add_assoc])
    intro k hk
    have hk' : k < n + 2 := by
      simpa [Nat.add_assoc] using Finset.mem_range.mp hk
    simp [extendedCoeff, hk', bernsteinNatBasis, bernstein_apply]
    ring_nf
    simp
  have hright :
      bernsteinCombination n (deCasteljauStep n coeff x) x =
        ∑ k ∈ Finset.range (n + 1),
          ((1 - (x : ℝ)) * extendedCoeff k + (x : ℝ) * extendedCoeff (k + 1)) *
            bernsteinNatBasis n k x := by
    unfold bernsteinCombination
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < n + 1 := Finset.mem_range.mp hk
    have hk0 : k < n + 2 := by omega
    have hk1 : k + 1 < n + 2 := by omega
    simp [extendedCoeff, hk0, hk1, deCasteljauStep, bernsteinNatBasis,
      bernstein_apply, hk']
    ring_nf
    simp
  exact hleft.trans (hstep.trans hright.symm)

/-- The scalar returned after recursively reducing every de Casteljau level. -/
def deCasteljauValue : (n : ℕ) → (Fin (n + 1) → ℝ) → ℝ → ℝ
  | 0, coeff, _t => coeff 0
  | n + 1, coeff, t => deCasteljauValue n (deCasteljauStep n coeff t) t

/-- Recursive de Casteljau evaluation agrees with the Bernstein combination at every degree. -/
theorem bernsteinCombination_eq_deCasteljauValue
    (n : ℕ) (coeff : Fin (n + 1) → ℝ) (x : Set.Icc (0 : ℝ) 1) :
    bernsteinCombination n coeff x = deCasteljauValue n coeff x := by
  induction n with
  | zero =>
      simp [bernsteinCombination, deCasteljauValue, bernstein_apply]
  | succ n ih =>
      rw [bernsteinCombination_deCasteljauStep n coeff x]
      exact ih (deCasteljauStep n coeff x)

/-- One de Casteljau level preserves coefficient nonnegativity on `[0,1]`. -/
theorem deCasteljauStep_nonneg
    (n : ℕ) (coeff : Fin (n + 2) → ℝ)
    (hcoeff : ∀ k, 0 ≤ coeff k) (t : Set.Icc (0 : ℝ) 1) :
    ∀ k, 0 ≤ deCasteljauStep n coeff t k := by
  intro k
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr t.property.2) (hcoeff k.castSucc))
    (mul_nonneg t.property.1 (hcoeff k.succ))

/-- A target bound to a Bernstein combination is also bound to exact de Casteljau evaluation. -/
theorem representedTarget_eq_deCasteljauValue
    (n : ℕ) (coeff : Fin (n + 1) → ℝ)
    (target : Set.Icc (0 : ℝ) 1 → ℝ)
    (hbind : ∀ x, target x = bernsteinCombination n coeff x) :
    ∀ x, target x = deCasteljauValue n coeff x := by
  intro x
  rw [hbind x, bernsteinCombination_eq_deCasteljauValue]

/-- Nonnegative coefficients make every arbitrary-degree Bernstein combination nonnegative. -/
theorem bernsteinCombination_nonneg
    (n : ℕ) (coeff : Fin (n + 1) → ℝ)
    (hcoeff : ∀ k, 0 ≤ coeff k) (x : Set.Icc (0 : ℝ) 1) :
    0 ≤ bernsteinCombination n coeff x := by
  unfold bernsteinCombination
  exact Finset.sum_nonneg fun k _hk => mul_nonneg (hcoeff k) bernstein_nonneg

/--
If a checker has bound a normalized target to its Bernstein combination, the
coefficient certificate proves target nonnegativity at every normalized point.
-/
theorem representedTarget_nonneg
    (n : ℕ) (coeff : Fin (n + 1) → ℝ)
    (target : Set.Icc (0 : ℝ) 1 → ℝ)
    (hcoeff : ∀ k, 0 ≤ coeff k)
    (hbind : ∀ x, target x = bernsteinCombination n coeff x) :
    ∀ x, 0 ≤ target x := by
  intro x
  rw [hbind x]
  exact bernsteinCombination_nonneg n coeff hcoeff x

/--
The adaptive dispatcher may choose any finite region list. Global soundness
depends only on the complete-cover and local-certificate obligations.
-/
theorem adaptiveCover_nonneg
    (target : ℝ → ℝ) (lo hi : ℝ) (pieces : List (ℝ × ℝ))
    (hcover :
      TauFragmentCertificates.CoversWithLocalCertificates target lo hi pieces) :
    ∀ x, lo ≤ x → x ≤ hi → 0 ≤ target x := by
  exact TauFragmentCertificates.intervalCover_certificatesLift
    target lo hi pieces hcover

end

end AdaptiveBernsteinRegionCertificates
