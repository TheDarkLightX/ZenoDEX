import Mathlib.Analysis.SpecialFunctions.Bernstein
import Proofs.TauFragmentCertificates

/-!
# Adaptive Bernstein Region Certificates

This module states the arbitrary-degree acceptance theorem used by the
critical-region dispatcher experiment. It also verifies the compiler's exact
power-to-Bernstein coefficient formula and recursive de Casteljau point
evaluation. Region selection and affine left/right subdivision arrays remain
outside these theorems. Once a checker binds the target to a Bernstein
combination with nonnegative coefficients, the target is nonnegative on the
normalized interval.
-/

namespace AdaptiveBernsteinRegionCertificates

open scoped BigOperators Polynomial unitInterval

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

private theorem bernsteinPolynomial_choose_moment
    (n j : ℕ) (hj : j ≤ n) :
    (∑ i ∈ Finset.range (n + 1),
        (i.choose j : ℝ[X]) * bernsteinPolynomial ℝ n i) =
      (n.choose j : ℝ[X]) * Polynomial.X ^ j := by
  calc
    (∑ i ∈ Finset.range (n + 1),
        (i.choose j : ℝ[X]) * bernsteinPolynomial ℝ n i) =
        ∑ i ∈ Finset.Ico j (n + 1),
          (i.choose j : ℝ[X]) * bernsteinPolynomial ℝ n i := by
      symm
      apply Finset.sum_subset
      · intro i hi
        simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
        omega
      · intro i hiRange hiIco
        have hij : i < j := by
          simp only [Finset.mem_range] at hiRange
          simp only [Finset.mem_Ico, not_and_or, not_lt] at hiIco
          omega
        simp [Nat.choose_eq_zero_of_lt hij]
    _ = ∑ k ∈ Finset.range (n + 1 - j),
          ((j + k).choose j : ℝ[X]) * bernsteinPolynomial ℝ n (j + k) := by
      rw [Finset.sum_Ico_eq_sum_range]
    _ = (n.choose j : ℝ[X]) * Polynomial.X ^ j *
          ∑ k ∈ Finset.range ((n - j) + 1),
            bernsteinPolynomial ℝ (n - j) k := by
      rw [show n + 1 - j = (n - j) + 1 by omega, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk_le : k ≤ n - j := by
        simpa [Finset.mem_range] using Finset.mem_range.mp hk
      have hjk_le : j + k ≤ n := by omega
      have hchoose :
          n.choose (j + k) * (j + k).choose j =
            n.choose j * (n - j).choose k := by
        simpa using Nat.choose_mul (n := n) (k := j + k) (s := j) (by omega)
      have hchooseCast :
          (n.choose (j + k) : ℝ[X]) * ((j + k).choose j : ℝ[X]) =
            (n.choose j : ℝ[X]) * ((n - j).choose k : ℝ[X]) := by
        exact_mod_cast hchoose
      rw [bernsteinPolynomial, bernsteinPolynomial]
      rw [pow_add, show n - (j + k) = n - j - k by omega]
      calc
        _ = ((n.choose (j + k) : ℝ[X]) * ((j + k).choose j : ℝ[X])) *
              (Polynomial.X ^ j * Polynomial.X ^ k *
                (1 - Polynomial.X) ^ (n - j - k)) := by ring
        _ = ((n.choose j : ℝ[X]) * ((n - j).choose k : ℝ[X])) *
              (Polynomial.X ^ j * Polynomial.X ^ k *
                (1 - Polynomial.X) ^ (n - j - k)) := by rw [hchooseCast]
        _ = _ := by ring
    _ = (n.choose j : ℝ[X]) * Polynomial.X ^ j := by
      rw [bernsteinPolynomial.sum]
      ring

/-- The `j`-th binomial moment of degree-`n` Bernstein basis values. -/
theorem bernstein_choose_moment
    (n j : ℕ) (hj : j ≤ n) (x : Set.Icc (0 : ℝ) 1) :
    (∑ i ∈ Finset.range (n + 1), (i.choose j : ℝ) * bernstein n i x) =
      (n.choose j : ℝ) * (x : ℝ) ^ j := by
  have hpoly := bernsteinPolynomial_choose_moment n j hj
  apply_fun Polynomial.evalRingHom (x : ℝ) at hpoly
  simpa [bernsteinPolynomial, bernstein_apply] using hpoly

/-- A degree-bounded polynomial evaluated in the power basis. -/
def powerBasisCombination (n : ℕ) (powerCoeff : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), powerCoeff j * x ^ j

/--
The exact power-to-Bernstein coefficient formula used by the Julia compiler.
Terms above `i` vanish because `i.choose j = 0` there.
-/
def powerToBernsteinCoefficient
    (n : ℕ) (powerCoeff : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    powerCoeff j * (i.choose j : ℝ) / (n.choose j : ℝ)

/-- The padded formula equals Julia's lower-triangular `j = 0..i` loop. -/
theorem powerToBernsteinCoefficient_eq_lowerRange
    (n i : ℕ) (hi : i ≤ n) (powerCoeff : ℕ → ℝ) :
    powerToBernsteinCoefficient n powerCoeff i =
      ∑ j ∈ Finset.range (i + 1),
        powerCoeff j * (i.choose j : ℝ) / (n.choose j : ℝ) := by
  unfold powerToBernsteinCoefficient
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j hjLarge hjSmall
    have hij : i < j := by
      simp only [Finset.mem_range] at hjLarge
      simp only [Finset.mem_range, not_lt] at hjSmall
      omega
    simp [Nat.choose_eq_zero_of_lt hij]

/-- The compiler coefficient function indexed by `Fin (n + 1)`. -/
def powerToBernsteinCoefficients
    (n : ℕ) (powerCoeff : ℕ → ℝ) : Fin (n + 1) → ℝ :=
  fun i ↦ powerToBernsteinCoefficient n powerCoeff i

private theorem powerBasisCombination_eq_bernsteinRange
    (n : ℕ) (powerCoeff : ℕ → ℝ) (x : Set.Icc (0 : ℝ) 1) :
    powerBasisCombination n powerCoeff x =
      ∑ i ∈ Finset.range (n + 1),
        powerToBernsteinCoefficient n powerCoeff i * bernstein n i x := by
  unfold powerBasisCombination powerToBernsteinCoefficient
  symm
  calc
    (∑ i ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.range (n + 1),
          powerCoeff j * (i.choose j : ℝ) / (n.choose j : ℝ)) * bernstein n i x) =
        ∑ i ∈ Finset.range (n + 1),
          ∑ j ∈ Finset.range (n + 1),
            (powerCoeff j * (i.choose j : ℝ) / (n.choose j : ℝ)) *
              bernstein n i x := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_mul]
    _ = ∑ j ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (n + 1),
            (powerCoeff j * (i.choose j : ℝ) / (n.choose j : ℝ)) *
              bernstein n i x := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (n + 1), powerCoeff j * (x : ℝ) ^ j := by
      apply Finset.sum_congr rfl
      intro j hjRange
      have hj_le : j ≤ n := by
        simpa [Finset.mem_range] using Finset.mem_range.mp hjRange
      have hden : (n.choose j : ℝ) ≠ 0 := by
        exact_mod_cast Nat.choose_ne_zero hj_le
      calc
        (∑ i ∈ Finset.range (n + 1),
            (powerCoeff j * (i.choose j : ℝ) / (n.choose j : ℝ)) *
              bernstein n i x) =
            (powerCoeff j / (n.choose j : ℝ)) *
              ∑ i ∈ Finset.range (n + 1),
                (i.choose j : ℝ) * bernstein n i x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
        _ = (powerCoeff j / (n.choose j : ℝ)) *
              ((n.choose j : ℝ) * (x : ℝ) ^ j) := by
          rw [bernstein_choose_moment n j hj_le x]
        _ = powerCoeff j * (x : ℝ) ^ j := by
          field_simp

/--
The exact power-to-Bernstein compiler preserves the represented polynomial on
the normalized interval.
-/
theorem powerBasisCombination_eq_bernsteinCombination
    (n : ℕ) (powerCoeff : ℕ → ℝ) (x : Set.Icc (0 : ℝ) 1) :
    powerBasisCombination n powerCoeff x =
      bernsteinCombination n (powerToBernsteinCoefficients n powerCoeff) x := by
  rw [powerBasisCombination_eq_bernsteinRange]
  unfold bernsteinCombination
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < n + 1 := Finset.mem_range.mp hi
  simp [powerToBernsteinCoefficients, hi']

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

/-- The power-basis compiler and recursive de Casteljau evaluator agree end to end. -/
theorem powerBasisCombination_eq_deCasteljauValue
    (n : ℕ) (powerCoeff : ℕ → ℝ) (x : Set.Icc (0 : ℝ) 1) :
    powerBasisCombination n powerCoeff x =
      deCasteljauValue n (powerToBernsteinCoefficients n powerCoeff) x := by
  rw [powerBasisCombination_eq_bernsteinCombination,
    bernsteinCombination_eq_deCasteljauValue]

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
