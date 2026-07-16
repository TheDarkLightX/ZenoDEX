import Mathlib.Analysis.SpecialFunctions.Bernstein
import Proofs.TauFragmentCertificates

/-!
# Adaptive Bernstein Region Certificates

This module states the arbitrary-degree acceptance theorem used by the
critical-region dispatcher experiment. It also verifies the compiler's exact
power-to-Bernstein coefficient formula, recursive de Casteljau point
evaluation, both affine subdivision arrays, and their composition into the
general `[lo, hi]` restriction transform. Region selection remains outside
these theorems. Once a checker binds the target to a Bernstein combination
with nonnegative coefficients, the target is nonnegative on the normalized
interval.
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

/-- Multiplication as an affine map from the unit square back to the unit interval. -/
def unitIntervalMul
    (t u : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨(t : ℝ) * (u : ℝ),
    mul_nonneg t.property.1 u.property.1,
    calc
      (t : ℝ) * (u : ℝ) ≤ 1 * (u : ℝ) :=
        mul_le_mul_of_nonneg_right t.property.2 u.property.1
      _ = (u : ℝ) := one_mul _
      _ ≤ 1 := u.property.2⟩

/-- The affine map from the unit interval onto the right segment `[t, 1]`. -/
def unitIntervalRight
    (t u : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨(t : ℝ) + (1 - (t : ℝ)) * (u : ℝ),
    add_nonneg t.property.1
      (mul_nonneg (sub_nonneg.mpr t.property.2) u.property.1),
    calc
      (t : ℝ) + (1 - (t : ℝ)) * (u : ℝ) ≤
          (t : ℝ) + (1 - (t : ℝ)) * 1 := by
        exact add_le_add (le_refl (t : ℝ))
          (mul_le_mul_of_nonneg_left u.property.2
            (sub_nonneg.mpr t.property.2))
      _ = 1 := by ring⟩

/-- The normalized local lower endpoint `lo / hi` used by interval restriction. -/
def unitIntervalRatio
    (lo hi : Set.Icc (0 : ℝ) 1) (hlohi : (lo : ℝ) ≤ (hi : ℝ))
    (hhi : 0 < (hi : ℝ)) : Set.Icc (0 : ℝ) 1 :=
  ⟨(lo : ℝ) / (hi : ℝ),
    div_nonneg lo.property.1 (le_of_lt hhi),
    (div_le_one hhi).2 hlohi⟩

/-- The affine map from the unit interval onto `[lo, hi]`. -/
def unitIntervalAffine
    (lo hi : Set.Icc (0 : ℝ) 1) (hlohi : (lo : ℝ) ≤ (hi : ℝ))
    (u : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨(lo : ℝ) + ((hi : ℝ) - (lo : ℝ)) * (u : ℝ),
    add_nonneg lo.property.1
      (mul_nonneg (sub_nonneg.mpr hlohi) u.property.1),
    calc
      (lo : ℝ) + ((hi : ℝ) - (lo : ℝ)) * (u : ℝ) ≤
          (lo : ℝ) + ((hi : ℝ) - (lo : ℝ)) * 1 := by
        exact add_le_add (le_refl (lo : ℝ))
          (mul_le_mul_of_nonneg_left u.property.2 (sub_nonneg.mpr hlohi))
      _ = (hi : ℝ) := by ring
      _ ≤ 1 := hi.property.2⟩

/-- Julia's `hi`-then-`lo / hi` parameterization equals the direct `[lo, hi]` map. -/
theorem unitIntervalMul_ratio_right_eq_affine
    (lo hi : Set.Icc (0 : ℝ) 1) (hlohi : (lo : ℝ) ≤ (hi : ℝ))
    (hhi : 0 < (hi : ℝ)) (u : Set.Icc (0 : ℝ) 1) :
    unitIntervalMul hi (unitIntervalRight (unitIntervalRatio lo hi hlohi hhi) u) =
      unitIntervalAffine lo hi hlohi u := by
  apply Subtype.ext
  simp only [unitIntervalMul, unitIntervalRight, unitIntervalRatio, unitIntervalAffine]
  field_simp [ne_of_gt hhi]

private theorem bernstein_left_subdivision_kernel
    (n i : ℕ) (hi : i ≤ n) (t u : Set.Icc (0 : ℝ) 1) :
    (∑ k ∈ Finset.range (n + 1), bernstein k i t * bernstein n k u) =
      bernstein n i (unitIntervalMul t u) := by
  calc
    (∑ k ∈ Finset.range (n + 1), bernstein k i t * bernstein n k u) =
        ∑ k ∈ Finset.Ico i (n + 1), bernstein k i t * bernstein n k u := by
      symm
      apply Finset.sum_subset
      · intro k hk
        simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
        omega
      · intro k hkRange hkIco
        have hki : k < i := by
          simp only [Finset.mem_range] at hkRange
          simp only [Finset.mem_Ico, not_and_or, not_lt] at hkIco
          omega
        simp [bernstein_apply, Nat.choose_eq_zero_of_lt hki]
    _ = ∑ r ∈ Finset.range (n + 1 - i),
          bernstein (i + r) i t * bernstein n (i + r) u := by
      rw [Finset.sum_Ico_eq_sum_range]
    _ = (n.choose i : ℝ) * ((t : ℝ) * (u : ℝ)) ^ i *
          ∑ r ∈ Finset.range ((n - i) + 1),
            (((1 - (t : ℝ)) * (u : ℝ)) ^ r *
              (1 - (u : ℝ)) ^ (n - i - r) * (n - i).choose r) := by
      rw [show n + 1 - i = (n - i) + 1 by omega, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hr_le : r ≤ n - i := by
        simpa [Finset.mem_range] using Finset.mem_range.mp hr
      have hir_le : i + r ≤ n := by omega
      have hchoose :
          n.choose (i + r) * (i + r).choose i =
            n.choose i * (n - i).choose r := by
        simpa using Nat.choose_mul (n := n) (k := i + r) (s := i) (by omega)
      have hchooseCast :
          (n.choose (i + r) : ℝ) * ((i + r).choose i : ℝ) =
            (n.choose i : ℝ) * ((n - i).choose r : ℝ) := by
        exact_mod_cast hchoose
      rw [bernstein_apply, bernstein_apply]
      rw [pow_add, show i + r - i = r by omega,
        show n - (i + r) = n - i - r by omega]
      have hpow :
          (((1 - (t : ℝ)) * (u : ℝ)) ^ r) =
            (1 - (t : ℝ)) ^ r * (u : ℝ) ^ r :=
        mul_pow (1 - (t : ℝ)) (u : ℝ) r
      calc
        _ = ((n.choose (i + r) : ℝ) * ((i + r).choose i : ℝ)) *
              ((t : ℝ) ^ i * (u : ℝ) ^ i *
                (((1 - (t : ℝ)) * (u : ℝ)) ^ r *
                  (1 - (u : ℝ)) ^ (n - i - r))) := by
            rw [hpow]
            ring
        _ = ((n.choose i : ℝ) * ((n - i).choose r : ℝ)) *
              ((t : ℝ) ^ i * (u : ℝ) ^ i *
                (((1 - (t : ℝ)) * (u : ℝ)) ^ r *
                  (1 - (u : ℝ)) ^ (n - i - r))) := by rw [hchooseCast]
        _ = _ := by rw [mul_pow]; ring
    _ = (n.choose i : ℝ) * ((t : ℝ) * (u : ℝ)) ^ i *
          (((1 - (t : ℝ)) * (u : ℝ)) + (1 - (u : ℝ))) ^ (n - i) := by
      rw [add_pow]
    _ = bernstein n i (unitIntervalMul t u) := by
      rw [bernstein_apply]
      simp only [unitIntervalMul]
      congr 1
      ring

private theorem bernstein_right_subdivision_kernel
    (n i : ℕ) (hi : i ≤ n) (t u : Set.Icc (0 : ℝ) 1) :
    (∑ k ∈ Finset.range (n + 1),
        (if k ≤ i then bernstein (n - k) (i - k) t else 0) * bernstein n k u) =
      bernstein n i (unitIntervalRight t u) := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        (if k ≤ i then bernstein (n - k) (i - k) t else 0) * bernstein n k u) =
        ∑ k ∈ Finset.range (i + 1),
          (if k ≤ i then bernstein (n - k) (i - k) t else 0) *
            bernstein n k u := by
      symm
      apply Finset.sum_subset
      · intro k hk
        simp only [Finset.mem_range] at hk ⊢
        omega
      · intro k hkLarge hkSmall
        have hik : i < k := by
          simp only [Finset.mem_range] at hkLarge
          simp only [Finset.mem_range, not_lt] at hkSmall
          omega
        simp [not_le.mpr hik]
    _ = ∑ k ∈ Finset.range (i + 1),
          bernstein (n - k) (i - k) t * bernstein n k u := by
      apply Finset.sum_congr rfl
      · intro k hk
        have hki : k ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        simp [hki]
    _ = (n.choose i : ℝ) * (1 - (t : ℝ)) ^ (n - i) *
          (1 - (u : ℝ)) ^ (n - i) *
          ∑ k ∈ Finset.range (i + 1),
            (u : ℝ) ^ k * ((t : ℝ) * (1 - (u : ℝ))) ^ (i - k) * i.choose k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hki : k ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hchoose :
          n.choose k * (n - k).choose (i - k) =
            n.choose i * i.choose k := by
        simpa using (Nat.choose_mul (n := n) (k := i) (s := k) hki).symm
      have hchooseCast :
          (n.choose k : ℝ) * ((n - k).choose (i - k) : ℝ) =
            (n.choose i : ℝ) * (i.choose k : ℝ) := by
        exact_mod_cast hchoose
      rw [bernstein_apply, bernstein_apply]
      rw [show n - k - (i - k) = n - i by omega]
      have hpowU :
          (1 - (u : ℝ)) ^ (n - k) =
            (1 - (u : ℝ)) ^ (n - i) * (1 - (u : ℝ)) ^ (i - k) := by
        rw [show n - k = (n - i) + (i - k) by omega, pow_add]
      have hpow :
          (((t : ℝ) * (1 - (u : ℝ))) ^ (i - k)) =
            (t : ℝ) ^ (i - k) * (1 - (u : ℝ)) ^ (i - k) :=
        mul_pow (t : ℝ) (1 - (u : ℝ)) (i - k)
      calc
        _ = ((n.choose k : ℝ) * ((n - k).choose (i - k) : ℝ)) *
              ((1 - (t : ℝ)) ^ (n - i) * (1 - (u : ℝ)) ^ (n - i) *
                ((u : ℝ) ^ k * ((t : ℝ) * (1 - (u : ℝ))) ^ (i - k))) := by
            rw [hpowU, hpow]
            ring
        _ = ((n.choose i : ℝ) * (i.choose k : ℝ)) *
              ((1 - (t : ℝ)) ^ (n - i) * (1 - (u : ℝ)) ^ (n - i) *
                ((u : ℝ) ^ k * ((t : ℝ) * (1 - (u : ℝ))) ^ (i - k))) := by
            rw [hchooseCast]
        _ = _ := by ring
    _ = (n.choose i : ℝ) * (1 - (t : ℝ)) ^ (n - i) *
          (1 - (u : ℝ)) ^ (n - i) *
          ((u : ℝ) + (t : ℝ) * (1 - (u : ℝ))) ^ i := by
      rw [add_pow]
    _ = bernstein n i (unitIntervalRight t u) := by
      rw [bernstein_apply]
      simp only [unitIntervalRight]
      have hpoint :
          (u : ℝ) + (t : ℝ) * (1 - (u : ℝ)) =
            (t : ℝ) + (1 - (t : ℝ)) * (u : ℝ) := by ring
      have hcomplement :
          (1 - (t : ℝ)) * (1 - (u : ℝ)) =
            1 - ((t : ℝ) + (1 - (t : ℝ)) * (u : ℝ)) := by ring
      rw [hpoint]
      calc
        _ = (n.choose i : ℝ) *
              ((t : ℝ) + (1 - (t : ℝ)) * (u : ℝ)) ^ i *
              (((1 - (t : ℝ)) * (1 - (u : ℝ))) ^ (n - i)) := by
            rw [mul_pow]
            ring
        _ = _ := by rw [hcomplement]

/--
The padded formula for the `k`-th left-subdivision coefficient. Basis terms
above `k` vanish, so this equals the lower-triangular de Casteljau prefix loop.
-/
def leftSubdivisionCoefficient
    (n : ℕ) (coeff : ℕ → ℝ) (t : Set.Icc (0 : ℝ) 1) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), coeff i * bernstein k i t

/-- The affine left-subdivision coefficient array indexed by `Fin (n + 1)`. -/
def leftSubdivisionCoefficients
    (n : ℕ) (coeff : ℕ → ℝ) (t : Set.Icc (0 : ℝ) 1) : Fin (n + 1) → ℝ :=
  fun k ↦ leftSubdivisionCoefficient n coeff t k

/--
The padded formula for the `k`-th right-subdivision coefficient. It evaluates
the source suffix beginning at `k` at the split point.
-/
def rightSubdivisionCoefficient
    (n : ℕ) (coeff : ℕ → ℝ) (t : Set.Icc (0 : ℝ) 1) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    if k ≤ i then coeff i * bernstein (n - k) (i - k) t else 0

/-- The affine right-subdivision coefficient array indexed by `Fin (n + 1)`. -/
def rightSubdivisionCoefficients
    (n : ℕ) (coeff : ℕ → ℝ) (t : Set.Icc (0 : ℝ) 1) : Fin (n + 1) → ℝ :=
  fun k ↦ rightSubdivisionCoefficient n coeff t k

/-- The padded left-subdivision formula equals its lower-triangular prefix. -/
theorem leftSubdivisionCoefficient_eq_lowerRange
    (n k : ℕ) (hk : k ≤ n) (coeff : ℕ → ℝ) (t : Set.Icc (0 : ℝ) 1) :
    leftSubdivisionCoefficient n coeff t k =
      ∑ i ∈ Finset.range (k + 1), coeff i * bernstein k i t := by
  unfold leftSubdivisionCoefficient
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hiLarge hiSmall
    have hki : k < i := by
      simp only [Finset.mem_range] at hiLarge
      simp only [Finset.mem_range, not_lt] at hiSmall
      omega
    simp [bernstein_apply, Nat.choose_eq_zero_of_lt hki]

/-- The padded right-subdivision formula equals Julia's suffix loop. -/
theorem rightSubdivisionCoefficient_eq_suffixRange
    (n k : ℕ) (hk : k ≤ n) (coeff : ℕ → ℝ) (t : Set.Icc (0 : ℝ) 1) :
    rightSubdivisionCoefficient n coeff t k =
      ∑ r ∈ Finset.range ((n - k) + 1),
        coeff (k + r) * bernstein (n - k) r t := by
  unfold rightSubdivisionCoefficient
  calc
    (∑ i ∈ Finset.range (n + 1),
        if k ≤ i then coeff i * bernstein (n - k) (i - k) t else 0) =
        ∑ i ∈ Finset.Ico k (n + 1),
          if k ≤ i then coeff i * bernstein (n - k) (i - k) t else 0 := by
      symm
      apply Finset.sum_subset
      · intro i hi
        simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
        omega
      · intro i hiRange hiIco
        have hik : i < k := by
          simp only [Finset.mem_range] at hiRange
          simp only [Finset.mem_Ico, not_and_or, not_lt] at hiIco
          omega
        simp [not_le.mpr hik]
    _ = ∑ i ∈ Finset.Ico k (n + 1),
          coeff i * bernstein (n - k) (i - k) t := by
      apply Finset.sum_congr rfl
      intro i hi
      have hki : k ≤ i := (Finset.mem_Ico.mp hi).1
      simp [hki]
    _ = ∑ r ∈ Finset.range (n + 1 - k),
          coeff (k + r) * bernstein (n - k) (k + r - k) t := by
      rw [Finset.sum_Ico_eq_sum_range]
    _ = ∑ r ∈ Finset.range ((n - k) + 1),
          coeff (k + r) * bernstein (n - k) r t := by
      rw [show n + 1 - k = (n - k) + 1 by omega]
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Nat.add_sub_cancel_left]

private theorem bernsteinRange_leftSubdivision
    (n : ℕ) (coeff : ℕ → ℝ) (t u : Set.Icc (0 : ℝ) 1) :
    (∑ k ∈ Finset.range (n + 1),
        leftSubdivisionCoefficient n coeff t k * bernstein n k u) =
      ∑ i ∈ Finset.range (n + 1),
        coeff i * bernstein n i (unitIntervalMul t u) := by
  unfold leftSubdivisionCoefficient
  calc
    (∑ k ∈ Finset.range (n + 1),
        (∑ i ∈ Finset.range (n + 1), coeff i * bernstein k i t) *
          bernstein n k u) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (n + 1),
            (coeff i * bernstein k i t) * bernstein n k u := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]
    _ = ∑ i ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range (n + 1),
            (coeff i * bernstein k i t) * bernstein n k u := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (n + 1),
          coeff i * bernstein n i (unitIntervalMul t u) := by
      apply Finset.sum_congr rfl
      intro i hiRange
      have hi : i ≤ n := by
        simpa [Finset.mem_range] using Finset.mem_range.mp hiRange
      rw [← bernstein_left_subdivision_kernel n i hi t u, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring

private theorem bernsteinRange_rightSubdivision
    (n : ℕ) (coeff : ℕ → ℝ) (t u : Set.Icc (0 : ℝ) 1) :
    (∑ k ∈ Finset.range (n + 1),
        rightSubdivisionCoefficient n coeff t k * bernstein n k u) =
      ∑ i ∈ Finset.range (n + 1),
        coeff i * bernstein n i (unitIntervalRight t u) := by
  unfold rightSubdivisionCoefficient
  calc
    (∑ k ∈ Finset.range (n + 1),
        (∑ i ∈ Finset.range (n + 1),
          if k ≤ i then coeff i * bernstein (n - k) (i - k) t else 0) *
            bernstein n k u) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (n + 1),
            (if k ≤ i then coeff i * bernstein (n - k) (i - k) t else 0) *
              bernstein n k u := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]
    _ = ∑ i ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range (n + 1),
            (if k ≤ i then coeff i * bernstein (n - k) (i - k) t else 0) *
              bernstein n k u := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (n + 1),
          coeff i * ∑ k ∈ Finset.range (n + 1),
            (if k ≤ i then bernstein (n - k) (i - k) t else 0) *
              bernstein n k u := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases hki : k ≤ i
      · simp [hki]
        ring
      · simp [hki]
    _ = ∑ i ∈ Finset.range (n + 1),
          coeff i * bernstein n i (unitIntervalRight t u) := by
      apply Finset.sum_congr rfl
      intro i hiRange
      have hi : i ≤ n := by
        simpa [Finset.mem_range] using Finset.mem_range.mp hiRange
      rw [bernstein_right_subdivision_kernel n i hi t u]

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

/-- Every left-subdivision coefficient is the de Casteljau value of its prefix. -/
theorem leftSubdivisionCoefficient_eq_deCasteljauValue
    (n k : ℕ) (hk : k ≤ n) (coeff : ℕ → ℝ) (t : Set.Icc (0 : ℝ) 1) :
    leftSubdivisionCoefficient n coeff t k =
      deCasteljauValue k (fun i : Fin (k + 1) ↦ coeff i) t := by
  rw [leftSubdivisionCoefficient_eq_lowerRange n k hk]
  calc
    (∑ i ∈ Finset.range (k + 1), coeff i * bernstein k i t) =
        bernsteinCombination k (fun i : Fin (k + 1) ↦ coeff i) t := by
      unfold bernsteinCombination
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < k + 1 := Finset.mem_range.mp hi
      simp [hi']
    _ = deCasteljauValue k (fun i : Fin (k + 1) ↦ coeff i) t :=
      bernsteinCombination_eq_deCasteljauValue k _ t

/-- Every right-subdivision coefficient is the de Casteljau value of its suffix. -/
theorem rightSubdivisionCoefficient_eq_deCasteljauValue
    (n k : ℕ) (hk : k ≤ n) (coeff : ℕ → ℝ) (t : Set.Icc (0 : ℝ) 1) :
    rightSubdivisionCoefficient n coeff t k =
      deCasteljauValue (n - k)
        (fun r : Fin ((n - k) + 1) ↦ coeff (k + r)) t := by
  rw [rightSubdivisionCoefficient_eq_suffixRange n k hk]
  calc
    (∑ r ∈ Finset.range ((n - k) + 1),
        coeff (k + r) * bernstein (n - k) r t) =
        bernsteinCombination (n - k)
          (fun r : Fin ((n - k) + 1) ↦ coeff (k + r)) t := by
      unfold bernsteinCombination
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro r hr
      have hr' : r < (n - k) + 1 := Finset.mem_range.mp hr
      simp [hr']
    _ = deCasteljauValue (n - k)
          (fun r : Fin ((n - k) + 1) ↦ coeff (k + r)) t :=
      bernsteinCombination_eq_deCasteljauValue (n - k) _ t

/--
The affine left-subdivision coefficient array represents the original
Bernstein polynomial after the parameter substitution `u ↦ t * u`.
-/
theorem bernsteinCombination_leftSubdivisionCoefficients
    (n : ℕ) (coeff : ℕ → ℝ) (t u : Set.Icc (0 : ℝ) 1) :
    bernsteinCombination n (leftSubdivisionCoefficients n coeff t) u =
      bernsteinCombination n (fun i : Fin (n + 1) ↦ coeff i)
        (unitIntervalMul t u) := by
  calc
    bernsteinCombination n (leftSubdivisionCoefficients n coeff t) u =
        ∑ k ∈ Finset.range (n + 1),
          leftSubdivisionCoefficient n coeff t k * bernstein n k u := by
      unfold bernsteinCombination
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < n + 1 := Finset.mem_range.mp hk
      simp [leftSubdivisionCoefficients, hk']
    _ = ∑ i ∈ Finset.range (n + 1),
          coeff i * bernstein n i (unitIntervalMul t u) :=
      bernsteinRange_leftSubdivision n coeff t u
    _ = bernsteinCombination n (fun i : Fin (n + 1) ↦ coeff i)
          (unitIntervalMul t u) := by
      unfold bernsteinCombination
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < n + 1 := Finset.mem_range.mp hi
      simp [hi']

/--
The affine right-subdivision coefficient array represents the original
Bernstein polynomial after the parameter substitution `u ↦ t + (1 - t) * u`.
-/
theorem bernsteinCombination_rightSubdivisionCoefficients
    (n : ℕ) (coeff : ℕ → ℝ) (t u : Set.Icc (0 : ℝ) 1) :
    bernsteinCombination n (rightSubdivisionCoefficients n coeff t) u =
      bernsteinCombination n (fun i : Fin (n + 1) ↦ coeff i)
        (unitIntervalRight t u) := by
  calc
    bernsteinCombination n (rightSubdivisionCoefficients n coeff t) u =
        ∑ k ∈ Finset.range (n + 1),
          rightSubdivisionCoefficient n coeff t k * bernstein n k u := by
      unfold bernsteinCombination
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < n + 1 := Finset.mem_range.mp hk
      simp [rightSubdivisionCoefficients, hk']
    _ = ∑ i ∈ Finset.range (n + 1),
          coeff i * bernstein n i (unitIntervalRight t u) :=
      bernsteinRange_rightSubdivision n coeff t u
    _ = bernsteinCombination n (fun i : Fin (n + 1) ↦ coeff i)
          (unitIntervalRight t u) := by
      unfold bernsteinCombination
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < n + 1 := Finset.mem_range.mp hi
      simp [hi']

/-- Left subdivision preserves nonnegativity of every source coefficient. -/
theorem leftSubdivisionCoefficient_nonneg
    (n k : ℕ) (coeff : ℕ → ℝ) (hcoeff : ∀ i, 0 ≤ coeff i)
    (t : Set.Icc (0 : ℝ) 1) :
    0 ≤ leftSubdivisionCoefficient n coeff t k := by
  unfold leftSubdivisionCoefficient
  exact Finset.sum_nonneg fun i _hi ↦ mul_nonneg (hcoeff i) bernstein_nonneg

/-- The entire affine left-subdivision coefficient array stays nonnegative. -/
theorem leftSubdivisionCoefficients_nonneg
    (n : ℕ) (coeff : ℕ → ℝ) (hcoeff : ∀ i, 0 ≤ coeff i)
    (t : Set.Icc (0 : ℝ) 1) :
    ∀ k, 0 ≤ leftSubdivisionCoefficients n coeff t k := by
  intro k
  exact leftSubdivisionCoefficient_nonneg n k coeff hcoeff t

/-- Right subdivision preserves nonnegativity of every source coefficient. -/
theorem rightSubdivisionCoefficient_nonneg
    (n k : ℕ) (coeff : ℕ → ℝ) (hcoeff : ∀ i, 0 ≤ coeff i)
    (t : Set.Icc (0 : ℝ) 1) :
    0 ≤ rightSubdivisionCoefficient n coeff t k := by
  unfold rightSubdivisionCoefficient
  apply Finset.sum_nonneg
  intro i _hi
  by_cases hki : k ≤ i
  · simp [hki]
    exact mul_nonneg (hcoeff i) bernstein_nonneg
  · simp [hki]

/-- The entire affine right-subdivision coefficient array stays nonnegative. -/
theorem rightSubdivisionCoefficients_nonneg
    (n : ℕ) (coeff : ℕ → ℝ) (hcoeff : ∀ i, 0 ≤ coeff i)
    (t : Set.Icc (0 : ℝ) 1) :
    ∀ k, 0 ≤ rightSubdivisionCoefficients n coeff t k := by
  intro k
  exact rightSubdivisionCoefficient_nonneg n k coeff hcoeff t

/--
The two-stage coefficient array used by interval restriction: first keep the
left segment ending at `hi`, then keep the right segment beginning at `localLo`.
-/
def intervalSubdivisionCoefficients
    (n : ℕ) (coeff : ℕ → ℝ) (hi localLo : Set.Icc (0 : ℝ) 1) :
    Fin (n + 1) → ℝ :=
  rightSubdivisionCoefficients n
    (fun i ↦ leftSubdivisionCoefficient n coeff hi i) localLo

/-- The exact two-stage coefficient transform used for restriction to `[lo, hi]`. -/
def restrictedSubdivisionCoefficients
    (n : ℕ) (coeff : ℕ → ℝ) (lo hi : Set.Icc (0 : ℝ) 1)
    (hlohi : (lo : ℝ) ≤ (hi : ℝ)) (hhi : 0 < (hi : ℝ)) :
    Fin (n + 1) → ℝ :=
  intervalSubdivisionCoefficients n coeff hi (unitIntervalRatio lo hi hlohi hhi)

/--
Two-stage subdivision represents the source polynomial under
`u ↦ hi * (localLo + (1 - localLo) * u)`.
-/
theorem bernsteinCombination_intervalSubdivisionCoefficients
    (n : ℕ) (coeff : ℕ → ℝ)
    (hi localLo u : Set.Icc (0 : ℝ) 1) :
    bernsteinCombination n
        (intervalSubdivisionCoefficients n coeff hi localLo) u =
      bernsteinCombination n (fun i : Fin (n + 1) ↦ coeff i)
        (unitIntervalMul hi (unitIntervalRight localLo u)) := by
  rw [show intervalSubdivisionCoefficients n coeff hi localLo =
      rightSubdivisionCoefficients n
        (fun i ↦ leftSubdivisionCoefficient n coeff hi i) localLo by rfl]
  rw [bernsteinCombination_rightSubdivisionCoefficients]
  change bernsteinCombination n (leftSubdivisionCoefficients n coeff hi)
    (unitIntervalRight localLo u) = _
  rw [bernsteinCombination_leftSubdivisionCoefficients]

/-- Two-stage interval subdivision preserves coefficient nonnegativity. -/
theorem intervalSubdivisionCoefficients_nonneg
    (n : ℕ) (coeff : ℕ → ℝ) (hcoeff : ∀ i, 0 ≤ coeff i)
    (hi localLo : Set.Icc (0 : ℝ) 1) :
    ∀ k, 0 ≤ intervalSubdivisionCoefficients n coeff hi localLo k := by
  apply rightSubdivisionCoefficients_nonneg
  intro i
  exact leftSubdivisionCoefficient_nonneg n i coeff hcoeff hi

/--
The complete two-stage coefficient transform represents the source Bernstein
polynomial under the direct affine map from `[0, 1]` onto `[lo, hi]`.
-/
theorem bernsteinCombination_restrictedSubdivisionCoefficients
    (n : ℕ) (coeff : ℕ → ℝ) (lo hi : Set.Icc (0 : ℝ) 1)
    (hlohi : (lo : ℝ) ≤ (hi : ℝ)) (hhi : 0 < (hi : ℝ))
    (u : Set.Icc (0 : ℝ) 1) :
    bernsteinCombination n
        (restrictedSubdivisionCoefficients n coeff lo hi hlohi hhi) u =
      bernsteinCombination n (fun i : Fin (n + 1) ↦ coeff i)
        (unitIntervalAffine lo hi hlohi u) := by
  rw [show restrictedSubdivisionCoefficients n coeff lo hi hlohi hhi =
      intervalSubdivisionCoefficients n coeff hi
        (unitIntervalRatio lo hi hlohi hhi) by rfl]
  rw [bernsteinCombination_intervalSubdivisionCoefficients]
  rw [unitIntervalMul_ratio_right_eq_affine lo hi hlohi hhi u]

/-- Restriction to `[lo, hi]` preserves coefficient nonnegativity. -/
theorem restrictedSubdivisionCoefficients_nonneg
    (n : ℕ) (coeff : ℕ → ℝ) (hcoeff : ∀ i, 0 ≤ coeff i)
    (lo hi : Set.Icc (0 : ℝ) 1) (hlohi : (lo : ℝ) ≤ (hi : ℝ))
    (hhi : 0 < (hi : ℝ)) :
    ∀ k, 0 ≤ restrictedSubdivisionCoefficients n coeff lo hi hlohi hhi k := by
  exact intervalSubdivisionCoefficients_nonneg n coeff hcoeff hi
    (unitIntervalRatio lo hi hlohi hhi)

/-- The power-basis compiler and recursive de Casteljau evaluator agree end to end. -/
theorem powerBasisCombination_eq_deCasteljauValue
    (n : ℕ) (powerCoeff : ℕ → ℝ) (x : Set.Icc (0 : ℝ) 1) :
    powerBasisCombination n powerCoeff x =
      deCasteljauValue n (powerToBernsteinCoefficients n powerCoeff) x := by
  rw [powerBasisCombination_eq_bernsteinCombination,
    bernsteinCombination_eq_deCasteljauValue]

/--
The power-to-Bernstein compiler followed by left subdivision represents the
source power-basis polynomial at `t * u`.
-/
theorem powerBasisCombination_mul_eq_leftSubdivision
    (n : ℕ) (powerCoeff : ℕ → ℝ) (t u : Set.Icc (0 : ℝ) 1) :
    powerBasisCombination n powerCoeff ((t : ℝ) * (u : ℝ)) =
      bernsteinCombination n
        (leftSubdivisionCoefficients n
          (fun i ↦ powerToBernsteinCoefficient n powerCoeff i) t) u := by
  change powerBasisCombination n powerCoeff (unitIntervalMul t u) = _
  rw [powerBasisCombination_eq_bernsteinCombination n powerCoeff (unitIntervalMul t u)]
  simpa [powerToBernsteinCoefficients] using
    (bernsteinCombination_leftSubdivisionCoefficients n
      (fun i ↦ powerToBernsteinCoefficient n powerCoeff i) t u).symm

/--
The power-to-Bernstein compiler followed by right subdivision represents the
source power-basis polynomial at `t + (1 - t) * u`.
-/
theorem powerBasisCombination_rightAffine_eq_rightSubdivision
    (n : ℕ) (powerCoeff : ℕ → ℝ) (t u : Set.Icc (0 : ℝ) 1) :
    powerBasisCombination n powerCoeff
        ((t : ℝ) + (1 - (t : ℝ)) * (u : ℝ)) =
      bernsteinCombination n
        (rightSubdivisionCoefficients n
          (fun i ↦ powerToBernsteinCoefficient n powerCoeff i) t) u := by
  change powerBasisCombination n powerCoeff (unitIntervalRight t u) = _
  rw [powerBasisCombination_eq_bernsteinCombination n powerCoeff (unitIntervalRight t u)]
  simpa [powerToBernsteinCoefficients] using
    (bernsteinCombination_rightSubdivisionCoefficients n
      (fun i ↦ powerToBernsteinCoefficient n powerCoeff i) t u).symm

/--
The complete power-basis compiler and two-stage interval subdivision pipeline
represents the source polynomial at
`hi * (localLo + (1 - localLo) * u)`.
-/
theorem powerBasisCombination_intervalAffine_eq_intervalSubdivision
    (n : ℕ) (powerCoeff : ℕ → ℝ)
    (hi localLo u : Set.Icc (0 : ℝ) 1) :
    powerBasisCombination n powerCoeff
        ((hi : ℝ) * ((localLo : ℝ) + (1 - (localLo : ℝ)) * (u : ℝ))) =
      bernsteinCombination n
        (intervalSubdivisionCoefficients n
          (fun i ↦ powerToBernsteinCoefficient n powerCoeff i) hi localLo) u := by
  change powerBasisCombination n powerCoeff
    (unitIntervalMul hi (unitIntervalRight localLo u)) = _
  rw [powerBasisCombination_eq_bernsteinCombination n powerCoeff
    (unitIntervalMul hi (unitIntervalRight localLo u))]
  simpa [powerToBernsteinCoefficients] using
    (bernsteinCombination_intervalSubdivisionCoefficients n
      (fun i ↦ powerToBernsteinCoefficient n powerCoeff i) hi localLo u).symm

/--
The complete power-basis compiler and `[lo, hi]` restriction transform
represents the source polynomial at `lo + (hi - lo) * u`.
-/
theorem powerBasisCombination_affine_eq_restrictedSubdivision
    (n : ℕ) (powerCoeff : ℕ → ℝ) (lo hi : Set.Icc (0 : ℝ) 1)
    (hlohi : (lo : ℝ) ≤ (hi : ℝ)) (hhi : 0 < (hi : ℝ))
    (u : Set.Icc (0 : ℝ) 1) :
    powerBasisCombination n powerCoeff
        ((lo : ℝ) + ((hi : ℝ) - (lo : ℝ)) * (u : ℝ)) =
      bernsteinCombination n
        (restrictedSubdivisionCoefficients n
          (fun i ↦ powerToBernsteinCoefficient n powerCoeff i)
          lo hi hlohi hhi) u := by
  change powerBasisCombination n powerCoeff (unitIntervalAffine lo hi hlohi u) = _
  rw [powerBasisCombination_eq_bernsteinCombination n powerCoeff
    (unitIntervalAffine lo hi hlohi u)]
  simpa [powerToBernsteinCoefficients] using
    (bernsteinCombination_restrictedSubdivisionCoefficients n
      (fun i ↦ powerToBernsteinCoefficient n powerCoeff i)
      lo hi hlohi hhi u).symm

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
