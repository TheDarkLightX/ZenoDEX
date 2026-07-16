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
