import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Cubic-sum curve (p=q=1) equilibrium ratio algebra.

For the continuous invariant `K = x*y*(x+y)` (baseline p=q=1), a standard derivation shows that
at an external price `p > 0`, the equilibrium ratio `r := y/x` solves:

  r*(2+r) / (1+2*r) = p

Solving the associated quadratic gives the explicit candidate:

  r(p) = p - 1 + sqrt(p^2 - p + 1)

This file proves the **algebraic identity** that this `r(p)` satisfies the price equation,
under the minimal nonnegativity assumptions needed for `sqrt`.
-/

namespace TauSwap
namespace CubicSum

open Real

noncomputable section

def ratio (p : ℝ) : ℝ := p - 1 + Real.sqrt (p ^ 2 - p + 1)

lemma disc_nonneg (p : ℝ) : 0 ≤ p ^ 2 - p + 1 := by
  -- p^2 - p + 1 = (p - 1/2)^2 + 3/4
  have : p ^ 2 - p + 1 = (p - (1 / 2 : ℝ)) ^ 2 + (3 / 4 : ℝ) := by
    ring
  -- Both terms on RHS are nonnegative.
  have hsq : 0 ≤ (p - (1 / 2 : ℝ)) ^ 2 := by nlinarith
  have hconst : 0 ≤ (3 / 4 : ℝ) := by norm_num
  nlinarith [this, hsq, hconst]

lemma ratio_quadratic (p : ℝ) :
    (ratio p) ^ 2 + (2 - 2 * p) * (ratio p) - p = 0 := by
  -- Expand in terms of s := sqrt(disc); the remainder is s^2 - disc.
  set disc : ℝ := p ^ 2 - p + 1
  set s : ℝ := Real.sqrt disc
  have hdisc : 0 ≤ disc := by
    simpa [disc] using disc_nonneg p
  have hs : s ^ 2 = disc := by
    -- `sqrt` is nonnegative and squares back to the input when the input is nonnegative.
    simpa [s] using (sq_sqrt hdisc)
  -- Now it's a ring computation plus `hs`.
  -- We push everything into an expression in `p` and `s`.
  calc
    (ratio p) ^ 2 + (2 - 2 * p) * (ratio p) - p
        = (p - 1 + s) ^ 2 + (2 - 2 * p) * (p - 1 + s) - p := by simp [ratio, disc, s]
    _ = s ^ 2 - disc := by
      -- Pure algebra: everything cancels except `s^2 - (p^2 - p + 1)`.
      simp [disc]
      ring_nf
    _ = 0 := by
      -- Substitute s^2 = disc.
      nlinarith [hs]

theorem ratio_price (p : ℝ) (hp : 0 < p) :
    ratio p * (2 + ratio p) / (1 + 2 * ratio p) = p := by
  set r : ℝ := ratio p with hr
  have hq : r ^ 2 + (2 - 2 * p) * r - p = 0 := by
    simpa [hr] using (ratio_quadratic p)
  -- Clear denominators in the price equation.
  have hr_nonneg : 0 ≤ r := by
    -- `r = p - 1 + sqrt(p^2 - p + 1) ≥ 0` for `p ≥ 0`.
    have hp0 : 0 ≤ p := le_of_lt hp
    have hdisc : 0 ≤ p ^ 2 - p + 1 := disc_nonneg p
    have hs : 0 ≤ Real.sqrt (p ^ 2 - p + 1) := Real.sqrt_nonneg _
    by_cases h : p ≤ 1
    · have h1p : 0 ≤ 1 - p := sub_nonneg.mpr h
      have hdisc_ge : (1 - p) ^ 2 ≤ p ^ 2 - p + 1 := by
        have : p ^ 2 - p + 1 - (1 - p) ^ 2 = p := by ring
        nlinarith [this, hp0]
      have hs_ge : 1 - p ≤ Real.sqrt (p ^ 2 - p + 1) := by
        exact (le_sqrt h1p hdisc).2 hdisc_ge
      -- Unfold `r`.
      -- r = p - 1 + sqrt(...) = - (1 - p) + sqrt(...)
      have : r = p - 1 + Real.sqrt (p ^ 2 - p + 1) := by simpa [hr, ratio]
      nlinarith [this, hs_ge]
    · have hp1 : 1 < p := lt_of_not_ge h
      have hp1' : 0 ≤ p - 1 := sub_nonneg.mpr (le_of_lt hp1)
      have : r = p - 1 + Real.sqrt (p ^ 2 - p + 1) := by simpa [hr, ratio]
      nlinarith [this, hp1', hs]
  have hden : 1 + 2 * r ≠ 0 := by
    have : 0 < 1 + 2 * r := by nlinarith [hr_nonneg]
    exact ne_of_gt this
  -- Use the quadratic identity to derive the price equation.
  -- Starting from: r^2 + (2 - 2p)r - p = 0
  -- Rearranged: r^2 + 2r = p(1 + 2r)
  have hmain : r * (2 + r) = p * (1 + 2 * r) := by
    -- Pure rearrangement of `hq`.
    nlinarith [hq]
  have hdiv : r * (2 + r) / (1 + 2 * r) = p := by
    exact (div_eq_iff hden).2 (by simpa [mul_assoc] using hmain)
  simpa [hr] using hdiv

end

end CubicSum
end TauSwap
