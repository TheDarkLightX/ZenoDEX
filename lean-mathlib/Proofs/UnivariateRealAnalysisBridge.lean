import Mathlib.Tactic

/-!
# Univariate real-analysis bridge

This module records small reusable Lean lemmas for the repo's
Julia-to-Lean theorem ladder around one-variable expansions.

The motivating external references are real-analysis source material, including
Klazar's `Univariate Real Analysis` notes.  The checked artifact here is only
the Lean statement below: a leading coefficient plus a positive basis determines
the eventual sign on the punctured neighborhood of the expansion point.

This is a reference bridge, not a runtime or assurance claim by itself.
-/

namespace TauSwap
namespace Analysis
namespace Punctured

noncomputable section

open Filter
open scoped Topology

/-- If `f = a*basis + rem` and `rem / basis -> 0`, then `f / basis -> a` on
the punctured neighborhood of the origin. -/
lemma ratio_tendsto_of_expansion {f basis rem : ℝ → ℝ} {a : ℝ}
    (hbasis_ne : ∀ᶠ x in 𝓝[≠] (0 : ℝ), basis x ≠ 0)
    (hdecomp : ∀ᶠ x in 𝓝[≠] (0 : ℝ), f x = a * basis x + rem x)
    (hrem : Tendsto (fun x => rem x / basis x) (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun x => f x / basis x) (𝓝[≠] (0 : ℝ)) (𝓝 a) := by
  have hrewrite :
      (fun x => f x / basis x) =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun x => a + rem x / basis x) := by
    filter_upwards [hbasis_ne, hdecomp] with x hb hx
    rw [hx]
    field_simp [hb]
  have htend :
      Tendsto (fun x => a + rem x / basis x) (𝓝[≠] (0 : ℝ)) (𝓝 (a + 0)) :=
    tendsto_const_nhds.add hrem
  simpa using htend.congr' hrewrite.symm

/-- A positive normalized limit and an eventually positive basis force the
original function to be eventually positive. -/
lemma eventually_pos_of_ratio_tendsto_pos {f basis : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a)
    (hbasis : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 0 < basis x)
    (hratio : Tendsto (fun x => f x / basis x) (𝓝[≠] (0 : ℝ)) (𝓝 a)) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ), 0 < f x := by
  have hratio_pos : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 0 < f x / basis x :=
    hratio.eventually (eventually_gt_nhds ha)
  filter_upwards [hbasis, hratio_pos] with x hb hr
  have hmul : 0 * basis x < f x / basis x * basis x :=
    mul_lt_mul_of_pos_right hr hb
  simpa [ne_of_gt hb] using hmul

/-- A negative normalized limit and an eventually positive basis force the
original function to be eventually negative. -/
lemma eventually_neg_of_ratio_tendsto_neg {f basis : ℝ → ℝ} {a : ℝ}
    (ha : a < 0)
    (hbasis : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 0 < basis x)
    (hratio : Tendsto (fun x => f x / basis x) (𝓝[≠] (0 : ℝ)) (𝓝 a)) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ), f x < 0 := by
  have hratio_neg : ∀ᶠ x in 𝓝[≠] (0 : ℝ), f x / basis x < 0 :=
    hratio.eventually (eventually_lt_nhds ha)
  filter_upwards [hbasis, hratio_neg] with x hb hr
  have hmul : f x / basis x * basis x < 0 * basis x :=
    mul_lt_mul_of_pos_right hr hb
  simpa [ne_of_gt hb] using hmul

/-- Two leading-ratio facts with opposite signs produce the eventual
no-free-lunch sign pattern used by local AMM Taylor arguments. -/
lemma leading_ratio_signs {loss gain basis : ℝ → ℝ} {lossCoeff gainCoeff : ℝ}
    (hloss : lossCoeff < 0)
    (hgain : 0 < gainCoeff)
    (hbasis : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 0 < basis x)
    (hloss_ratio :
      Tendsto (fun x => loss x / basis x) (𝓝[≠] (0 : ℝ)) (𝓝 lossCoeff))
    (hgain_ratio :
      Tendsto (fun x => gain x / basis x) (𝓝[≠] (0 : ℝ)) (𝓝 gainCoeff)) :
    (∀ᶠ x in 𝓝[≠] (0 : ℝ), loss x < 0) ∧
      (∀ᶠ x in 𝓝[≠] (0 : ℝ), 0 < gain x) :=
  ⟨eventually_neg_of_ratio_tendsto_neg hloss hbasis hloss_ratio,
    eventually_pos_of_ratio_tendsto_pos hgain hbasis hgain_ratio⟩

/-- Eventual positivity on the punctured origin contradicts a global
nonpositive bound. -/
lemma eventually_pos_contradicts_global_nonpos {f : ℝ → ℝ}
    (hpos : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 0 < f x)
    (hglobal : ∀ x, f x ≤ 0) :
    False := by
  obtain ⟨x, hxpos⟩ := hpos.exists
  exact not_lt_of_ge (hglobal x) hxpos

end

end Punctured
end Analysis
end TauSwap
