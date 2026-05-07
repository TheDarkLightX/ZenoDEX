import Proofs.AMMPowerFamilyOriginalHODLSurfaceMismatch

/-!
# Original-HODL normalized slippage bridge

This file packages the slippage-side semantic boundary discovered during the
power-family bridge work.

The old exact bridge family `hodlSlipDeltaExact n b A` is incompatible with any
slippage surface whose first nonzero even-order coefficient is strictly
positive:

* if `A = 3`, the old bridge has negative quadratic coefficient;
* if `A ≥ 4`, the old bridge has zero quadratic coefficient.

So future bridge work for the center-normalized power-family surface must target
a new slippage object, not the old `hodlSlipDeltaExact` family.
-/

open Filter Topology

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

/-- Slippage-side bridge object for a center-normalized surface whose first
visible even-order term is quadratic with positive coefficient. -/
structure PositiveQuadraticSlippageSurface where
  delta : ℝ → ℝ
  coeff : ℝ
  coeff_pos : 0 < coeff
  coeff_tendsto :
    Tendsto (fun d => delta d / d ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 coeff)

/-- Any positive quadratic slippage surface is incompatible with the old exact
bridge family `hodlSlipDeltaExact n b A` under the positive-parameter semantics
used by the current original-HODL bridge. -/
theorem PositiveQuadraticSlippageSurface.ne_hodlSlipDeltaExact
    (S : PositiveQuadraticSlippageSurface)
    {n b : ℝ} {A : ℕ} (hn : 0 < n) (hb : 0 < b) (hA : 3 ≤ A) :
    S.delta ≠ TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A := by
  by_cases hA3 : A = 3
  · subst hA3
    intro hEq
    have hhodl :
        Tendsto
          (fun d => S.delta d / d ^ 2)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (-(3 : ℝ) * b / n)) := by
      simpa [hEq] using
        (TauSwap.Impossibility.OriginalHODL.slip_expansion n b 3 hn (by norm_num : 3 ≤ 3))
    have hcoeff : S.coeff = -(3 : ℝ) * b / n :=
      tendsto_nhds_unique S.coeff_tendsto hhodl
    have hneg : -(3 : ℝ) * b / n < 0 :=
      TauSwap.Impossibility.LocalJetFrontier.hodlSlipDeltaExact_three_coeff_neg hn hb
    nlinarith [S.coeff_pos, hcoeff, hneg]
  · intro hEq
    have hA4 : 4 ≤ A := by omega
    have hhodl :
      Tendsto
        (fun d => S.delta d / d ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by
      simpa [hEq] using
        TauSwap.Impossibility.LocalJetFrontier.hodlSlipDeltaExact_div_sq_tendsto_zero
          (n := n) (b := b) (A := A) hn hA4
    have hcoeff : S.coeff = 0 :=
      tendsto_nhds_unique S.coeff_tendsto hhodl
    nlinarith [S.coeff_pos, hcoeff]

/-- The local-normalized power-family original-HODL slippage surface packages
into the positive quadratic bridge object. -/
def powerFamilyOriginalHODLNormalizedSlippageSurface
    (alpha : ℝ) (_halpha : 0 < alpha) : PositiveQuadraticSlippageSurface where
  delta := powerFamilyOriginalHODLNormalizedSlippageDelta alpha
  coeff := 4 * alpha * (alpha + 1) / (alpha + 2) ^ 3
  coeff_pos := powerFamilyOriginalHODLNormalizedSlippageCoeff_pos _halpha
  coeff_tendsto := powerFamilyOriginalHODLNormalizedSlippageDelta_div_sq_tendsto _halpha

/-- Reusable corollary: the power-family normalized slippage surface cannot be
any old exact bridge surface `hodlSlipDeltaExact n b A` with positive
parameters and `A ≥ 3`. -/
theorem powerFamilyOriginalHODLNormalizedSlippageSurface_ne_hodlSlipDeltaExact
    {alpha n b : ℝ} {A : ℕ} (halpha : 0 < alpha) (hn : 0 < n) (hb : 0 < b)
    (hA : 3 ≤ A) :
    powerFamilyOriginalHODLNormalizedSlippageDelta alpha ≠
      TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A :=
  (powerFamilyOriginalHODLNormalizedSlippageSurface alpha halpha).ne_hodlSlipDeltaExact
    hn hb hA

/-- Existential no-witness form for the packaged normalized power-family
slippage surface. -/
theorem no_positive_hodlSlipDeltaExact_witness_for_powerFamilyNormalizedSlippageSurface
    {alpha : ℝ} (halpha : 0 < alpha) :
    ¬ ∃ n b : ℝ, ∃ A : ℕ,
        0 < n ∧ 0 < b ∧ 3 ≤ A ∧
        powerFamilyOriginalHODLNormalizedSlippageDelta alpha =
          TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A := by
  rintro ⟨n, b, A, hn, hb, hA, hEq⟩
  exact powerFamilyOriginalHODLNormalizedSlippageSurface_ne_hodlSlipDeltaExact
    halpha hn hb hA hEq

end
end LocalJetFrontier
end Impossibility
end TauSwap
