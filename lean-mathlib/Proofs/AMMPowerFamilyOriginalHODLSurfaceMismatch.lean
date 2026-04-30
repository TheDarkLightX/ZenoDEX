import Proofs.AMMPowerFamilyGlobal
import Proofs.OriginalHODLCurvatureLeadingLaw

/-!
# Power-family original-HODL surface mismatch

This file turns the current bridge blocker into a checked theorem.

The local-normalized power-family original-HODL slippage surface has a positive
quadratic coefficient at the center, while the existing first-even
`hodlSlipDeltaExact` surface has negative quadratic coefficient when `n > 0`
and `b > 0`.

So the new normalized power-family surface cannot simply be identified with the
old `hodlSlipDeltaExact` bridge surface under the current positive-parameter
semantics.
-/

open Filter Topology

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

/-- The leading quadratic coefficient of the local-normalized power-family
original-HODL slippage surface is positive for positive `alpha`. -/
theorem powerFamilyOriginalHODLNormalizedSlippageCoeff_pos
    {alpha : ℝ} (halpha : 0 < alpha) :
    0 < 4 * alpha * (alpha + 1) / (alpha + 2) ^ 3 := by
  positivity

/-- The existing first-even exact slippage bridge surface always has negative
quadratic coefficient when `n > 0` and `b > 0`. -/
theorem hodlSlipDeltaExact_three_coeff_neg
    {n b : ℝ} (hn : 0 < n) (hb : 0 < b) :
    -(3 : ℝ) * b / n < 0 := by
  have hpos : 0 < (3 : ℝ) * b / n := by positivity
  have hrewrite : -(3 : ℝ) * b / n = -((3 : ℝ) * b / n) := by ring
  rw [hrewrite]
  linarith

/-- If `A ≥ 4`, the old exact bridge surface is too high-order to have a
nonzero quadratic leading coefficient. -/
theorem hodlSlipDeltaExact_div_sq_tendsto_zero
    {n b : ℝ} {A : ℕ} (hn : 0 < n) (hA : 4 ≤ A) :
    Tendsto
      (fun d => TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A d / d ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hslip :
      Tendsto
        (fun d => TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A d / d ^ (A - 1))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (-(A : ℝ) * b / n)) := by
    simpa using
      (TauSwap.Impossibility.OriginalHODL.slip_expansion n b A hn (by omega : 3 ≤ A))
  have hpow :
      Tendsto (fun d : ℝ => d ^ (A - 3)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun d : ℝ => d ^ (A - 3)) 0 := by
      fun_prop
    have hA3 : A - 3 ≠ 0 := by omega
    simpa [zero_pow hA3] using hcont.tendsto.mono_left inf_le_left
  have hmul :
      Tendsto
        (fun d =>
          (TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A d / d ^ (A - 1)) *
            d ^ (A - 3))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa using hslip.mul hpow
  have hrewrite :
      (fun d => TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A d / d ^ 2)
        =ᶠ[𝓝[≠] (0 : ℝ)]
          (fun d =>
            (TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A d / d ^ (A - 1)) *
              d ^ (A - 3)) := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    have hdA1 : d ^ (A - 1) ≠ 0 := pow_ne_zero (A - 1) hd
    have hpowsub : d ^ (A - 3) = d ^ (A - 1) * (d ^ 2)⁻¹ := by
      have hle : 2 ≤ A - 1 := by omega
      convert (pow_sub₀ d hd hle) using 1
    have hcancel : (d ^ (A - 1))⁻¹ * d ^ (A - 3) = (d ^ 2)⁻¹ := by
      rw [hpowsub]
      simp [hdA1]
    calc
      TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A d / d ^ 2
          = TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A d * (d ^ 2)⁻¹ := by
              rw [div_eq_mul_inv]
      _ = TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A d *
            ((d ^ (A - 1))⁻¹ * d ^ (A - 3)) := by rw [hcancel]
      _ = (TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A d / d ^ (A - 1)) *
            d ^ (A - 3) := by
              rw [div_eq_mul_inv, mul_assoc]
  exact hmul.congr' hrewrite.symm

/-- The local-normalized power-family original-HODL slippage surface cannot be
the old exact first-even bridge surface `hodlSlipDeltaExact n b 3` with
positive `n` and `b`. -/
theorem powerFamilyOriginalHODLNormalizedSlippageDelta_ne_hodlSlipDeltaExact_three
    {alpha n b : ℝ} (halpha : 0 < alpha) (hn : 0 < n) (hb : 0 < b) :
    powerFamilyOriginalHODLNormalizedSlippageDelta alpha ≠
      TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b 3 := by
  intro hEq
  have hpower :
      Tendsto
        (fun d => powerFamilyOriginalHODLNormalizedSlippageDelta alpha d / d ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (4 * alpha * (alpha + 1) / (alpha + 2) ^ 3)) :=
    powerFamilyOriginalHODLNormalizedSlippageDelta_div_sq_tendsto halpha
  have hhodl :
      Tendsto
        (fun d => powerFamilyOriginalHODLNormalizedSlippageDelta alpha d / d ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (-(3 : ℝ) * b / n)) := by
    simpa [hEq] using
      (TauSwap.Impossibility.OriginalHODL.slip_expansion n b 3 hn (by norm_num : 3 ≤ 3))
  have hcoeff :
      4 * alpha * (alpha + 1) / (alpha + 2) ^ 3 = -(3 : ℝ) * b / n :=
    tendsto_nhds_unique hpower hhodl
  have hpos : 0 < 4 * alpha * (alpha + 1) / (alpha + 2) ^ 3 :=
    powerFamilyOriginalHODLNormalizedSlippageCoeff_pos halpha
  have hneg : -(3 : ℝ) * b / n < 0 :=
    hodlSlipDeltaExact_three_coeff_neg hn hb
  nlinarith [hcoeff, hpos, hneg]

/-- The local-normalized power-family slippage surface cannot match any old
exact bridge surface `hodlSlipDeltaExact n b A` with positive parameters and
`A ≥ 3`. -/
theorem powerFamilyOriginalHODLNormalizedSlippageDelta_ne_hodlSlipDeltaExact
    {alpha n b : ℝ} {A : ℕ} (halpha : 0 < alpha) (hn : 0 < n) (hb : 0 < b)
    (hA : 3 ≤ A) :
    powerFamilyOriginalHODLNormalizedSlippageDelta alpha ≠
      TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A := by
  by_cases hA3 : A = 3
  · subst hA3
    exact powerFamilyOriginalHODLNormalizedSlippageDelta_ne_hodlSlipDeltaExact_three
      halpha hn hb
  · intro hEq
    have hA4 : 4 ≤ A := by omega
    have hpower :
        Tendsto
          (fun d => powerFamilyOriginalHODLNormalizedSlippageDelta alpha d / d ^ 2)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (4 * alpha * (alpha + 1) / (alpha + 2) ^ 3)) :=
      powerFamilyOriginalHODLNormalizedSlippageDelta_div_sq_tendsto halpha
    have hhodl :
        Tendsto
          (fun d => powerFamilyOriginalHODLNormalizedSlippageDelta alpha d / d ^ 2)
          (𝓝[≠] (0 : ℝ))
          (𝓝 0) := by
      simpa [hEq] using hodlSlipDeltaExact_div_sq_tendsto_zero (n := n) (b := b) (A := A) hn hA4
    have hcoeff :
        4 * alpha * (alpha + 1) / (alpha + 2) ^ 3 = 0 :=
      tendsto_nhds_unique hpower hhodl
    have hpos : 0 < 4 * alpha * (alpha + 1) / (alpha + 2) ^ 3 :=
      powerFamilyOriginalHODLNormalizedSlippageCoeff_pos halpha
    linarith

/-- There is no positive-parameter witness identifying the local-normalized
power-family slippage surface with the old exact first-even bridge surface. -/
theorem no_positive_hodlSlipDeltaExact_three_witness_for_powerFamilyNormalizedSlippage
    {alpha : ℝ} (halpha : 0 < alpha) :
    ¬ ∃ n b : ℝ,
        0 < n ∧ 0 < b ∧
        powerFamilyOriginalHODLNormalizedSlippageDelta alpha =
          TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b 3 := by
  rintro ⟨n, b, hn, hb, hEq⟩
  exact powerFamilyOriginalHODLNormalizedSlippageDelta_ne_hodlSlipDeltaExact_three
    halpha hn hb hEq

/-- Stronger no-witness form: the local-normalized power-family slippage
surface cannot be any old exact bridge surface `hodlSlipDeltaExact n b A` with
positive parameters and `A ≥ 3`. -/
theorem no_positive_hodlSlipDeltaExact_witness_for_powerFamilyNormalizedSlippage
    {alpha : ℝ} (halpha : 0 < alpha) :
    ¬ ∃ n b : ℝ, ∃ A : ℕ,
        0 < n ∧ 0 < b ∧ 3 ≤ A ∧
        powerFamilyOriginalHODLNormalizedSlippageDelta alpha =
          TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A := by
  rintro ⟨n, b, A, hn, hb, hA, hEq⟩
  exact powerFamilyOriginalHODLNormalizedSlippageDelta_ne_hodlSlipDeltaExact
    halpha hn hb hA hEq

end
end LocalJetFrontier
end Impossibility
end TauSwap
