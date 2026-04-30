import Proofs.AMMOriginalHODLGlobalBridge
import Proofs.AMMGlobalCPMMBudget

/-!
# Raw AMM semantics bridge

This file records the first raw-AMM structural bridge above the checked global
obstruction APIs.

The current result is intentionally not the full universal AMM theorem. It
shows that a symmetric positively homogeneous bonding curve supplies the
normalization facts needed by the CPMM-budget route. The remaining load-bearing
work is semantic extraction: proving that raw AMM slippage and original-HODL
curvature coefficients instantiate `OriginalHODLConcreteExtractionSemantics` or
`SameBenchmarkAnalyticSurfaceAssumptions`.
-/

open Real Filter Topology

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier
namespace RawAMMBridge

noncomputable section

/-- Minimal raw representation for a symmetric positively homogeneous two-asset
AMM bonding curve. Smoothness is supplied later as hypotheses on the derived
one-dimensional potentials, so this structure stays purely algebraic. -/
structure RawSymmetricHomogeneousAMM where
  K : ℝ → ℝ → ℝ
  degree : ℝ
  degree_pos : 0 < degree
  symmetric : ∀ x y : ℝ, 0 < x → 0 < y → K x y = K y x
  homogeneous : ∀ t x y : ℝ, 0 < t → 0 < x → 0 < y →
    K (t * x) (t * y) = t ^ degree * K x y
  pos : ∀ x y : ℝ, 0 < x → 0 < y → 0 < K x y

/-- Symmetry of the bonding curve forces the raw imbalance potential to be
even. -/
theorem rawImbalancePotential_even (A : RawSymmetricHomogeneousAMM) (d : ℝ) :
    rawImbalancePotential A.K (-d) = rawImbalancePotential A.K d := by
  simp only [rawImbalancePotential]
  rw [neg_neg]
  congr 1
  exact A.symmetric (exp d) (exp (-d)) (exp_pos d) (exp_pos (-d))

/-- Normalization at balance preserves evenness. -/
theorem normalizedImbalancePotential_even
    (A : RawSymmetricHomogeneousAMM) (d : ℝ) :
    normalizedImbalancePotential A.K (-d) =
      normalizedImbalancePotential A.K d := by
  simp only [normalizedImbalancePotential]
  rw [rawImbalancePotential_even A d]

/-- A differentiable even function has zero derivative at the origin. -/
theorem deriv_zero_of_even {f : ℝ → ℝ}
    (heven : ∀ d, f (-d) = f d)
    (hdiff : DifferentiableAt ℝ f 0) :
    deriv f 0 = 0 := by
  have hf : HasDerivAt f (deriv f 0) 0 := hdiff.hasDerivAt
  have hfun_eq : (fun d => f (-d)) = f := funext (fun d => heven d)
  have hneg : HasDerivAt (fun x : ℝ => -x) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).neg
  have hcomp : HasDerivAt (fun d => f (-d)) (deriv f 0 * -1) 0 := by
    have hf_at_neg_zero : HasDerivAt f (deriv f 0) (-0) := by
      simpa using hf
    exact hf_at_neg_zero.comp 0 hneg
  have hf_neg : HasDerivAt f (-(deriv f 0)) 0 := by
    have hcomp' : HasDerivAt (fun d => f (-d)) (-(deriv f 0)) 0 := by
      simpa using hcomp
    simpa [hfun_eq] using hcomp'
  linarith [HasDerivAt.unique hf hf_neg]

/-- The derivative of a symmetric AMM's normalized imbalance potential vanishes
at balance whenever that one-dimensional potential is differentiable there. -/
theorem deriv_normalizedImbalancePotential_zero
    (A : RawSymmetricHomogeneousAMM)
    (hdiff : DifferentiableAt ℝ (normalizedImbalancePotential A.K) 0) :
    deriv (normalizedImbalancePotential A.K) 0 = 0 :=
  deriv_zero_of_even (normalizedImbalancePotential_even A) hdiff

/-- The derivative of a differentiable even function is odd. -/
theorem deriv_neg_of_even {f : ℝ → ℝ} {x : ℝ}
    (heven : ∀ d, f (-d) = f d)
    (hdiff_x : DifferentiableAt ℝ f x)
    (hdiff_neg_x : DifferentiableAt ℝ f (-x)) :
    deriv f (-x) = -deriv f x := by
  have hf_x : HasDerivAt f (deriv f x) x := hdiff_x.hasDerivAt
  have hf_neg_x : HasDerivAt f (deriv f (-x)) (-x) :=
    hdiff_neg_x.hasDerivAt
  have hfun_eq : (fun d => f (-d)) = f := funext (fun d => heven d)
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) (-x) := by
    simpa using (hasDerivAt_id (-x)).neg
  have hf_at_neg_neg : HasDerivAt f (deriv f x) (- -x) := by
    simpa using hf_x
  have hcomp : HasDerivAt (fun d => f (-d)) (deriv f x * -1) (-x) :=
    hf_at_neg_neg.comp (-x) hneg
  have hf_neg : HasDerivAt f (-(deriv f x)) (-x) := by
    have hcomp' : HasDerivAt (fun d => f (-d)) (-(deriv f x)) (-x) := by
      simpa using hcomp
    simpa [hfun_eq] using hcomp'
  exact HasDerivAt.unique hf_neg_x hf_neg

/-- The derivative of a symmetric AMM's normalized imbalance potential is odd
where the potential is differentiable at both mirrored points. -/
theorem deriv_normalizedImbalancePotential_neg
    (A : RawSymmetricHomogeneousAMM) (x : ℝ)
    (hdiff_x : DifferentiableAt ℝ (normalizedImbalancePotential A.K) x)
    (hdiff_neg_x : DifferentiableAt ℝ (normalizedImbalancePotential A.K) (-x)) :
    deriv (normalizedImbalancePotential A.K) (-x) =
      -deriv (normalizedImbalancePotential A.K) x :=
  deriv_neg_of_even (normalizedImbalancePotential_even A) hdiff_x hdiff_neg_x

/-- Candidate-minus-baseline normalized imbalance potential deltas are even
when both raw AMMs are symmetric. -/
theorem normalizedImbalancePotential_delta_even
    (baseline candidate : RawSymmetricHomogeneousAMM) (d : ℝ) :
    normalizedImbalancePotential candidate.K (-d) -
        normalizedImbalancePotential baseline.K (-d) =
      normalizedImbalancePotential candidate.K d -
        normalizedImbalancePotential baseline.K d := by
  rw [normalizedImbalancePotential_even candidate d,
    normalizedImbalancePotential_even baseline d]

/-- The first derivative of the candidate-minus-baseline normalized potential
vanishes at balance under differentiability. -/
theorem deriv_normalizedImbalancePotential_delta_zero
    (baseline candidate : RawSymmetricHomogeneousAMM)
    (hdiff :
      DifferentiableAt ℝ
        (fun d =>
          normalizedImbalancePotential candidate.K d -
            normalizedImbalancePotential baseline.K d)
        0) :
    deriv
        (fun d =>
          normalizedImbalancePotential candidate.K d -
            normalizedImbalancePotential baseline.K d)
        0 = 0 :=
  deriv_zero_of_even
    (normalizedImbalancePotential_delta_even baseline candidate)
    hdiff

/-- At balance, the raw imbalance potential is just `log K(1,1)`. -/
theorem rawImbalancePotential_at_zero (A : RawSymmetricHomogeneousAMM) :
    rawImbalancePotential A.K 0 = Real.log (A.K 1 1) := by
  simp [rawImbalancePotential]

/-- Raw homogeneous AMMs induce the expected log-normal form on log-reserve
coordinates.  This version uses the raw positivity-domain hypotheses directly,
instead of requiring a globally homogeneous function on all real reserves. -/
theorem raw_homogeneous_to_log_normalForm
    (A : RawSymmetricHomogeneousAMM) (m d : ℝ) :
    logInvariantOf A.K (m - d) (m + d) =
      A.degree * m + rawImbalancePotential A.K d := by
  have hm_pos : 0 < exp m := exp_pos m
  have hslice_pos : 0 < A.K (exp (-d)) (exp d) :=
    A.pos _ _ (exp_pos (-d)) (exp_pos d)
  have hpow_pos : 0 < (exp m) ^ A.degree :=
    Real.rpow_pos_of_pos hm_pos A.degree
  have hleft :
      A.K (exp (m - d)) (exp (m + d)) =
        (exp m) ^ A.degree * A.K (exp (-d)) (exp d) := by
    rw [sub_eq_add_neg, exp_add, exp_add]
    simpa [mul_assoc] using
      A.homogeneous (exp m) (exp (-d)) (exp d)
        hm_pos (exp_pos (-d)) (exp_pos d)
  unfold logInvariantOf rawImbalancePotential
  rw [hleft, Real.log_mul hpow_pos.ne' hslice_pos.ne']
  rw [Real.log_rpow hm_pos, Real.log_exp]

/-- Normalizing at the balanced slice removes the constant term, leaving
`degree * scale + imbalance-potential`. -/
theorem raw_homogeneous_to_normalizedLogNormalForm
    (A : RawSymmetricHomogeneousAMM) (m d : ℝ) :
    normalizedLogInvariantOf A.K (m - d) (m + d) =
      A.degree * m + normalizedImbalancePotential A.K d := by
  unfold normalizedLogInvariantOf normalizedImbalancePotential
  rw [raw_homogeneous_to_log_normalForm A m d]
  ring

/-- For two same-degree raw AMMs, the scale term cancels in the normalized
candidate-minus-baseline log-invariant delta. -/
theorem normalizedLogInvariant_delta_same_degree
    (baseline candidate : RawSymmetricHomogeneousAMM)
    (hsame : candidate.degree = baseline.degree) (m d : ℝ) :
    normalizedLogInvariantOf candidate.K (m - d) (m + d) -
        normalizedLogInvariantOf baseline.K (m - d) (m + d) =
      normalizedImbalancePotential candidate.K d -
        normalizedImbalancePotential baseline.K d := by
  rw [raw_homogeneous_to_normalizedLogNormalForm candidate m d,
    raw_homogeneous_to_normalizedLogNormalForm baseline m d, hsame]
  ring

/-- The same-degree normalized log-invariant delta is asset-swap even in the
imbalance coordinate. -/
theorem normalizedLogInvariant_delta_same_degree_even
    (baseline candidate : RawSymmetricHomogeneousAMM)
    (hsame : candidate.degree = baseline.degree) (m d : ℝ) :
    normalizedLogInvariantOf candidate.K (m + d) (m - d) -
        normalizedLogInvariantOf baseline.K (m + d) (m - d) =
      normalizedLogInvariantOf candidate.K (m - d) (m + d) -
        normalizedLogInvariantOf baseline.K (m - d) (m + d) := by
  calc
    normalizedLogInvariantOf candidate.K (m + d) (m - d) -
        normalizedLogInvariantOf baseline.K (m + d) (m - d)
        = normalizedImbalancePotential candidate.K (-d) -
            normalizedImbalancePotential baseline.K (-d) := by
          convert normalizedLogInvariant_delta_same_degree
            baseline candidate hsame m (-d) using 1
          all_goals ring_nf
    _ = normalizedImbalancePotential candidate.K d -
          normalizedImbalancePotential baseline.K d :=
        normalizedImbalancePotential_delta_even baseline candidate d
    _ = normalizedLogInvariantOf candidate.K (m - d) (m + d) -
          normalizedLogInvariantOf baseline.K (m - d) (m + d) := by
        exact (normalizedLogInvariant_delta_same_degree
          baseline candidate hsame m d).symm

/-- Positive homogeneity on the imbalance slice. -/
theorem bonding_curve_homogeneity_slice
    (A : RawSymmetricHomogeneousAMM) (d : ℝ) :
    A.K (exp (-d)) (exp d) =
      exp (-d) ^ A.degree * A.K 1 (exp (2 * d)) := by
  have hcalc : exp (-d) * exp (2 * d) = exp d := by
    rw [← exp_add]
    ring_nf
  conv_lhs =>
    rw [show exp (-d) = exp (-d) * 1 from (mul_one _).symm,
      show exp d = exp (-d) * exp (2 * d) from hcalc.symm]
  exact A.homogeneous (exp (-d)) 1 (exp (2 * d))
    (exp_pos _) one_pos (exp_pos _)

/-- Homogeneity decomposes the raw imbalance potential into a linear scale term
and a reduced one-sided slice. -/
theorem rawImbalancePotential_decomposition
    (A : RawSymmetricHomogeneousAMM) (d : ℝ) :
    rawImbalancePotential A.K d =
      A.degree * (-d) + Real.log (A.K 1 (exp (2 * d))) := by
  simp only [rawImbalancePotential]
  rw [bonding_curve_homogeneity_slice A d]
  rw [Real.log_mul (by positivity)
    (ne_of_gt (A.pos 1 (exp (2 * d)) one_pos (exp_pos _)))]
  rw [Real.log_rpow (exp_pos (-d))]
  rw [Real.log_exp]

/-- The normalized defect field `s(d) := phi'(d) / degree` satisfies `s(0)=0`
for a symmetric homogeneous AMM when `phi` is differentiable at balance. -/
theorem defect_field_zero_at_origin
    (A : RawSymmetricHomogeneousAMM)
    (hdiff : DifferentiableAt ℝ (normalizedImbalancePotential A.K) 0) :
    deriv (normalizedImbalancePotential A.K) 0 / A.degree = 0 := by
  rw [deriv_normalizedImbalancePotential_zero A hdiff]
  simp

/-- Canonical defect field extracted from a raw AMM normalized imbalance
potential. -/
def rawDefectField (A : RawSymmetricHomogeneousAMM) : ℝ → ℝ :=
  fun d => deriv (normalizedImbalancePotential A.K) d / A.degree

/-- The canonical raw defect field is zero at the balanced point when the
normalized imbalance potential is differentiable there. -/
theorem rawDefectField_zero_at_origin
    (A : RawSymmetricHomogeneousAMM)
    (hdiff : DifferentiableAt ℝ (normalizedImbalancePotential A.K) 0) :
    rawDefectField A 0 = 0 :=
  defect_field_zero_at_origin A hdiff

/-- If the normalized imbalance potential is differentiable everywhere, the
canonical defect field satisfies the derivative relation required by the global
CPMM budget theorem. -/
theorem rawDefectField_hasDerivAt_normalizedImbalancePotential
    (A : RawSymmetricHomogeneousAMM)
    (hdiff : ∀ x, DifferentiableAt ℝ (normalizedImbalancePotential A.K) x) :
    ∀ x,
      HasDerivAt
        (normalizedImbalancePotential A.K)
        (A.degree * rawDefectField A x)
        x := by
  intro x
  have hdeg_ne : A.degree ≠ 0 := ne_of_gt A.degree_pos
  have hmul :
      A.degree * rawDefectField A x =
        deriv (normalizedImbalancePotential A.K) x := by
    unfold rawDefectField
    field_simp [hdeg_ne]
  simpa [hmul] using (hdiff x).hasDerivAt

/-- The canonical raw defect field is odd when the normalized imbalance
potential is differentiable everywhere. -/
theorem rawDefectField_odd
    (A : RawSymmetricHomogeneousAMM)
    (hdiff : ∀ x, DifferentiableAt ℝ (normalizedImbalancePotential A.K) x) :
    ∀ x, rawDefectField A (-x) = -rawDefectField A x := by
  intro x
  unfold rawDefectField
  rw [deriv_normalizedImbalancePotential_neg A x (hdiff x) (hdiff (-x))]
  ring

/-- Raw-AMM wrapper for the checked global CPMM budget theorem.  Under the
paper-style pathwise slippage hypotheses on the extracted same-price defect
field, the candidate original-HODL value ratio is globally bounded by CPMM. -/
theorem raw_cpmm_same_price_no_free_lunch_of_pathwise_slippage
    (A : RawSymmetricHomogeneousAMM) {s : ℝ → ℝ}
    (hs : Differentiable ℝ s)
    (hphi :
      ∀ x, HasDerivAt (normalizedImbalancePotential A.K) (A.degree * s x) x)
    (hbounded : ∀ x, (s x) ^ 2 < 1)
    (hq_nonneg : ∀ x, 0 ≤ deriv (qOfState s) x)
    (hq_le_two : ∀ x, deriv (qOfState s) x ≤ 2)
    (hs0 : s 0 = 0) :
    ∀ x,
      candidateOriginalHODLValueRatio
          A.degree (normalizedImbalancePotential A.K) s x ≤
        cpmmOriginalHODLValueRatio (qOfState s x) := by
  exact cpmm_same_price_no_free_lunch_of_pathwise_slippage_from_normalizedInvariant
    (K := A.K) (n := A.degree) (s := s)
    (ne_of_gt A.degree_pos) hs hphi hbounded hq_nonneg hq_le_two hs0

/-- Strict-price-path variant of the raw-AMM CPMM budget wrapper. -/
theorem raw_cpmm_same_price_no_free_lunch_of_strict_price_pathwise_slippage
    (A : RawSymmetricHomogeneousAMM) {s : ℝ → ℝ}
    (hs : Differentiable ℝ s)
    (hphi :
      ∀ x, HasDerivAt (normalizedImbalancePotential A.K) (A.degree * s x) x)
    (hbounded : ∀ x, (s x) ^ 2 < 1)
    (hq_pos : ∀ x, 0 < deriv (qOfState s) x)
    (hq_le_two : ∀ x, deriv (qOfState s) x ≤ 2)
    (hs0 : s 0 = 0) :
    ∀ x,
      candidateOriginalHODLValueRatio
          A.degree (normalizedImbalancePotential A.K) s x ≤
        cpmmOriginalHODLValueRatio (qOfState s x) := by
  exact
    cpmm_same_price_no_free_lunch_of_strict_price_pathwise_slippage_from_normalizedInvariant
      (K := A.K) (n := A.degree) (s := s)
      (ne_of_gt A.degree_pos) hs hphi hbounded hq_pos hq_le_two hs0

/-- Global CPMM budget wrapper specialized to the canonical derivative defect
field. -/
theorem raw_cpmm_same_price_no_free_lunch_of_derivative_defect_field
    (A : RawSymmetricHomogeneousAMM)
    (hphi_diff : Differentiable ℝ (normalizedImbalancePotential A.K))
    (hs : Differentiable ℝ (rawDefectField A))
    (hbounded : ∀ x, (rawDefectField A x) ^ 2 < 1)
    (hq_nonneg : ∀ x, 0 ≤ deriv (qOfState (rawDefectField A)) x)
    (hq_le_two : ∀ x, deriv (qOfState (rawDefectField A)) x ≤ 2) :
    ∀ x,
      candidateOriginalHODLValueRatio
          A.degree (normalizedImbalancePotential A.K) (rawDefectField A) x ≤
        cpmmOriginalHODLValueRatio (qOfState (rawDefectField A) x) := by
  exact raw_cpmm_same_price_no_free_lunch_of_pathwise_slippage
    A hs
    (rawDefectField_hasDerivAt_normalizedImbalancePotential A
      (fun x => hphi_diff x))
    hbounded hq_nonneg hq_le_two
    (rawDefectField_zero_at_origin A (hphi_diff 0))

/-- Strict-price-path variant specialized to the canonical derivative defect
field. -/
theorem raw_cpmm_same_price_no_free_lunch_of_strict_derivative_defect_field
    (A : RawSymmetricHomogeneousAMM)
    (hphi_diff : Differentiable ℝ (normalizedImbalancePotential A.K))
    (hs : Differentiable ℝ (rawDefectField A))
    (hbounded : ∀ x, (rawDefectField A x) ^ 2 < 1)
    (hq_pos : ∀ x, 0 < deriv (qOfState (rawDefectField A)) x)
    (hq_le_two : ∀ x, deriv (qOfState (rawDefectField A)) x ≤ 2) :
    ∀ x,
      candidateOriginalHODLValueRatio
          A.degree (normalizedImbalancePotential A.K) (rawDefectField A) x ≤
        cpmmOriginalHODLValueRatio (qOfState (rawDefectField A) x) := by
  exact raw_cpmm_same_price_no_free_lunch_of_strict_price_pathwise_slippage
    A hs
    (rawDefectField_hasDerivAt_normalizedImbalancePotential A
      (fun x => hphi_diff x))
    hbounded hq_pos hq_le_two
    (rawDefectField_zero_at_origin A (hphi_diff 0))

/-!
## Remaining bridge obligations

To turn this raw structure into the final global AMM theorem, the next Lean
surface should prove the following extraction steps for two raw AMMs sharing one
coordinate and degree:

1. Slippage identification: the candidate-minus-baseline slippage delta is
   `hodlSlipDeltaExact n b (2*k+1)` for the first nonzero even Taylor
   coefficient `b > 0`.
2. Chain-rule expansion limits: the extracted `deltaR2`, `deltaQ1`, and
   `deltaQ2` functions satisfy the three `Tendsto` hypotheses required by
   `OriginalHODLPairExpansionObligations`.
3. Curvature identification: the candidate-minus-baseline original-HODL
   curvature delta is `originalHODLCurvatureChainDelta deltaR2 deltaQ1 deltaQ2`.
-/

end
end RawAMMBridge
end LocalJetFrontier
end Impossibility
end TauSwap
