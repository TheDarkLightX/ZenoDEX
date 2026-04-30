import Proofs.AMMGlobalCounterexamples
import Proofs.OriginalHODLCurvatureLeadingLaw

/-!
# Original-HODL global bridge

This file plugs the Aristotle-derived original-HODL coefficient law into the
global obstruction API from `AMMGlobalCounterexamples`.

The key bridge is deliberately small:

* ratio limits against the first even basis `(d^order)^2` produce
  `FirstEvenTaylorCoefficientData`;
* the original-HODL chain-rule law supplies the curvature ratio limit;
* therefore a positive first odd monomial perturbation cannot be globally
  no-worse in both slippage and original-HODL curvature.

The remaining raw-AMM obligation is still explicit: callers must provide the
three chain-rule expansion limits for `δR''`, `δq'`, and `δq''`.
-/

open Real Filter Topology

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

namespace OriginalHODLBridge

/-- Odd perturbation exponent attached to a first even Taylor order. -/
def firstEvenHODLExponent (order : ℕ) : ℕ :=
  2 * order + 1

/-- For odd exponent `2*order+1`, the normalized original-HODL basis
`d^(A-1)` is exactly `(d^order)^2`. -/
lemma pow_firstEvenHODLExponent_sub_one (order : ℕ) (d : ℝ) :
    d ^ (firstEvenHODLExponent order - 1) = (d ^ order) ^ 2 := by
  have hpow : firstEvenHODLExponent order - 1 = order * 2 := by
    unfold firstEvenHODLExponent
    omega
  rw [hpow, pow_mul]

/-- Chain-rule curvature delta used by the original-HODL coefficient law. -/
def originalHODLCurvatureChainDelta
    (δR'' δq' δq'' : ℝ → ℝ) : ℝ → ℝ :=
  fun d => (-1 / 16 : ℝ) *
    (2 * δR'' d -
      2 * δq' d * ((2 * sinh d ^ 2 - cosh d ^ 2) / cosh d ^ 3) -
      (-(sinh d / cosh d ^ 2)) * δq'' d)

/-- Ratio limits against the first even basis are enough to construct the
coefficient-facing Taylor certificate expected by the global obstruction API. -/
def firstEvenTaylorCoefficientData_of_tendsto_ratios
    {slipDelta curvDelta : ℝ → ℝ}
    (order : ℕ) (horder : 0 < order)
    (slipCoeff : ℝ) (hslipCoeff : slipCoeff < 0)
    (hslip :
      Tendsto (fun d => slipDelta d / (d ^ order) ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 slipCoeff))
    (hcurv :
      Tendsto (fun d => curvDelta d / (d ^ order) ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 (-slipCoeff / 8))) :
    FirstEvenTaylorCoefficientData slipDelta curvDelta where
  order := order
  order_pos := horder
  slipCoeff := slipCoeff
  slipCoeff_neg := hslipCoeff
  slipRem := fun d => slipDelta d - slipCoeff * (d ^ order) ^ 2
  curvRem := fun d => curvDelta d - (-slipCoeff / 8) * (d ^ order) ^ 2
  slip_decomp := by
    filter_upwards with d
    ring_nf
  curv_decomp := by
    filter_upwards with d
    ring_nf
  slip_rem_small := by
    have hbasis_ne :
        ∀ᶠ d in 𝓝[≠] (0 : ℝ), (d ^ order) ^ 2 ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with d hd
      exact pow_ne_zero 2 (pow_ne_zero order hd)
    have hsmall :
        Tendsto (fun d => slipDelta d / (d ^ order) ^ 2 - slipCoeff)
          (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have hconst :
          Tendsto (fun _ : ℝ => slipCoeff) (𝓝[≠] (0 : ℝ)) (𝓝 slipCoeff) :=
        tendsto_const_nhds
      simpa using hslip.sub hconst
    have hrewrite :
        (fun d => (slipDelta d - slipCoeff * (d ^ order) ^ 2) /
            (d ^ order) ^ 2) =ᶠ[𝓝[≠] (0 : ℝ)]
          (fun d => slipDelta d / (d ^ order) ^ 2 - slipCoeff) := by
      filter_upwards [hbasis_ne] with d hbasis
      rw [sub_div]
      rw [mul_div_cancel_right₀ slipCoeff hbasis]
    exact hsmall.congr' hrewrite.symm
  curv_rem_small := by
    have hbasis_ne :
        ∀ᶠ d in 𝓝[≠] (0 : ℝ), (d ^ order) ^ 2 ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with d hd
      exact pow_ne_zero 2 (pow_ne_zero order hd)
    have hsmall :
        Tendsto (fun d => curvDelta d / (d ^ order) ^ 2 - (-slipCoeff / 8))
          (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have hconst :
          Tendsto (fun _ : ℝ => -slipCoeff / 8)
            (𝓝[≠] (0 : ℝ)) (𝓝 (-slipCoeff / 8)) :=
        tendsto_const_nhds
      simpa using hcurv.sub hconst
    have hrewrite :
        (fun d => (curvDelta d - (-slipCoeff / 8) * (d ^ order) ^ 2) /
            (d ^ order) ^ 2) =ᶠ[𝓝[≠] (0 : ℝ)]
          (fun d => curvDelta d / (d ^ order) ^ 2 - (-slipCoeff / 8)) := by
      filter_upwards [hbasis_ne] with d hbasis
      rw [sub_div]
      rw [mul_div_cancel_right₀ (-slipCoeff / 8) hbasis]
    exact hsmall.congr' hrewrite.symm

/-- The Aristotle-derived original-HODL law, plus the explicit raw chain-rule
expansion hypotheses, constructs the coefficient-facing first-even Taylor
certificate used by the global obstruction theorem. -/
def originalHODL_firstEvenTaylorCoefficientData
    (order : ℕ) (horder : 0 < order)
    (n b : ℝ) (hn : 0 < n) (hb : 0 < b)
    (δR'' δq' δq'' : ℝ → ℝ)
    (hδR :
      Tendsto
        (fun d => δR'' d / d ^ (firstEvenHODLExponent order - 1))
        (𝓝[≠] (0 : ℝ))
        (𝓝 ((b / n) * ((firstEvenHODLExponent order : ℝ) ^ 2))))
    (hδq' :
      Tendsto
        (fun d => δq' d / d ^ (firstEvenHODLExponent order - 1))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (-2 * (b / n) * (firstEvenHODLExponent order : ℝ))))
    (hδq'' :
      Tendsto
        (fun d => δq'' d / d ^ (firstEvenHODLExponent order - 2))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (-2 * (b / n) * (firstEvenHODLExponent order : ℝ) *
          ((firstEvenHODLExponent order : ℝ) - 1)))) :
    FirstEvenTaylorCoefficientData
      (TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact
        n b (firstEvenHODLExponent order))
      (originalHODLCurvatureChainDelta δR'' δq' δq'') := by
  let A : ℕ := firstEvenHODLExponent order
  have hA : 3 ≤ A := by
    dsimp [A, firstEvenHODLExponent]
    omega
  have hβ : 0 < b / n := div_pos hb hn
  have hApos : 0 < (A : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hA)
  have hslipCoeff_neg : -((A : ℝ) * (b / n)) < 0 := by
    exact neg_neg_of_pos (mul_pos hApos hβ)
  have hslipA :
      Tendsto
        (fun d =>
          TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A d /
            d ^ (A - 1))
        (𝓝[≠] (0 : ℝ)) (𝓝 (-(A : ℝ) * b / n)) :=
    TauSwap.Impossibility.OriginalHODL.slip_expansion n b A hn hA
  have hslip :
      Tendsto
        (fun d =>
          TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact n b A d /
            (d ^ order) ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 (-((A : ℝ) * (b / n)))) := by
    convert hslipA using 1
    · ext d
      rw [show A = firstEvenHODLExponent order by rfl]
      rw [pow_firstEvenHODLExponent_sub_one]
    · ring_nf
  have hcurvA :
      Tendsto
        (fun d => originalHODLCurvatureChainDelta δR'' δq' δq'' d /
          d ^ (A - 1))
        (𝓝[≠] (0 : ℝ)) (𝓝 (-(-(b / n) * (A : ℝ)) / 8)) := by
    simpa [A, originalHODLCurvatureChainDelta] using
      (TauSwap.Impossibility.OriginalHODL.hodl_curvature_leading_law
        A hA (b / n) hβ δR'' δq' δq'' hδR hδq' hδq'')
  have hcurv :
      Tendsto
        (fun d => originalHODLCurvatureChainDelta δR'' δq' δq'' d /
          (d ^ order) ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 (- (-((A : ℝ) * (b / n))) / 8)) := by
    convert hcurvA using 1
    · ext d
      rw [show A = firstEvenHODLExponent order by rfl]
      rw [pow_firstEvenHODLExponent_sub_one]
    · ring_nf
  exact firstEvenTaylorCoefficientData_of_tendsto_ratios
    order horder (-((A : ℝ) * (b / n))) hslipCoeff_neg hslip hcurv

/-- Global no-free-lunch consequence of the original-HODL chain-rule expansion
law: a positive first odd perturbation cannot make both slippage and
original-HODL curvature globally no worse. -/
theorem originalHODL_not_simultaneous_global_no_worse
    (order : ℕ) (horder : 0 < order)
    (n b : ℝ) (hn : 0 < n) (hb : 0 < b)
    (δR'' δq' δq'' : ℝ → ℝ)
    (hδR :
      Tendsto
        (fun d => δR'' d / d ^ (firstEvenHODLExponent order - 1))
        (𝓝[≠] (0 : ℝ))
        (𝓝 ((b / n) * ((firstEvenHODLExponent order : ℝ) ^ 2))))
    (hδq' :
      Tendsto
        (fun d => δq' d / d ^ (firstEvenHODLExponent order - 1))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (-2 * (b / n) * (firstEvenHODLExponent order : ℝ))))
    (hδq'' :
      Tendsto
        (fun d => δq'' d / d ^ (firstEvenHODLExponent order - 2))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (-2 * (b / n) * (firstEvenHODLExponent order : ℝ) *
          ((firstEvenHODLExponent order : ℝ) - 1)))) :
    ¬ ((∀ d,
          TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact
            n b (firstEvenHODLExponent order) d ≤ 0) ∧
        (∀ d, originalHODLCurvatureChainDelta δR'' δq' δq'' d ≤ 0)) :=
  FirstEvenTaylorCoefficientData.not_simultaneous_global_no_worse
    (originalHODL_firstEvenTaylorCoefficientData
      order horder n b hn hb δR'' δq' δq'' hδR hδq' hδq'')

/-!
## Named expansion payload

This structure is the exact assumption object that a future universal raw-AMM
semantics theorem should construct.  The global obstruction above is already
checked once this object exists.
-/

/-- Original-HODL first-even expansion payload.  This packages the raw
chain-rule expansion limits, reserve scale, perturbation coefficient, and first
even order into one reusable semantic boundary object. -/
structure OriginalHODLFirstEvenExpansion where
  order : ℕ
  order_pos : 0 < order
  n : ℝ
  b : ℝ
  n_pos : 0 < n
  b_pos : 0 < b
  δR'' : ℝ → ℝ
  δq' : ℝ → ℝ
  δq'' : ℝ → ℝ
  δR_tendsto :
    Tendsto
      (fun d => δR'' d / d ^ (firstEvenHODLExponent order - 1))
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((b / n) * ((firstEvenHODLExponent order : ℝ) ^ 2)))
  δq'_tendsto :
    Tendsto
      (fun d => δq' d / d ^ (firstEvenHODLExponent order - 1))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-2 * (b / n) * (firstEvenHODLExponent order : ℝ)))
  δq''_tendsto :
    Tendsto
      (fun d => δq'' d / d ^ (firstEvenHODLExponent order - 2))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-2 * (b / n) * (firstEvenHODLExponent order : ℝ) *
        ((firstEvenHODLExponent order : ℝ) - 1)))

/-- Slippage delta attached to an original-HODL first-even expansion payload. -/
def OriginalHODLFirstEvenExpansion.slipDelta
    (E : OriginalHODLFirstEvenExpansion) : ℝ → ℝ :=
  TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact
    E.n E.b (firstEvenHODLExponent E.order)

/-- Curvature delta attached to an original-HODL first-even expansion payload. -/
def OriginalHODLFirstEvenExpansion.curvDelta
    (E : OriginalHODLFirstEvenExpansion) : ℝ → ℝ :=
  originalHODLCurvatureChainDelta E.δR'' E.δq' E.δq''

/-- A named original-HODL expansion payload constructs the coefficient-facing
Taylor certificate required by the global obstruction API. -/
def OriginalHODLFirstEvenExpansion.coefficientData
    (E : OriginalHODLFirstEvenExpansion) :
    FirstEvenTaylorCoefficientData E.slipDelta E.curvDelta := by
  unfold OriginalHODLFirstEvenExpansion.slipDelta
    OriginalHODLFirstEvenExpansion.curvDelta
  exact originalHODL_firstEvenTaylorCoefficientData
    E.order E.order_pos E.n E.b E.n_pos E.b_pos
    E.δR'' E.δq' E.δq''
    E.δR_tendsto E.δq'_tendsto E.δq''_tendsto

/-- An original-HODL first-even expansion payload supplies the abstract
same-benchmark analytic obligations used by the older global theorem surface. -/
def OriginalHODLFirstEvenExpansion.toSameBenchmarkAnalyticPairObligations
    (E : OriginalHODLFirstEvenExpansion) :
    SameBenchmarkAnalyticPairObligations E.slipDelta E.curvDelta :=
  E.coefficientData.toSameBenchmarkAnalyticPairObligations

/-- Payload-level global no-free-lunch theorem.  This is the form a raw-AMM
semantics layer should use after proving it can construct
`OriginalHODLFirstEvenExpansion`. -/
theorem OriginalHODLFirstEvenExpansion.not_simultaneous_global_no_worse
    (E : OriginalHODLFirstEvenExpansion) :
    ¬ ((∀ d, E.slipDelta d ≤ 0) ∧ (∀ d, E.curvDelta d ≤ 0)) :=
  E.coefficientData.not_simultaneous_global_no_worse

/-!
## Pair-level extraction obligations

The next structure decomposes the missing concrete-AMM bridge into local proof
obligations for one baseline/candidate pair.  A concrete semantics theorem
should construct this certificate for every admissible pair.
-/

/-- Concrete pair-level extraction obligations for the original-HODL global
bridge.  The fields are intentionally local:

* the first-even order and positive scale/coefficient;
* the three chain-rule expansion limits for `δR''`, `δq'`, and `δq''`;
* the two alignment equations identifying extracted candidate-minus-baseline
  deltas with the original-HODL slippage and curvature deltas.

Once this object exists, the global obstruction follows by packaging it into
`OriginalHODLFirstEvenExpansion`. -/
structure OriginalHODLPairExpansionObligations
    {RawAMM : Type} (coeffs : RawAMMCoefficientExtractors RawAMM)
    (baseline candidate : RawAMM) where
  order : ℕ
  order_pos : 0 < order
  n : ℝ
  b : ℝ
  n_pos : 0 < n
  b_pos : 0 < b
  deltaR2 : ℝ → ℝ
  deltaQ1 : ℝ → ℝ
  deltaQ2 : ℝ → ℝ
  deltaR2_tendsto :
    Tendsto
      (fun d => deltaR2 d / d ^ (firstEvenHODLExponent order - 1))
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((b / n) * ((firstEvenHODLExponent order : ℝ) ^ 2)))
  deltaQ1_tendsto :
    Tendsto
      (fun d => deltaQ1 d / d ^ (firstEvenHODLExponent order - 1))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-2 * (b / n) * (firstEvenHODLExponent order : ℝ)))
  deltaQ2_tendsto :
    Tendsto
      (fun d => deltaQ2 d / d ^ (firstEvenHODLExponent order - 2))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-2 * (b / n) * (firstEvenHODLExponent order : ℝ) *
        ((firstEvenHODLExponent order : ℝ) - 1)))
  slippage_delta_eq :
    FunctionDelta (coeffs.slippage candidate) (coeffs.slippage baseline) =
      TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact
        n b (firstEvenHODLExponent order)
  curvature_delta_eq :
    FunctionDelta (coeffs.curvature candidate) (coeffs.curvature baseline) =
      originalHODLCurvatureChainDelta deltaR2 deltaQ1 deltaQ2

/-- Package pair-level extraction obligations into the named original-HODL
first-even expansion payload. -/
def OriginalHODLPairExpansionObligations.toExpansion
    {RawAMM : Type} {coeffs : RawAMMCoefficientExtractors RawAMM}
    {baseline candidate : RawAMM}
    (C : OriginalHODLPairExpansionObligations coeffs baseline candidate) :
    OriginalHODLFirstEvenExpansion where
  order := C.order
  order_pos := C.order_pos
  n := C.n
  b := C.b
  n_pos := C.n_pos
  b_pos := C.b_pos
  δR'' := C.deltaR2
  δq' := C.deltaQ1
  δq'' := C.deltaQ2
  δR_tendsto := C.deltaR2_tendsto
  δq'_tendsto := C.deltaQ1_tendsto
  δq''_tendsto := C.deltaQ2_tendsto

/-- Pair-level extraction obligations produce the expansion witness required by
`OriginalHODLRawExpansionSemantics.construct_expansion`. -/
theorem OriginalHODLPairExpansionObligations.exists_expansion
    {RawAMM : Type} {coeffs : RawAMMCoefficientExtractors RawAMM}
    {baseline candidate : RawAMM}
    (C : OriginalHODLPairExpansionObligations coeffs baseline candidate) :
    ∃ E : OriginalHODLFirstEvenExpansion,
      FunctionDelta (coeffs.slippage candidate) (coeffs.slippage baseline) =
          E.slipDelta ∧
        FunctionDelta (coeffs.curvature candidate) (coeffs.curvature baseline) =
          E.curvDelta := by
  exact ⟨C.toExpansion,
    by
      simpa [OriginalHODLPairExpansionObligations.toExpansion,
        OriginalHODLFirstEvenExpansion.slipDelta] using C.slippage_delta_eq,
    by
      simpa [OriginalHODLPairExpansionObligations.toExpansion,
        OriginalHODLFirstEvenExpansion.curvDelta] using C.curvature_delta_eq⟩

/-- A pair-level original-HODL certificate also supplies the older abstract
same-benchmark surface assumptions on the extracted coefficient surface. -/
def OriginalHODLPairExpansionObligations.toSurfaceAssumptions
    {RawAMM : Type} {coeffs : RawAMMCoefficientExtractors RawAMM}
    {baseline candidate : RawAMM}
    (C : OriginalHODLPairExpansionObligations coeffs baseline candidate) :
    SameBenchmarkAnalyticSurfaceAssumptions (coeffs.surface baseline candidate) := by
  rcases C.exists_expansion with ⟨E, hslip, hcurv⟩
  constructor
  · simpa [RawAMMCoefficientExtractors.surface, AMMCoefficientSurface.slipDelta,
      hslip] using
      E.toSameBenchmarkAnalyticPairObligations.slippage_extraction
  · simpa [RawAMMCoefficientExtractors.surface, AMMCoefficientSurface.slipDelta,
      AMMCoefficientSurface.curvDelta, hslip, hcurv] using
      E.toSameBenchmarkAnalyticPairObligations.curvature_law

/-- A pair-level original-HODL certificate packages into the generic concrete
same-benchmark analytic AMM pair. -/
def OriginalHODLPairExpansionObligations.toConcretePair
    {RawAMM : Type} {coeffs : RawAMMCoefficientExtractors RawAMM}
    {baseline candidate : RawAMM}
    (C : OriginalHODLPairExpansionObligations coeffs baseline candidate) :
    ConcreteSameBenchmarkAnalyticAMMPair :=
  (coeffs.surface baseline candidate).toConcretePair C.toSurfaceAssumptions

/-- Direct pair-certificate obstruction: once a concrete pair supplies the
original-HODL expansion obligations, its extracted slippage and curvature
deltas cannot both be globally no-worse. -/
theorem OriginalHODLPairExpansionObligations.not_simultaneous_global_no_worse
    {RawAMM : Type} {coeffs : RawAMMCoefficientExtractors RawAMM}
    {baseline candidate : RawAMM}
    (C : OriginalHODLPairExpansionObligations coeffs baseline candidate) :
    ¬ (GloballyNoWorse (coeffs.slippage candidate) (coeffs.slippage baseline) ∧
        GloballyNoWorse (coeffs.curvature candidate) (coeffs.curvature baseline)) := by
  intro hglobal
  rcases C.exists_expansion with ⟨E, hslip, hcurv⟩
  apply E.not_simultaneous_global_no_worse
  constructor
  · rw [← hslip]
    exact (deltaNoWorse_functionDelta_iff).2 hglobal.1
  · rw [← hcurv]
    exact (deltaNoWorse_functionDelta_iff).2 hglobal.2

/-- Direct pair-certificate strict form: a certified original-HODL pair cannot
have globally no-worse curvature together with globally no-worse and strictly
better slippage. -/
theorem OriginalHODLPairExpansionObligations.not_simultaneous_with_strict
    {RawAMM : Type} {coeffs : RawAMMCoefficientExtractors RawAMM}
    {baseline candidate : RawAMM}
    (C : OriginalHODLPairExpansionObligations coeffs baseline candidate) :
    ¬ (GloballyNoWorse (coeffs.slippage candidate) (coeffs.slippage baseline) ∧
        StrictlyBetterSomewhere (coeffs.slippage candidate) (coeffs.slippage baseline) ∧
        GloballyNoWorse (coeffs.curvature candidate) (coeffs.curvature baseline)) := by
  intro h
  exact C.not_simultaneous_global_no_worse ⟨h.1, h.2.2⟩

/-!
## Raw-semantics interface

The universal theorem is not proved by broadening the no-free-lunch theorem.
It is proved by showing that the raw AMM semantics construct one of the named
expansion payloads and that the payload deltas are exactly the extracted
candidate-minus-baseline deltas.
-/

/-- Original-HODL raw semantics interface.  It packages deterministic
coefficient extractors and the remaining universal proof obligation: every
admissible raw pair must realize a first-even original-HODL expansion payload. -/
structure OriginalHODLRawExpansionSemantics (RawAMM : Type) where
  AdmissiblePair : RawAMM → RawAMM → Prop
  coeffs : RawAMMCoefficientExtractors RawAMM
  construct_expansion :
    ∀ {baseline candidate : RawAMM},
      AdmissiblePair baseline candidate →
        ∃ E : OriginalHODLFirstEvenExpansion,
          FunctionDelta (coeffs.slippage candidate) (coeffs.slippage baseline) =
              E.slipDelta ∧
            FunctionDelta (coeffs.curvature candidate) (coeffs.curvature baseline) =
              E.curvDelta

/-- The extracted coefficient surface for an original-HODL raw semantics
model. -/
def OriginalHODLRawExpansionSemantics.surface
    {RawAMM : Type} (M : OriginalHODLRawExpansionSemantics RawAMM)
    (baseline candidate : RawAMM) : AMMCoefficientSurface :=
  M.coeffs.surface baseline candidate

/-- Original-HODL raw expansion semantics imply the older abstract
same-benchmark surface assumptions on each admissible extracted surface. -/
def OriginalHODLRawExpansionSemantics.surface_assumptions
    {RawAMM : Type} (M : OriginalHODLRawExpansionSemantics RawAMM)
    {baseline candidate : RawAMM}
    (hpair : M.AdmissiblePair baseline candidate) :
    SameBenchmarkAnalyticSurfaceAssumptions (M.surface baseline candidate) := by
  rcases M.construct_expansion hpair with ⟨E, hslip, hcurv⟩
  constructor
  · simpa [OriginalHODLRawExpansionSemantics.surface,
      RawAMMCoefficientExtractors.surface, AMMCoefficientSurface.slipDelta,
      hslip] using
      E.toSameBenchmarkAnalyticPairObligations.slippage_extraction
  · simpa [OriginalHODLRawExpansionSemantics.surface,
      RawAMMCoefficientExtractors.surface, AMMCoefficientSurface.slipDelta,
      AMMCoefficientSurface.curvDelta, hslip, hcurv] using
      E.toSameBenchmarkAnalyticPairObligations.curvature_law

/-- Forget the original-HODL-specific payload and expose the deterministic raw
semantics as an abstract same-benchmark analytic extractor model. -/
def OriginalHODLRawExpansionSemantics.toExtractedRawAMMSemanticsModel
    {RawAMM : Type} (M : OriginalHODLRawExpansionSemantics RawAMM) :
    ExtractedRawAMMSemanticsModel RawAMM where
  SameBenchmarkAnalytic := M.AdmissiblePair
  coeffs := M.coeffs
  surface_assumptions := by
    intro baseline candidate hpair
    exact M.surface_assumptions hpair

/-- Compatibility with the older abstract same-benchmark theorem surface:
original-HODL expansion semantics also rule out simultaneous global no-worse
curvature together with a strict global slippage improvement. -/
theorem originalHODL_surface_not_simultaneous_global_no_worse_with_strict
    {RawAMM : Type} (M : OriginalHODLRawExpansionSemantics RawAMM)
    {baseline candidate : RawAMM}
    (hpair : M.AdmissiblePair baseline candidate) :
    ¬ (GloballyNoWorse (M.surface baseline candidate).candidateSlippage
          (M.surface baseline candidate).baselineSlippage ∧
        StrictlyBetterSomewhere (M.surface baseline candidate).candidateSlippage
          (M.surface baseline candidate).baselineSlippage ∧
        GloballyNoWorse (M.surface baseline candidate).candidateCurvature
          (M.surface baseline candidate).baselineCurvature) := by
  simpa [OriginalHODLRawExpansionSemantics.toExtractedRawAMMSemanticsModel,
    ExtractedRawAMMSemanticsModel.surface,
    OriginalHODLRawExpansionSemantics.surface] using
    (M.toExtractedRawAMMSemanticsModel.surface_not_simultaneous_global_no_worse hpair)

/-- Coefficient-extractor form of the strict-slippage compatibility theorem. -/
theorem OriginalHODLRawExpansionSemantics.not_simultaneous_with_strict
    {RawAMM : Type} (M : OriginalHODLRawExpansionSemantics RawAMM)
    {baseline candidate : RawAMM}
    (hpair : M.AdmissiblePair baseline candidate) :
    ¬ (GloballyNoWorse (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
        StrictlyBetterSomewhere (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
        GloballyNoWorse (M.coeffs.curvature candidate) (M.coeffs.curvature baseline)) := by
  simpa [OriginalHODLRawExpansionSemantics.surface,
    RawAMMCoefficientExtractors.surface] using
    originalHODL_surface_not_simultaneous_global_no_worse_with_strict M hpair

/-- Universal raw-semantics consequence, conditional only on the model's
explicit expansion-construction obligation.  For every admissible raw pair in
the model, the extracted slippage and curvature functions cannot both be
globally no worse. -/
theorem OriginalHODLRawExpansionSemantics.not_simultaneous_global_no_worse
    {RawAMM : Type} (M : OriginalHODLRawExpansionSemantics RawAMM)
    {baseline candidate : RawAMM}
    (hpair : M.AdmissiblePair baseline candidate) :
    ¬ (GloballyNoWorse (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
        GloballyNoWorse (M.coeffs.curvature candidate) (M.coeffs.curvature baseline)) := by
  intro hglobal
  rcases M.construct_expansion hpair with ⟨E, hslip, hcurv⟩
  apply E.not_simultaneous_global_no_worse
  constructor
  · rw [← hslip]
    exact (deltaNoWorse_functionDelta_iff).2 hglobal.1
  · rw [← hcurv]
    exact (deltaNoWorse_functionDelta_iff).2 hglobal.2

/-- Surface-level form of the universal raw-semantics consequence. -/
theorem OriginalHODLRawExpansionSemantics.surface_not_simultaneous_global_no_worse
    {RawAMM : Type} (M : OriginalHODLRawExpansionSemantics RawAMM)
    {baseline candidate : RawAMM}
    (hpair : M.AdmissiblePair baseline candidate) :
    ¬ (GloballyNoWorse (M.surface baseline candidate).candidateSlippage
          (M.surface baseline candidate).baselineSlippage ∧
        GloballyNoWorse (M.surface baseline candidate).candidateCurvature
          (M.surface baseline candidate).baselineCurvature) := by
  simpa [OriginalHODLRawExpansionSemantics.surface,
    RawAMMCoefficientExtractors.surface] using
    M.not_simultaneous_global_no_worse hpair

/-- Global existential form: an original-HODL raw expansion model has no
admissible pair whose extracted slippage and curvature are both globally
no-worse than the baseline. -/
theorem OriginalHODLRawExpansionSemantics.no_admissible_simultaneous_global_no_worse
    {RawAMM : Type} (M : OriginalHODLRawExpansionSemantics RawAMM) :
    ¬ ∃ (baseline candidate : RawAMM),
        M.AdmissiblePair baseline candidate ∧
          GloballyNoWorse (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
          GloballyNoWorse (M.coeffs.curvature candidate) (M.coeffs.curvature baseline) := by
  rintro ⟨baseline, candidate, hpair, hslip, hcurv⟩
  exact M.not_simultaneous_global_no_worse hpair ⟨hslip, hcurv⟩

/-- Global existential form of the strict-slippage bridge: an original-HODL raw
expansion model has no admissible pair with globally no-worse curvature and a
strict global slippage improvement. -/
theorem OriginalHODLRawExpansionSemantics.no_admissible_simultaneous_with_strict
    {RawAMM : Type} (M : OriginalHODLRawExpansionSemantics RawAMM) :
    ¬ ∃ (baseline candidate : RawAMM),
        M.AdmissiblePair baseline candidate ∧
          GloballyNoWorse (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
          StrictlyBetterSomewhere (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
          GloballyNoWorse (M.coeffs.curvature candidate) (M.coeffs.curvature baseline) := by
  rintro ⟨baseline, candidate, hpair, hslip, hstrict, hcurv⟩
  exact M.not_simultaneous_with_strict hpair ⟨hslip, hstrict, hcurv⟩

/-!
## Concrete extraction interface

This layer is the decomposed target for a future raw-AMM calculus.  It asks for
one local extraction certificate per admissible pair and then reuses the checked
global theorem above.
-/

/-- A concrete extraction semantics model for original-HODL.  Compared with
`OriginalHODLRawExpansionSemantics`, this version exposes the local obligations
that a concrete AMM proof should actually construct for each pair. -/
structure OriginalHODLConcreteExtractionSemantics (RawAMM : Type) where
  AdmissiblePair : RawAMM → RawAMM → Prop
  coeffs : RawAMMCoefficientExtractors RawAMM
  pair_obligations :
    ∀ {baseline candidate : RawAMM},
      AdmissiblePair baseline candidate →
        OriginalHODLPairExpansionObligations coeffs baseline candidate

/-- A concrete extraction semantics model forgets the local proof-carrying
fields into the more compact raw expansion semantics interface. -/
def OriginalHODLConcreteExtractionSemantics.toRawExpansionSemantics
    {RawAMM : Type} (M : OriginalHODLConcreteExtractionSemantics RawAMM) :
    OriginalHODLRawExpansionSemantics RawAMM where
  AdmissiblePair := M.AdmissiblePair
  coeffs := M.coeffs
  construct_expansion := by
    intro baseline candidate hpair
    exact (M.pair_obligations hpair).exists_expansion

/-- The extracted coefficient surface for a concrete extraction model. -/
def OriginalHODLConcreteExtractionSemantics.surface
    {RawAMM : Type} (M : OriginalHODLConcreteExtractionSemantics RawAMM)
    (baseline candidate : RawAMM) : AMMCoefficientSurface :=
  M.coeffs.surface baseline candidate

/-- Every admissible pair in a concrete extraction model supplies the generic
same-benchmark analytic surface assumptions on its extracted coefficient
surface. -/
def OriginalHODLConcreteExtractionSemantics.surface_assumptions
    {RawAMM : Type} (M : OriginalHODLConcreteExtractionSemantics RawAMM)
    {baseline candidate : RawAMM}
    (hpair : M.AdmissiblePair baseline candidate) :
    SameBenchmarkAnalyticSurfaceAssumptions (M.surface baseline candidate) := by
  simpa [OriginalHODLConcreteExtractionSemantics.surface] using
    (M.pair_obligations hpair).toSurfaceAssumptions

/-- A concrete extraction model forgets its original-HODL-specific local packet
format and plugs directly into the generic extracted-surface AMM interface. -/
def OriginalHODLConcreteExtractionSemantics.toExtractedRawAMMSemanticsModel
    {RawAMM : Type} (M : OriginalHODLConcreteExtractionSemantics RawAMM) :
    ExtractedRawAMMSemanticsModel RawAMM where
  SameBenchmarkAnalytic := M.AdmissiblePair
  coeffs := M.coeffs
  surface_assumptions := by
    intro baseline candidate hpair
    exact M.surface_assumptions hpair

/-- Pairwise concrete extraction consequence: for every admissible concrete
pair, the extracted slippage and curvature functions cannot both be globally
no-worse. -/
theorem OriginalHODLConcreteExtractionSemantics.not_simultaneous_global_no_worse
    {RawAMM : Type} (M : OriginalHODLConcreteExtractionSemantics RawAMM)
    {baseline candidate : RawAMM}
    (hpair : M.AdmissiblePair baseline candidate) :
    ¬ (GloballyNoWorse (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
        GloballyNoWorse (M.coeffs.curvature candidate) (M.coeffs.curvature baseline)) :=
  (M.pair_obligations hpair).not_simultaneous_global_no_worse

/-- Pairwise concrete extraction strict-slippage consequence. -/
theorem OriginalHODLConcreteExtractionSemantics.not_simultaneous_with_strict
    {RawAMM : Type} (M : OriginalHODLConcreteExtractionSemantics RawAMM)
    {baseline candidate : RawAMM}
    (hpair : M.AdmissiblePair baseline candidate) :
    ¬ (GloballyNoWorse (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
        StrictlyBetterSomewhere (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
        GloballyNoWorse (M.coeffs.curvature candidate) (M.coeffs.curvature baseline)) :=
  (M.pair_obligations hpair).not_simultaneous_with_strict

/-- Surface-level pairwise concrete extraction consequence. -/
theorem OriginalHODLConcreteExtractionSemantics.surface_not_simultaneous_global_no_worse
    {RawAMM : Type} (M : OriginalHODLConcreteExtractionSemantics RawAMM)
    {baseline candidate : RawAMM}
    (hpair : M.AdmissiblePair baseline candidate) :
    ¬ (GloballyNoWorse (M.surface baseline candidate).candidateSlippage
          (M.surface baseline candidate).baselineSlippage ∧
        GloballyNoWorse (M.surface baseline candidate).candidateCurvature
          (M.surface baseline candidate).baselineCurvature) := by
  simpa [OriginalHODLConcreteExtractionSemantics.surface,
    RawAMMCoefficientExtractors.surface] using
    M.not_simultaneous_global_no_worse hpair

/-- Surface-level pairwise concrete extraction consequence, strict-slippage
form.  This is the direct concrete-model version of the generic same-benchmark
surface obstruction. -/
theorem OriginalHODLConcreteExtractionSemantics.surface_not_simultaneous_global_no_worse_with_strict
    {RawAMM : Type} (M : OriginalHODLConcreteExtractionSemantics RawAMM)
    {baseline candidate : RawAMM}
    (hpair : M.AdmissiblePair baseline candidate) :
    ¬ (GloballyNoWorse (M.surface baseline candidate).candidateSlippage
          (M.surface baseline candidate).baselineSlippage ∧
        StrictlyBetterSomewhere (M.surface baseline candidate).candidateSlippage
          (M.surface baseline candidate).baselineSlippage ∧
        GloballyNoWorse (M.surface baseline candidate).candidateCurvature
          (M.surface baseline candidate).baselineCurvature) := by
  simpa [OriginalHODLConcreteExtractionSemantics.surface,
    RawAMMCoefficientExtractors.surface] using
    M.not_simultaneous_with_strict hpair

/-- Concrete extraction interface, global existential form: once every
admissible pair supplies the local original-HODL expansion certificate, no
admissible pair can be globally no-worse in both extracted coordinates. -/
theorem OriginalHODLConcreteExtractionSemantics.no_admissible_simultaneous_global_no_worse
    {RawAMM : Type} (M : OriginalHODLConcreteExtractionSemantics RawAMM) :
    ¬ ∃ (baseline candidate : RawAMM),
        M.AdmissiblePair baseline candidate ∧
          GloballyNoWorse (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
          GloballyNoWorse (M.coeffs.curvature candidate) (M.coeffs.curvature baseline) := by
  simpa [OriginalHODLConcreteExtractionSemantics.toRawExpansionSemantics] using
    M.toRawExpansionSemantics.no_admissible_simultaneous_global_no_worse

/-- Concrete extraction interface, strict-slippage form. -/
theorem OriginalHODLConcreteExtractionSemantics.no_admissible_simultaneous_with_strict
    {RawAMM : Type} (M : OriginalHODLConcreteExtractionSemantics RawAMM) :
    ¬ ∃ (baseline candidate : RawAMM),
        M.AdmissiblePair baseline candidate ∧
          GloballyNoWorse (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
          StrictlyBetterSomewhere (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
          GloballyNoWorse (M.coeffs.curvature candidate) (M.coeffs.curvature baseline) := by
  simpa [OriginalHODLConcreteExtractionSemantics.toRawExpansionSemantics] using
    M.toRawExpansionSemantics.no_admissible_simultaneous_with_strict

/-!
## Necessity boundary

The next structure intentionally omits the expansion-construction obligation.
It records the weaker assumption set that is tempting but insufficient:
admissible raw pairs plus deterministic coefficient extractors.
-/

/-- Weak original-HODL raw semantics: admissibility plus coefficient
extractors, with no obligation that raw pairs realize the original-HODL
first-even expansion payload. -/
structure WeakOriginalHODLRawSemantics (RawAMM : Type) where
  AdmissiblePair : RawAMM → RawAMM → Prop
  coeffs : RawAMMCoefficientExtractors RawAMM

/-- The extracted coefficient surface for a weak raw semantics model. -/
def WeakOriginalHODLRawSemantics.surface
    {RawAMM : Type} (M : WeakOriginalHODLRawSemantics RawAMM)
    (baseline candidate : RawAMM) : AMMCoefficientSurface :=
  M.coeffs.surface baseline candidate

/-- Coefficients-only raw semantics is too weak: a legal two-object model can
make the candidate strictly better in both extracted coordinates everywhere.
This countermodel isolates the exact missing assumption for a universal theorem:
construction of `OriginalHODLFirstEvenExpansion`. -/
theorem weak_raw_semantics_simultaneous_dominance_possible :
    ∃ (M : WeakOriginalHODLRawSemantics Bool) (baseline candidate : Bool),
      M.AdmissiblePair baseline candidate ∧
        GloballyNoWorse (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
        StrictlyBetterSomewhere
          (M.coeffs.slippage candidate) (M.coeffs.slippage baseline) ∧
        GloballyNoWorse (M.coeffs.curvature candidate) (M.coeffs.curvature baseline) ∧
        StrictlyBetterSomewhere
          (M.coeffs.curvature candidate) (M.coeffs.curvature baseline) := by
  exact ⟨{
    AdmissiblePair := fun _ _ => True
    coeffs := {
      slippage := fun A _ => if A then (1 / 2 : ℝ) else 1
      curvature := fun A _ => if A then (1 / 2 : ℝ) else 1
    }
  }, false, true, by
    constructor
    · trivial
    · constructor
      · intro d
        norm_num
      · constructor
        · exact ⟨0, by norm_num⟩
        · constructor
          · intro d
            norm_num
          · exact ⟨0, by norm_num⟩⟩

/-- Necessity boundary: raw coefficient extractors alone do not imply a
no-free-lunch theorem.  Without an expansion/frontier obligation, a two-object
raw universe can assign the candidate lower slippage and lower curvature
everywhere by fiat. -/
theorem raw_coefficients_simultaneous_dominance_possible_without_expansion :
    ∃ (baseline candidate : Bool) (coeffs : RawAMMCoefficientExtractors Bool),
      GloballyNoWorse (coeffs.slippage candidate) (coeffs.slippage baseline) ∧
        StrictlyBetterSomewhere (coeffs.slippage candidate) (coeffs.slippage baseline) ∧
        GloballyNoWorse (coeffs.curvature candidate) (coeffs.curvature baseline) ∧
        StrictlyBetterSomewhere (coeffs.curvature candidate) (coeffs.curvature baseline) := by
  rcases weak_raw_semantics_simultaneous_dominance_possible with
    ⟨M, baseline, candidate, _hpair, hslip_no_worse, hslip_strict,
      hcurv_no_worse, hcurv_strict⟩
  exact ⟨baseline, candidate, M.coeffs, hslip_no_worse, hslip_strict,
    hcurv_no_worse, hcurv_strict⟩

end OriginalHODLBridge

end

end LocalJetFrontier
end Impossibility
end TauSwap
