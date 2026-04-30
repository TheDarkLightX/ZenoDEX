import Mathlib.Tactic

/-!
# AMM local-jet frontier

This file isolates the algebraic core suggested by the local AMM impossibility
proof.  The existing `ImpossibilityTheorem` proves the statement for the power
family

`K(x,y; alpha) = x * y * (x + y)^alpha`.

In local log coordinates, a broader symmetric homogeneous invariant has two
balance-point parameters:

* `n`: homogeneous degree,
* `a`: second derivative of the even imbalance potential at balance.

Under the local smoothness assumptions that justify the Taylor expansion, the
coefficients have the algebraic form

`localSlippage n a = (n - a) / n`

and

`localILCoeff n a = n / (8 * (n - a))`.

The product identity below is deliberately small: it is the checker-backed
algebraic frontier that a later calculus proof can connect to a formal smooth
CFMM statement.
-/

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

/-- Local inverse-depth / slippage coefficient from the local log-price slope. -/
def localSlippage (n a : ℝ) : ℝ :=
  (n - a) / n

/-- Positive quadratic coefficient of impermanent loss near balance. -/
def localILCoeff (n a : ℝ) : ℝ :=
  n / (8 * (n - a))

/-- Balance-point derivative of log marginal price with respect to log imbalance. -/
def localLogPriceSlope (n a : ℝ) : ℝ :=
  2 * (n - a) / n

/-- Quadratic coefficient of IL as a function of log price.  It is negative;
`localILCoeff` is its positive loss-curvature magnitude. -/
def localILLogPriceQuadraticCoeff (n a : ℝ) : ℝ :=
  -n / (8 * (n - a))

/-- The local AMM no-free-lunch invariant: slippage-depth and IL curvature
multiply to the normalized constant `1/8`. -/
def FrontierInvariant (slippage ilCoeff : ℝ) : Prop :=
  slippage * ilCoeff = (1 / 8 : ℝ)

/-- On the frontier, a positive slippage coefficient determines the IL
coefficient uniquely. -/
lemma frontier_ilCoeff_eq {slippage ilCoeff : ℝ}
    (hfrontier : FrontierInvariant slippage ilCoeff) (hslip : 0 < slippage) :
    ilCoeff = (1 / 8 : ℝ) / slippage := by
  unfold FrontierInvariant at hfrontier
  calc
    ilCoeff = (slippage * ilCoeff) / slippage := by
      field_simp [ne_of_gt hslip]
    _ = (1 / 8 : ℝ) / slippage := by rw [hfrontier]

/-- The abstract no-free-lunch law: for positive coefficient pairs on the same
frontier, lowering slippage forces higher IL curvature. -/
theorem frontier_no_simultaneous_improvement {slippage₀ ilCoeff₀ slippage₁ ilCoeff₁ : ℝ}
    (hfrontier₀ : FrontierInvariant slippage₀ ilCoeff₀)
    (hfrontier₁ : FrontierInvariant slippage₁ ilCoeff₁)
    (hslip₀ : 0 < slippage₀) (hslip₁ : 0 < slippage₁)
    (hbetter_slippage : slippage₁ < slippage₀) :
    ilCoeff₀ < ilCoeff₁ := by
  rw [frontier_ilCoeff_eq hfrontier₀ hslip₀, frontier_ilCoeff_eq hfrontier₁ hslip₁]
  exact div_lt_div_of_pos_left (by positivity : (0 : ℝ) < 1 / 8) hslip₁ hbetter_slippage

/-- Dual abstract no-free-lunch law: for positive coefficient pairs on the same
frontier, lowering IL curvature forces higher slippage. -/
theorem frontier_slippage_worse_at_strict_il_gain {slippage₀ ilCoeff₀ slippage₁ ilCoeff₁ : ℝ}
    (hfrontier₀ : FrontierInvariant slippage₀ ilCoeff₀)
    (hfrontier₁ : FrontierInvariant slippage₁ ilCoeff₁)
    (hslip₀ : 0 < slippage₀) (hslip₁ : 0 < slippage₁)
    (hbetter_il : ilCoeff₁ < ilCoeff₀) :
    slippage₀ < slippage₁ := by
  by_contra hnot
  rcases lt_or_eq_of_le (le_of_not_gt hnot) with hbetter_slippage | heq
  · have hcurvature_worse : ilCoeff₀ < ilCoeff₁ :=
      frontier_no_simultaneous_improvement
        hfrontier₀ hfrontier₁ hslip₀ hslip₁ hbetter_slippage
    exact not_lt_of_ge (le_of_lt hbetter_il) hcurvature_worse
  · rw [frontier_ilCoeff_eq hfrontier₀ hslip₀,
      frontier_ilCoeff_eq hfrontier₁ hslip₁, heq] at hbetter_il
    exact (lt_irrefl _ hbetter_il)

/-- A pointwise frontier over an arbitrary price/index domain. -/
def PointwiseFrontier {ι : Type*} (slippage ilCoeff : ι → ℝ) : Prop :=
  ∀ q, FrontierInvariant (slippage q) (ilCoeff q)

/-- Function-level dominance order for "no worse everywhere."  For slippage,
lower is better; for IL curvature, lower is also better. -/
def GloballyNoWorse {ι : Type*} (candidate baseline : ι → ℝ) : Prop :=
  ∀ q, candidate q ≤ baseline q

/-- Strict improvement at at least one price/index. -/
def StrictlyBetterSomewhere {ι : Type*} (candidate baseline : ι → ℝ) : Prop :=
  ∃ q, candidate q < baseline q

/-- A benchmark-coherent global profile: the two coefficient functions are
assumed to come from the same local frontier packet at each price/index.  This
is the exact assumption needed to lift the local theorem to a function-level
no-dominance theorem. -/
structure GlobalFrontierProfile (ι : Type*) where
  slippage : ι → ℝ
  ilCoeff : ι → ℝ
  frontier : PointwiseFrontier slippage ilCoeff
  slippage_pos : ∀ q, 0 < slippage q

/-- Pointwise version of the no-free-lunch law: at any price/index where one
frontier profile has strictly lower slippage, it has strictly higher IL
curvature. -/
theorem global_frontier_curvature_worse_at_strict_slippage_gain {ι : Type*}
    (baseline candidate : GlobalFrontierProfile ι) {q : ι}
    (hbetter_slippage : candidate.slippage q < baseline.slippage q) :
    baseline.ilCoeff q < candidate.ilCoeff q :=
  frontier_no_simultaneous_improvement
    (baseline.frontier q)
    (candidate.frontier q)
    (baseline.slippage_pos q)
    (candidate.slippage_pos q)
    hbetter_slippage

/-- Pointwise dual: at any price/index where one frontier profile has strictly
lower IL curvature, it has strictly higher slippage. -/
theorem global_frontier_slippage_worse_at_strict_il_gain {ι : Type*}
    (baseline candidate : GlobalFrontierProfile ι) {q : ι}
    (hbetter_il : candidate.ilCoeff q < baseline.ilCoeff q) :
    baseline.slippage q < candidate.slippage q :=
  frontier_slippage_worse_at_strict_il_gain
    (baseline.frontier q)
    (candidate.frontier q)
    (baseline.slippage_pos q)
    (candidate.slippage_pos q)
    hbetter_il

/-- Global dominance impossibility under a pointwise frontier: a candidate cannot
be no worse in slippage everywhere, strictly better in slippage somewhere, and
also no worse in IL curvature everywhere. -/
theorem global_frontier_no_simultaneous_dominance {ι : Type*}
    (baseline candidate : GlobalFrontierProfile ι)
    (_hslippage_no_worse : GloballyNoWorse candidate.slippage baseline.slippage)
    (hslippage_strict : StrictlyBetterSomewhere candidate.slippage baseline.slippage) :
    ¬ GloballyNoWorse candidate.ilCoeff baseline.ilCoeff := by
  intro hil_no_worse
  let q : ι := Classical.choose hslippage_strict
  have hbetter_slippage : candidate.slippage q < baseline.slippage q :=
    Classical.choose_spec hslippage_strict
  have hcurvature_worse : baseline.ilCoeff q < candidate.ilCoeff q :=
    global_frontier_curvature_worse_at_strict_slippage_gain
      baseline candidate hbetter_slippage
  exact not_lt_of_ge (hil_no_worse q) hcurvature_worse

/-- Dual global dominance impossibility under a pointwise frontier: a candidate
cannot be no worse in IL curvature everywhere, strictly better in IL curvature
somewhere, and also no worse in slippage everywhere. -/
theorem global_frontier_no_simultaneous_dominance_from_il_gain {ι : Type*}
    (baseline candidate : GlobalFrontierProfile ι)
    (_hil_no_worse : GloballyNoWorse candidate.ilCoeff baseline.ilCoeff)
    (hil_strict : StrictlyBetterSomewhere candidate.ilCoeff baseline.ilCoeff) :
    ¬ GloballyNoWorse candidate.slippage baseline.slippage := by
  intro hslippage_no_worse
  let q : ι := Classical.choose hil_strict
  have hbetter_il : candidate.ilCoeff q < baseline.ilCoeff q :=
    Classical.choose_spec hil_strict
  have hslippage_worse : baseline.slippage q < candidate.slippage q :=
    global_frontier_slippage_worse_at_strict_il_gain
      baseline candidate hbetter_il
  exact not_lt_of_ge (hslippage_no_worse q) hslippage_worse

/-- The frontier assumption is necessary.  Without it, simultaneous global
improvement in the two coefficient functions is consistent even on a one-point
domain.  This does not claim such functions come from an AMM; it rules out a
purely order-theoretic global impossibility theorem with no frontier/budget
invariant. -/
theorem simultaneous_global_dominance_possible_without_frontier :
    ∃ (baselineSlippage candidateSlippage baselineILCoeff candidateILCoeff : PUnit → ℝ),
      GloballyNoWorse candidateSlippage baselineSlippage ∧
        StrictlyBetterSomewhere candidateSlippage baselineSlippage ∧
        GloballyNoWorse candidateILCoeff baselineILCoeff ∧
        StrictlyBetterSomewhere candidateILCoeff baselineILCoeff ∧
        ¬ PointwiseFrontier baselineSlippage baselineILCoeff ∧
        ¬ PointwiseFrontier candidateSlippage candidateILCoeff := by
  refine ⟨fun _ => (1 : ℝ), fun _ => (1 / 2 : ℝ),
    fun _ => (1 : ℝ), fun _ => (1 / 2 : ℝ), ?_⟩
  norm_num [GloballyNoWorse, StrictlyBetterSomewhere, PointwiseFrontier, FrontierInvariant]

/-- CPMM original-HODL global curvature product after writing
`z = sech(q/2)`.

For the CPMM, the global original-HODL IL function is
`IL(q) = sech(q/2) - 1`; the associated pointwise product is
`(1/8) * z * (2*z^2 - 1)`.  This is not the local frontier constant away from
balance. -/
def cpmmOriginalHodlGlobalProductFromSech (z : ℝ) : ℝ :=
  (1 / 8 : ℝ) * z * (2 * z ^ 2 - 1)

/-- The naive pointwise global frontier identity is false for the CPMM under the
original-HODL curvature metric.

At `q = 2*log 2`, one has `sech(q/2)=4/5`, so the product is `7/250`, not
`1/8`.  This theorem records the algebraic witness; the hyperbolic evaluation is
kept in the paper/SymPy note to avoid importing unnecessary transcendental
machinery into the local frontier file. -/
theorem cpmm_originalHodl_global_product_witness :
    cpmmOriginalHodlGlobalProductFromSech (4 / 5) = (7 / 250 : ℝ) ∧
      cpmmOriginalHodlGlobalProductFromSech (4 / 5) ≠ (1 / 8 : ℝ) := by
  constructor <;> norm_num [cpmmOriginalHodlGlobalProductFromSech]

/-- The slippage coefficient is half the local log-price slope, because
`log(y/x)` has balance-point slope `2` in the imbalance coordinate. -/
lemma localSlippage_eq_half_logPriceSlope {n a : ℝ} :
    localSlippage n a = localLogPriceSlope n a / 2 := by
  unfold localSlippage localLogPriceSlope
  ring_nf

/-- The positive IL coefficient is the negation of the log-price quadratic term. -/
lemma localILCoeff_eq_neg_quadraticCoeff {n a : ℝ} :
    localILCoeff n a = -localILLogPriceQuadraticCoeff n a := by
  unfold localILCoeff localILLogPriceQuadraticCoeff
  ring_nf

/-- Minimal local data of a smooth symmetric homogeneous AMM invariant at balance.

`degree` is the homogeneous degree `n`.  `curvature` is the second derivative
`a = phi''(0)` of the even imbalance potential in log coordinates.  The
condition `curvature < degree` is the local stability condition that keeps the
price slope and denominators positive. -/
structure SymmetricHomogeneousJet where
  degree : ℝ
  curvature : ℝ
  degree_pos : 0 < degree
  curvature_lt_degree : curvature < degree

/-- Slippage coefficient attached to a local symmetric homogeneous jet. -/
def jetSlippage (J : SymmetricHomogeneousJet) : ℝ :=
  localSlippage J.degree J.curvature

/-- IL curvature coefficient attached to a local symmetric homogeneous jet. -/
def jetILCoeff (J : SymmetricHomogeneousJet) : ℝ :=
  localILCoeff J.degree J.curvature

/-- Local log-price slope attached to a symmetric homogeneous jet. -/
def jetLogPriceSlope (J : SymmetricHomogeneousJet) : ℝ :=
  localLogPriceSlope J.degree J.curvature

/-- Local log-price model in the imbalance coordinate. -/
def jetLogPriceModel (J : SymmetricHomogeneousJet) (d : ℝ) : ℝ :=
  jetLogPriceSlope J * d

/-- Local quadratic IL model as a function of log price. -/
def jetILLogPriceQuadraticModel (J : SymmetricHomogeneousJet) (q : ℝ) : ℝ :=
  localILLogPriceQuadraticCoeff J.degree J.curvature * q ^ 2

/-- First derivative model of the local quadratic IL approximation. -/
def jetILLogPriceQuadraticModelDeriv (J : SymmetricHomogeneousJet) (q : ℝ) : ℝ :=
  2 * localILLogPriceQuadraticCoeff J.degree J.curvature * q

/-- Quadratic imbalance potential `phi(d) = a*d^2/2` from the local normal form. -/
def imbalancePotentialQuadraticModel (J : SymmetricHomogeneousJet) (d : ℝ) : ℝ :=
  (J.curvature / 2) * d ^ 2

/-- First derivative model of the quadratic imbalance potential. -/
def imbalancePotentialQuadraticModelDeriv (J : SymmetricHomogeneousJet) (d : ℝ) : ℝ :=
  J.curvature * d

/-- Local quadratic normal form of the log-invariant: `L(m,d)=n*m+a*d^2/2`. -/
def localLogInvariantQuadraticModel (J : SymmetricHomogeneousJet) (m d : ℝ) : ℝ :=
  J.degree * m + imbalancePotentialQuadraticModel J d

/-- Log-price slope obtained from the local normal form:
`2 - 2*phi''(0)/n`. -/
def normalFormLogPriceSlope (J : SymmetricHomogeneousJet) : ℝ :=
  2 - 2 * (deriv (imbalancePotentialQuadraticModelDeriv J) 0) / J.degree

/-- Log-price linearization obtained from the local normal form. -/
def normalFormLogPriceModel (J : SymmetricHomogeneousJet) (d : ℝ) : ℝ :=
  normalFormLogPriceSlope J * d

/-- Exact smooth normal-form log marginal price from the imbalance derivative.

For a local log-invariant `L(m,d)=n*m+phi(d)`, the marginal price ratio in log
coordinates has the form

`2*d + log(n - phi'(d)) - log(n + phi'(d))`.

The derivative theorem below is the first real smooth-to-jet bridge: it derives
the local log-price slope from the normal-form formula and the curvature datum
`phi''(0)`. -/
def smoothNormalFormLogPriceModel
    (J : SymmetricHomogeneousJet) (imbalancePotentialDeriv : ℝ → ℝ) (d : ℝ) : ℝ :=
  2 * d + Real.log (J.degree - imbalancePotentialDeriv d) -
    Real.log (J.degree + imbalancePotentialDeriv d)

/-- Derivative of the imbalance potential quadratic model. -/
lemma hasDerivAt_imbalancePotentialQuadraticModel (J : SymmetricHomogeneousJet) (d : ℝ) :
    HasDerivAt (imbalancePotentialQuadraticModel J)
      (imbalancePotentialQuadraticModelDeriv J d) d := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * d) d := by
    simpa [pow_two] using (hasDerivAt_id d).fun_pow 2
  unfold imbalancePotentialQuadraticModel imbalancePotentialQuadraticModelDeriv
  convert hsq.const_mul (J.curvature / 2) using 1
  ring

/-- The imbalance potential has zero first derivative at balance. -/
lemma deriv_imbalancePotentialQuadraticModel_zero (J : SymmetricHomogeneousJet) :
    deriv (imbalancePotentialQuadraticModel J) 0 = 0 := by
  rw [(hasDerivAt_imbalancePotentialQuadraticModel J 0).deriv]
  simp [imbalancePotentialQuadraticModelDeriv]

/-- The derivative model of the imbalance potential has derivative equal to curvature. -/
lemma hasDerivAt_imbalancePotentialQuadraticModelDeriv
    (J : SymmetricHomogeneousJet) (d : ℝ) :
    HasDerivAt (imbalancePotentialQuadraticModelDeriv J) J.curvature d := by
  unfold imbalancePotentialQuadraticModelDeriv
  simpa using (hasDerivAt_id d).const_mul J.curvature

/-- The quadratic potential's second-order datum is exactly the jet curvature. -/
lemma deriv_imbalancePotentialQuadraticModelDeriv_zero (J : SymmetricHomogeneousJet) :
    deriv (imbalancePotentialQuadraticModelDeriv J) 0 = J.curvature :=
  (hasDerivAt_imbalancePotentialQuadraticModelDeriv J 0).deriv

/-- The local log-invariant normal form has mean derivative equal to homogeneous degree. -/
lemma hasDerivAt_localLogInvariantQuadraticModel_mean
    (J : SymmetricHomogeneousJet) (m d : ℝ) :
    HasDerivAt (fun t : ℝ => localLogInvariantQuadraticModel J t d) J.degree m := by
  unfold localLogInvariantQuadraticModel
  simpa using (hasDerivAt_id m).const_mul J.degree

/-- The local normal-form log-price slope agrees with the jet log-price slope. -/
lemma normalFormLogPriceSlope_eq_jetLogPriceSlope (J : SymmetricHomogeneousJet) :
    normalFormLogPriceSlope J = jetLogPriceSlope J := by
  unfold normalFormLogPriceSlope jetLogPriceSlope localLogPriceSlope
  rw [deriv_imbalancePotentialQuadraticModelDeriv_zero]
  field_simp [ne_of_gt J.degree_pos]

/-- The normal-form log-price model has the same derivative as the jet model. -/
lemma hasDerivAt_normalFormLogPriceModel (J : SymmetricHomogeneousJet) (d : ℝ) :
    HasDerivAt (normalFormLogPriceModel J) (jetLogPriceSlope J) d := by
  unfold normalFormLogPriceModel
  rw [normalFormLogPriceSlope_eq_jetLogPriceSlope]
  simpa using (hasDerivAt_id d).const_mul (jetLogPriceSlope J)

/-- Balance-point derivative of the normal-form log-price model. -/
lemma deriv_normalFormLogPriceModel_zero (J : SymmetricHomogeneousJet) :
    deriv (normalFormLogPriceModel J) 0 = jetLogPriceSlope J :=
  (hasDerivAt_normalFormLogPriceModel J 0).deriv

/-- The smooth normal-form log-price formula has the jet slope at balance. -/
lemma hasDerivAt_smoothNormalFormLogPriceModel
    (J : SymmetricHomogeneousJet) {imbalancePotentialDeriv : ℝ → ℝ}
    (hzero : imbalancePotentialDeriv 0 = 0)
    (hderiv : HasDerivAt imbalancePotentialDeriv J.curvature 0) :
    HasDerivAt (smoothNormalFormLogPriceModel J imbalancePotentialDeriv)
      (2 - 2 * (deriv imbalancePotentialDeriv 0) / J.degree) 0 := by
  have hlinear : HasDerivAt (fun d : ℝ => 2 * d) 2 0 := by
    simpa using (hasDerivAt_id 0).const_mul (2 : ℝ)
  have hminus_arg :
      HasDerivAt (fun d : ℝ => J.degree - imbalancePotentialDeriv d)
        (-J.curvature) 0 := by
    simpa using (hasDerivAt_const 0 J.degree).sub hderiv
  have hminus_ne : J.degree - imbalancePotentialDeriv 0 ≠ 0 := by
    simpa [hzero] using ne_of_gt J.degree_pos
  have hminus_log :
      HasDerivAt (fun d : ℝ => Real.log (J.degree - imbalancePotentialDeriv d))
        (-J.curvature / J.degree) 0 := by
    simpa [hzero] using hminus_arg.log hminus_ne
  have hplus_arg :
      HasDerivAt (fun d : ℝ => J.degree + imbalancePotentialDeriv d)
        J.curvature 0 := by
    simpa using hderiv.const_add J.degree
  have hplus_ne : J.degree + imbalancePotentialDeriv 0 ≠ 0 := by
    simpa [hzero] using ne_of_gt J.degree_pos
  have hplus_log :
      HasDerivAt (fun d : ℝ => Real.log (J.degree + imbalancePotentialDeriv d))
        (J.curvature / J.degree) 0 := by
    simpa [hzero] using hplus_arg.log hplus_ne
  unfold smoothNormalFormLogPriceModel
  convert (hlinear.add hminus_log).sub hplus_log using 1
  rw [hderiv.deriv]
  field_simp [ne_of_gt J.degree_pos]
  ring

/-- The smooth normal-form log-price formula has the expected derivative at any
imbalance point where the two marginal-denominator terms are nonzero.  This is
the price-coordinate invariant needed for a global interval theorem. -/
lemma hasDerivAt_smoothNormalFormLogPriceModel_at
    (J : SymmetricHomogeneousJet) {imbalancePotentialDeriv : ℝ → ℝ}
    {d curvatureAt derivValue : ℝ}
    (hvalue : imbalancePotentialDeriv d = curvatureAt)
    (hderiv : HasDerivAt imbalancePotentialDeriv derivValue d)
    (hminus : J.degree - curvatureAt ≠ 0)
    (hplus : J.degree + curvatureAt ≠ 0) :
    HasDerivAt (smoothNormalFormLogPriceModel J imbalancePotentialDeriv)
      (2 - derivValue / (J.degree - curvatureAt) -
        derivValue / (J.degree + curvatureAt)) d := by
  have hlinear : HasDerivAt (fun t : ℝ => 2 * t) 2 d := by
    simpa using (hasDerivAt_id d).const_mul (2 : ℝ)
  have hminus_arg :
      HasDerivAt (fun t : ℝ => J.degree - imbalancePotentialDeriv t)
        (-derivValue) d := by
    simpa using (hasDerivAt_const d J.degree).sub hderiv
  have hminus_log :
      HasDerivAt (fun t : ℝ => Real.log (J.degree - imbalancePotentialDeriv t))
        (-derivValue / (J.degree - curvatureAt)) d := by
    simpa [hvalue] using hminus_arg.log (by simpa [hvalue] using hminus)
  have hplus_arg :
      HasDerivAt (fun t : ℝ => J.degree + imbalancePotentialDeriv t)
        derivValue d := by
    simpa using hderiv.const_add J.degree
  have hplus_log :
      HasDerivAt (fun t : ℝ => Real.log (J.degree + imbalancePotentialDeriv t))
        (derivValue / (J.degree + curvatureAt)) d := by
    simpa [hvalue] using hplus_arg.log (by simpa [hvalue] using hplus)
  unfold smoothNormalFormLogPriceModel
  convert (hlinear.add hminus_log).sub hplus_log using 1
  ring

/-- Local log-price slope is positive under the jet stability condition. -/
lemma jetLogPriceSlope_pos (J : SymmetricHomogeneousJet) : 0 < jetLogPriceSlope J := by
  unfold jetLogPriceSlope localLogPriceSlope
  have hgap : 0 < J.degree - J.curvature := sub_pos.mpr J.curvature_lt_degree
  exact div_pos (mul_pos (by positivity) hgap) J.degree_pos

/-- Jet slippage is half the local log-price slope. -/
lemma jetSlippage_eq_half_logPriceSlope (J : SymmetricHomogeneousJet) :
    jetSlippage J = jetLogPriceSlope J / 2 := by
  simpa [jetSlippage, jetLogPriceSlope] using
    (localSlippage_eq_half_logPriceSlope (n := J.degree) (a := J.curvature))

/-- Jet slippage is positive exactly because the local price slope is positive. -/
lemma jetSlippage_pos (J : SymmetricHomogeneousJet) : 0 < jetSlippage J := by
  rw [jetSlippage_eq_half_logPriceSlope]
  exact div_pos (jetLogPriceSlope_pos J) (by positivity)

/-- Jet IL curvature coefficient is positive under the same stability gap. -/
lemma jetILCoeff_pos (J : SymmetricHomogeneousJet) : 0 < jetILCoeff J := by
  unfold jetILCoeff localILCoeff
  have hgap : 0 < J.degree - J.curvature := sub_pos.mpr J.curvature_lt_degree
  exact div_pos J.degree_pos (mul_pos (by positivity) hgap)

/-- The local log-price model has derivative equal to the jet log-price slope. -/
lemma hasDerivAt_jetLogPriceModel (J : SymmetricHomogeneousJet) (d : ℝ) :
    HasDerivAt (jetLogPriceModel J) (jetLogPriceSlope J) d := by
  unfold jetLogPriceModel
  simpa using (hasDerivAt_id d).const_mul (jetLogPriceSlope J)

/-- Balance-point derivative of the local log-price model. -/
lemma deriv_jetLogPriceModel_zero (J : SymmetricHomogeneousJet) :
    deriv (jetLogPriceModel J) 0 = jetLogPriceSlope J :=
  (hasDerivAt_jetLogPriceModel J 0).deriv

/-- The local quadratic IL model differentiates to its explicit first-derivative model. -/
lemma hasDerivAt_jetILLogPriceQuadraticModel (J : SymmetricHomogeneousJet) (q : ℝ) :
    HasDerivAt (jetILLogPriceQuadraticModel J)
      (jetILLogPriceQuadraticModelDeriv J q) q := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * q) q := by
    simpa [pow_two] using (hasDerivAt_id q).fun_pow 2
  unfold jetILLogPriceQuadraticModel jetILLogPriceQuadraticModelDeriv
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    hsq.const_mul (localILLogPriceQuadraticCoeff J.degree J.curvature)

/-- First derivative of the local quadratic IL model vanishes at balance. -/
lemma deriv_jetILLogPriceQuadraticModel_zero (J : SymmetricHomogeneousJet) :
    deriv (jetILLogPriceQuadraticModel J) 0 = 0 := by
  rw [(hasDerivAt_jetILLogPriceQuadraticModel J 0).deriv]
  simp [jetILLogPriceQuadraticModelDeriv]

/-- The explicit derivative model has constant derivative equal to twice the
quadratic coefficient. -/
lemma hasDerivAt_jetILLogPriceQuadraticModelDeriv (J : SymmetricHomogeneousJet) (q : ℝ) :
    HasDerivAt (jetILLogPriceQuadraticModelDeriv J)
      (2 * localILLogPriceQuadraticCoeff J.degree J.curvature) q := by
  unfold jetILLogPriceQuadraticModelDeriv
  simpa using
    (hasDerivAt_id q).const_mul (2 * localILLogPriceQuadraticCoeff J.degree J.curvature)

/-- Balance-point derivative of the explicit IL derivative model. -/
lemma deriv_jetILLogPriceQuadraticModelDeriv_zero (J : SymmetricHomogeneousJet) :
    deriv (jetILLogPriceQuadraticModelDeriv J) 0 =
      2 * localILLogPriceQuadraticCoeff J.degree J.curvature :=
  (hasDerivAt_jetILLogPriceQuadraticModelDeriv J 0).deriv

/-- The positive IL coefficient is recovered from the local quadratic model's curvature. -/
lemma jetILCoeff_eq_model_curvature (J : SymmetricHomogeneousJet) :
    -(deriv (jetILLogPriceQuadraticModelDeriv J) 0) / 2 = jetILCoeff J := by
  rw [deriv_jetILLogPriceQuadraticModelDeriv_zero]
  unfold jetILCoeff
  rw [localILCoeff_eq_neg_quadraticCoeff]
  ring

/-- A local second-order CFMM witness supplies the concrete functions and
derivative facts needed to instantiate the local-jet frontier.

This is the proof boundary a real smooth CFMM must cross: once its log-price
function and IL function have these balance-point derivative witnesses, the
frontier follows from the jet theorem. -/
structure LocalSecondOrderCFMMWitness where
  jet : SymmetricHomogeneousJet
  logPrice : ℝ → ℝ
  ilLogPrice : ℝ → ℝ
  ilLogPriceDeriv : ℝ → ℝ
  logPrice_hasDerivAt_zero : HasDerivAt logPrice (jetLogPriceSlope jet) 0
  ilLogPrice_hasDerivAt_zero : HasDerivAt ilLogPrice (ilLogPriceDeriv 0) 0
  ilLogPriceDeriv_zero : ilLogPriceDeriv 0 = 0
  ilLogPriceDeriv_hasDerivAt_zero :
    HasDerivAt ilLogPriceDeriv
      (2 * localILLogPriceQuadraticCoeff jet.degree jet.curvature) 0

/-- Calculus-facing derivative packet for a smooth local normal form.

The packet separates the semantic smooth-CFMM obligations from the algebraic
frontier proof.  A future full smooth theorem must construct this packet from
an actual invariant.  Once the packet exists, the `1/8` frontier follows from
the local-jet theorem without redoing the AMM algebra. -/
structure LocalNormalFormDerivativePacket where
  jet : SymmetricHomogeneousJet
  imbalancePotentialDeriv : ℝ → ℝ
  logPrice : ℝ → ℝ
  ilLogPrice : ℝ → ℝ
  ilLogPriceDeriv : ℝ → ℝ
  imbalancePotentialDeriv_hasDerivAt_zero :
    HasDerivAt imbalancePotentialDeriv jet.curvature 0
  logPrice_hasDerivAt_zero :
    HasDerivAt logPrice
      (2 - 2 * (deriv imbalancePotentialDeriv 0) / jet.degree) 0
  ilLogPrice_hasDerivAt_zero : HasDerivAt ilLogPrice (ilLogPriceDeriv 0) 0
  ilLogPriceDeriv_zero : ilLogPriceDeriv 0 = 0
  ilLogPriceDeriv_hasDerivAt_zero :
    HasDerivAt ilLogPriceDeriv
      (2 * localILLogPriceQuadraticCoeff jet.degree jet.curvature) 0

/-- Smooth local normal-form data with the exact marginal-price formula.

This moves one step closer to the broad smooth CFMM theorem.  The log-price
function is no longer an arbitrary field: it is fixed to the normal-form
marginal-price expression.  The remaining explicit obligations are the
curvature of the imbalance potential and the second-order IL facts. -/
structure SmoothLocalNormalForm where
  jet : SymmetricHomogeneousJet
  imbalancePotentialDeriv : ℝ → ℝ
  ilLogPrice : ℝ → ℝ
  ilLogPriceDeriv : ℝ → ℝ
  imbalancePotentialDeriv_zero : imbalancePotentialDeriv 0 = 0
  imbalancePotentialDeriv_hasDerivAt_zero :
    HasDerivAt imbalancePotentialDeriv jet.curvature 0
  ilLogPrice_hasDerivAt_zero : HasDerivAt ilLogPrice (ilLogPriceDeriv 0) 0
  ilLogPriceDeriv_zero : ilLogPriceDeriv 0 = 0
  ilLogPriceDeriv_hasDerivAt_zero :
    HasDerivAt ilLogPriceDeriv
      (2 * localILLogPriceQuadraticCoeff jet.degree jet.curvature) 0

/-- The normal-form slope law reduces to the jet log-price slope once the
imbalance-potential curvature is known. -/
lemma normalFormDerivativePacket_slope_law (P : LocalNormalFormDerivativePacket) :
    2 - 2 * (deriv P.imbalancePotentialDeriv 0) / P.jet.degree =
      jetLogPriceSlope P.jet := by
  unfold jetLogPriceSlope localLogPriceSlope
  rw [P.imbalancePotentialDeriv_hasDerivAt_zero.deriv]
  field_simp [ne_of_gt P.jet.degree_pos]

/-- A calculus-facing derivative packet canonically produces the concrete
second-order CFMM witness needed by the frontier theorem. -/
def normalFormDerivativePacketWitness
    (P : LocalNormalFormDerivativePacket) : LocalSecondOrderCFMMWitness where
  jet := P.jet
  logPrice := P.logPrice
  ilLogPrice := P.ilLogPrice
  ilLogPriceDeriv := P.ilLogPriceDeriv
  logPrice_hasDerivAt_zero := by
    rw [← normalFormDerivativePacket_slope_law P]
    exact P.logPrice_hasDerivAt_zero
  ilLogPrice_hasDerivAt_zero := P.ilLogPrice_hasDerivAt_zero
  ilLogPriceDeriv_zero := P.ilLogPriceDeriv_zero
  ilLogPriceDeriv_hasDerivAt_zero := P.ilLogPriceDeriv_hasDerivAt_zero

/-- Smooth normal-form data canonically produces the derivative packet required
by the frontier theorem. -/
def smoothLocalNormalFormDerivativePacket
    (S : SmoothLocalNormalForm) : LocalNormalFormDerivativePacket where
  jet := S.jet
  imbalancePotentialDeriv := S.imbalancePotentialDeriv
  logPrice := smoothNormalFormLogPriceModel S.jet S.imbalancePotentialDeriv
  ilLogPrice := S.ilLogPrice
  ilLogPriceDeriv := S.ilLogPriceDeriv
  imbalancePotentialDeriv_hasDerivAt_zero := S.imbalancePotentialDeriv_hasDerivAt_zero
  logPrice_hasDerivAt_zero :=
    hasDerivAt_smoothNormalFormLogPriceModel S.jet
      S.imbalancePotentialDeriv_zero S.imbalancePotentialDeriv_hasDerivAt_zero
  ilLogPrice_hasDerivAt_zero := S.ilLogPrice_hasDerivAt_zero
  ilLogPriceDeriv_zero := S.ilLogPriceDeriv_zero
  ilLogPriceDeriv_hasDerivAt_zero := S.ilLogPriceDeriv_hasDerivAt_zero

/-- Smooth normal-form data canonically produces the concrete second-order
CFMM witness used by the frontier theorem. -/
def smoothLocalNormalFormWitness
    (S : SmoothLocalNormalForm) : LocalSecondOrderCFMMWitness :=
  normalFormDerivativePacketWitness (smoothLocalNormalFormDerivativePacket S)

/-- Slippage coefficient extracted from the witness's concrete log-price function. -/
def cfmmWitnessSlippage (W : LocalSecondOrderCFMMWitness) : ℝ :=
  deriv W.logPrice 0 / 2

/-- IL coefficient extracted from the witness's concrete IL derivative function. -/
def cfmmWitnessILCoeff (W : LocalSecondOrderCFMMWitness) : ℝ :=
  -(deriv W.ilLogPriceDeriv 0) / 2

/-- The concrete IL function has zero first derivative at balance. -/
lemma cfmmWitnessILDeriv_zero (W : LocalSecondOrderCFMMWitness) :
    deriv W.ilLogPrice 0 = 0 := by
  rw [W.ilLogPrice_hasDerivAt_zero.deriv, W.ilLogPriceDeriv_zero]

/-- The witness-extracted slippage agrees with the jet slippage. -/
lemma cfmmWitnessSlippage_eq_jet (W : LocalSecondOrderCFMMWitness) :
    cfmmWitnessSlippage W = jetSlippage W.jet := by
  unfold cfmmWitnessSlippage
  rw [W.logPrice_hasDerivAt_zero.deriv]
  rw [← jetSlippage_eq_half_logPriceSlope W.jet]

/-- The witness-extracted IL coefficient agrees with the jet IL coefficient. -/
lemma cfmmWitnessILCoeff_eq_jet (W : LocalSecondOrderCFMMWitness) :
    cfmmWitnessILCoeff W = jetILCoeff W.jet := by
  unfold cfmmWitnessILCoeff
  rw [W.ilLogPriceDeriv_hasDerivAt_zero.deriv]
  unfold jetILCoeff
  rw [localILCoeff_eq_neg_quadraticCoeff]
  ring

/-- The local slippage and IL coefficients sit on the same `1/8` frontier. -/
theorem local_frontier_product {n a : ℝ} (hn : n ≠ 0) (hna : n - a ≠ 0) :
    localSlippage n a * localILCoeff n a = (1 / 8 : ℝ) := by
  unfold localSlippage localILCoeff
  field_simp [hn, hna]

/-- Local coefficient form of the frontier invariant. -/
theorem local_frontier_invariant {n a : ℝ} (hn : n ≠ 0) (hna : n - a ≠ 0) :
    FrontierInvariant (localSlippage n a) (localILCoeff n a) :=
  local_frontier_product hn hna

/-- Jet-level statement of the local frontier. -/
theorem jet_frontier_product (J : SymmetricHomogeneousJet) :
    jetSlippage J * jetILCoeff J = (1 / 8 : ℝ) := by
  have hn : J.degree ≠ 0 := ne_of_gt J.degree_pos
  have hna : J.degree - J.curvature ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr J.curvature_lt_degree)
  simpa [jetSlippage, jetILCoeff] using
    local_frontier_product (n := J.degree) (a := J.curvature) hn hna

/-- Jet-level statement of the named local frontier invariant. -/
theorem jet_frontier_invariant (J : SymmetricHomogeneousJet) :
    FrontierInvariant (jetSlippage J) (jetILCoeff J) :=
  jet_frontier_product J

/-- Any indexed family of symmetric homogeneous jets is a global pointwise
frontier profile.  This is the pure jet-level global bridge: it turns a local
coefficient theorem into a theorem about functions over an arbitrary
price/market-state domain. -/
def jetFamilyGlobalProfile {ι : Type*}
    (J : ι → SymmetricHomogeneousJet) : GlobalFrontierProfile ι where
  slippage q := jetSlippage (J q)
  ilCoeff q := jetILCoeff (J q)
  frontier q := jet_frontier_invariant (J q)
  slippage_pos q := jetSlippage_pos (J q)

/-- Global no-free-lunch theorem for indexed local-jet families: if a candidate
jet family has no worse slippage everywhere and strictly better slippage
somewhere, then it cannot also have no worse IL curvature everywhere. -/
theorem jetFamily_global_no_simultaneous_dominance {ι : Type*}
    (baseline candidate : ι → SymmetricHomogeneousJet)
    (hslippage_no_worse :
      GloballyNoWorse
        (jetFamilyGlobalProfile candidate).slippage
        (jetFamilyGlobalProfile baseline).slippage)
    (hslippage_strict :
      StrictlyBetterSomewhere
        (jetFamilyGlobalProfile candidate).slippage
        (jetFamilyGlobalProfile baseline).slippage) :
    ¬ GloballyNoWorse
      (jetFamilyGlobalProfile candidate).ilCoeff
      (jetFamilyGlobalProfile baseline).ilCoeff :=
  global_frontier_no_simultaneous_dominance
    (jetFamilyGlobalProfile baseline)
    (jetFamilyGlobalProfile candidate)
    hslippage_no_worse
    hslippage_strict

/-- Any concrete local second-order CFMM witness satisfying the jet derivative
obligations lies on the local `1/8` frontier. -/
theorem cfmm_witness_frontier (W : LocalSecondOrderCFMMWitness) :
    cfmmWitnessSlippage W * cfmmWitnessILCoeff W = (1 / 8 : ℝ) := by
  rw [cfmmWitnessSlippage_eq_jet W, cfmmWitnessILCoeff_eq_jet W]
  exact jet_frontier_product W.jet

/-- Witness-level statement of the named local frontier invariant. -/
theorem cfmm_witness_frontier_invariant (W : LocalSecondOrderCFMMWitness) :
    FrontierInvariant (cfmmWitnessSlippage W) (cfmmWitnessILCoeff W) :=
  cfmm_witness_frontier W

/-- Calculus-facing normal-form packets inherit the local frontier. -/
theorem normalFormDerivativePacket_frontier (P : LocalNormalFormDerivativePacket) :
    cfmmWitnessSlippage (normalFormDerivativePacketWitness P) *
      cfmmWitnessILCoeff (normalFormDerivativePacketWitness P) = (1 / 8 : ℝ) :=
  cfmm_witness_frontier (normalFormDerivativePacketWitness P)

/-- Named invariant form for calculus-facing normal-form packets. -/
theorem normalFormDerivativePacket_frontier_invariant (P : LocalNormalFormDerivativePacket) :
    FrontierInvariant
      (cfmmWitnessSlippage (normalFormDerivativePacketWitness P))
      (cfmmWitnessILCoeff (normalFormDerivativePacketWitness P)) :=
  cfmm_witness_frontier_invariant (normalFormDerivativePacketWitness P)

/-- Smooth local normal forms inherit the local `1/8` frontier. -/
theorem smoothLocalNormalForm_frontier (S : SmoothLocalNormalForm) :
    cfmmWitnessSlippage (smoothLocalNormalFormWitness S) *
      cfmmWitnessILCoeff (smoothLocalNormalFormWitness S) = (1 / 8 : ℝ) :=
  cfmm_witness_frontier (smoothLocalNormalFormWitness S)

/-- Named invariant form for smooth local normal forms. -/
theorem smoothLocalNormalForm_frontier_invariant (S : SmoothLocalNormalForm) :
    FrontierInvariant
      (cfmmWitnessSlippage (smoothLocalNormalFormWitness S))
      (cfmmWitnessILCoeff (smoothLocalNormalFormWitness S)) :=
  cfmm_witness_frontier_invariant (smoothLocalNormalFormWitness S)

/-- A family of smooth local normal forms indexed by prices/market states is a
benchmark-coherent global frontier profile.  This is the checked bridge from
same-benchmark pointwise smooth normal-form witnesses to the abstract global
dominance theorem. -/
def smoothLocalNormalFormGlobalProfile {ι : Type*}
    (S : ι → SmoothLocalNormalForm) : GlobalFrontierProfile ι where
  slippage q := cfmmWitnessSlippage (smoothLocalNormalFormWitness (S q))
  ilCoeff q := cfmmWitnessILCoeff (smoothLocalNormalFormWitness (S q))
  frontier q := smoothLocalNormalForm_frontier_invariant (S q)
  slippage_pos q := by
    rw [cfmmWitnessSlippage_eq_jet]
    exact jetSlippage_pos (S q).jet

/-- Global no-free-lunch theorem for indexed smooth local normal-form families:
if a candidate family has no worse slippage everywhere and strictly better
slippage somewhere, then it cannot also have no worse IL curvature everywhere. -/
theorem smoothLocalNormalForm_global_no_simultaneous_dominance {ι : Type*}
    (baseline candidate : ι → SmoothLocalNormalForm)
    (hslippage_no_worse :
      GloballyNoWorse
        (smoothLocalNormalFormGlobalProfile candidate).slippage
        (smoothLocalNormalFormGlobalProfile baseline).slippage)
    (hslippage_strict :
      StrictlyBetterSomewhere
        (smoothLocalNormalFormGlobalProfile candidate).slippage
        (smoothLocalNormalFormGlobalProfile baseline).slippage) :
    ¬ GloballyNoWorse
      (smoothLocalNormalFormGlobalProfile candidate).ilCoeff
      (smoothLocalNormalFormGlobalProfile baseline).ilCoeff :=
  global_frontier_no_simultaneous_dominance
    (smoothLocalNormalFormGlobalProfile baseline)
    (smoothLocalNormalFormGlobalProfile candidate)
    hslippage_no_worse
    hslippage_strict

/-- Calculus-facing frontier for the local quadratic model. -/
theorem jet_quadratic_model_frontier (J : SymmetricHomogeneousJet) :
    (deriv (jetLogPriceModel J) 0 / 2) *
      (-(deriv (jetILLogPriceQuadraticModelDeriv J) 0) / 2) = (1 / 8 : ℝ) := by
  rw [deriv_jetLogPriceModel_zero, jetILCoeff_eq_model_curvature]
  rw [← jetSlippage_eq_half_logPriceSlope J]
  exact jet_frontier_product J

/-- The explicit quadratic model is itself a local second-order CFMM witness. -/
def quadraticModelWitness (J : SymmetricHomogeneousJet) : LocalSecondOrderCFMMWitness where
  jet := J
  logPrice := jetLogPriceModel J
  ilLogPrice := jetILLogPriceQuadraticModel J
  ilLogPriceDeriv := jetILLogPriceQuadraticModelDeriv J
  logPrice_hasDerivAt_zero := hasDerivAt_jetLogPriceModel J 0
  ilLogPrice_hasDerivAt_zero := hasDerivAt_jetILLogPriceQuadraticModel J 0
  ilLogPriceDeriv_zero := by
    simp [jetILLogPriceQuadraticModelDeriv]
  ilLogPriceDeriv_hasDerivAt_zero := hasDerivAt_jetILLogPriceQuadraticModelDeriv J 0

/-- The generic witness theorem specializes back to the explicit quadratic model. -/
theorem quadraticModelWitness_frontier (J : SymmetricHomogeneousJet) :
    cfmmWitnessSlippage (quadraticModelWitness J) *
      cfmmWitnessILCoeff (quadraticModelWitness J) = (1 / 8 : ℝ) :=
  cfmm_witness_frontier (quadraticModelWitness J)

/-- The local normal-form model is a concrete second-order CFMM witness. -/
def normalFormWitness (J : SymmetricHomogeneousJet) : LocalSecondOrderCFMMWitness where
  jet := J
  logPrice := normalFormLogPriceModel J
  ilLogPrice := jetILLogPriceQuadraticModel J
  ilLogPriceDeriv := jetILLogPriceQuadraticModelDeriv J
  logPrice_hasDerivAt_zero := hasDerivAt_normalFormLogPriceModel J 0
  ilLogPrice_hasDerivAt_zero := hasDerivAt_jetILLogPriceQuadraticModel J 0
  ilLogPriceDeriv_zero := by
    simp [jetILLogPriceQuadraticModelDeriv]
  ilLogPriceDeriv_hasDerivAt_zero := hasDerivAt_jetILLogPriceQuadraticModelDeriv J 0

/-- The normal-form model inherits the local frontier from the witness theorem. -/
theorem normalFormWitness_frontier (J : SymmetricHomogeneousJet) :
    cfmmWitnessSlippage (normalFormWitness J) *
      cfmmWitnessILCoeff (normalFormWitness J) = (1 / 8 : ℝ) :=
  cfmm_witness_frontier (normalFormWitness J)

/-- Increasing the local curvature parameter lowers the slippage coefficient. -/
lemma localSlippage_strictAntiOn_curvature {n a b : ℝ}
    (hnpos : 0 < n) (hab : a < b) :
    localSlippage n b < localSlippage n a := by
  unfold localSlippage
  exact div_lt_div_of_pos_right (sub_lt_sub_left hab n) hnpos

/-- Increasing the local curvature parameter raises the IL coefficient. -/
lemma localILCoeff_strictMonoOn_curvature {n a b : ℝ}
    (hnpos : 0 < n) (hb : b < n) (hab : a < b) :
    localILCoeff n a < localILCoeff n b := by
  unfold localILCoeff
  have hnb_pos : 0 < n - b := sub_pos.mpr hb
  have hden : 8 * (n - b) < 8 * (n - a) :=
    mul_lt_mul_of_pos_left (sub_lt_sub_left hab n) (by positivity)
  exact div_lt_div_of_pos_left hnpos (mul_pos (by positivity) hnb_pos) hden

/-- Local no-free-lunch: lower slippage from more curvature means higher IL. -/
theorem local_tradeoff_monotone {n a b : ℝ}
    (hnpos : 0 < n) (hb : b < n) (hab : a < b) :
    localSlippage n b < localSlippage n a ∧
      localILCoeff n a < localILCoeff n b :=
  ⟨localSlippage_strictAntiOn_curvature hnpos hab,
    localILCoeff_strictMonoOn_curvature hnpos hb hab⟩

/-- If two local jets have the same degree, the higher-curvature jet has lower
slippage and higher IL curvature. -/
theorem jet_tradeoff_same_degree {J K : SymmetricHomogeneousJet}
    (hdegree : K.degree = J.degree) (hcurv : J.curvature < K.curvature) :
    jetSlippage K < jetSlippage J ∧ jetILCoeff J < jetILCoeff K := by
  have hb : K.curvature < J.degree := by
    simpa [hdegree] using K.curvature_lt_degree
  simpa [jetSlippage, jetILCoeff, hdegree] using
    local_tradeoff_monotone (n := J.degree) (a := J.curvature) (b := K.curvature)
      J.degree_pos hb hcurv

/-- The power family contributes the jet `(n,a) = (alpha+2, alpha)`. -/
def powerFamilyJet (alpha : ℕ) : SymmetricHomogeneousJet where
  degree := (alpha : ℝ) + 2
  curvature := (alpha : ℝ)
  degree_pos := by
    have hnonneg : (0 : ℝ) ≤ (alpha : ℝ) := Nat.cast_nonneg alpha
    exact add_pos_of_nonneg_of_pos hnonneg (by positivity)
  curvature_lt_degree := by
    exact lt_add_of_pos_right (alpha : ℝ) (by positivity : (0 : ℝ) < 2)

/-- The power-family theorem is the special case `n = alpha + 2`, `a = alpha`. -/
lemma power_family_localSlippage (alpha : ℝ) (h : alpha + 2 ≠ 0) :
    localSlippage (alpha + 2) alpha = 2 / (alpha + 2) := by
  unfold localSlippage
  field_simp [h]
  ring

/-- The power-family IL coefficient reduces to `(alpha + 2) / 16`. -/
lemma power_family_localILCoeff (alpha : ℝ) :
    localILCoeff (alpha + 2) alpha = (alpha + 2) / 16 := by
  unfold localILCoeff
  ring

/-- Power-family specialization of the local frontier identity. -/
theorem power_family_frontier_product (alpha : ℝ) (h : alpha + 2 ≠ 0) :
    localSlippage (alpha + 2) alpha *
      localILCoeff (alpha + 2) alpha = (1 / 8 : ℝ) := by
  simpa [power_family_localSlippage alpha h, power_family_localILCoeff alpha] using
    (local_frontier_product (n := alpha + 2) (a := alpha) h (by norm_num : (alpha + 2) - alpha ≠ 0))

/-- Jet-level restatement of the checked power-family frontier. -/
theorem power_family_jet_frontier_product (alpha : ℕ) :
    jetSlippage (powerFamilyJet alpha) *
      jetILCoeff (powerFamilyJet alpha) = (1 / 8 : ℝ) :=
  jet_frontier_product (powerFamilyJet alpha)

end

end LocalJetFrontier
end Impossibility
end TauSwap
