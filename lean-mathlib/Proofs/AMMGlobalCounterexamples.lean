import Proofs.AMMLocalJetFrontier

/-!
# AMM global counterexamples

This file keeps global negative-knowledge examples separate from the local
frontier theorem.  The local theorem remains a balance-point statement; this
module records an exact CPMM witness showing that the naive original-HODL
pointwise global extension is false.
-/

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

open Filter
open scoped Topology

/-- Witness log price for the CPMM original-HODL global counterexample. -/
def cpmmOriginalHodlWitnessQ : ℝ :=
  2 * Real.log 2

/-- CPMM original-HODL impermanent-loss function as a function of log price. -/
def cpmmOriginalHodlIL (q : ℝ) : ℝ :=
  2 * Real.exp (q / 2) / (Real.exp q + 1) - 1

/-- First-derivative model for `cpmmOriginalHodlIL`. -/
def cpmmOriginalHodlILPrimeModel (q : ℝ) : ℝ :=
  Real.exp (q / 2) * (1 - Real.exp q) / (Real.exp q + 1) ^ 2

lemma exp_cpmmOriginalHodlWitnessQ_half :
    Real.exp (cpmmOriginalHodlWitnessQ / 2) = (2 : ℝ) := by
  unfold cpmmOriginalHodlWitnessQ
  norm_num [Real.exp_log]

lemma exp_cpmmOriginalHodlWitnessQ :
    Real.exp cpmmOriginalHodlWitnessQ = (4 : ℝ) := by
  unfold cpmmOriginalHodlWitnessQ
  rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring]
  rw [Real.exp_add]
  norm_num [Real.exp_log]

lemma deriv_exp_half_cpmmOriginalHodlWitnessQ :
    deriv (fun q : ℝ => Real.exp (q / 2)) cpmmOriginalHodlWitnessQ = (1 : ℝ) := by
  have hraw := (((hasDerivAt_id cpmmOriginalHodlWitnessQ).div_const 2).exp).deriv
  have h :
      deriv (fun q : ℝ => Real.exp (id q / 2)) cpmmOriginalHodlWitnessQ =
        Real.exp (id cpmmOriginalHodlWitnessQ / 2) * (1 / 2) := hraw
  change deriv (fun q : ℝ => Real.exp (id q / 2)) cpmmOriginalHodlWitnessQ = 1
  rw [h]
  simp [id, exp_cpmmOriginalHodlWitnessQ_half]

lemma hasDerivAt_cpmmOriginalHodlIL (q : ℝ) :
    HasDerivAt cpmmOriginalHodlIL (cpmmOriginalHodlILPrimeModel q) q := by
  unfold cpmmOriginalHodlIL cpmmOriginalHodlILPrimeModel
  have hnum : HasDerivAt (fun t : ℝ => 2 * Real.exp (t / 2)) (Real.exp (q / 2)) q := by
    simpa [id, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id q).div_const 2).exp.const_mul (2 : ℝ))
  have hden : HasDerivAt (fun t : ℝ => Real.exp t + 1) (Real.exp q) q := by
    simpa using (Real.hasDerivAt_exp q).const_add 1
  have hdiv := hnum.div hden (by positivity : (Real.exp q + 1 : ℝ) ≠ 0)
  convert hdiv.sub (hasDerivAt_const q (1 : ℝ)) using 1
  ring

lemma deriv_cpmmOriginalHodlIL (q : ℝ) :
    deriv cpmmOriginalHodlIL q = cpmmOriginalHodlILPrimeModel q :=
  (hasDerivAt_cpmmOriginalHodlIL q).deriv

lemma deriv_cpmmOriginalHodlILPrimeModel_num_witness :
    deriv (fun q : ℝ => Real.exp (q / 2) * (1 - Real.exp q))
      cpmmOriginalHodlWitnessQ = (-11 : ℝ) := by
  change deriv ((fun q : ℝ => Real.exp (q / 2)) *
      (fun q : ℝ => 1 - Real.exp q)) cpmmOriginalHodlWitnessQ = (-11 : ℝ)
  have hmul := deriv_mul (x := cpmmOriginalHodlWitnessQ)
    (c := fun q : ℝ => Real.exp (q / 2)) (d := fun q : ℝ => 1 - Real.exp q)
    (by fun_prop) (by fun_prop)
  rw [hmul]
  rw [deriv_exp_half_cpmmOriginalHodlWitnessQ, deriv_const_sub, Real.deriv_exp]
  dsimp
  rw [exp_cpmmOriginalHodlWitnessQ_half, exp_cpmmOriginalHodlWitnessQ]
  norm_num

lemma deriv_cpmmOriginalHodlILPrimeModel_den_witness :
    deriv (fun q : ℝ => (Real.exp q + 1) ^ 2) cpmmOriginalHodlWitnessQ = (40 : ℝ) := by
  change deriv ((fun q : ℝ => Real.exp q + 1) ^ 2) cpmmOriginalHodlWitnessQ = (40 : ℝ)
  have hpow := deriv_pow (x := cpmmOriginalHodlWitnessQ)
    (f := fun q : ℝ => Real.exp q + 1) (by fun_prop) 2
  rw [hpow]
  rw [deriv_add_const, Real.deriv_exp, exp_cpmmOriginalHodlWitnessQ]
  norm_num

lemma deriv_cpmmOriginalHodlILPrimeModel_witness :
    deriv cpmmOriginalHodlILPrimeModel cpmmOriginalHodlWitnessQ = (-7 / 125 : ℝ) := by
  unfold cpmmOriginalHodlILPrimeModel
  change deriv ((fun q : ℝ => Real.exp (q / 2) * (1 - Real.exp q)) /
      (fun q : ℝ => (Real.exp q + 1) ^ 2)) cpmmOriginalHodlWitnessQ = (-7 / 125 : ℝ)
  have hdiv := deriv_div (x := cpmmOriginalHodlWitnessQ)
    (c := fun q : ℝ => Real.exp (q / 2) * (1 - Real.exp q))
    (d := fun q : ℝ => (Real.exp q + 1) ^ 2)
    (by fun_prop) (by fun_prop)
    (by dsimp; rw [exp_cpmmOriginalHodlWitnessQ]; norm_num)
  rw [hdiv, deriv_cpmmOriginalHodlILPrimeModel_num_witness,
    deriv_cpmmOriginalHodlILPrimeModel_den_witness]
  dsimp
  rw [exp_cpmmOriginalHodlWitnessQ_half, exp_cpmmOriginalHodlWitnessQ]
  norm_num

/-- Exact second-derivative version of the CPMM original-HODL global
counterexample.  At `q = 2*log 2`, the positive global curvature coefficient is
`7/250`, so the naive pointwise product is not the local frontier value `1/8`. -/
theorem cpmm_originalHodl_second_derivative_witness :
    -(deriv (deriv cpmmOriginalHodlIL) cpmmOriginalHodlWitnessQ) / 2 = (7 / 250 : ℝ) := by
  have hfun : deriv cpmmOriginalHodlIL = cpmmOriginalHodlILPrimeModel := by
    funext q
    exact deriv_cpmmOriginalHodlIL q
  rw [hfun, deriv_cpmmOriginalHodlILPrimeModel_witness]
  norm_num

/-- Direct negative form of the CPMM global counterexample: the original-HODL
pointwise curvature coefficient at the witness is not the local frontier value
`1/8`. -/
theorem cpmm_originalHodl_second_derivative_not_frontier :
    -(deriv (deriv cpmmOriginalHodlIL) cpmmOriginalHodlWitnessQ) / 2 ≠ (1 / 8 : ℝ) := by
  rw [cpmm_originalHodl_second_derivative_witness]
  norm_num

/-- Gap form of the same counterexample.  The value is below the local frontier
constant by `97/1000`, so the naive pointwise global equality fails exactly. -/
theorem cpmm_originalHodl_second_derivative_frontier_gap :
    -(deriv (deriv cpmmOriginalHodlIL) cpmmOriginalHodlWitnessQ) / 2 -
        (1 / 8 : ℝ) = (-97 / 1000 : ℝ) := by
  rw [cpmm_originalHodl_second_derivative_witness]
  norm_num

/-!
## First perturbation tradeoff coefficients

The symbolic discovery probe `normal_form_series_probe.py` found that for
normal-form perturbations with no quadratic term,

`L(m,d) = n*m + b4*d^4/4 + b6*d^6/6`,

the first nonzero high-order term that lowers original-HODL global slippage also
raises original-HODL global curvature at the same local order.  The next lemmas
formalize the leading-coefficient sign invariant.  They do not claim the full
analytic series expansion; they are the small algebraic target that the series
probe suggests should be promoted next.
-/

/-- Leading slippage delta from a positive quartic perturbation. -/
def quarticSlippageLeadingDelta (n b4 d : ℝ) : ℝ :=
  -d ^ 2 * (3 * b4) / n

/-- Leading original-HODL curvature delta from a positive quartic perturbation. -/
def quarticCurvatureLeadingDelta (n b4 d : ℝ) : ℝ :=
  d ^ 2 * (12 * b4 * n) / (32 * n ^ 2)

/-- The leading quartic slippage delta is invariant under asset swap
`d -> -d`. -/
lemma quarticSlippageLeadingDelta_swap (n b4 d : ℝ) :
    quarticSlippageLeadingDelta n b4 (-d) =
      quarticSlippageLeadingDelta n b4 d := by
  unfold quarticSlippageLeadingDelta
  ring

/-- The leading quartic curvature delta is invariant under asset swap
`d -> -d`. -/
lemma quarticCurvatureLeadingDelta_swap (n b4 d : ℝ) :
    quarticCurvatureLeadingDelta n b4 (-d) =
      quarticCurvatureLeadingDelta n b4 d := by
  unfold quarticCurvatureLeadingDelta
  ring

/-- A positive quartic perturbation has the leading-order no-free-lunch sign:
it lowers slippage and raises curvature at every nonzero imbalance. -/
theorem quartic_first_perturbation_tradeoff {n b4 d : ℝ}
    (hn : 0 < n) (hb4 : 0 < b4) (hd : d ≠ 0) :
    quarticSlippageLeadingDelta n b4 d < 0 ∧
      0 < quarticCurvatureLeadingDelta n b4 d := by
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  constructor
  · unfold quarticSlippageLeadingDelta
    have hneg_num : -d ^ 2 * (3 * b4) < 0 := by
      have hfactor : 0 < 3 * b4 := by positivity
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hd2) hfactor
    exact div_neg_of_neg_of_pos hneg_num hn
  · unfold quarticCurvatureLeadingDelta
    positivity

/-- Canonical positive-imbalance representative for the quartic leading
tradeoff. -/
theorem quartic_first_perturbation_tradeoff_pos {n b4 d : ℝ}
    (hn : 0 < n) (hb4 : 0 < b4) (hd : 0 < d) :
    quarticSlippageLeadingDelta n b4 d < 0 ∧
      0 < quarticCurvatureLeadingDelta n b4 d :=
  quartic_first_perturbation_tradeoff hn hb4 (ne_of_gt hd)

/-- Negative imbalances transfer to the positive canonical case by the asset
swap symmetry `d -> -d`. -/
theorem quartic_first_perturbation_tradeoff_neg {n b4 d : ℝ}
    (hn : 0 < n) (hb4 : 0 < b4) (hd : d < 0) :
    quarticSlippageLeadingDelta n b4 d < 0 ∧
      0 < quarticCurvatureLeadingDelta n b4 d := by
  have hcanon :
      quarticSlippageLeadingDelta n b4 (-d) < 0 ∧
        0 < quarticCurvatureLeadingDelta n b4 (-d) :=
    quartic_first_perturbation_tradeoff_pos hn hb4 (neg_pos.mpr hd)
  simpa [quarticSlippageLeadingDelta_swap, quarticCurvatureLeadingDelta_swap] using hcanon

/-- Leading slippage delta from a positive sextic perturbation when the quartic
term vanishes. -/
def sexticSlippageLeadingDelta (n b6 d : ℝ) : ℝ :=
  -d ^ 4 * (5 * b6) / n

/-- Leading original-HODL curvature delta from a positive sextic perturbation
when the quartic term vanishes. -/
def sexticCurvatureLeadingDelta (n b6 d : ℝ) : ℝ :=
  d ^ 4 * (20 * b6 * n) / (32 * n ^ 2)

/-- The leading sextic slippage delta is invariant under asset swap
`d -> -d`. -/
lemma sexticSlippageLeadingDelta_swap (n b6 d : ℝ) :
    sexticSlippageLeadingDelta n b6 (-d) =
      sexticSlippageLeadingDelta n b6 d := by
  unfold sexticSlippageLeadingDelta
  ring

/-- The leading sextic curvature delta is invariant under asset swap
`d -> -d`. -/
lemma sexticCurvatureLeadingDelta_swap (n b6 d : ℝ) :
    sexticCurvatureLeadingDelta n b6 (-d) =
      sexticCurvatureLeadingDelta n b6 d := by
  unfold sexticCurvatureLeadingDelta
  ring

/-- If the quartic perturbation vanishes, a positive sextic perturbation has
the same leading-order no-free-lunch sign one order later. -/
theorem sextic_first_perturbation_tradeoff {n b6 d : ℝ}
    (hn : 0 < n) (hb6 : 0 < b6) (hd : d ≠ 0) :
    sexticSlippageLeadingDelta n b6 d < 0 ∧
      0 < sexticCurvatureLeadingDelta n b6 d := by
  have hd4 : 0 < d ^ 4 := by
    have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
    nlinarith [sq_pos_of_pos hd2]
  constructor
  · unfold sexticSlippageLeadingDelta
    have hneg_num : -d ^ 4 * (5 * b6) < 0 := by
      have hfactor : 0 < 5 * b6 := by positivity
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hd4) hfactor
    exact div_neg_of_neg_of_pos hneg_num hn
  · unfold sexticCurvatureLeadingDelta
    positivity

/-- Canonical positive-imbalance representative for the sextic leading
tradeoff. -/
theorem sextic_first_perturbation_tradeoff_pos {n b6 d : ℝ}
    (hn : 0 < n) (hb6 : 0 < b6) (hd : 0 < d) :
    sexticSlippageLeadingDelta n b6 d < 0 ∧
      0 < sexticCurvatureLeadingDelta n b6 d :=
  sextic_first_perturbation_tradeoff hn hb6 (ne_of_gt hd)

/-- Negative imbalances transfer to the positive canonical case by the asset
swap symmetry `d -> -d`. -/
theorem sextic_first_perturbation_tradeoff_neg {n b6 d : ℝ}
    (hn : 0 < n) (hb6 : 0 < b6) (hd : d < 0) :
    sexticSlippageLeadingDelta n b6 d < 0 ∧
      0 < sexticCurvatureLeadingDelta n b6 d := by
  have hcanon :
      sexticSlippageLeadingDelta n b6 (-d) < 0 ∧
        0 < sexticCurvatureLeadingDelta n b6 (-d) :=
    sextic_first_perturbation_tradeoff_pos hn hb6 (neg_pos.mpr hd)
  simpa [sexticSlippageLeadingDelta_swap, sexticCurvatureLeadingDelta_swap] using hcanon

/-!
The quartic and sextic probes are instances of a single leading-coefficient
law: after quotienting by the asset-swap symmetry, the first nonzero even
perturbation has a shared positive scale.  Its leading slippage delta is the
negative of that scale, while its leading curvature delta is one eighth of the
same scale.
-/

/-- Shared leading scale for a first nonzero even perturbation.  `j = 1`
corresponds to the quartic case and `j = 2` to the sextic case. -/
def evenPerturbLeadingScale (j : ℕ) (n b d : ℝ) : ℝ :=
  (((2 * j + 1 : ℕ) : ℝ) * b * (d ^ j) ^ 2) / n

/-- General leading slippage delta for a positive first nonzero even
perturbation. -/
def evenPerturbSlippageLeadingDelta (j : ℕ) (n b d : ℝ) : ℝ :=
  -evenPerturbLeadingScale j n b d

/-- General leading original-HODL curvature delta for a positive first nonzero
even perturbation. -/
def evenPerturbCurvatureLeadingDelta (j : ℕ) (n b d : ℝ) : ℝ :=
  evenPerturbLeadingScale j n b d / 8

/-- The leading curvature delta is exactly `-1/8` times the leading slippage
delta for every first nonzero even perturbation order. -/
lemma evenPerturbCurvature_eq_neg_slippage_div_eight (j : ℕ) (n b d : ℝ) :
    evenPerturbCurvatureLeadingDelta j n b d =
      -evenPerturbSlippageLeadingDelta j n b d / 8 := by
  unfold evenPerturbCurvatureLeadingDelta evenPerturbSlippageLeadingDelta
  ring

/-- The shared leading scale is positive for positive reserve scale, positive
perturbation coefficient, and nonzero imbalance. -/
lemma evenPerturbLeadingScale_pos (j : ℕ) {n b d : ℝ}
    (hn : 0 < n) (hb : 0 < b) (hd : d ≠ 0) :
    0 < evenPerturbLeadingScale j n b d := by
  unfold evenPerturbLeadingScale
  have hcoef : 0 < (((2 * j + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos (2 * j)
  have hpow_ne : d ^ j ≠ 0 := pow_ne_zero j hd
  have hsquare : 0 < (d ^ j) ^ 2 := sq_pos_of_ne_zero hpow_ne
  have hnum : 0 < (((2 * j + 1 : ℕ) : ℝ) * b * (d ^ j) ^ 2) :=
    mul_pos (mul_pos hcoef hb) hsquare
  exact div_pos hnum hn

/-- Any positive first nonzero even perturbation has the same leading-order
no-free-lunch sign: it lowers slippage and raises curvature. -/
theorem evenPerturb_first_nonzero_tradeoff (j : ℕ) {n b d : ℝ}
    (hn : 0 < n) (hb : 0 < b) (hd : d ≠ 0) :
    evenPerturbSlippageLeadingDelta j n b d < 0 ∧
      0 < evenPerturbCurvatureLeadingDelta j n b d := by
  have hscale : 0 < evenPerturbLeadingScale j n b d :=
    evenPerturbLeadingScale_pos j hn hb hd
  constructor
  · unfold evenPerturbSlippageLeadingDelta
    exact neg_neg_of_pos hscale
  · unfold evenPerturbCurvatureLeadingDelta
    positivity

/-- If a delta has a leading expansion `a * basis + rem` and
`rem / basis -> 0`, then the normalized delta tends to its leading coefficient
`a`.  This is the small analytic bridge expected from a Taylor extraction. -/
lemma leading_expansion_ratio_tendsto {f basis rem : ℝ → ℝ} {a : ℝ}
    (hbasis_ne : ∀ᶠ d in 𝓝[≠] (0 : ℝ), basis d ≠ 0)
    (hdecomp : ∀ᶠ d in 𝓝[≠] (0 : ℝ), f d = a * basis d + rem d)
    (hrem : Tendsto (fun d => rem d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun d => f d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 a) := by
  have hrewrite :
      (fun d => f d / basis d) =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun d => a + rem d / basis d) := by
    filter_upwards [hbasis_ne, hdecomp] with d hb hd
    rw [hd]
    field_simp [hb]
  have htend :
      Tendsto (fun d => a + rem d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 (a + 0)) :=
    tendsto_const_nhds.add hrem
  have htend' :
      Tendsto (fun d => a + rem d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 a) := by
    simpa using htend
  exact htend'.congr' hrewrite.symm

/-- Analytic bridge shape for a first-separation argument.  If the normalized
slippage delta tends to a negative leading coefficient and the normalized
curvature delta tends to the matching positive coefficient, and the normalizing
basis is positive on the punctured neighborhood, then the actual deltas have
the no-free-lunch signs near the separation point. -/
lemma leading_ratio_sign_obstruction {slipDelta curvDelta basis : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hbasis : ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < basis d)
    (hslip : Tendsto (fun d => slipDelta d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 (-c)))
    (hcurv : Tendsto (fun d => curvDelta d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 (c / 8))) :
    (∀ᶠ d in 𝓝[≠] (0 : ℝ), slipDelta d < 0) ∧
      (∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < curvDelta d) := by
  have hslip_ratio : ∀ᶠ d in 𝓝[≠] (0 : ℝ), slipDelta d / basis d < 0 :=
    hslip.eventually (eventually_lt_nhds (neg_neg_of_pos hc))
  have hcurv_ratio : ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < curvDelta d / basis d :=
    hcurv.eventually (eventually_gt_nhds
      (div_pos hc (by exact_mod_cast (show (0 : ℕ) < 8 by decide))))
  constructor
  · filter_upwards [hbasis, hslip_ratio] with d hb hr
    have hmul : slipDelta d / basis d * basis d < 0 * basis d :=
      mul_lt_mul_of_pos_right hr hb
    simpa [ne_of_gt hb] using hmul
  · filter_upwards [hbasis, hcurv_ratio] with d hb hr
    have hmul : 0 * basis d < curvDelta d / basis d * basis d :=
      mul_lt_mul_of_pos_right hr hb
    simpa [ne_of_gt hb] using hmul

/-- A globally nonpositive curvature delta is incompatible with an eventually
positive curvature delta on any nonempty punctured neighborhood. -/
lemma punctured_positive_contradicts_global_nonpos {curvDelta : ℝ → ℝ}
    (hcurv_pos : ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < curvDelta d)
    (hglobal : ∀ d, curvDelta d ≤ 0) :
    False := by
  obtain ⟨d, hdpos⟩ := hcurv_pos.exists
  exact not_lt_of_ge (hglobal d) hdpos

/-- Local leading-ratio separation is enough to refute global curvature
dominance.  This is the abstract bridge needed by the proposed global proof:
once a Taylor/analytic argument supplies the normalized limits, global
no-worse curvature cannot hold. -/
theorem leading_ratio_obstruction_not_global_curvature_no_worse
    {slipDelta curvDelta basis : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hbasis : ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < basis d)
    (hslip : Tendsto (fun d => slipDelta d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 (-c)))
    (hcurv : Tendsto (fun d => curvDelta d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 (c / 8))) :
    ¬ ∀ d, curvDelta d ≤ 0 := by
  intro hglobal
  exact punctured_positive_contradicts_global_nonpos
    (leading_ratio_sign_obstruction hc hbasis hslip hcurv).2 hglobal

/-- Expansion form of the local-to-global obstruction.  A Taylor extraction
only needs to provide a positive basis, leading coefficients `-c` and `c/8`,
and remainders that are small relative to the basis; the global curvature
dominance contradiction then follows. -/
theorem leading_expansions_obstruct_global_curvature_no_worse
    {slipDelta curvDelta basis slipRem curvRem : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hbasis : ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < basis d)
    (hslip_decomp :
      ∀ᶠ d in 𝓝[≠] (0 : ℝ), slipDelta d = (-c) * basis d + slipRem d)
    (hcurv_decomp :
      ∀ᶠ d in 𝓝[≠] (0 : ℝ), curvDelta d = (c / 8) * basis d + curvRem d)
    (hslip_rem :
      Tendsto (fun d => slipRem d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (hcurv_rem :
      Tendsto (fun d => curvRem d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    ¬ ∀ d, curvDelta d ≤ 0 := by
  have hbasis_ne : ∀ᶠ d in 𝓝[≠] (0 : ℝ), basis d ≠ 0 :=
    hbasis.mono fun _ hd => ne_of_gt hd
  have hslip :
      Tendsto (fun d => slipDelta d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 (-c)) :=
    leading_expansion_ratio_tendsto hbasis_ne hslip_decomp hslip_rem
  have hcurv :
      Tendsto (fun d => curvDelta d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 (c / 8)) :=
    leading_expansion_ratio_tendsto hbasis_ne hcurv_decomp hcurv_rem
  exact leading_ratio_obstruction_not_global_curvature_no_worse hc hbasis hslip hcurv

/-- The exact payload the remaining AMM-specific Taylor theorem should
produce at a first separation point.  The coordinate has already been
translated so the separation point is `d = 0`, and the asset-swap symmetry has
already reduced to an even positive basis. -/
structure FirstSeparationExpansion (slipDelta curvDelta : ℝ → ℝ) where
  basis : ℝ → ℝ
  slipRem : ℝ → ℝ
  curvRem : ℝ → ℝ
  coeff : ℝ
  coeff_pos : 0 < coeff
  basis_pos : ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < basis d
  slip_decomp :
    ∀ᶠ d in 𝓝[≠] (0 : ℝ),
      slipDelta d = (-coeff) * basis d + slipRem d
  curv_decomp :
    ∀ᶠ d in 𝓝[≠] (0 : ℝ),
      curvDelta d = (coeff / 8) * basis d + curvRem d
  slip_rem_small :
    Tendsto (fun d => slipRem d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 0)
  curv_rem_small :
    Tendsto (fun d => curvRem d / basis d) (𝓝[≠] (0 : ℝ)) (𝓝 0)

/-- A first-separation expansion refutes global curvature dominance. -/
theorem FirstSeparationExpansion.not_global_curvature_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (E : FirstSeparationExpansion slipDelta curvDelta) :
    ¬ ∀ d, curvDelta d ≤ 0 :=
  leading_expansions_obstruct_global_curvature_no_worse
    E.coeff_pos E.basis_pos E.slip_decomp E.curv_decomp
    E.slip_rem_small E.curv_rem_small

/-- A first-separation expansion rules out simultaneous global no-worse
slippage and curvature deltas.  The slippage side is included to match the
global AMM theorem surface, although the contradiction is carried by the
curvature penalty forced by the leading expansion. -/
theorem FirstSeparationExpansion.not_simultaneous_global_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (E : FirstSeparationExpansion slipDelta curvDelta) :
    ¬ ((∀ d, slipDelta d ≤ 0) ∧ (∀ d, curvDelta d ≤ 0)) := by
  intro hglobal
  exact E.not_global_curvature_no_worse hglobal.2

/-- A more concrete first-separation payload for the asset-symmetric AMM
normal form.  The positive basis is the first nonzero even term
`(d^order)^2`; the coefficient is positive; and the remaining terms are small
relative to that basis. -/
structure FirstEvenTaylorSeparation (slipDelta curvDelta : ℝ → ℝ) where
  order : ℕ
  order_pos : 0 < order
  coeff : ℝ
  slipRem : ℝ → ℝ
  curvRem : ℝ → ℝ
  coeff_pos : 0 < coeff
  slip_decomp :
    ∀ᶠ d in 𝓝[≠] (0 : ℝ),
      slipDelta d = (-coeff) * (d ^ order) ^ 2 + slipRem d
  curv_decomp :
    ∀ᶠ d in 𝓝[≠] (0 : ℝ),
      curvDelta d = (coeff / 8) * (d ^ order) ^ 2 + curvRem d
  slip_rem_small :
    Tendsto (fun d => slipRem d / (d ^ order) ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0)
  curv_rem_small :
    Tendsto (fun d => curvRem d / (d ^ order) ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0)

/-- Delta-form "no worse everywhere": the candidate-minus-baseline delta is
nonpositive at every imbalance. -/
def DeltaNoWorse (delta : ℝ → ℝ) : Prop :=
  ∀ d, delta d ≤ 0

/-- Delta-form strict improvement: the candidate-minus-baseline delta is
strictly negative somewhere. -/
def DeltaStrictlyBetterSomewhere (delta : ℝ → ℝ) : Prop :=
  ∃ d, delta d < 0

/-- Delta-form simultaneous dominance claim for slippage and curvature:
slippage is no worse everywhere and strictly better somewhere, while curvature
is also no worse everywhere. -/
def DeltaSimultaneousNoWorseWithStrictSlippage
    (slipDelta curvDelta : ℝ → ℝ) : Prop :=
  DeltaNoWorse slipDelta ∧
    DeltaStrictlyBetterSomewhere slipDelta ∧
    DeltaNoWorse curvDelta

/-- Candidate-minus-baseline delta for a pair of coefficient functions. -/
def FunctionDelta (candidate baseline : ℝ → ℝ) : ℝ → ℝ :=
  fun d => candidate d - baseline d

/-- Function-level no-worse is exactly delta nonpositivity for the
candidate-minus-baseline delta. -/
theorem deltaNoWorse_functionDelta_iff {candidate baseline : ℝ → ℝ} :
    DeltaNoWorse (FunctionDelta candidate baseline) ↔
      GloballyNoWorse candidate baseline := by
  unfold DeltaNoWorse FunctionDelta GloballyNoWorse
  constructor
  · intro h d
    exact sub_nonpos.mp (h d)
  · intro h d
    exact sub_nonpos.mpr (h d)

/-- Function-level strict improvement is exactly strict negativity somewhere
for the candidate-minus-baseline delta. -/
theorem deltaStrictlyBetter_functionDelta_iff {candidate baseline : ℝ → ℝ} :
    DeltaStrictlyBetterSomewhere (FunctionDelta candidate baseline) ↔
      StrictlyBetterSomewhere candidate baseline := by
  unfold DeltaStrictlyBetterSomewhere FunctionDelta StrictlyBetterSomewhere
  constructor
  · intro h
    rcases h with ⟨d, hd⟩
    exact ⟨d, sub_neg.mp hd⟩
  · intro h
    rcases h with ⟨d, hd⟩
    exact ⟨d, sub_neg.mpr hd⟩

/-- Translate function-level simultaneous dominance into delta-form
simultaneous dominance. -/
theorem deltaSimultaneous_from_function_dominance
    {candidateSlippage baselineSlippage candidateCurvature baselineCurvature : ℝ → ℝ}
    (hslip_no_worse : GloballyNoWorse candidateSlippage baselineSlippage)
    (hslip_strict : StrictlyBetterSomewhere candidateSlippage baselineSlippage)
    (hcurv_no_worse : GloballyNoWorse candidateCurvature baselineCurvature) :
    DeltaSimultaneousNoWorseWithStrictSlippage
      (FunctionDelta candidateSlippage baselineSlippage)
      (FunctionDelta candidateCurvature baselineCurvature) := by
  constructor
  · exact (deltaNoWorse_functionDelta_iff).2 hslip_no_worse
  constructor
  · exact (deltaStrictlyBetter_functionDelta_iff).2 hslip_strict
  · exact (deltaNoWorse_functionDelta_iff).2 hcurv_no_worse

/-- Coefficient-facing form of the first even Taylor payload.  This is the
shape a future analytic extraction theorem should naturally produce: the first
nonzero slippage coefficient is negative, and the corresponding curvature
coefficient is `-slipCoeff/8`. -/
structure FirstEvenTaylorCoefficientData (slipDelta curvDelta : ℝ → ℝ) where
  order : ℕ
  order_pos : 0 < order
  slipCoeff : ℝ
  slipCoeff_neg : slipCoeff < 0
  slipRem : ℝ → ℝ
  curvRem : ℝ → ℝ
  slip_decomp :
    ∀ᶠ d in 𝓝[≠] (0 : ℝ),
      slipDelta d = slipCoeff * (d ^ order) ^ 2 + slipRem d
  curv_decomp :
    ∀ᶠ d in 𝓝[≠] (0 : ℝ),
      curvDelta d = (-slipCoeff / 8) * (d ^ order) ^ 2 + curvRem d
  slip_rem_small :
    Tendsto (fun d => slipRem d / (d ^ order) ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0)
  curv_rem_small :
    Tendsto (fun d => curvRem d / (d ^ order) ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0)

/-- Slippage-only half of the first even Taylor extraction.  This isolates the
finite-order contact obligation: under the global slippage assumptions, find
the first negative even coefficient and a small remainder. -/
structure FirstEvenSlippageData (slipDelta : ℝ → ℝ) where
  order : ℕ
  order_pos : 0 < order
  slipCoeff : ℝ
  slipCoeff_neg : slipCoeff < 0
  slipRem : ℝ → ℝ
  slip_decomp :
    ∀ᶠ d in 𝓝[≠] (0 : ℝ),
      slipDelta d = slipCoeff * (d ^ order) ^ 2 + slipRem d
  slip_rem_small :
    Tendsto (fun d => slipRem d / (d ^ order) ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0)

/-- Forget curvature data and retain the slippage-only first-even payload. -/
def FirstEvenTaylorCoefficientData.toFirstEvenSlippageData
    {slipDelta curvDelta : ℝ → ℝ}
    (T : FirstEvenTaylorCoefficientData slipDelta curvDelta) :
    FirstEvenSlippageData slipDelta where
  order := T.order
  order_pos := T.order_pos
  slipCoeff := T.slipCoeff
  slipCoeff_neg := T.slipCoeff_neg
  slipRem := T.slipRem
  slip_decomp := T.slip_decomp
  slip_rem_small := T.slip_rem_small

/-- The first extraction sub-obligation: global no-worse slippage plus strict
slippage gain yields a first negative even slippage coefficient. -/
structure FirstEvenSlippageExtractionPrinciple (slipDelta : ℝ → ℝ) :
    Prop where
  construct :
    DeltaNoWorse slipDelta →
    DeltaStrictlyBetterSomewhere slipDelta →
      Nonempty (FirstEvenSlippageData slipDelta)

/-- A concrete coefficient-facing payload is already enough to satisfy the
slippage-extraction half of the abstract same-benchmark interface. -/
def FirstEvenTaylorCoefficientData.toFirstEvenSlippageExtractionPrinciple
    {slipDelta curvDelta : ℝ → ℝ}
    (T : FirstEvenTaylorCoefficientData slipDelta curvDelta) :
    FirstEvenSlippageExtractionPrinciple slipDelta where
  construct _hslip_no_worse _hslip_strict :=
    ⟨T.toFirstEvenSlippageData⟩

/-- The normalized slippage ratio of a first-even slippage payload tends to
its leading coefficient. -/
private lemma FirstEvenSlippageData.tendsto_normalized
    {slipDelta : ℝ → ℝ} (S : FirstEvenSlippageData slipDelta) :
    Tendsto (fun d => slipDelta d / (d ^ S.order) ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 S.slipCoeff) := by
  obtain ⟨S_order, _S_order_pos, S_slipCoeff, _S_slipCoeff_neg, S_slipRem,
    S_slip_decomp, S_slip_rem_small⟩ := S
  rw [Filter.tendsto_congr' (by
    filter_upwards [S_slip_decomp, self_mem_nhdsWithin] with x hx hx'
    rw [hx, add_div])]
  simpa using
    (Filter.Tendsto.add
      (tendsto_const_nhds.congr' <| by
        filter_upwards [self_mem_nhdsWithin] with x hx using by
          rw [mul_div_cancel_right₀ _ <| pow_ne_zero _ <| pow_ne_zero _ hx])
      S_slip_rem_small)

/-- A positive-exponent even power tends to zero at the punctured origin. -/
private lemma tendsto_pow_sq_zero {n : ℕ} (hn : 0 < n) :
    Tendsto (fun d : ℝ => (d ^ n) ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hpow :
      Tendsto (fun d : ℝ => (d ^ n) ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [zero_pow (Nat.ne_of_gt hn)] using
      ((continuous_id.pow n).pow 2).tendsto (0 : ℝ)
  exact tendsto_nhdsWithin_of_tendsto_nhds hpow

/-- If a function is normalized by a higher even power and has a finite limit,
then normalizing it by a lower even power tends to zero at the punctured origin. -/
private lemma tendsto_normalized_lower
    {f : ℝ → ℝ} {L : ℝ} {m n : ℕ}
    (hmn : m < n)
    (hL : Tendsto (fun d => f d / (d ^ n) ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun d => f d / (d ^ m) ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  suffices h_suff :
      Tendsto (fun d : ℝ =>
        (f d / (d ^ n) ^ 2) * (d ^ (2 * (n - m)))) (𝓝[≠] 0) (𝓝 0) by
    apply h_suff.congr'
    filter_upwards [self_mem_nhdsWithin] with d hd
    have hd_ne : d ≠ 0 := hd
    simp [pow_mul', mul_comm, mul_left_comm, div_eq_mul_inv]
    field_simp
    exact Or.inl (by
      rw [show d ^ n = d ^ m * d ^ (n - m) by
        rw [← pow_add, Nat.add_sub_of_le hmn.le]]
      rw [mul_pow]
      have hswap : (d ^ (n - m)) ^ 2 = (d ^ 2) ^ (n - m) := by
        calc
          (d ^ (n - m)) ^ 2 = d ^ ((n - m) * 2) := by rw [← pow_mul]
          _ = d ^ (2 * (n - m)) := by rw [Nat.mul_comm]
          _ = (d ^ 2) ^ (n - m) := by rw [pow_mul]
      rw [hswap]
      ac_rfl)
  have hpow :
      Tendsto (fun d : ℝ => d ^ (2 * (n - m))) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa [pow_mul, Nat.mul_comm] using
      tendsto_pow_sq_zero (Nat.sub_pos_of_lt hmn)
  simpa using hL.mul hpow

/-- The first nonzero even slippage order and coefficient are unique for a
fixed slippage delta. -/
theorem FirstEvenSlippageData.unique_order_and_coeff
    {slipDelta : ℝ → ℝ}
    (S T : FirstEvenSlippageData slipDelta) :
    S.order = T.order ∧ S.slipCoeff = T.slipCoeff := by
  have hS := S.tendsto_normalized
  have hT := T.tendsto_normalized
  rcases lt_trichotomy S.order T.order with hlt | heq | hgt
  · have hLower := tendsto_normalized_lower hlt hT
    have hzero : S.slipCoeff = 0 := tendsto_nhds_unique hS hLower
    exact (lt_irrefl (0 : ℝ) (by simpa [hzero] using S.slipCoeff_neg)).elim
  · have hcoeff : S.slipCoeff = T.slipCoeff := by
      exact tendsto_nhds_unique hS (by simpa [heq] using hT)
    exact ⟨heq, hcoeff⟩
  · have hLower := tendsto_normalized_lower hgt hS
    have hzero : T.slipCoeff = 0 := tendsto_nhds_unique hT hLower
    exact (lt_irrefl (0 : ℝ) (by simpa [hzero] using T.slipCoeff_neg)).elim

/-- The second extraction sub-obligation: once the first slippage coefficient is
known, the curvature delta has the matching leading coefficient
`-slipCoeff/8` with a small remainder. -/
structure FirstEvenCurvatureLeadingLaw (slipDelta curvDelta : ℝ → ℝ) :
    Prop where
  match_first :
    (S : FirstEvenSlippageData slipDelta) →
      ∃ curvRem : ℝ → ℝ,
        (∀ᶠ d in 𝓝[≠] (0 : ℝ),
          curvDelta d = (-S.slipCoeff / 8) * (d ^ S.order) ^ 2 + curvRem d) ∧
        Tendsto (fun d => curvRem d / (d ^ S.order) ^ 2)
          (𝓝[≠] (0 : ℝ)) (𝓝 0)

/-- A concrete coefficient-facing Taylor payload promotes to the abstract
curvature-leading-law interface because first-even slippage data is unique. -/
theorem FirstEvenTaylorCoefficientData.toFirstEvenCurvatureLeadingLaw
    {slipDelta curvDelta : ℝ → ℝ}
    (T : FirstEvenTaylorCoefficientData slipDelta curvDelta) :
    FirstEvenCurvatureLeadingLaw slipDelta curvDelta := by
  constructor
  intro S
  rcases FirstEvenSlippageData.unique_order_and_coeff
      S T.toFirstEvenSlippageData with ⟨horder, hcoeff⟩
  exact ⟨T.curvRem, by
    filter_upwards [T.curv_decomp] with d hd
    rw [horder, hcoeff]
    exact hd, by
    rw [horder]
    exact T.curv_rem_small⟩

/-- Abstract same-benchmark analytic obligation bundle.  This is not yet a
concrete AMM semantics theorem; it is the exact pair of obligations that a
future same-benchmark analytic AMM proof must supply. -/
structure SameBenchmarkAnalyticPairObligations
    (slipDelta curvDelta : ℝ → ℝ) : Prop where
  slippage_extraction : FirstEvenSlippageExtractionPrinciple slipDelta
  curvature_law : FirstEvenCurvatureLeadingLaw slipDelta curvDelta

/-- A concrete coefficient-facing Taylor payload is a same-benchmark analytic
obligation bundle for its two deltas. -/
def FirstEvenTaylorCoefficientData.toSameBenchmarkAnalyticPairObligations
    {slipDelta curvDelta : ℝ → ℝ}
    (T : FirstEvenTaylorCoefficientData slipDelta curvDelta) :
    SameBenchmarkAnalyticPairObligations slipDelta curvDelta where
  slippage_extraction := T.toFirstEvenSlippageExtractionPrinciple
  curvature_law := T.toFirstEvenCurvatureLeadingLaw

/-- Semantics-ready wrapper for the final global theorem surface.  This
structure does not claim that arbitrary AMMs satisfy the assumptions; it is the
exact object that a future concrete same-benchmark analytic AMM semantics proof
must construct. -/
structure SameBenchmarkAnalyticAMMPair where
  slipDelta : ℝ → ℝ
  curvDelta : ℝ → ℝ
  obligations : SameBenchmarkAnalyticPairObligations slipDelta curvDelta

/-- Function-level same-benchmark analytic pair.  This is the surface closer to
concrete AMM semantics: it stores baseline/candidate coefficient functions and
proves the delta obligations for their candidate-minus-baseline deltas. -/
structure SameBenchmarkAnalyticFunctionPair where
  baselineSlippage : ℝ → ℝ
  candidateSlippage : ℝ → ℝ
  baselineCurvature : ℝ → ℝ
  candidateCurvature : ℝ → ℝ
  obligations :
    SameBenchmarkAnalyticPairObligations
      (FunctionDelta candidateSlippage baselineSlippage)
      (FunctionDelta candidateCurvature baselineCurvature)

/-- The coefficient-function surface exposed by concrete AMM semantics.  This
is deliberately just the observable surface: the future semantic theorem must
prove that these functions are extracted from the same coordinate and benchmark
before constructing a `ConcreteSameBenchmarkAnalyticAMMPair`. -/
structure AMMCoefficientSurface where
  baselineSlippage : ℝ → ℝ
  candidateSlippage : ℝ → ℝ
  baselineCurvature : ℝ → ℝ
  candidateCurvature : ℝ → ℝ

/-- A function-level obstruction pair realizes a concrete coefficient surface
when it stores exactly the same baseline/candidate slippage and curvature
functions. -/
def AMMCoefficientSurface.PairRealizes
    (F : AMMCoefficientSurface) (P : SameBenchmarkAnalyticFunctionPair) : Prop :=
  P.baselineSlippage = F.baselineSlippage ∧
    P.candidateSlippage = F.candidateSlippage ∧
    P.baselineCurvature = F.baselineCurvature ∧
    P.candidateCurvature = F.candidateCurvature

/-- Candidate-minus-baseline slippage delta exposed by a coefficient surface. -/
def AMMCoefficientSurface.slipDelta (F : AMMCoefficientSurface) : ℝ → ℝ :=
  FunctionDelta F.candidateSlippage F.baselineSlippage

/-- Candidate-minus-baseline curvature delta exposed by a coefficient surface. -/
def AMMCoefficientSurface.curvDelta (F : AMMCoefficientSurface) : ℝ → ℝ :=
  FunctionDelta F.candidateCurvature F.baselineCurvature

/-- Same-benchmark analytic assumptions attached to one coefficient surface.
This is the reusable subtarget for raw AMM semantics: construct the surface,
then prove first-even slippage extraction and the matching curvature leading law
for its two candidate-minus-baseline deltas. -/
structure SameBenchmarkAnalyticSurfaceAssumptions
    (F : AMMCoefficientSurface) : Prop where
  slippage_extraction : FirstEvenSlippageExtractionPrinciple F.slipDelta
  curvature_law : FirstEvenCurvatureLeadingLaw F.slipDelta F.curvDelta

/-- Surface assumptions are exactly the pair-obligation bundle on the surface
deltas. -/
def SameBenchmarkAnalyticSurfaceAssumptions.toPairObligations
    {F : AMMCoefficientSurface}
    (A : SameBenchmarkAnalyticSurfaceAssumptions F) :
    SameBenchmarkAnalyticPairObligations F.slipDelta F.curvDelta where
  slippage_extraction := A.slippage_extraction
  curvature_law := A.curvature_law

/-- Package a coefficient surface and its same-benchmark analytic assumptions
into the function-level obstruction pair. -/
def AMMCoefficientSurface.toFunctionPair
    (F : AMMCoefficientSurface)
    (A : SameBenchmarkAnalyticSurfaceAssumptions F) :
    SameBenchmarkAnalyticFunctionPair where
  baselineSlippage := F.baselineSlippage
  candidateSlippage := F.candidateSlippage
  baselineCurvature := F.baselineCurvature
  candidateCurvature := F.candidateCurvature
  obligations := by
    simpa [AMMCoefficientSurface.slipDelta, AMMCoefficientSurface.curvDelta]
      using A.toPairObligations

/-- Interface for a future raw AMM semantics layer.  It is parameterized over
the raw AMM object type, so this file does not need to commit to a concrete AMM
representation.  A model must state when two raw AMMs share the same analytic
benchmark and must extract a realized coefficient surface with the two checked
surface assumptions. -/
structure RawAMMSemanticsModel (RawAMM : Type) where
  SameBenchmarkAnalytic : RawAMM → RawAMM → Prop
  SurfaceRealizes : RawAMM → RawAMM → AMMCoefficientSurface → Prop
  construct_surface_assumptions :
    ∀ {baseline candidate : RawAMM},
      SameBenchmarkAnalytic baseline candidate →
        ∃ F : AMMCoefficientSurface,
          SurfaceRealizes baseline candidate F ∧
            SameBenchmarkAnalyticSurfaceAssumptions F

/-- The raw-semantics model extracts the exact surface target needed by the
checked obstruction theorem. -/
theorem RawAMMSemanticsModel.exists_surface_assumptions
    {RawAMM : Type} (M : RawAMMSemanticsModel RawAMM)
    {baseline candidate : RawAMM}
    (h : M.SameBenchmarkAnalytic baseline candidate) :
    ∃ F : AMMCoefficientSurface,
      M.SurfaceRealizes baseline candidate F ∧
        SameBenchmarkAnalyticSurfaceAssumptions F :=
  M.construct_surface_assumptions h

/-- Deterministic coefficient extractors for a raw AMM type.  A concrete
semantics layer should provide these by deriving slippage and curvature
coefficient functions from the raw AMM object under one benchmark convention. -/
structure RawAMMCoefficientExtractors (RawAMM : Type) where
  slippage : RawAMM → ℝ → ℝ
  curvature : RawAMM → ℝ → ℝ

/-- The baseline/candidate coefficient surface determined by raw extractors. -/
def RawAMMCoefficientExtractors.surface
    {RawAMM : Type} (E : RawAMMCoefficientExtractors RawAMM)
    (baseline candidate : RawAMM) : AMMCoefficientSurface where
  baselineSlippage := E.slippage baseline
  candidateSlippage := E.slippage candidate
  baselineCurvature := E.curvature baseline
  candidateCurvature := E.curvature candidate

/-- Deterministic raw-semantics model.  This is the preferred future target:
define coefficient extractors once, then prove that every same-benchmark
analytic raw pair has the surface assumptions on the extracted surface. -/
structure ExtractedRawAMMSemanticsModel (RawAMM : Type) where
  SameBenchmarkAnalytic : RawAMM → RawAMM → Prop
  coeffs : RawAMMCoefficientExtractors RawAMM
  surface_assumptions :
    ∀ {baseline candidate : RawAMM},
      SameBenchmarkAnalytic baseline candidate →
        SameBenchmarkAnalyticSurfaceAssumptions
          (coeffs.surface baseline candidate)

/-- The deterministic surface extracted from a baseline/candidate raw pair. -/
def ExtractedRawAMMSemanticsModel.surface
    {RawAMM : Type} (M : ExtractedRawAMMSemanticsModel RawAMM)
    (baseline candidate : RawAMM) : AMMCoefficientSurface :=
  M.coeffs.surface baseline candidate

/-- A deterministic extractor model is a raw-semantics model whose realization
relation is equality with the extracted surface. -/
def ExtractedRawAMMSemanticsModel.toRawAMMSemanticsModel
    {RawAMM : Type} (M : ExtractedRawAMMSemanticsModel RawAMM) :
    RawAMMSemanticsModel RawAMM where
  SameBenchmarkAnalytic := M.SameBenchmarkAnalytic
  SurfaceRealizes := fun baseline candidate F =>
    F = M.surface baseline candidate
  construct_surface_assumptions := by
    intro baseline candidate h
    exact ⟨M.surface baseline candidate, rfl, by
      simpa [ExtractedRawAMMSemanticsModel.surface] using
        M.surface_assumptions h⟩

/-- The next concrete global-theorem target.  A proof of this object from raw AMM
semantics must supply coefficient functions from one benchmark/coordinate, a
first-even slippage extraction principle, and the matching curvature leading
law.  This structure is a formal assumption boundary, not a claim that arbitrary
AMMs satisfy those obligations. -/
structure ConcreteSameBenchmarkAnalyticAMMPair where
  baselineSlippage : ℝ → ℝ
  candidateSlippage : ℝ → ℝ
  baselineCurvature : ℝ → ℝ
  candidateCurvature : ℝ → ℝ
  slippage_extraction :
    FirstEvenSlippageExtractionPrinciple
      (FunctionDelta candidateSlippage baselineSlippage)
  curvature_law :
    FirstEvenCurvatureLeadingLaw
      (FunctionDelta candidateSlippage baselineSlippage)
      (FunctionDelta candidateCurvature baselineCurvature)

/-- Forget the proof obligations and retain only the coefficient-function
surface. -/
def ConcreteSameBenchmarkAnalyticAMMPair.toSurface
    (P : ConcreteSameBenchmarkAnalyticAMMPair) : AMMCoefficientSurface where
  baselineSlippage := P.baselineSlippage
  candidateSlippage := P.candidateSlippage
  baselineCurvature := P.baselineCurvature
  candidateCurvature := P.candidateCurvature

/-- A concrete same-benchmark analytic AMM pair induces the corresponding
surface assumptions. -/
def ConcreteSameBenchmarkAnalyticAMMPair.toSurfaceAssumptions
    (P : ConcreteSameBenchmarkAnalyticAMMPair) :
    SameBenchmarkAnalyticSurfaceAssumptions P.toSurface where
  slippage_extraction := by
    simpa [ConcreteSameBenchmarkAnalyticAMMPair.toSurface,
      AMMCoefficientSurface.slipDelta] using P.slippage_extraction
  curvature_law := by
    simpa [ConcreteSameBenchmarkAnalyticAMMPair.toSurface,
      AMMCoefficientSurface.slipDelta, AMMCoefficientSurface.curvDelta]
      using P.curvature_law

/-- Package a concrete semantic bridge into the existing function-level
same-benchmark analytic pair. -/
def ConcreteSameBenchmarkAnalyticAMMPair.toFunctionPair
    (P : ConcreteSameBenchmarkAnalyticAMMPair) : SameBenchmarkAnalyticFunctionPair where
  baselineSlippage := P.baselineSlippage
  candidateSlippage := P.candidateSlippage
  baselineCurvature := P.baselineCurvature
  candidateCurvature := P.candidateCurvature
  obligations := {
    slippage_extraction := P.slippage_extraction
    curvature_law := P.curvature_law
  }

/-- Package a coefficient surface and its same-benchmark analytic assumptions
into the concrete semantic-boundary object. -/
def AMMCoefficientSurface.toConcretePair
    (F : AMMCoefficientSurface)
    (A : SameBenchmarkAnalyticSurfaceAssumptions F) :
    ConcreteSameBenchmarkAnalyticAMMPair where
  baselineSlippage := F.baselineSlippage
  candidateSlippage := F.candidateSlippage
  baselineCurvature := F.baselineCurvature
  candidateCurvature := F.candidateCurvature
  slippage_extraction := by
    simpa [AMMCoefficientSurface.slipDelta] using A.slippage_extraction
  curvature_law := by
    simpa [AMMCoefficientSurface.slipDelta, AMMCoefficientSurface.curvDelta]
      using A.curvature_law

/-- The concrete semantic bridge constructs a realized function-level
obstruction pair.  This is the exact shape of the future Aristotle/Morph
construction target after raw AMM semantics are formalized. -/
theorem ConcreteSameBenchmarkAnalyticAMMPair.exists_realized_function_pair
    (P : ConcreteSameBenchmarkAnalyticAMMPair) :
    ∃ Q : SameBenchmarkAnalyticFunctionPair,
      P.toSurface.PairRealizes Q := by
  exact ⟨P.toFunctionPair, rfl, rfl, rfl, rfl⟩

/-- A negative first slippage coefficient and the checked `-1/8` leading-ratio
law are exactly a first even Taylor separation. -/
def FirstEvenTaylorCoefficientData.toFirstEvenTaylorSeparation
    {slipDelta curvDelta : ℝ → ℝ}
    (T : FirstEvenTaylorCoefficientData slipDelta curvDelta) :
    FirstEvenTaylorSeparation slipDelta curvDelta where
  order := T.order
  order_pos := T.order_pos
  coeff := -T.slipCoeff
  slipRem := T.slipRem
  curvRem := T.curvRem
  coeff_pos := neg_pos.mpr T.slipCoeff_neg
  slip_decomp := by
    filter_upwards [T.slip_decomp] with d hd
    simpa using hd
  curv_decomp := by
    filter_upwards [T.curv_decomp] with d hd
    simpa using hd
  slip_rem_small := T.slip_rem_small
  curv_rem_small := T.curv_rem_small

/-- The even Taylor payload is a first-separation expansion with basis
`(d^order)^2`. -/
def FirstEvenTaylorSeparation.toFirstSeparationExpansion
    {slipDelta curvDelta : ℝ → ℝ}
    (E : FirstEvenTaylorSeparation slipDelta curvDelta) :
    FirstSeparationExpansion slipDelta curvDelta where
  basis := fun d => (d ^ E.order) ^ 2
  slipRem := E.slipRem
  curvRem := E.curvRem
  coeff := E.coeff
  coeff_pos := E.coeff_pos
  basis_pos := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact sq_pos_of_ne_zero (pow_ne_zero E.order hd)
  slip_decomp := E.slip_decomp
  curv_decomp := E.curv_decomp
  slip_rem_small := E.slip_rem_small
  curv_rem_small := E.curv_rem_small

/-- A first nonzero even Taylor separation refutes global curvature
dominance. -/
theorem FirstEvenTaylorSeparation.not_global_curvature_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (E : FirstEvenTaylorSeparation slipDelta curvDelta) :
    ¬ ∀ d, curvDelta d ≤ 0 :=
  E.toFirstSeparationExpansion.not_global_curvature_no_worse

/-- A first nonzero even Taylor separation rules out simultaneous global
no-worse slippage and curvature deltas. -/
theorem FirstEvenTaylorSeparation.not_simultaneous_global_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (E : FirstEvenTaylorSeparation slipDelta curvDelta) :
    ¬ ((∀ d, slipDelta d ≤ 0) ∧ (∀ d, curvDelta d ≤ 0)) :=
  E.toFirstSeparationExpansion.not_simultaneous_global_no_worse

/-- Coefficient-facing Taylor data already refutes global curvature
dominance. -/
theorem FirstEvenTaylorCoefficientData.not_global_curvature_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (T : FirstEvenTaylorCoefficientData slipDelta curvDelta) :
    ¬ ∀ d, curvDelta d ≤ 0 :=
  T.toFirstEvenTaylorSeparation.not_global_curvature_no_worse

/-- Coefficient-facing Taylor data already rules out simultaneous global
no-worse slippage and curvature deltas. -/
theorem FirstEvenTaylorCoefficientData.not_simultaneous_global_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (T : FirstEvenTaylorCoefficientData slipDelta curvDelta) :
    ¬ ((∀ d, slipDelta d ≤ 0) ∧ (∀ d, curvDelta d ≤ 0)) :=
  T.toFirstEvenTaylorSeparation.not_simultaneous_global_no_worse

/-- Existential form: if at least one first even Taylor separation certificate
exists, simultaneous global no-worse slippage and curvature are impossible. -/
theorem FirstEvenTaylorSeparation.nonempty_not_simultaneous_global_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (h : Nonempty (FirstEvenTaylorSeparation slipDelta curvDelta)) :
    ¬ ((∀ d, slipDelta d ≤ 0) ∧ (∀ d, curvDelta d ≤ 0)) := by
  rcases h with ⟨E⟩
  exact E.not_simultaneous_global_no_worse

/-- Existential coefficient-data form: if analytic extraction can produce at
least one coefficient-facing Taylor certificate, simultaneous global no-worse
slippage and curvature are impossible. -/
theorem FirstEvenTaylorCoefficientData.nonempty_not_simultaneous_global_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (h : Nonempty (FirstEvenTaylorCoefficientData slipDelta curvDelta)) :
    ¬ ((∀ d, slipDelta d ≤ 0) ∧ (∀ d, curvDelta d ≤ 0)) := by
  rcases h with ⟨T⟩
  exact T.not_simultaneous_global_no_worse

/-- The remaining AMM-specific analytic obligation as an explicit extraction
principle.  It says: whenever slippage is globally no worse and strictly better
somewhere, the AMM assumptions can construct the coefficient-facing Taylor
certificate. -/
structure FirstEvenTaylorExtractionPrinciple (slipDelta curvDelta : ℝ → ℝ) :
    Prop where
  construct :
    DeltaNoWorse slipDelta →
    DeltaStrictlyBetterSomewhere slipDelta →
      Nonempty (FirstEvenTaylorCoefficientData slipDelta curvDelta)

/-- The two smaller analytic obligations imply the coefficient-facing Taylor
extraction principle. -/
theorem FirstEvenTaylorExtractionPrinciple.of_slippage_extraction_and_curvature_law
    {slipDelta curvDelta : ℝ → ℝ}
    (S : FirstEvenSlippageExtractionPrinciple slipDelta)
    (C : FirstEvenCurvatureLeadingLaw slipDelta curvDelta) :
    FirstEvenTaylorExtractionPrinciple slipDelta curvDelta where
  construct hslip_no_worse hslip_strict := by
    rcases S.construct hslip_no_worse hslip_strict with ⟨Sdata⟩
    rcases C.match_first Sdata with ⟨curvRem, hcurv_decomp, hcurv_small⟩
    exact ⟨{
      order := Sdata.order
      order_pos := Sdata.order_pos
      slipCoeff := Sdata.slipCoeff
      slipCoeff_neg := Sdata.slipCoeff_neg
      slipRem := Sdata.slipRem
      curvRem := curvRem
      slip_decomp := Sdata.slip_decomp
      curv_decomp := hcurv_decomp
      slip_rem_small := Sdata.slip_rem_small
      curv_rem_small := hcurv_small
    }⟩

/-- A concrete coefficient-facing Taylor payload promotes to the abstract
Taylor-extraction principle. -/
def FirstEvenTaylorCoefficientData.toFirstEvenTaylorExtractionPrinciple
    {slipDelta curvDelta : ℝ → ℝ}
    (T : FirstEvenTaylorCoefficientData slipDelta curvDelta) :
    FirstEvenTaylorExtractionPrinciple slipDelta curvDelta :=
  FirstEvenTaylorExtractionPrinciple.of_slippage_extraction_and_curvature_law
    T.toFirstEvenSlippageExtractionPrinciple T.toFirstEvenCurvatureLeadingLaw

/-- If the analytic extraction principle holds, strict global slippage
improvement rules out global curvature no-worse. -/
theorem FirstEvenTaylorExtractionPrinciple.not_global_curvature_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (P : FirstEvenTaylorExtractionPrinciple slipDelta curvDelta)
    (hslip_no_worse : DeltaNoWorse slipDelta)
    (hslip_strict : DeltaStrictlyBetterSomewhere slipDelta) :
    ¬ DeltaNoWorse curvDelta := by
  intro hcurv_no_worse
  exact
    (FirstEvenTaylorCoefficientData.nonempty_not_simultaneous_global_no_worse
      (P.construct hslip_no_worse hslip_strict))
      ⟨hslip_no_worse, hcurv_no_worse⟩

/-- Fully bundled obstruction theorem: under the analytic extraction principle,
global no-worse slippage, strict slippage gain, and global no-worse curvature
cannot all hold together. -/
theorem FirstEvenTaylorExtractionPrinciple.not_simultaneous_global_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (P : FirstEvenTaylorExtractionPrinciple slipDelta curvDelta) :
    ¬ DeltaSimultaneousNoWorseWithStrictSlippage slipDelta curvDelta := by
  intro h
  exact P.not_global_curvature_no_worse h.1 h.2.1 h.2.2

/-- Decomposed version of the obstruction theorem: a first-even slippage
extraction principle plus the matching curvature leading law rules out
simultaneous global no-worse slippage and curvature. -/
theorem firstEven_slippage_extraction_and_curvature_law_not_simultaneous_global_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (S : FirstEvenSlippageExtractionPrinciple slipDelta)
    (C : FirstEvenCurvatureLeadingLaw slipDelta curvDelta) :
    ¬ DeltaSimultaneousNoWorseWithStrictSlippage slipDelta curvDelta :=
  (FirstEvenTaylorExtractionPrinciple.of_slippage_extraction_and_curvature_law
    S C).not_simultaneous_global_no_worse

/-- Same-benchmark analytic obligation bundles imply the extraction
principle. -/
theorem SameBenchmarkAnalyticPairObligations.toFirstEvenTaylorExtractionPrinciple
    {slipDelta curvDelta : ℝ → ℝ}
    (A : SameBenchmarkAnalyticPairObligations slipDelta curvDelta) :
    FirstEvenTaylorExtractionPrinciple slipDelta curvDelta :=
  FirstEvenTaylorExtractionPrinciple.of_slippage_extraction_and_curvature_law
    A.slippage_extraction A.curvature_law

/-- From a same-benchmark analytic obligation bundle and the slippage dominance
assumptions, construct the coefficient-facing Taylor certificate. -/
theorem SameBenchmarkAnalyticPairObligations.constructFirstEvenTaylorCoefficientData
    {slipDelta curvDelta : ℝ → ℝ}
    (A : SameBenchmarkAnalyticPairObligations slipDelta curvDelta)
    (hslip_no_worse : DeltaNoWorse slipDelta)
    (hslip_strict : DeltaStrictlyBetterSomewhere slipDelta) :
    Nonempty (FirstEvenTaylorCoefficientData slipDelta curvDelta) :=
  A.toFirstEvenTaylorExtractionPrinciple.construct hslip_no_worse hslip_strict

/-- Same-benchmark analytic obligation bundles turn strict global slippage
improvement into a refutation of global curvature no-worse. -/
theorem SameBenchmarkAnalyticPairObligations.not_global_curvature_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (A : SameBenchmarkAnalyticPairObligations slipDelta curvDelta)
    (hslip_no_worse : DeltaNoWorse slipDelta)
    (hslip_strict : DeltaStrictlyBetterSomewhere slipDelta) :
    ¬ DeltaNoWorse curvDelta :=
  A.toFirstEvenTaylorExtractionPrinciple.not_global_curvature_no_worse
    hslip_no_worse hslip_strict

/-- Final abstract global obstruction surface: once the same-benchmark analytic
obligation bundle is proved for a pair of deltas, simultaneous delta dominance
is impossible. -/
theorem SameBenchmarkAnalyticPairObligations.not_simultaneous_global_no_worse
    {slipDelta curvDelta : ℝ → ℝ}
    (A : SameBenchmarkAnalyticPairObligations slipDelta curvDelta) :
    ¬ DeltaSimultaneousNoWorseWithStrictSlippage slipDelta curvDelta :=
  A.toFirstEvenTaylorExtractionPrinciple.not_simultaneous_global_no_worse

/-- Pair-level certificate construction: once a concrete same-benchmark
analytic AMM pair has supplied the obligation bundle, strict global slippage
gain constructs the first-even Taylor coefficient certificate. -/
theorem SameBenchmarkAnalyticAMMPair.constructFirstEvenTaylorCoefficientData
    (P : SameBenchmarkAnalyticAMMPair)
    (hslip_no_worse : DeltaNoWorse P.slipDelta)
    (hslip_strict : DeltaStrictlyBetterSomewhere P.slipDelta) :
    Nonempty (FirstEvenTaylorCoefficientData P.slipDelta P.curvDelta) :=
  P.obligations.constructFirstEvenTaylorCoefficientData hslip_no_worse hslip_strict

/-- Pair-level curvature refuter: for a concrete same-benchmark analytic AMM
pair satisfying the obligation bundle, strict global slippage gain rules out
global curvature no-worse. -/
theorem SameBenchmarkAnalyticAMMPair.not_global_curvature_no_worse
    (P : SameBenchmarkAnalyticAMMPair)
    (hslip_no_worse : DeltaNoWorse P.slipDelta)
    (hslip_strict : DeltaStrictlyBetterSomewhere P.slipDelta) :
    ¬ DeltaNoWorse P.curvDelta :=
  P.obligations.not_global_curvature_no_worse hslip_no_worse hslip_strict

/-- Final pair-level global obstruction theorem.  This is the theorem a future
concrete AMM semantics proof should be able to use after constructing
`SameBenchmarkAnalyticAMMPair`. -/
theorem SameBenchmarkAnalyticAMMPair.not_simultaneous_global_no_worse
    (P : SameBenchmarkAnalyticAMMPair) :
    ¬ DeltaSimultaneousNoWorseWithStrictSlippage P.slipDelta P.curvDelta :=
  P.obligations.not_simultaneous_global_no_worse

/-- Convert a function-level pair into the delta-level same-benchmark analytic
AMM pair used by the obstruction theorems. -/
def SameBenchmarkAnalyticFunctionPair.toDeltaPair
    (P : SameBenchmarkAnalyticFunctionPair) : SameBenchmarkAnalyticAMMPair where
  slipDelta := FunctionDelta P.candidateSlippage P.baselineSlippage
  curvDelta := FunctionDelta P.candidateCurvature P.baselineCurvature
  obligations := P.obligations

/-- Function-level curvature refuter: once the same-benchmark analytic
obligations are proved for the candidate-minus-baseline deltas, strict global
slippage improvement rules out global curvature no-worse. -/
theorem SameBenchmarkAnalyticFunctionPair.not_global_curvature_no_worse
    (P : SameBenchmarkAnalyticFunctionPair)
    (hslip_no_worse :
      GloballyNoWorse P.candidateSlippage P.baselineSlippage)
    (hslip_strict :
      StrictlyBetterSomewhere P.candidateSlippage P.baselineSlippage) :
    ¬ GloballyNoWorse P.candidateCurvature P.baselineCurvature := by
  intro hcurv_no_worse
  exact
    (P.toDeltaPair.not_simultaneous_global_no_worse)
      (deltaSimultaneous_from_function_dominance
        hslip_no_worse hslip_strict hcurv_no_worse)

/-- Final function-level global obstruction theorem.  This is the version that
uses ordinary baseline/candidate coefficient functions rather than deltas. -/
theorem SameBenchmarkAnalyticFunctionPair.not_simultaneous_global_no_worse
    (P : SameBenchmarkAnalyticFunctionPair) :
    ¬ (GloballyNoWorse P.candidateSlippage P.baselineSlippage ∧
        StrictlyBetterSomewhere P.candidateSlippage P.baselineSlippage ∧
        GloballyNoWorse P.candidateCurvature P.baselineCurvature) := by
  intro h
  exact P.not_global_curvature_no_worse h.1 h.2.1 h.2.2

/-- Surface-level curvature refuter.  Once a coefficient surface has the
same-benchmark analytic assumptions, strict global slippage improvement rules
out global curvature no-worse on that same surface. -/
theorem SameBenchmarkAnalyticSurfaceAssumptions.not_global_curvature_no_worse
    {F : AMMCoefficientSurface}
    (A : SameBenchmarkAnalyticSurfaceAssumptions F)
    (hslip_no_worse :
      GloballyNoWorse F.candidateSlippage F.baselineSlippage)
    (hslip_strict :
      StrictlyBetterSomewhere F.candidateSlippage F.baselineSlippage) :
    ¬ GloballyNoWorse F.candidateCurvature F.baselineCurvature :=
  (F.toFunctionPair A).not_global_curvature_no_worse
    hslip_no_worse hslip_strict

/-- Surface-level global obstruction theorem.  This is the smallest checked
target after raw AMM semantics have produced coefficient functions and the two
same-benchmark analytic assumptions on their deltas. -/
theorem SameBenchmarkAnalyticSurfaceAssumptions.not_simultaneous_global_no_worse
    {F : AMMCoefficientSurface}
    (A : SameBenchmarkAnalyticSurfaceAssumptions F) :
    ¬ (GloballyNoWorse F.candidateSlippage F.baselineSlippage ∧
        StrictlyBetterSomewhere F.candidateSlippage F.baselineSlippage ∧
        GloballyNoWorse F.candidateCurvature F.baselineCurvature) :=
  (F.toFunctionPair A).not_simultaneous_global_no_worse

/-- Any realized surface equipped with the same-benchmark analytic assumptions
inherits the checked global obstruction. -/
theorem RawAMMSemanticsModel.realized_surface_not_simultaneous_global_no_worse
    {RawAMM : Type} (M : RawAMMSemanticsModel RawAMM)
    {baseline candidate : RawAMM} {F : AMMCoefficientSurface}
    (_hrealizes : M.SurfaceRealizes baseline candidate F)
    (A : SameBenchmarkAnalyticSurfaceAssumptions F) :
    ¬ (GloballyNoWorse F.candidateSlippage F.baselineSlippage ∧
        StrictlyBetterSomewhere F.candidateSlippage F.baselineSlippage ∧
        GloballyNoWorse F.candidateCurvature F.baselineCurvature) :=
  A.not_simultaneous_global_no_worse

/-- Raw-semantics consequence: any same-benchmark analytic raw AMM pair has at
least one realized coefficient surface on which the global obstruction holds. -/
theorem RawAMMSemanticsModel.exists_realized_surface_not_simultaneous_global_no_worse
    {RawAMM : Type} (M : RawAMMSemanticsModel RawAMM)
    {baseline candidate : RawAMM}
    (h : M.SameBenchmarkAnalytic baseline candidate) :
    ∃ F : AMMCoefficientSurface,
      M.SurfaceRealizes baseline candidate F ∧
        ¬ (GloballyNoWorse F.candidateSlippage F.baselineSlippage ∧
            StrictlyBetterSomewhere F.candidateSlippage F.baselineSlippage ∧
            GloballyNoWorse F.candidateCurvature F.baselineCurvature) := by
  rcases M.exists_surface_assumptions h with ⟨F, hrealizes, A⟩
  exact ⟨F, hrealizes, M.realized_surface_not_simultaneous_global_no_worse
    hrealizes A⟩

/-- Deterministic extractor consequence: on the surface extracted from a
same-benchmark analytic raw AMM pair, simultaneous slippage improvement and
curvature no-worse are impossible. -/
theorem ExtractedRawAMMSemanticsModel.surface_not_simultaneous_global_no_worse
    {RawAMM : Type} (M : ExtractedRawAMMSemanticsModel RawAMM)
    {baseline candidate : RawAMM}
    (h : M.SameBenchmarkAnalytic baseline candidate) :
    ¬ (GloballyNoWorse (M.surface baseline candidate).candidateSlippage
          (M.surface baseline candidate).baselineSlippage ∧
        StrictlyBetterSomewhere (M.surface baseline candidate).candidateSlippage
          (M.surface baseline candidate).baselineSlippage ∧
        GloballyNoWorse (M.surface baseline candidate).candidateCurvature
          (M.surface baseline candidate).baselineCurvature) := by
  simpa [ExtractedRawAMMSemanticsModel.surface] using
    (M.surface_assumptions h).not_simultaneous_global_no_worse

/-- Deterministic extractor models also satisfy the existential raw model
consequence. -/
theorem ExtractedRawAMMSemanticsModel.exists_realized_surface_not_simultaneous_global_no_worse
    {RawAMM : Type} (M : ExtractedRawAMMSemanticsModel RawAMM)
    {baseline candidate : RawAMM}
    (h : M.SameBenchmarkAnalytic baseline candidate) :
    ∃ F : AMMCoefficientSurface,
      M.toRawAMMSemanticsModel.SurfaceRealizes baseline candidate F ∧
        ¬ (GloballyNoWorse F.candidateSlippage F.baselineSlippage ∧
            StrictlyBetterSomewhere F.candidateSlippage F.baselineSlippage ∧
            GloballyNoWorse F.candidateCurvature F.baselineCurvature) :=
  M.toRawAMMSemanticsModel.exists_realized_surface_not_simultaneous_global_no_worse h

/-- Concrete semantic-bridge curvature refuter.  Once raw AMM semantics have
constructed `ConcreteSameBenchmarkAnalyticAMMPair`, strict global slippage
improvement rules out global curvature no-worse on the same coefficient
surface. -/
theorem ConcreteSameBenchmarkAnalyticAMMPair.not_global_curvature_no_worse
    (P : ConcreteSameBenchmarkAnalyticAMMPair)
    (hslip_no_worse :
      GloballyNoWorse P.candidateSlippage P.baselineSlippage)
    (hslip_strict :
      StrictlyBetterSomewhere P.candidateSlippage P.baselineSlippage) :
    ¬ GloballyNoWorse P.candidateCurvature P.baselineCurvature :=
  P.toFunctionPair.not_global_curvature_no_worse hslip_no_worse hslip_strict

/-- Final concrete semantic-bridge obstruction theorem.  This is not yet the
full raw-AMM theorem; it is the checked theorem that will fire once the concrete
semantics construct the same-benchmark analytic bridge object. -/
theorem ConcreteSameBenchmarkAnalyticAMMPair.not_simultaneous_global_no_worse
    (P : ConcreteSameBenchmarkAnalyticAMMPair) :
    ¬ (GloballyNoWorse P.candidateSlippage P.baselineSlippage ∧
        StrictlyBetterSomewhere P.candidateSlippage P.baselineSlippage ∧
        GloballyNoWorse P.candidateCurvature P.baselineCurvature) :=
  P.toFunctionPair.not_simultaneous_global_no_worse

end

end LocalJetFrontier
end Impossibility
end TauSwap
