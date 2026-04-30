import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Proofs.AMMGlobalCounterexamples

/-!
# AMM global CPMM budget lemmas

This file formalizes the peer-review-driven global AMM budget route.  The
current endpoint is a strong-form CPMM-relative original-HODL no-free-lunch law
under pathwise slippage dominance, together with the normalized invariant bridge
from positive homogeneous AMM surfaces.

Mechanized here:

* invariant-to-normal-form bridge on `(m,d)` coordinates,
* normalized `phi(0) = 0` convention,
* derivative of the smooth same-price log-price state map,
* derivative of the collapsed original-HODL budget,
* strong global same-price CPMM no-free-lunch theorem.

Still open: the final sharp interval/pathwise theorem surface starting directly
from arbitrary smooth symmetric homogeneous AMM data with the minimum reviewed
hypotheses.
-/

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

open Real

/-- Same-price log-price state map written in terms of the defect field `s`. -/
def qOfState (s : ℝ → ℝ) (d : ℝ) : ℝ :=
  2 * d + Real.log (1 - s d) - Real.log (1 + s d)

/-- Collapsed original-HODL value budget suggested by the peer-review route. -/
def collapsedBudget (n : ℝ) (phi s : ℝ → ℝ) (d : ℝ) : ℝ :=
  phi d / n + (1 / 2 : ℝ) * Real.log (1 - (s d) ^ 2)

/-- Candidate original-HODL value ratio written in the same-price `q`-coordinate. -/
def candidateOriginalHODLValueRatio (n : ℝ) (phi s : ℝ → ℝ) (d : ℝ) : ℝ :=
  Real.exp (-(phi d) / n) *
    (Real.exp (qOfState s d - d) + Real.exp d) /
    (Real.exp (qOfState s d) + 1)

/-- CPMM original-HODL value ratio as a function of log price. -/
def cpmmOriginalHODLValueRatio (q : ℝ) : ℝ :=
  2 * Real.exp (q / 2) / (Real.exp q + 1)

/-- Log-invariant of a positive AMM surface pulled back to log-reserve
coordinates. -/
def logInvariantOf (K : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  Real.log (K (Real.exp u) (Real.exp v))

/-- Raw imbalance potential obtained by restricting the log-invariant to the
asset-symmetric slice. -/
def rawImbalancePotential (K : ℝ → ℝ → ℝ) (d : ℝ) : ℝ :=
  Real.log (K (Real.exp (-d)) (Real.exp d))

/-- Normalized imbalance potential, shifted so the balance point is zero. -/
def normalizedImbalancePotential (K : ℝ → ℝ → ℝ) (d : ℝ) : ℝ :=
  rawImbalancePotential K d - rawImbalancePotential K 0

/-- Normalized log-invariant in log coordinates. -/
def normalizedLogInvariantOf (K : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  logInvariantOf K u v - rawImbalancePotential K 0

/-- A positive homogeneous invariant induces the expected one-dimensional log
normal form on the `(m,d)` coordinates. -/
theorem homogeneous_to_log_normalForm
    {K : ℝ → ℝ → ℝ} {n m d : ℝ}
    (hhom : ∀ t x y : ℝ, 0 < t -> K (t * x) (t * y) = t ^ n * K x y)
    (hpos : ∀ x y : ℝ, 0 < x -> 0 < y -> 0 < K x y) :
    logInvariantOf K (m - d) (m + d) = n * m + rawImbalancePotential K d := by
  have hm_pos : 0 < Real.exp m := Real.exp_pos m
  have hslice_pos : 0 < K (Real.exp (-d)) (Real.exp d) := by
    exact hpos _ _ (Real.exp_pos (-d)) (Real.exp_pos d)
  have hpow_pos : 0 < (Real.exp m) ^ n := by
    exact Real.rpow_pos_of_pos hm_pos n
  have hleft :
      K (Real.exp (m - d)) (Real.exp (m + d)) =
        (Real.exp m) ^ n * K (Real.exp (-d)) (Real.exp d) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
    simpa [mul_assoc] using hhom (Real.exp m) (Real.exp (-d)) (Real.exp d) hm_pos
  unfold logInvariantOf rawImbalancePotential
  rw [hleft, Real.log_mul hpow_pos.ne' hslice_pos.ne']
  rw [Real.log_rpow hm_pos, Real.log_exp]

/-- After normalization at the balanced slice, the homogeneous log-invariant
has exact normal form `n*m + phi(d)` with `phi(0)=0`. -/
theorem homogeneous_to_normalizedLogNormalForm
    {K : ℝ → ℝ → ℝ} {n m d : ℝ}
    (hhom : ∀ t x y : ℝ, 0 < t -> K (t * x) (t * y) = t ^ n * K x y)
    (hpos : ∀ x y : ℝ, 0 < x -> 0 < y -> 0 < K x y) :
    normalizedLogInvariantOf K (m - d) (m + d) =
      n * m + normalizedImbalancePotential K d := by
  unfold normalizedLogInvariantOf normalizedImbalancePotential
  rw [homogeneous_to_log_normalForm hhom hpos]
  ring

/-- The normalized imbalance potential vanishes at balance. -/
lemma normalizedImbalancePotential_zero {K : ℝ → ℝ → ℝ} :
    normalizedImbalancePotential K 0 = 0 := by
  unfold normalizedImbalancePotential
  ring

/-- Asset symmetry makes the imbalance potential an even function. -/
theorem rawImbalancePotential_even
    {K : ℝ → ℝ → ℝ}
    (hsymm : ∀ x y : ℝ, K x y = K y x) :
    Function.Even (rawImbalancePotential K) := by
  intro d
  unfold rawImbalancePotential
  calc
    Real.log (K (Real.exp (-(-d))) (Real.exp (-d)))
        = Real.log (K (Real.exp d) (Real.exp (-d))) := by simp
    _ = Real.log (K (Real.exp (-d)) (Real.exp d)) := by rw [hsymm]
    _ = rawImbalancePotential K d := by rfl

/-- Asset symmetry also makes the normalized imbalance potential even. -/
theorem normalizedImbalancePotential_even
    {K : ℝ → ℝ → ℝ}
    (hsymm : ∀ x y : ℝ, K x y = K y x) :
    Function.Even (normalizedImbalancePotential K) := by
  intro d
  unfold normalizedImbalancePotential
  rw [rawImbalancePotential_even hsymm d]

/-- Under the positive-domain assumptions, the state-price map exponentiates to
the rational defect ratio. -/
lemma exp_qOfState_sub_two_mul
    {s : ℝ → ℝ} {d : ℝ}
    (hminus : 0 < 1 - s d)
    (hplus : 0 < 1 + s d) :
    Real.exp (qOfState s d - 2 * d) = (1 - s d) / (1 + s d) := by
  unfold qOfState
  have hrewrite :
      (2 * d + Real.log (1 - s d) - Real.log (1 + s d)) - 2 * d =
        Real.log (1 - s d) - Real.log (1 + s d) := by
    ring
  rw [hrewrite, Real.exp_sub, Real.exp_log hminus, Real.exp_log hplus]

/-- Half-exponent version of the same-price map. -/
lemma exp_half_log_eq_sqrt {x : ℝ} (hx : 0 < x) :
    Real.exp (((1 : ℝ) / 2) * Real.log x) = Real.sqrt x := by
  rw [← Real.log_rpow hx ((1 : ℝ) / 2), Real.exp_log (Real.rpow_pos_of_pos hx _),
    Real.sqrt_eq_rpow]

/-- Under the positive-domain assumptions, the half-price exponentiates to the
square-root defect ratio. -/
lemma exp_qOfState_half_sub
    {s : ℝ → ℝ} {d : ℝ}
    (hminus : 0 < 1 - s d)
    (hplus : 0 < 1 + s d) :
    Real.exp (qOfState s d / 2 - d) =
      Real.sqrt (1 - s d) / Real.sqrt (1 + s d) := by
  unfold qOfState
  have hrewrite :
      (2 * d + Real.log (1 - s d) - Real.log (1 + s d)) / 2 - d =
        ((1 : ℝ) / 2) * Real.log (1 - s d) -
          ((1 : ℝ) / 2) * Real.log (1 + s d) := by
    ring
  rw [hrewrite, Real.exp_sub, exp_half_log_eq_sqrt hminus, exp_half_log_eq_sqrt hplus]

/-- Factorized same-price value identity for the candidate-vs-CPMM ratio. -/
lemma candidate_vs_cpmm_value_ratio_factorized
    {n : ℝ} {phi s : ℝ → ℝ} {d : ℝ}
    (hminus : 0 < 1 - s d)
    (hplus : 0 < 1 + s d) :
    candidateOriginalHODLValueRatio n phi s d /
        cpmmOriginalHODLValueRatio (qOfState s d) =
      Real.exp (-(phi d) / n) /
        (Real.sqrt (1 - s d) * Real.sqrt (1 + s d)) := by
  have hqhalf :
      Real.exp (qOfState s d / 2) =
        Real.exp d * (Real.sqrt (1 - s d) / Real.sqrt (1 + s d)) := by
    calc
      Real.exp (qOfState s d / 2) = Real.exp ((qOfState s d / 2 - d) + d) := by
        congr 1
        ring
      _ = Real.exp (qOfState s d / 2 - d) * Real.exp d := by
        rw [Real.exp_add]
      _ = (Real.sqrt (1 - s d) / Real.sqrt (1 + s d)) * Real.exp d := by
        rw [exp_qOfState_half_sub (s := s) (d := d) hminus hplus]
      _ = Real.exp d * (Real.sqrt (1 - s d) / Real.sqrt (1 + s d)) := by
        ring
  have hq : Real.exp (qOfState s d - 2 * d) = (1 - s d) / (1 + s d) :=
    exp_qOfState_sub_two_mul (s := s) (d := d) hminus hplus
  have hqsub :
      Real.exp (qOfState s d - d) =
        Real.exp d * ((1 - s d) / (1 + s d)) := by
    calc
      Real.exp (qOfState s d - d) = Real.exp ((qOfState s d - 2 * d) + d) := by
        congr 1
        ring
      _ = Real.exp (qOfState s d - 2 * d) * Real.exp d := by
        rw [Real.exp_add]
      _ = ((1 - s d) / (1 + s d)) * Real.exp d := by
        rw [hq]
      _ = Real.exp d * ((1 - s d) / (1 + s d)) := by
        ring
  unfold candidateOriginalHODLValueRatio cpmmOriginalHODLValueRatio
  have hexp_ne : Real.exp (qOfState s d) + 1 ≠ 0 := by positivity
  have hqhalf_ne : (2 * Real.exp (qOfState s d / 2) / (Real.exp (qOfState s d) + 1)) ≠ 0 := by
    positivity
  field_simp [hexp_ne, hqhalf_ne]
  rw [hqsub, hqhalf]
  field_simp [ne_of_gt hplus, ne_of_gt (Real.sqrt_pos.2 hminus),
    ne_of_gt (Real.sqrt_pos.2 hplus)]
  rw [sq_sqrt (le_of_lt hplus)]
  ring

/-- The same-price candidate-vs-CPMM ratio is exactly the exponential of the
negative collapsed budget. -/
lemma candidate_vs_cpmm_value_ratio_eq_exp_neg_collapsedBudget
    {n : ℝ} {phi s : ℝ → ℝ} {d : ℝ}
    (hminus : 0 < 1 - s d)
    (hplus : 0 < 1 + s d) :
    candidateOriginalHODLValueRatio n phi s d /
        cpmmOriginalHODLValueRatio (qOfState s d) =
      Real.exp (-(collapsedBudget n phi s d)) := by
  have harg_pos : 0 < 1 - (s d) ^ 2 := by
    nlinarith [hminus, hplus]
  have hsqrt_mul :
      Real.sqrt (1 - s d) * Real.sqrt (1 + s d) =
        Real.sqrt (1 - (s d) ^ 2) := by
    rw [← Real.sqrt_mul (le_of_lt hminus) (1 + s d)]
    congr 1
    ring
  calc
    candidateOriginalHODLValueRatio n phi s d /
        cpmmOriginalHODLValueRatio (qOfState s d)
        =
          Real.exp (-(phi d) / n) /
            (Real.sqrt (1 - s d) * Real.sqrt (1 + s d)) :=
      candidate_vs_cpmm_value_ratio_factorized (n := n) (phi := phi) (s := s) (d := d)
        hminus hplus
    _ = Real.exp (-(phi d) / n) / Real.sqrt (1 - (s d) ^ 2) := by
      rw [hsqrt_mul]
    _ = Real.exp (-(phi d) / n) /
          Real.exp (((1 : ℝ) / 2) * Real.log (1 - (s d) ^ 2)) := by
      rw [exp_half_log_eq_sqrt harg_pos]
    _ = Real.exp (-(phi d) / n - (((1 : ℝ) / 2) * Real.log (1 - (s d) ^ 2))) := by
      rw [← Real.exp_sub]
    _ = Real.exp (-(collapsedBudget n phi s d)) := by
      unfold collapsedBudget
      congr 1
      ring

/-- A nonnegative collapsed budget forces the candidate same-price value ratio
to be no better than CPMM. -/
lemma candidate_vs_cpmm_value_ratio_le_one_of_budget_nonneg
    {n : ℝ} {phi s : ℝ → ℝ} {d : ℝ}
    (hminus : 0 < 1 - s d)
    (hplus : 0 < 1 + s d)
    (hbudget : 0 ≤ collapsedBudget n phi s d) :
    candidateOriginalHODLValueRatio n phi s d /
        cpmmOriginalHODLValueRatio (qOfState s d) ≤ 1 := by
  rw [candidate_vs_cpmm_value_ratio_eq_exp_neg_collapsedBudget
    (n := n) (phi := phi) (s := s) (d := d) hminus hplus]
  exact Real.exp_le_one_iff.mpr (by linarith)

/-- A strictly positive collapsed budget forces strict same-price value loss
against CPMM. -/
lemma candidate_vs_cpmm_value_ratio_lt_one_of_budget_pos
    {n : ℝ} {phi s : ℝ → ℝ} {d : ℝ}
    (hminus : 0 < 1 - s d)
    (hplus : 0 < 1 + s d)
    (hbudget : 0 < collapsedBudget n phi s d) :
    candidateOriginalHODLValueRatio n phi s d /
        cpmmOriginalHODLValueRatio (qOfState s d) < 1 := by
  rw [candidate_vs_cpmm_value_ratio_eq_exp_neg_collapsedBudget
    (n := n) (phi := phi) (s := s) (d := d) hminus hplus]
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-- Pointwise derivative of the same-price log-price map. -/
lemma hasDerivAt_qOfState_at
    {s : ℝ → ℝ} {d sval sderiv : ℝ}
    (hvalue : s d = sval)
    (hderiv : HasDerivAt s sderiv d)
    (hminus : 1 - sval ≠ 0)
    (hplus : 1 + sval ≠ 0) :
    HasDerivAt (qOfState s)
      (2 - sderiv / (1 - sval) - sderiv / (1 + sval)) d := by
  have hlinear : HasDerivAt (fun t : ℝ => 2 * t) 2 d := by
    simpa using (hasDerivAt_id d).const_mul (2 : ℝ)
  have hminus_arg : HasDerivAt (fun t : ℝ => 1 - s t) (-sderiv) d := by
    simpa using (hasDerivAt_const d (1 : ℝ)).sub hderiv
  have hminus_log :
      HasDerivAt (fun t : ℝ => Real.log (1 - s t))
        (-sderiv / (1 - sval)) d := by
    simpa [hvalue] using hminus_arg.log (by simpa [hvalue] using hminus)
  have hplus_arg : HasDerivAt (fun t : ℝ => 1 + s t) sderiv d := by
    simpa using hderiv.const_add 1
  have hplus_log :
      HasDerivAt (fun t : ℝ => Real.log (1 + s t))
        (sderiv / (1 + sval)) d := by
    simpa [hvalue] using hplus_arg.log (by simpa [hvalue] using hplus)
  unfold qOfState
  convert (hlinear.add hminus_log).sub hplus_log using 1
  ring

/-- Algebraic simplification of the same-price log-price derivative. -/
lemma qOfState_deriv_simplified
    {sval sderiv : ℝ}
    (harg : 1 - sval ^ 2 ≠ 0) :
    2 - sderiv / (1 - sval) - sderiv / (1 + sval) =
      2 - 2 * sderiv / (1 - sval ^ 2) := by
  have hminus : 1 - sval ≠ 0 := by
    intro hz
    apply harg
    have hsval : sval = 1 := by linarith
    nlinarith [hsval]
  have hplus : 1 + sval ≠ 0 := by
    intro hz
    apply harg
    have hsval : sval = -1 := by linarith
    nlinarith [hsval]
  field_simp [harg, hminus, hplus]
  ring

/-- Pointwise derivative of the collapsed budget. -/
lemma hasDerivAt_collapsedBudget_at
    {n : ℝ} {phi s : ℝ → ℝ} {d phideriv sval sderiv : ℝ}
    (hn : n ≠ 0)
    (hphi : HasDerivAt phi phideriv d)
    (hvalue : s d = sval)
    (hderiv : HasDerivAt s sderiv d)
    (harg : 1 - sval ^ 2 ≠ 0) :
    HasDerivAt (collapsedBudget n phi s)
      (phideriv / n - sval * sderiv / (1 - sval ^ 2)) d := by
  have hphi_div : HasDerivAt (fun t : ℝ => phi t / n) (phideriv / n) d := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hphi.const_mul (n⁻¹)
  have hsq : HasDerivAt (fun t : ℝ => (s t) ^ 2) (2 * sval * sderiv) d := by
    simpa [hvalue, two_mul, mul_comm, mul_left_comm, mul_assoc] using hderiv.pow 2
  have harg_deriv : HasDerivAt (fun t : ℝ => 1 - (s t) ^ 2) (-(2 * sval * sderiv)) d := by
    simpa [hvalue] using (hasDerivAt_const d (1 : ℝ)).sub hsq
  have hlog : HasDerivAt (fun t : ℝ => Real.log (1 - (s t) ^ 2))
      (-(2 * sval * sderiv) / (1 - sval ^ 2)) d := by
    simpa [hvalue] using harg_deriv.log (by simpa [hvalue] using harg)
  have hhalf_log :
      HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 - (s t) ^ 2))
        ((1 / 2 : ℝ) * (-(2 * sval * sderiv) / (1 - sval ^ 2))) d := by
    simpa using hlog.const_mul (1 / 2 : ℝ)
  unfold collapsedBudget
  convert hphi_div.add hhalf_log using 1
  have harg2 : 1 - sval ^ 2 ≠ 0 := harg
  field_simp [harg2]
  ring

/-- If `phi' = n * s`, the collapsed budget derivative takes the clean
review-form `s * q' / 2`. -/
lemma hasDerivAt_collapsedBudget_from_normalForm
    {n : ℝ} {phi s : ℝ → ℝ} {d sval sderiv : ℝ}
    (hn : n ≠ 0)
    (hphi : HasDerivAt phi (n * sval) d)
    (hvalue : s d = sval)
    (hderiv : HasDerivAt s sderiv d)
    (harg : 1 - sval ^ 2 ≠ 0) :
    HasDerivAt (collapsedBudget n phi s)
      (sval * (2 - 2 * sderiv / (1 - sval ^ 2)) / 2) d := by
  have hbase :=
    hasDerivAt_collapsedBudget_at
      (n := n) (phi := phi) (s := s)
      hn hphi hvalue hderiv harg
  have hcoeff :
      (n * sval) / n - sval * sderiv / (1 - sval ^ 2) =
        sval * (2 - 2 * sderiv / (1 - sval ^ 2)) / 2 := by
    field_simp [hn, harg]
  simpa [hcoeff] using hbase

/-- Derivative identity for the collapsed budget in terms of the same-price
log-price derivative. -/
lemma deriv_collapsedBudget_eq_half_mul_deriv_qOfState
    {n : ℝ} {phi s : ℝ → ℝ} {d sval sderiv : ℝ}
    (hn : n ≠ 0)
    (hphi : HasDerivAt phi (n * sval) d)
    (hvalue : s d = sval)
    (hderiv : HasDerivAt s sderiv d)
    (harg : 1 - sval ^ 2 ≠ 0) :
    deriv (collapsedBudget n phi s) d =
      sval * deriv (qOfState s) d / 2 := by
  have hq :
      HasDerivAt (qOfState s)
        (2 - sderiv / (1 - sval) - sderiv / (1 + sval)) d :=
    hasDerivAt_qOfState_at hvalue hderiv
      (by
        intro hz
        apply harg
        have hsval : sval = 1 := by linarith
        nlinarith [hsval])
      (by
        intro hz
        apply harg
        have hsval : sval = -1 := by linarith
        nlinarith [hsval])
  have hq' :
      deriv (qOfState s) d = 2 - 2 * sderiv / (1 - sval ^ 2) := by
    rw [hq.deriv, qOfState_deriv_simplified harg]
  rw [hq']
  exact (hasDerivAt_collapsedBudget_from_normalForm
    (n := n) (phi := phi) (s := s)
    hn hphi hvalue hderiv harg).deriv

/-- Pathwise slippage dominance against CPMM forces the defect derivative to be
nonnegative. -/
lemma deriv_nonneg_of_deriv_qOfState_le_two
    {s : ℝ → ℝ} {x : ℝ}
    (hs : DifferentiableAt ℝ s x)
    (hbounded : (s x) ^ 2 < 1)
    (hq_le_two : deriv (qOfState s) x ≤ 2) :
    0 ≤ deriv s x := by
  have hminus : 1 - s x ≠ 0 := by
    intro hz
    nlinarith [hbounded, hz]
  have hplus : 1 + s x ≠ 0 := by
    intro hz
    nlinarith [hbounded, hz]
  have harg : 1 - (s x) ^ 2 ≠ 0 := by
    nlinarith [hbounded]
  have hq_formula :
      deriv (qOfState s) x = 2 - 2 * deriv s x / (1 - (s x) ^ 2) := by
    rw [((hasDerivAt_qOfState_at (d := x) (sval := s x) (sderiv := deriv s x)
      rfl hs.hasDerivAt hminus hplus)).deriv, qOfState_deriv_simplified harg]
  have hden_pos : 0 < 1 - (s x) ^ 2 := by
    nlinarith [hbounded]
  have hineq : 2 - 2 * deriv s x / (1 - (s x) ^ 2) ≤ 2 := by
    simpa [hq_formula] using hq_le_two
  set z : ℝ := 2 * deriv s x / (1 - (s x) ^ 2)
  have hzineq : 2 - z ≤ 2 := by
    simpa [z] using hineq
  have hz_nonneg : 0 ≤ z := by
    linarith
  have hz_eq : z = 2 * (deriv s x / (1 - (s x) ^ 2)) := by
    unfold z
    ring_nf
  have hfrac_nonneg : 0 ≤ deriv s x / (1 - (s x) ^ 2) := by
    nlinarith [hz_nonneg, hz_eq]
  have hmul_nonneg :
      0 ≤ (deriv s x / (1 - (s x) ^ 2)) * (1 - (s x) ^ 2) := by
    exact mul_nonneg hfrac_nonneg (le_of_lt hden_pos)
  have hderiv_nonneg : 0 ≤ deriv s x := by
    have hmul_nonneg' := hmul_nonneg
    field_simp [harg] at hmul_nonneg'
    simpa using hmul_nonneg'
  exact hderiv_nonneg

/-- Under global pathwise slippage dominance against CPMM on the positive half-line,
the collapsed budget is nonnegative. This is a strong-hypothesis monotonicity
form of the reviewed global route, not yet the final sharp theorem. -/
theorem collapsedBudget_nonneg_on_Ici_of_pathwise_slippage
    {n : ℝ} {phi s : ℝ → ℝ}
    (hn : n ≠ 0)
    (hs : Differentiable ℝ s)
    (hphi : ∀ x, HasDerivAt phi (n * s x) x)
    (hbounded : ∀ x, (s x) ^ 2 < 1)
    (hq_nonneg : ∀ x, 0 ≤ deriv (qOfState s) x)
    (hq_le_two : ∀ x, deriv (qOfState s) x ≤ 2)
    (hs0 : s 0 = 0)
    (hphi0 : phi 0 = 0) :
    ∀ x, 0 ≤ x → 0 ≤ collapsedBudget n phi s x := by
  have hmono_s : Monotone s :=
    monotone_of_deriv_nonneg hs fun x =>
      deriv_nonneg_of_deriv_qOfState_le_two (hs := hs x) (hbounded := hbounded x)
        (hq_le_two := hq_le_two x)
  have hs_nonneg : ∀ x, 0 ≤ x → 0 ≤ s x := by
    intro x hx
    have hsx : s 0 ≤ s x := hmono_s hx
    simpa [hs0] using hsx
  have hbudget_diff : Differentiable ℝ (collapsedBudget n phi s) := by
    intro x
    exact (hasDerivAt_collapsedBudget_from_normalForm
      (n := n) (phi := phi) (s := s) (d := x)
      (sval := s x) (sderiv := deriv s x)
      hn (hphi x) rfl (hs x).hasDerivAt (by nlinarith [hbounded x])).differentiableAt
  have hmono_budget : MonotoneOn (collapsedBudget n phi s) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    · exact hbudget_diff.continuous.continuousOn
    · exact hbudget_diff.differentiableOn
    · intro x hx
      rw [deriv_collapsedBudget_eq_half_mul_deriv_qOfState
        (n := n) (phi := phi) (s := s) (d := x)
        (sval := s x) (sderiv := deriv s x)
        hn (hphi x) rfl (hs x).hasDerivAt (by nlinarith [hbounded x])]
      have hx' : 0 < x := by
        simpa [interior_Ici] using hx
      have hsx : 0 ≤ s x := hs_nonneg x (le_of_lt hx')
      have hqx : 0 ≤ deriv (qOfState s) x := hq_nonneg x
      nlinarith
  have hbudget0 : collapsedBudget n phi s 0 = 0 := by
    simp [collapsedBudget, hs0, hphi0]
  intro x hx
  have hmono0x : collapsedBudget n phi s 0 ≤ collapsedBudget n phi s x :=
    hmono_budget (by simp) hx hx
  simpa [hbudget0] using hmono0x

/-- Strong-form same-price CPMM no-free-lunch theorem on the positive half-line.
This packages the budget monotonicity result into the actual value comparison. -/
theorem cpmm_same_price_no_free_lunch_on_Ici_of_pathwise_slippage
    {n : ℝ} {phi s : ℝ → ℝ}
    (hn : n ≠ 0)
    (hs : Differentiable ℝ s)
    (hphi : ∀ x, HasDerivAt phi (n * s x) x)
    (hbounded : ∀ x, (s x) ^ 2 < 1)
    (hq_nonneg : ∀ x, 0 ≤ deriv (qOfState s) x)
    (hq_le_two : ∀ x, deriv (qOfState s) x ≤ 2)
    (hs0 : s 0 = 0)
    (hphi0 : phi 0 = 0) :
    ∀ x, 0 ≤ x →
      candidateOriginalHODLValueRatio n phi s x ≤
        cpmmOriginalHODLValueRatio (qOfState s x) := by
  intro x hx
  have hminus : 0 < 1 - s x := by
    nlinarith [hbounded x]
  have hplus : 0 < 1 + s x := by
    nlinarith [hbounded x]
  have hbudget_nonneg : 0 ≤ collapsedBudget n phi s x :=
    collapsedBudget_nonneg_on_Ici_of_pathwise_slippage
      (n := n) (phi := phi) (s := s)
      hn hs hphi hbounded hq_nonneg hq_le_two hs0 hphi0 x hx
  have hratio_le :
      candidateOriginalHODLValueRatio n phi s x /
          cpmmOriginalHODLValueRatio (qOfState s x) ≤ 1 :=
    candidate_vs_cpmm_value_ratio_le_one_of_budget_nonneg
      (n := n) (phi := phi) (s := s) (d := x) hminus hplus hbudget_nonneg
  have hcpmm_pos : 0 < cpmmOriginalHODLValueRatio (qOfState s x) := by
    unfold cpmmOriginalHODLValueRatio
    positivity
  simpa using (_root_.div_le_iff₀ hcpmm_pos).mp hratio_le

/-- Strong-hypothesis global budget nonnegativity: under pathwise slippage
dominance against CPMM and the current global regularity assumptions, the
collapsed budget is nonnegative for every state. -/
theorem collapsedBudget_nonneg_of_pathwise_slippage
    {n : ℝ} {phi s : ℝ → ℝ}
    (hn : n ≠ 0)
    (hs : Differentiable ℝ s)
    (hphi : ∀ x, HasDerivAt phi (n * s x) x)
    (hbounded : ∀ x, (s x) ^ 2 < 1)
    (hq_nonneg : ∀ x, 0 ≤ deriv (qOfState s) x)
    (hq_le_two : ∀ x, deriv (qOfState s) x ≤ 2)
    (hs0 : s 0 = 0)
    (hphi0 : phi 0 = 0) :
    ∀ x, 0 ≤ collapsedBudget n phi s x := by
  have hmono_s : Monotone s :=
    monotone_of_deriv_nonneg hs fun x =>
      deriv_nonneg_of_deriv_qOfState_le_two (hs := hs x) (hbounded := hbounded x)
        (hq_le_two := hq_le_two x)
  have hs_nonpos : ∀ x, x ≤ 0 → s x ≤ 0 := by
    intro x hx
    have hsx : s x ≤ s 0 := hmono_s hx
    simpa [hs0] using hsx
  have hbudget_diff : Differentiable ℝ (collapsedBudget n phi s) := by
    intro x
    exact (hasDerivAt_collapsedBudget_from_normalForm
      (n := n) (phi := phi) (s := s) (d := x)
      (sval := s x) (sderiv := deriv s x)
      hn (hphi x) rfl (hs x).hasDerivAt (by nlinarith [hbounded x])).differentiableAt
  have hanti_budget : AntitoneOn (collapsedBudget n phi s) (Set.Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic (0 : ℝ))
    · exact hbudget_diff.continuous.continuousOn
    · exact hbudget_diff.differentiableOn
    · intro x hx
      rw [deriv_collapsedBudget_eq_half_mul_deriv_qOfState
        (n := n) (phi := phi) (s := s) (d := x)
        (sval := s x) (sderiv := deriv s x)
        hn (hphi x) rfl (hs x).hasDerivAt (by nlinarith [hbounded x])]
      have hx' : x < 0 := by
        simpa [interior_Iic] using hx
      have hsx : s x ≤ 0 := hs_nonpos x (le_of_lt hx')
      have hqx : 0 ≤ deriv (qOfState s) x := hq_nonneg x
      nlinarith
  have hbudget0 : collapsedBudget n phi s 0 = 0 := by
    simp [collapsedBudget, hs0, hphi0]
  intro x
  by_cases hx : 0 ≤ x
  · exact collapsedBudget_nonneg_on_Ici_of_pathwise_slippage
      (n := n) (phi := phi) (s := s)
      hn hs hphi hbounded hq_nonneg hq_le_two hs0 hphi0 x hx
  · have hxle : x ≤ 0 := le_of_not_ge hx
    have h0lex : collapsedBudget n phi s 0 ≤ collapsedBudget n phi s x :=
      hanti_budget hxle (by simp) hxle
    simpa [hbudget0] using h0lex

/-- Strong-hypothesis global same-price CPMM no-free-lunch theorem. -/
theorem cpmm_same_price_no_free_lunch_of_pathwise_slippage
    {n : ℝ} {phi s : ℝ → ℝ}
    (hn : n ≠ 0)
    (hs : Differentiable ℝ s)
    (hphi : ∀ x, HasDerivAt phi (n * s x) x)
    (hbounded : ∀ x, (s x) ^ 2 < 1)
    (hq_nonneg : ∀ x, 0 ≤ deriv (qOfState s) x)
    (hq_le_two : ∀ x, deriv (qOfState s) x ≤ 2)
    (hs0 : s 0 = 0)
    (hphi0 : phi 0 = 0) :
    ∀ x,
      candidateOriginalHODLValueRatio n phi s x ≤
        cpmmOriginalHODLValueRatio (qOfState s x) := by
  intro x
  have hminus : 0 < 1 - s x := by
    nlinarith [hbounded x]
  have hplus : 0 < 1 + s x := by
    nlinarith [hbounded x]
  have hbudget_nonneg : 0 ≤ collapsedBudget n phi s x :=
    collapsedBudget_nonneg_of_pathwise_slippage
      (n := n) (phi := phi) (s := s)
      hn hs hphi hbounded hq_nonneg hq_le_two hs0 hphi0 x
  have hratio_le :
      candidateOriginalHODLValueRatio n phi s x /
          cpmmOriginalHODLValueRatio (qOfState s x) ≤ 1 :=
    candidate_vs_cpmm_value_ratio_le_one_of_budget_nonneg
      (n := n) (phi := phi) (s := s) (d := x) hminus hplus hbudget_nonneg
  have hcpmm_pos : 0 < cpmmOriginalHODLValueRatio (qOfState s x) := by
    unfold cpmmOriginalHODLValueRatio
    positivity
  simpa using (_root_.div_le_iff₀ hcpmm_pos).mp hratio_le

/-- Segment-sharpened positive-side budget theorem: to compare CPMM against a
target state `x >= 0`, it is enough to assume the pathwise hypotheses on
`[0, x]` rather than globally. -/
theorem collapsedBudget_nonneg_at_of_pathwise_slippage_on_Icc
    {n : ℝ} {phi s : ℝ → ℝ} {x : ℝ}
    (hx : 0 ≤ x)
    (hn : n ≠ 0)
    (hs : Differentiable ℝ s)
    (hphi : ∀ y, y ∈ Set.Icc 0 x -> HasDerivAt phi (n * s y) y)
    (hbounded : ∀ y, y ∈ Set.Icc 0 x -> (s y) ^ 2 < 1)
    (hq_nonneg : ∀ y, y ∈ Set.Icc 0 x -> 0 ≤ deriv (qOfState s) y)
    (hq_le_two : ∀ y, y ∈ Set.Icc 0 x -> deriv (qOfState s) y ≤ 2)
    (hs0 : s 0 = 0)
    (hphi0 : phi 0 = 0) :
    0 ≤ collapsedBudget n phi s x := by
  have hmono_s : MonotoneOn s (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · exact hs.continuous.continuousOn
    · exact hs.differentiableOn
    · intro y hy
      have hyIcc : y ∈ Set.Icc 0 x := interior_subset hy
      exact deriv_nonneg_of_deriv_qOfState_le_two
        (hs := hs y) (hbounded := hbounded y hyIcc) (hq_le_two := hq_le_two y hyIcc)
  have hs_nonneg : ∀ y, y ∈ Set.Icc 0 x -> 0 ≤ s y := by
    intro y hy
    have hsx : s 0 ≤ s y := hmono_s (by simp [hx]) hy hy.1
    simpa [hs0] using hsx
  have hbudget_diff : DifferentiableOn ℝ (collapsedBudget n phi s) (interior (Set.Icc 0 x)) := by
    intro y hy
    have hyIcc : y ∈ Set.Icc 0 x := interior_subset hy
    exact (hasDerivAt_collapsedBudget_from_normalForm
      (n := n) (phi := phi) (s := s) (d := y)
      (sval := s y) (sderiv := deriv s y)
      hn (hphi y hyIcc) rfl (hs y).hasDerivAt (by nlinarith [hbounded y hyIcc])).differentiableAt.differentiableWithinAt
  have hbudget_cont : ContinuousOn (collapsedBudget n phi s) (Set.Icc 0 x) := by
    intro y hy
    exact (hasDerivAt_collapsedBudget_from_normalForm
      (n := n) (phi := phi) (s := s) (d := y)
      (sval := s y) (sderiv := deriv s y)
      hn (hphi y hy) rfl (hs y).hasDerivAt (by nlinarith [hbounded y hy])).continuousAt.continuousWithinAt
  have hmono_budget : MonotoneOn (collapsedBudget n phi s) (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · exact hbudget_cont
    · exact hbudget_diff
    · intro y hy
      have hyIcc : y ∈ Set.Icc 0 x := interior_subset hy
      rw [deriv_collapsedBudget_eq_half_mul_deriv_qOfState
        (n := n) (phi := phi) (s := s) (d := y)
        (sval := s y) (sderiv := deriv s y)
        hn (hphi y hyIcc) rfl (hs y).hasDerivAt (by nlinarith [hbounded y hyIcc])]
      have hsx : 0 ≤ s y := hs_nonneg y hyIcc
      have hqy : 0 ≤ deriv (qOfState s) y := hq_nonneg y hyIcc
      nlinarith
  have hbudget0 : collapsedBudget n phi s 0 = 0 := by
    simp [collapsedBudget, hs0, hphi0]
  have hmono0x : collapsedBudget n phi s 0 ≤ collapsedBudget n phi s x :=
    hmono_budget (by simp [hx]) (by simp [hx]) hx
  simpa [hbudget0] using hmono0x

/-- Segment-sharpened negative-side budget theorem: to compare CPMM against a
target state `x <= 0`, it is enough to assume the pathwise hypotheses on
`[x, 0]` rather than globally. -/
theorem collapsedBudget_nonneg_at_of_pathwise_slippage_on_Icc_neg
    {n : ℝ} {phi s : ℝ → ℝ} {x : ℝ}
    (hx : x ≤ 0)
    (hn : n ≠ 0)
    (hs : Differentiable ℝ s)
    (hphi : ∀ y, y ∈ Set.Icc x 0 -> HasDerivAt phi (n * s y) y)
    (hbounded : ∀ y, y ∈ Set.Icc x 0 -> (s y) ^ 2 < 1)
    (hq_nonneg : ∀ y, y ∈ Set.Icc x 0 -> 0 ≤ deriv (qOfState s) y)
    (hq_le_two : ∀ y, y ∈ Set.Icc x 0 -> deriv (qOfState s) y ≤ 2)
    (hs0 : s 0 = 0)
    (hphi0 : phi 0 = 0) :
    0 ≤ collapsedBudget n phi s x := by
  have hmono_s : MonotoneOn s (Set.Icc x 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x 0)
    · exact hs.continuous.continuousOn
    · exact hs.differentiableOn
    · intro y hy
      have hyIcc : y ∈ Set.Icc x 0 := interior_subset hy
      exact deriv_nonneg_of_deriv_qOfState_le_two
        (hs := hs y) (hbounded := hbounded y hyIcc) (hq_le_two := hq_le_two y hyIcc)
  have hs_nonpos : ∀ y, y ∈ Set.Icc x 0 -> s y ≤ 0 := by
    intro y hy
    have hsx : s y ≤ s 0 := hmono_s hy (by simp [hx]) hy.2
    simpa [hs0] using hsx
  have hbudget_diff : DifferentiableOn ℝ (collapsedBudget n phi s) (interior (Set.Icc x 0)) := by
    intro y hy
    have hyIcc : y ∈ Set.Icc x 0 := interior_subset hy
    exact (hasDerivAt_collapsedBudget_from_normalForm
      (n := n) (phi := phi) (s := s) (d := y)
      (sval := s y) (sderiv := deriv s y)
      hn (hphi y hyIcc) rfl (hs y).hasDerivAt (by nlinarith [hbounded y hyIcc])).differentiableAt.differentiableWithinAt
  have hbudget_cont : ContinuousOn (collapsedBudget n phi s) (Set.Icc x 0) := by
    intro y hy
    exact (hasDerivAt_collapsedBudget_from_normalForm
      (n := n) (phi := phi) (s := s) (d := y)
      (sval := s y) (sderiv := deriv s y)
      hn (hphi y hy) rfl (hs y).hasDerivAt (by nlinarith [hbounded y hy])).continuousAt.continuousWithinAt
  have hanti_budget : AntitoneOn (collapsedBudget n phi s) (Set.Icc x 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc x 0)
    · exact hbudget_cont
    · exact hbudget_diff
    · intro y hy
      have hyIcc : y ∈ Set.Icc x 0 := interior_subset hy
      rw [deriv_collapsedBudget_eq_half_mul_deriv_qOfState
        (n := n) (phi := phi) (s := s) (d := y)
        (sval := s y) (sderiv := deriv s y)
        hn (hphi y hyIcc) rfl (hs y).hasDerivAt (by nlinarith [hbounded y hyIcc])]
      have hsx : s y ≤ 0 := hs_nonpos y hyIcc
      have hqy : 0 ≤ deriv (qOfState s) y := hq_nonneg y hyIcc
      nlinarith
  have hbudget0 : collapsedBudget n phi s 0 = 0 := by
    simp [collapsedBudget, hs0, hphi0]
  have h0lex : collapsedBudget n phi s 0 ≤ collapsedBudget n phi s x :=
    hanti_budget (by simp [hx]) (by simp [hx]) hx
  simpa [hbudget0] using h0lex

/-- Pathwise sharpening at a single target state `x`: it is enough to assume
the CPMM-dominance hypotheses along the segment `[[0, x]]`. -/
theorem cpmm_same_price_no_free_lunch_at_of_segment_pathwise_slippage
    {n : ℝ} {phi s : ℝ → ℝ} {x : ℝ}
    (hn : n ≠ 0)
    (hs : Differentiable ℝ s)
    (hphi : ∀ y, y ∈ Set.uIcc 0 x -> HasDerivAt phi (n * s y) y)
    (hbounded : ∀ y, y ∈ Set.uIcc 0 x -> (s y) ^ 2 < 1)
    (hq_nonneg : ∀ y, y ∈ Set.uIcc 0 x -> 0 ≤ deriv (qOfState s) y)
    (hq_le_two : ∀ y, y ∈ Set.uIcc 0 x -> deriv (qOfState s) y ≤ 2)
    (hs0 : s 0 = 0)
    (hphi0 : phi 0 = 0) :
    candidateOriginalHODLValueRatio n phi s x ≤
      cpmmOriginalHODLValueRatio (qOfState s x) := by
  have hxmem : x ∈ Set.uIcc 0 x := by simp
  have hminus : 0 < 1 - s x := by
    nlinarith [hbounded x hxmem]
  have hplus : 0 < 1 + s x := by
    nlinarith [hbounded x hxmem]
  have hbudget_nonneg : 0 ≤ collapsedBudget n phi s x := by
    by_cases hx : 0 ≤ x
    · exact collapsedBudget_nonneg_at_of_pathwise_slippage_on_Icc
        (x := x) hx (n := n) (phi := phi) (s := s)
        hn hs
        (fun y hy => hphi y (by simpa [Set.uIcc_of_le hx] using hy))
        (fun y hy => hbounded y (by simpa [Set.uIcc_of_le hx] using hy))
        (fun y hy => hq_nonneg y (by simpa [Set.uIcc_of_le hx] using hy))
        (fun y hy => hq_le_two y (by simpa [Set.uIcc_of_le hx] using hy))
        hs0 hphi0
    · have hx' : x ≤ 0 := le_of_not_ge hx
      exact collapsedBudget_nonneg_at_of_pathwise_slippage_on_Icc_neg
        (x := x) hx' (n := n) (phi := phi) (s := s)
        hn hs
        (fun y hy => hphi y (by simpa [Set.uIcc_of_ge hx'] using hy))
        (fun y hy => hbounded y (by simpa [Set.uIcc_of_ge hx'] using hy))
        (fun y hy => hq_nonneg y (by simpa [Set.uIcc_of_ge hx'] using hy))
        (fun y hy => hq_le_two y (by simpa [Set.uIcc_of_ge hx'] using hy))
        hs0 hphi0
  have hratio_le :
      candidateOriginalHODLValueRatio n phi s x /
          cpmmOriginalHODLValueRatio (qOfState s x) ≤ 1 :=
    candidate_vs_cpmm_value_ratio_le_one_of_budget_nonneg
      (n := n) (phi := phi) (s := s) (d := x) hminus hplus hbudget_nonneg
  have hcpmm_pos : 0 < cpmmOriginalHODLValueRatio (qOfState s x) := by
    unfold cpmmOriginalHODLValueRatio
    positivity
  simpa using (_root_.div_le_iff₀ hcpmm_pos).mp hratio_le

/-- Same global no-free-lunch theorem, but stated with the stricter paper-style
price-path hypothesis `0 < q' <= 2`. -/
theorem cpmm_same_price_no_free_lunch_of_strict_price_pathwise_slippage
    {n : ℝ} {phi s : ℝ → ℝ}
    (hn : n ≠ 0)
    (hs : Differentiable ℝ s)
    (hphi : ∀ x, HasDerivAt phi (n * s x) x)
    (hbounded : ∀ x, (s x) ^ 2 < 1)
    (hq_pos : ∀ x, 0 < deriv (qOfState s) x)
    (hq_le_two : ∀ x, deriv (qOfState s) x ≤ 2)
    (hs0 : s 0 = 0)
    (hphi0 : phi 0 = 0) :
    ∀ x,
      candidateOriginalHODLValueRatio n phi s x ≤
        cpmmOriginalHODLValueRatio (qOfState s x) := by
  exact cpmm_same_price_no_free_lunch_of_pathwise_slippage
    (n := n) (phi := phi) (s := s)
    hn hs hphi hbounded (fun x => le_of_lt (hq_pos x)) hq_le_two hs0 hphi0

/-- Concrete normalized-invariant wrapper: once the defect field `s` and its
normal-form derivative relation are supplied for a positive homogeneous AMM
surface, the strong same-price CPMM no-free-lunch theorem applies to the
normalized imbalance potential directly. -/
theorem cpmm_same_price_no_free_lunch_of_pathwise_slippage_from_normalizedInvariant
    {K : ℝ → ℝ → ℝ} {n : ℝ} {s : ℝ → ℝ}
    (hn : n ≠ 0)
    (hs : Differentiable ℝ s)
    (hphi : ∀ x, HasDerivAt (normalizedImbalancePotential K) (n * s x) x)
    (hbounded : ∀ x, (s x) ^ 2 < 1)
    (hq_nonneg : ∀ x, 0 ≤ deriv (qOfState s) x)
    (hq_le_two : ∀ x, deriv (qOfState s) x ≤ 2)
    (hs0 : s 0 = 0) :
    ∀ x,
      candidateOriginalHODLValueRatio n (normalizedImbalancePotential K) s x ≤
        cpmmOriginalHODLValueRatio (qOfState s x) := by
  exact cpmm_same_price_no_free_lunch_of_pathwise_slippage
    (n := n) (phi := normalizedImbalancePotential K) (s := s)
    hn hs hphi hbounded hq_nonneg hq_le_two hs0
    (normalizedImbalancePotential_zero (K := K))

/-- Paper-style normalized-invariant wrapper with the strict price-path
hypothesis `0 < q' <= 2`. -/
theorem cpmm_same_price_no_free_lunch_of_strict_price_pathwise_slippage_from_normalizedInvariant
    {K : ℝ → ℝ → ℝ} {n : ℝ} {s : ℝ → ℝ}
    (hn : n ≠ 0)
    (hs : Differentiable ℝ s)
    (hphi : ∀ x, HasDerivAt (normalizedImbalancePotential K) (n * s x) x)
    (hbounded : ∀ x, (s x) ^ 2 < 1)
    (hq_pos : ∀ x, 0 < deriv (qOfState s) x)
    (hq_le_two : ∀ x, deriv (qOfState s) x ≤ 2)
    (hs0 : s 0 = 0) :
    ∀ x,
      candidateOriginalHODLValueRatio n (normalizedImbalancePotential K) s x ≤
        cpmmOriginalHODLValueRatio (qOfState s x) := by
  exact cpmm_same_price_no_free_lunch_of_strict_price_pathwise_slippage
    (n := n) (phi := normalizedImbalancePotential K) (s := s)
    hn hs hphi hbounded hq_pos hq_le_two hs0
    (normalizedImbalancePotential_zero (K := K))

/-- Strict positive-side budget theorem: if the balance target is positive and
the pathwise slippage derivative is strictly positive on the open segment from
`0` to `x`, then the collapsed CPMM-comparison budget is strictly positive at
`x`. This is the strict version of
`collapsedBudget_nonneg_at_of_pathwise_slippage_on_Icc`. -/
theorem collapsedBudget_pos_at_of_strict_pathwise_slippage_on_Icc_pos
    {n : ℝ} {phi s : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x)
    (hn : n ≠ 0)
    (hs : Differentiable ℝ s)
    (hphi : ∀ y, y ∈ Set.Icc 0 x -> HasDerivAt phi (n * s y) y)
    (hbounded : ∀ y, y ∈ Set.Icc 0 x -> (s y) ^ 2 < 1)
    (hq_pos : ∀ y, y ∈ Set.Ioo 0 x -> 0 < deriv (qOfState s) y)
    (hs_pos : ∀ y, y ∈ Set.Ioo 0 x -> 0 < s y)
    (hs0 : s 0 = 0)
    (hphi0 : phi 0 = 0) :
    0 < collapsedBudget n phi s x := by
  have h_strict_mono :
      StrictMonoOn (collapsedBudget n phi s) (Set.Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos
    · exact convex_Icc _ _
    · refine ContinuousOn.add ?_ ?_
      · exact ContinuousOn.div_const
          (continuousOn_of_forall_continuousAt fun y hy =>
            HasDerivAt.continuousAt (hphi y hy)) _
      · exact ContinuousOn.mul continuousOn_const <|
          ContinuousOn.log
            (continuousOn_const.sub <| hs.continuous.continuousOn.pow 2)
            fun y hy => by nlinarith [hbounded y hy]
    · intro y hy
      have hyIcc : y ∈ Set.Icc 0 x := interior_subset hy
      have hyIoo : y ∈ Set.Ioo 0 x := by
        simpa [interior_Icc] using hy
      rw [deriv_collapsedBudget_eq_half_mul_deriv_qOfState
        (n := n) (phi := phi) (s := s) (d := y)
        (sval := s y) (sderiv := deriv s y)
        hn (hphi y hyIcc) rfl (hs y).hasDerivAt
        (by nlinarith [hbounded y hyIcc])]
      exact div_pos (mul_pos (hs_pos y hyIoo) (hq_pos y hyIoo)) zero_lt_two
  have hbudget0 : collapsedBudget n phi s 0 = 0 := by
    simp [collapsedBudget, hs0, hphi0]
  have hlt :
      collapsedBudget n phi s 0 < collapsedBudget n phi s x :=
    h_strict_mono (Set.left_mem_Icc.mpr hx.le) (Set.right_mem_Icc.mpr hx.le) hx
  simpa [hbudget0] using hlt

/-- Strict positive-side same-price CPMM theorem: under strict segment-local
pathwise slippage and positive state displacement, the candidate original-HODL
value ratio is strictly lower than CPMM. -/
theorem cpmm_same_price_strict_loss_at_of_strict_segment_pathwise_slippage_pos
    {n : ℝ} {phi s : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x)
    (hn : n ≠ 0)
    (hs : Differentiable ℝ s)
    (hphi : ∀ y, y ∈ Set.Icc 0 x -> HasDerivAt phi (n * s y) y)
    (hbounded : ∀ y, y ∈ Set.Icc 0 x -> (s y) ^ 2 < 1)
    (hq_pos : ∀ y, y ∈ Set.Ioo 0 x -> 0 < deriv (qOfState s) y)
    (hs_pos : ∀ y, y ∈ Set.Ioo 0 x -> 0 < s y)
    (hs0 : s 0 = 0)
    (hphi0 : phi 0 = 0) :
    candidateOriginalHODLValueRatio n phi s x <
      cpmmOriginalHODLValueRatio (qOfState s x) := by
  have hbudget_pos :
      0 < collapsedBudget n phi s x :=
    collapsedBudget_pos_at_of_strict_pathwise_slippage_on_Icc_pos
      hx hn hs hphi hbounded hq_pos hs_pos hs0 hphi0
  have hratio_lt_one :
      candidateOriginalHODLValueRatio n phi s x /
          cpmmOriginalHODLValueRatio (qOfState s x) < 1 := by
    apply candidate_vs_cpmm_value_ratio_lt_one_of_budget_pos
    · nlinarith [hbounded x ⟨hx.le, le_rfl⟩]
    · nlinarith [hbounded x ⟨hx.le, le_rfl⟩]
    · exact hbudget_pos
  rwa [div_lt_one (by unfold cpmmOriginalHODLValueRatio; positivity)] at hratio_lt_one

end
end LocalJetFrontier
end Impossibility
end TauSwap
