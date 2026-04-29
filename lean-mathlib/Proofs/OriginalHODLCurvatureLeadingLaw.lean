import Mathlib

/-!
# Original-HODL Curvature-Leading Law

This file records the reusable coefficient law extracted from the Aristotle
packet `d753aa5e-05fc-493a-acc3-6ddcfa3b6672`.

It proves the non-circular chain-rule bridge:

`slipCoeff = -β*A` and the original-HODL curvature expansion hypotheses imply
`curvCoeff = -slipCoeff / 8`.

The remaining AMM-specific analytic work is intentionally explicit: callers must
provide the leading expansion facts for `δR''`, `δq'`, and `δq''`.  This file
then proves that the `-1/8` coefficient follows from the chain-rule structure
and the CPMM benchmark limits.
-/

open Real Filter Topology

namespace TauSwap
namespace Impossibility
namespace OriginalHODL

set_option maxHeartbeats 8000000

noncomputable section

/-! ## Algebraic core -/

/-- The curvature bracket identity behind the original-HODL `-1/8` law. -/
theorem curvature_bracket_identity (A : ℝ) :
    2 * A ^ 2 - 4 * A - 2 * A * (A - 1) = -2 * A := by
  calc
    2 * A ^ 2 - 4 * A - 2 * A * (A - 1) = -2 * A := by
      ring_nf

/-- From the bracket, the curvature coefficient is `β*A/8`. -/
theorem curvature_coeff_value (β A : ℝ) :
    (-1 / 16 : ℝ) * (-2 * β * A) = β * A / 8 := by
  calc
    (-1 / 16 : ℝ) * (-2 * β * A) = β * A / 8 := by
      ring_nf

/-- `β*A/8 = -(-β*A)/8`, connecting curvature and slippage coefficients. -/
theorem coeff_is_neg_slip_over_8 (β A : ℝ) :
    β * A / 8 = -(- β * A) / 8 := by
  calc
    β * A / 8 = -(- β * A) / 8 := by
      ring_nf

/-- The full coefficient bracket yields `-slipCoeff/8` when
`slipCoeff = -β*A`. -/
theorem full_bracket_calculation (β A : ℝ) :
    (-1 / 16 : ℝ) *
      (2 * (β * A ^ 2) - 2 * (-2 * β * A) * (-1 : ℝ) -
        (-1 : ℝ) * (-2 * β * A * (A - 1))) =
    -(- β * A) / 8 := by
  calc
    (-1 / 16 : ℝ) *
        (2 * (β * A ^ 2) - 2 * (-2 * β * A) * (-1 : ℝ) -
          (-1 : ℝ) * (-2 * β * A * (A - 1))) =
      -(- β * A) / 8 := by
        ring_nf

/-! ## Coefficient extraction from chain-rule limits -/

/-- Product limit with one factor scaled by `d^m`. -/
theorem tendsto_mul_div_pow
    (m : ℕ) (a c : ℝ) (f g : ℝ → ℝ)
    (hf : Tendsto (fun d => f d / d ^ m) (𝓝[≠] (0 : ℝ)) (𝓝 a))
    (hg : Tendsto g (𝓝 (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun d => f d * g d / d ^ m) (𝓝[≠] (0 : ℝ)) (𝓝 (a * c)) := by
  simpa [mul_div_right_comm] using hf.mul (hg.mono_left inf_le_left)

/-- Product limit with orders splitting as `1 + (m - 1) = m`. -/
theorem tendsto_mul_split_pow
    (m : ℕ) (hm : 1 ≤ m) (a c : ℝ) (f g : ℝ → ℝ)
    (hf : Tendsto (fun d => f d / d ^ (m - 1)) (𝓝[≠] (0 : ℝ)) (𝓝 a))
    (hg : Tendsto (fun d => g d / d) (𝓝[≠] (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun d => g d * f d / d ^ m) (𝓝[≠] (0 : ℝ)) (𝓝 (c * a)) := by
  convert hg.mul hf using 2
  cases m with
  | zero => omega
  | succ m =>
      simp [pow_succ', div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- Coefficient extraction for the linearized original-HODL curvature chain-rule
formula.

The linearized curvature delta is

`(-1/16) * (2*f₁ - 2*f₂*g₁ - g₂*f₃)`.

If `f₁`, `f₂`, `f₃`, `g₁`, and `g₂` have the stated leading limits, then the
curvature delta has the corresponding bracket coefficient. -/
theorem coefficient_extraction
    (m : ℕ) (hm : 2 ≤ m)
    (a₁ a₂ a₃ c₁ c₂ : ℝ)
    (f₁ f₂ f₃ g₁ g₂ : ℝ → ℝ)
    (hf₁ : Tendsto (fun d => f₁ d / d ^ m) (𝓝[≠] (0 : ℝ)) (𝓝 a₁))
    (hf₂ : Tendsto (fun d => f₂ d / d ^ m) (𝓝[≠] (0 : ℝ)) (𝓝 a₂))
    (hf₃ : Tendsto (fun d => f₃ d / d ^ (m - 1)) (𝓝[≠] (0 : ℝ)) (𝓝 a₃))
    (hg₁ : Tendsto g₁ (𝓝 (0 : ℝ)) (𝓝 c₁))
    (hg₂ : Tendsto (fun d => g₂ d / d) (𝓝[≠] (0 : ℝ)) (𝓝 c₂)) :
    Tendsto (fun d => (-1 / 16 : ℝ) *
      (2 * f₁ d - 2 * f₂ d * g₁ d - g₂ d * f₃ d) / d ^ m)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((-1 / 16 : ℝ) * (2 * a₁ - 2 * a₂ * c₁ - c₂ * a₃))) := by
  convert
    Tendsto.const_mul (-1 / 16)
      (Tendsto.sub
        (Tendsto.sub
          (hf₁.const_mul 2)
          ((hf₂.const_mul 2).mul (hg₁.mono_left inf_le_left)))
        (hf₃.mul hg₂))
    using 2 <;> ring_nf
  · cases m with
    | zero => omega
    | succ m =>
        simp [pow_succ']
        ring_nf

/-! ## CPMM benchmark limits -/

/-- `sinh(d)/d -> 1` at `d = 0`, from the derivative of `sinh` at zero. -/
private theorem sinh_div_tendsto :
    Tendsto (fun d => Real.sinh d / d) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  simpa [div_eq_inv_mul] using
    (Real.hasDerivAt_sinh 0).tendsto_slope_zero

/-- `1/cosh(d)^2 -> 1` at `d = 0`, by continuity of `cosh`. -/
private theorem inv_cosh_sq_tendsto :
    Tendsto (fun x : ℝ => (Real.cosh x ^ 2)⁻¹)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hcont : ContinuousAt (fun x : ℝ => (Real.cosh x ^ 2)⁻¹) 0 :=
    ContinuousAt.inv₀
      (Continuous.continuousAt (Real.continuous_cosh.pow 2))
      (by norm_num)
  simpa using hcont.tendsto.mono_left inf_le_left

/-- For the CPMM benchmark `R₀(d)=sech(d)`, one has `R₀'(d)/d -> -1`. -/
theorem sech_deriv_ratio_tendsto :
    Tendsto (fun d => -(sinh d / cosh d ^ 2) / d)
      (𝓝[≠] (0 : ℝ)) (𝓝 (-1 : ℝ)) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    (sinh_div_tendsto.mul inv_cosh_sq_tendsto).neg

/-- For the CPMM benchmark `R₀(d)=sech(d)`, one has `R₀''(d) -> -1`. -/
theorem sech_second_deriv_tendsto :
    Tendsto (fun d => (2 * sinh d ^ 2 - cosh d ^ 2) / cosh d ^ 3)
      (𝓝 (0 : ℝ)) (𝓝 (-1 : ℝ)) := by
  convert ContinuousAt.tendsto _ using 2 <;> norm_num
  exact ContinuousAt.div
    (Continuous.continuousAt (by continuity))
    (Continuous.continuousAt (by continuity))
    (by norm_num)

/-! ## Raw metric definitions used by the expansion hypotheses -/

/-- Perturbation potential `phi(d) = b*d^(A+1)/(A+1)`. -/
def hodlPhi (b : ℝ) (A : ℕ) (d : ℝ) : ℝ :=
  b * d ^ (A + 1) / (↑A + 1)

/-- Derivative of perturbation potential `p(d) = b*d^A`. -/
def hodlP (b : ℝ) (A : ℕ) (d : ℝ) : ℝ :=
  b * d ^ A

/-- Log-price offset `q(d) = 2*d + log(n-p(d)) - log(n+p(d))`. -/
def hodlQ (n b : ℝ) (A : ℕ) (d : ℝ) : ℝ :=
  2 * d + log (n - hodlP b A d) - log (n + hodlP b A d)

/-- Mass offset `m(d) = -phi(d)/n`. -/
def hodlM (n b : ℝ) (A : ℕ) (d : ℝ) : ℝ :=
  -(hodlPhi b A d) / n

/-- CPMM benchmark ratio `R₀(d)=sech(d)`. -/
def hodlR₀ (d : ℝ) : ℝ :=
  1 / cosh d

/-- Original-HODL ratio. -/
def hodlR (n b : ℝ) (A : ℕ) (d : ℝ) : ℝ :=
  exp (hodlM n b A d) *
    (exp (hodlQ n b A d - d) + exp d) /
    (exp (hodlQ n b A d) + 1)

/-- Exact closed-form slippage delta used by the monomial perturbation
calculation. -/
def hodlSlipDeltaExact (n b : ℝ) (A : ℕ) (d : ℝ) : ℝ :=
  -(↑A : ℝ) * b * n * d ^ (A - 1) / (n ^ 2 - b ^ 2 * d ^ (2 * A))

/-- Away from zero, the normalized exact slippage delta cancels the common
`d^(A-1)` factor. -/
private theorem slip_cancel_pow (n b : ℝ) (A : ℕ) {d : ℝ} (hd : d ≠ 0) :
    hodlSlipDeltaExact n b A d / d ^ (A - 1) =
      -↑A * b * n / (n ^ 2 - b ^ 2 * d ^ (2 * A)) := by
  unfold hodlSlipDeltaExact
  rw [div_right_comm, mul_div_cancel_right₀ _ (pow_ne_zero _ hd)]

/-- The denominator `n^2 - b^2*d^(2A)` tends to `n^2` as `d -> 0` when
`A` is positive. -/
private theorem slip_denom_tendsto (n b : ℝ) (A : ℕ) (hA : 1 ≤ A) :
    Tendsto (fun d => n ^ 2 - b ^ 2 * d ^ (2 * A))
      (𝓝[≠] (0 : ℝ)) (𝓝 (n ^ 2)) := by
  have hcont : ContinuousAt (fun d : ℝ => n ^ 2 - b ^ 2 * d ^ (2 * A)) 0 := by
    fun_prop
  have h_eval : n ^ 2 - b ^ 2 * (0 : ℝ) ^ (2 * A) = n ^ 2 := by
    simp [zero_pow (by omega : 2 * A ≠ 0)]
  simpa [h_eval] using hcont.tendsto.mono_left inf_le_left

/-- Slippage leading term:
`hodlSlipDeltaExact(d)/d^(A-1) -> -A*b/n`. -/
theorem slip_expansion (n b : ℝ) (A : ℕ) (hn : 0 < n) (hA : 3 ≤ A) :
    Tendsto (fun d => hodlSlipDeltaExact n b A d / d ^ (A - 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-(↑A : ℝ) * b / n)) := by
  have hdenom_ne : (n : ℝ) ^ 2 ≠ 0 := by
    positivity
  have htarget : -(↑A : ℝ) * b / n = -↑A * b * n / n ^ 2 := by
    field_simp [ne_of_gt hn]
  rw [htarget]
  have hcancelled :
      Tendsto
        (fun d => -↑A * b * n / (n ^ 2 - b ^ 2 * d ^ (2 * A)))
        (𝓝[≠] (0 : ℝ)) (𝓝 (-↑A * b * n / n ^ 2)) :=
    Tendsto.div tendsto_const_nhds
      (slip_denom_tendsto n b A (by omega))
      hdenom_ne
  exact hcancelled.congr' (by
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact (slip_cancel_pow n b A hd).symm)

/-! ## Original-HODL `-1/8` coefficient law -/

/-- Original-HODL curvature-leading law from the explicit chain-rule expansion
hypotheses.

This theorem does not assume the target `-1/8` relation.  It assumes the three
raw expansion facts for `δR''`, `δq'`, and `δq''`, then derives the curvature
coefficient from the chain-rule bracket and CPMM benchmark limits. -/
theorem hodl_curvature_leading_law
    (A : ℕ) (hA : 3 ≤ A)
    (β : ℝ) (_hβ : 0 < β)
    (δR'' δq' δq'' : ℝ → ℝ)
    (hδR : Tendsto (fun d => δR'' d / d ^ (A - 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 (β * (↑A : ℝ) ^ 2)))
    (hδq' : Tendsto (fun d => δq' d / d ^ (A - 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-2 * β * (↑A : ℝ))))
    (hδq'' : Tendsto (fun d => δq'' d / d ^ (A - 2))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-2 * β * (↑A : ℝ) * ((↑A : ℝ) - 1)))) :
    Tendsto (fun d => (-1 / 16 : ℝ) *
      (2 * δR'' d -
        2 * δq' d * ((2 * sinh d ^ 2 - cosh d ^ 2) / cosh d ^ 3) -
        (-(sinh d / cosh d ^ 2)) * δq'' d) / d ^ (A - 1))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-(-β * (↑A : ℝ)) / 8)) := by
  have h_coeff :
      Tendsto (fun d => (-1 / 16 : ℝ) *
        (2 * δR'' d -
          2 * δq' d * ((2 * sinh d ^ 2 - cosh d ^ 2) / cosh d ^ 3) -
          (-(sinh d / cosh d ^ 2)) * δq'' d) / d ^ (A - 1))
        (𝓝[≠] (0 : ℝ))
        (𝓝 ((-1 / 16 : ℝ) *
          (2 * (β * (↑A : ℝ) ^ 2) -
            2 * (-2 * β * (↑A : ℝ)) * (-1) -
            (-1) * (-2 * β * (↑A : ℝ) * ((↑A : ℝ) - 1))))) := by
    apply_rules [coefficient_extraction]
    · omega
    · exact sech_second_deriv_tendsto
    · convert sech_deriv_ratio_tendsto using 1
  convert h_coeff using 2
  ring

end

end OriginalHODL
end Impossibility
end TauSwap
