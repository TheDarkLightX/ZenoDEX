import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Basic
import Mathlib.Tactic

/-!
# AMM curve tradeoff (local, proved)

This file provides a **Lean-checked** (no `sorry`) local tradeoff result for the power family

`K(x,y; α) = x * y * (x + y)^α`  with `α : ℕ`,

around the balanced point `(x,y)=(1,1)` (where the invariant level is `K₀ = 2^α`).

We formalize a *local* “slippage vs impermanent loss curvature” tradeoff:

* A simple local slippage coefficient for this family is `slippage_coeff α = 2 / n`,
  where `n := α + 2` is the homogeneous degree.
* The LP impermanent-loss function `IL(p)` (after arbitrage to external price `p`) satisfies:
  `IL''(1) = - n / 8`.

Hence `slippage_coeff α * (-IL''(1)/2) = 1/8`, so no `α>0` can improve both coefficients over CPMM (`α=0`).

This is intentionally *local*: it certifies second-order behavior at balance (the regime relevant for
small trades and small price moves).
-/

namespace TauSwap
namespace Impossibility

open Real
open scoped Topology

noncomputable section

/-! ## Equilibrium ratio for the power family -/

/-- Convenience constant `A := α + 1` as a real. -/
def A (α : ℕ) : ℝ := (α : ℝ) + 1

/-- Homogeneous degree `n := α + 2` as a real. -/
def n (α : ℕ) : ℝ := (α : ℝ) + 2

/-- Discriminant used in the closed-form equilibrium ratio. -/
def disc (α : ℕ) (p : ℝ) : ℝ := (p - 1) ^ 2 * (A α) ^ 2 + p * 4

/-- Derivative of `disc α` w.r.t. `p`. -/
def disc_deriv (α : ℕ) (p : ℝ) : ℝ := 2 * (p - 1) * (A α) ^ 2 + 4

/-- Equilibrium ratio `r(p) := y/x` after arbitrage to external price `p > 0`. -/
def ratio (α : ℕ) (p : ℝ) : ℝ := ((p - 1) * A α + Real.sqrt (disc α p)) / 2

/-- Derivative of `sqrt (disc α p)` w.r.t. `p` (for `p > 0`). -/
def sqrt_disc_deriv (α : ℕ) (p : ℝ) : ℝ := disc_deriv α p / (2 * Real.sqrt (disc α p))

/-- Closed-form derivative of `ratio α` (for `p > 0`). -/
def ratio_deriv (α : ℕ) (p : ℝ) : ℝ := (A α + sqrt_disc_deriv α p) / 2

lemma ratio_one (α : ℕ) : ratio α 1 = 1 := by
  simp [ratio, disc, A]
  norm_num

lemma disc_pos (α : ℕ) {p : ℝ} (hp : 0 < p) : 0 < disc α p := by
  have hnonneg : 0 ≤ (p - 1) ^ 2 * (A α) ^ 2 := by nlinarith
  have h4p : 0 < p * 4 := by nlinarith
  have : disc α p = (p - 1) ^ 2 * (A α) ^ 2 + p * 4 := rfl
  nlinarith [this, hnonneg, h4p]

lemma hasDerivAt_disc (α : ℕ) (p : ℝ) : HasDerivAt (disc α) (disc_deriv α p) p := by
  have hsub : HasDerivAt (fun x : ℝ => x - 1) 1 p := by
    simpa using (hasDerivAt_id p).sub_const (1 : ℝ)
  have hsq : HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (p - 1)) p := by
    simpa [pow_two] using (hsub.fun_pow 2)
  have hmul :
      HasDerivAt (fun x : ℝ => (x - 1) ^ 2 * (A α) ^ 2) (2 * (p - 1) * (A α) ^ 2) p := by
    simpa [mul_assoc] using hsq.mul_const ((A α) ^ 2)
  have hlin : HasDerivAt (fun x : ℝ => x * 4) 4 p := by
    simpa using (hasDerivAt_id p).mul_const (4 : ℝ)
  have hadd := hmul.add hlin
  have hdisc_eq : (fun x : ℝ => (x - 1) ^ 2 * (A α) ^ 2 + x * 4) = disc α := by
    funext x
    simp [disc, add_comm]
  have hadd' : HasDerivAt (disc α) (2 * (p - 1) * A α ^ 2 + 4) p := by
    have :
        HasDerivAt (fun x : ℝ => (x - 1) ^ 2 * (A α) ^ 2 + x * 4)
          (2 * (p - 1) * (A α) ^ 2 + 4) p := by
      simpa [add_assoc, add_left_comm, add_comm] using hadd
    simpa [hdisc_eq] using this
  simpa [disc_deriv, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hadd'

lemma hasDerivAt_sqrt_disc (α : ℕ) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (fun x => Real.sqrt (disc α x)) (sqrt_disc_deriv α p) p := by
  have hdisc : HasDerivAt (disc α) (disc_deriv α p) p := hasDerivAt_disc α p
  have hdisc_ne : disc α p ≠ 0 := ne_of_gt (disc_pos α hp)
  have hsqrt :
      HasDerivAt (fun x => Real.sqrt (disc α x)) (disc_deriv α p / (2 * Real.sqrt (disc α p))) p := by
    simpa using (hdisc.sqrt hdisc_ne)
  simpa [sqrt_disc_deriv] using hsqrt

lemma hasDerivAt_ratio (α : ℕ) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (ratio α) (ratio_deriv α p) p := by
  have hsub : HasDerivAt (fun x : ℝ => x - 1) 1 p := by
    simpa using (hasDerivAt_id p).sub_const (1 : ℝ)
  have hmulA : HasDerivAt (fun x : ℝ => (x - 1) * A α) (1 * A α) p := by
    simpa [mul_assoc] using hsub.mul_const (A α)
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (disc α x)) (sqrt_disc_deriv α p) p :=
    hasDerivAt_sqrt_disc α hp
  have hsum :
      HasDerivAt (fun x : ℝ => (x - 1) * A α + Real.sqrt (disc α x))
        (1 * A α + sqrt_disc_deriv α p) p :=
    hmulA.add hsqrt
  have hdiv :
      HasDerivAt (fun x : ℝ => ((x - 1) * A α + Real.sqrt (disc α x)) / 2)
        ((1 * A α + sqrt_disc_deriv α p) / 2) p := by
    simpa using hsum.div_const (2 : ℝ)
  simpa [ratio, ratio_deriv, mul_assoc, add_assoc, add_left_comm, add_comm] using hdiv

lemma deriv_ratio_one (α : ℕ) : deriv (ratio α) 1 = n α / 2 := by
  have h : HasDerivAt (ratio α) (ratio_deriv α 1) 1 :=
    hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)
  rw [h.deriv]
  have hdisc1 : disc α 1 = 4 := by
    simp [disc, A]
  have hsqrt1 : Real.sqrt (disc α 1) = 2 := by
    simpa [hdisc1] using (by norm_num : Real.sqrt (4 : ℝ) = 2)
  have hdiscderiv1 : disc_deriv α 1 = 4 := by
    simp [disc_deriv, A]
  have hsqrtderiv1 : sqrt_disc_deriv α 1 = 1 := by
    simp [sqrt_disc_deriv, hdiscderiv1, hsqrt1]
    norm_num
  have : ratio_deriv α 1 = n α / 2 := by
    simp [ratio_deriv, A, n, hsqrtderiv1]
    ring
  simpa [this]

/-! ## Second derivative of `ratio` at 1 -/

lemma hasDerivAt_disc_deriv (α : ℕ) (p : ℝ) :
    HasDerivAt (disc_deriv α) (2 * (A α) ^ 2) p := by
  have hsub : HasDerivAt (fun x : ℝ => x - 1) 1 p := by
    simpa using (hasDerivAt_id p).sub_const (1 : ℝ)
  have hmul :
      HasDerivAt (fun x : ℝ => 2 * (x - 1) * (A α) ^ 2) (2 * 1 * (A α) ^ 2) p := by
    have h1 : HasDerivAt (fun x : ℝ => 2 * (x - 1)) (2 * 1) p := by
      simpa [mul_assoc] using (hsub.const_mul (2 : ℝ))
    simpa [mul_assoc] using h1.mul_const ((A α) ^ 2)
  have hconst : HasDerivAt (fun _x : ℝ => (4 : ℝ)) 0 p := hasDerivAt_const p 4
  have hadd := hconst.add hmul
  have hfun :
      ((fun _x : ℝ => (4 : ℝ)) + fun x : ℝ => 2 * (x - 1) * (A α) ^ 2) = disc_deriv α := by
    funext x
    simp [disc_deriv, add_comm, add_left_comm, add_assoc]
  have hadd' : HasDerivAt (disc_deriv α) (0 + (2 * 1 * (A α) ^ 2)) p := by
    simpa [hfun] using hadd
  simpa [mul_assoc, mul_left_comm, mul_comm] using hadd'

lemma deriv_ratio_deriv_one (α : ℕ) : deriv (ratio_deriv α) 1 = n α * (n α - 2) / 4 := by
  have hp : (0 : ℝ) < 1 := by norm_num
  have hnum : HasDerivAt (disc_deriv α) (2 * (A α) ^ 2) 1 := hasDerivAt_disc_deriv α 1
  have hsqrt : HasDerivAt (fun x => Real.sqrt (disc α x)) (sqrt_disc_deriv α 1) 1 :=
    hasDerivAt_sqrt_disc α hp
  have hden : HasDerivAt (fun x => 2 * Real.sqrt (disc α x)) (2 * sqrt_disc_deriv α 1) 1 := by
    simpa [mul_assoc] using hsqrt.const_mul (2 : ℝ)
  have hden_ne : (2 * Real.sqrt (disc α 1)) ≠ 0 := by
    have hdisc1 : disc α 1 = 4 := by simp [disc, A]
    have hsqrt1 : Real.sqrt (disc α 1) = 2 := by
      simpa [hdisc1] using (by norm_num : Real.sqrt (4 : ℝ) = 2)
    nlinarith [hsqrt1]
  have hquot :
      HasDerivAt (fun x => disc_deriv α x / (2 * Real.sqrt (disc α x)))
        (((2 * (A α) ^ 2) * (2 * Real.sqrt (disc α 1)) - disc_deriv α 1 * (2 * sqrt_disc_deriv α 1)) /
              (2 * Real.sqrt (disc α 1)) ^ 2)
        1 := by
    exact hnum.div hden hden_ne
  have hsdd :
      HasDerivAt (sqrt_disc_deriv α)
        (((2 * (A α) ^ 2) * (2 * Real.sqrt (disc α 1)) - disc_deriv α 1 * (2 * sqrt_disc_deriv α 1)) /
              (2 * Real.sqrt (disc α 1)) ^ 2)
        1 := by
    simpa [sqrt_disc_deriv] using hquot
  have hAconst : HasDerivAt (fun _x : ℝ => A α) 0 1 := hasDerivAt_const 1 (A α)
  have hsum :
      HasDerivAt (fun x => A α + sqrt_disc_deriv α x)
        (0 +
          (((2 * (A α) ^ 2) * (2 * Real.sqrt (disc α 1)) - disc_deriv α 1 * (2 * sqrt_disc_deriv α 1)) /
              (2 * Real.sqrt (disc α 1)) ^ 2))
        1 :=
    hAconst.add hsdd
  have hdiv :
      HasDerivAt (fun x => (A α + sqrt_disc_deriv α x) / 2)
        ((0 +
              (((2 * (A α) ^ 2) * (2 * Real.sqrt (disc α 1)) - disc_deriv α 1 * (2 * sqrt_disc_deriv α 1)) /
                  (2 * Real.sqrt (disc α 1)) ^ 2)) /
            2)
        1 := by
    simpa using hsum.div_const (2 : ℝ)
  have hrd :
      HasDerivAt (ratio_deriv α)
        ((0 +
              (((2 * (A α) ^ 2) * (2 * Real.sqrt (disc α 1)) - disc_deriv α 1 * (2 * sqrt_disc_deriv α 1)) /
                  (2 * Real.sqrt (disc α 1)) ^ 2)) /
            2)
        1 := by
    simpa [ratio_deriv] using hdiv
  rw [hrd.deriv]
  have hdisc1 : disc α 1 = 4 := by simp [disc, A]
  have hsqrt1 : Real.sqrt (disc α 1) = 2 := by
    simpa [hdisc1] using (by norm_num : Real.sqrt (4 : ℝ) = 2)
  have hdiscderiv1 : disc_deriv α 1 = 4 := by simp [disc_deriv, A]
  have hsqrtderiv1 : sqrt_disc_deriv α 1 = 1 := by
    simp [sqrt_disc_deriv, hdiscderiv1, hsqrt1]
    norm_num
  simp [hdisc1, hsqrt1, hdiscderiv1, hsqrtderiv1, n, A]
  ring

lemma hasDerivAt_ratio_deriv_one (α : ℕ) :
    HasDerivAt (ratio_deriv α) (n α * (n α - 2) / 4) 1 := by
  have hp : (0 : ℝ) < 1 := by norm_num
  have hnum : HasDerivAt (disc_deriv α) (2 * (A α) ^ 2) 1 := hasDerivAt_disc_deriv α 1
  have hsqrt : HasDerivAt (fun x => Real.sqrt (disc α x)) (sqrt_disc_deriv α 1) 1 :=
    hasDerivAt_sqrt_disc α hp
  have hden : HasDerivAt (fun x => 2 * Real.sqrt (disc α x)) (2 * sqrt_disc_deriv α 1) 1 := by
    simpa [mul_assoc] using hsqrt.const_mul (2 : ℝ)
  have hden_ne : (2 * Real.sqrt (disc α 1)) ≠ 0 := by
    have hdisc1 : disc α 1 = 4 := by simp [disc, A]
    have hsqrt1 : Real.sqrt (disc α 1) = 2 := by
      simpa [hdisc1] using (by norm_num : Real.sqrt (4 : ℝ) = 2)
    nlinarith [hsqrt1]
  have hquot :
      HasDerivAt (fun x => disc_deriv α x / (2 * Real.sqrt (disc α x)))
        (((2 * (A α) ^ 2) * (2 * Real.sqrt (disc α 1)) - disc_deriv α 1 * (2 * sqrt_disc_deriv α 1)) /
              (2 * Real.sqrt (disc α 1)) ^ 2)
        1 := by
    exact hnum.div hden hden_ne
  have hsdd :
      HasDerivAt (sqrt_disc_deriv α)
        (((2 * (A α) ^ 2) * (2 * Real.sqrt (disc α 1)) - disc_deriv α 1 * (2 * sqrt_disc_deriv α 1)) /
              (2 * Real.sqrt (disc α 1)) ^ 2)
        1 := by
    simpa [sqrt_disc_deriv] using hquot
  have hAconst : HasDerivAt (fun _x : ℝ => A α) 0 1 := hasDerivAt_const 1 (A α)
  have hsum :
      HasDerivAt (fun x => A α + sqrt_disc_deriv α x)
        (0 +
          (((2 * (A α) ^ 2) * (2 * Real.sqrt (disc α 1)) - disc_deriv α 1 * (2 * sqrt_disc_deriv α 1)) /
              (2 * Real.sqrt (disc α 1)) ^ 2))
        1 :=
    hAconst.add hsdd
  have hdiv :
      HasDerivAt (fun x => (A α + sqrt_disc_deriv α x) / 2)
        ((0 +
              (((2 * (A α) ^ 2) * (2 * Real.sqrt (disc α 1)) - disc_deriv α 1 * (2 * sqrt_disc_deriv α 1)) /
                  (2 * Real.sqrt (disc α 1)) ^ 2)) /
            2)
        1 := by
    simpa using hsum.div_const (2 : ℝ)
  have hrd :
      HasDerivAt (ratio_deriv α)
        ((0 +
              (((2 * (A α) ^ 2) * (2 * Real.sqrt (disc α 1)) - disc_deriv α 1 * (2 * sqrt_disc_deriv α 1)) /
                  (2 * Real.sqrt (disc α 1)) ^ 2)) /
            2)
        1 := by
    simpa [ratio_deriv] using hdiv
  -- simplify the derivative expression at `p=1`
  have hdisc1 : disc α 1 = 4 := by simp [disc, A]
  have hsqrt1 : Real.sqrt (disc α 1) = 2 := by
    simpa [hdisc1] using (by norm_num : Real.sqrt (4 : ℝ) = 2)
  have hdiscderiv1 : disc_deriv α 1 = 4 := by simp [disc_deriv, A]
  have hsqrtderiv1 : sqrt_disc_deriv α 1 = 1 := by
    simp [sqrt_disc_deriv, hdiscderiv1, hsqrt1]
    norm_num
  -- Rewrite `hrd`'s derivative value into the closed form `n α * (n α - 2) / 4`.
  refine hrd.congr_deriv ?_
  simp [hdisc1, hsqrt1, hdiscderiv1, hsqrtderiv1, n, A]
  ring

lemma deriv2_ratio_one (α : ℕ) : deriv (deriv (ratio α)) 1 = n α * (n α - 2) / 4 := by
  have hEq :
      deriv (ratio α) =ᶠ[𝓝 (1 : ℝ)] fun p => ratio_deriv α p := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with p hp
    exact (hasDerivAt_ratio α hp).deriv
  calc
    deriv (deriv (ratio α)) 1 = deriv (fun p => ratio_deriv α p) 1 := by
      simpa using (Filter.EventuallyEq.deriv_eq hEq)
    _ = n α * (n α - 2) / 4 := deriv_ratio_deriv_one α

/-! ## Impermanent loss and its second derivative at balance -/

/-- Log of the equilibrium `x` reserve at price `p` (so `x_res = exp log_x_res`). -/
def log_x_res (α : ℕ) (p : ℝ) : ℝ :=
  (α : ℝ) / (n α) * Real.log 2
    - (1 / (n α)) * Real.log (ratio α p)
    - (α : ℝ) / (n α) * Real.log (1 + ratio α p)

/-- Equilibrium `x` reserve (starting from `(1,1)` with invariant `2^α`). -/
def x_res (α : ℕ) (p : ℝ) : ℝ := Real.exp (log_x_res α p)

/-- LP value (in units of `y`) after arbitrage to external price `p`. -/
def lp_value (α : ℕ) (p : ℝ) : ℝ := x_res α p * (p + ratio α p)

/-- Impermanent loss for the initial 1:1 deposit, as a function of external price `p`. -/
def il (α : ℕ) (p : ℝ) : ℝ := lp_value α p / (p + 1) - 1

lemma log_x_res_one (α : ℕ) : log_x_res α 1 = 0 := by
  have hr : ratio α 1 = 1 := ratio_one α
  simp [log_x_res, hr]
  ring

lemma x_res_one (α : ℕ) : x_res α 1 = 1 := by
  simp [x_res, log_x_res_one]

lemma lp_value_one (α : ℕ) : lp_value α 1 = 2 := by
  simp [lp_value, x_res_one, ratio_one]
  norm_num

lemma il_one (α : ℕ) : il α 1 = 0 := by
  simp [il, lp_value_one]
  norm_num

/-! ### First derivative of `log_x_res` at 1 -/

lemma deriv_log_x_res_one (α : ℕ) : deriv (log_x_res α) 1 = -(n α) / 4 := by
  have hratio : HasDerivAt (ratio α) (ratio_deriv α 1) 1 :=
    hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)
  have hlog_ratio : HasDerivAt (fun p => Real.log (ratio α p)) (ratio_deriv α 1 / ratio α 1) 1 :=
    (hratio.log (by simpa [ratio_one α] using (show ratio α 1 ≠ 0 from by nlinarith)))
  have hlog_one_add_ratio :
      HasDerivAt (fun p => Real.log (1 + ratio α p)) (ratio_deriv α 1 / (1 + ratio α 1)) 1 := by
    have hone_add :
        HasDerivAt (fun p => 1 + ratio α p) (0 + ratio_deriv α 1) 1 :=
      (hasDerivAt_const 1 (1 : ℝ)).add hratio
    have hne : (1 + ratio α 1) ≠ 0 := by
      simp [ratio_one]
    -- `log` derivative needs nonzero input
    have hlog := hone_add.log hne
    simpa [add_assoc, add_comm, add_left_comm, add_comm] using hlog
  have hconst1 : HasDerivAt (fun _p : ℝ => (α : ℝ) / (n α) * Real.log 2) 0 1 :=
    hasDerivAt_const 1 ((α : ℝ) / (n α) * Real.log 2)
  have hterm2 :
      HasDerivAt (fun p : ℝ => - (1 / n α) * Real.log (ratio α p))
        (-(1 / n α) * (ratio_deriv α 1 / ratio α 1)) 1 := by
    simpa [neg_mul] using (hlog_ratio.const_mul (-(1 / (n α)) : ℝ))
  have hterm3 :
      HasDerivAt (fun p : ℝ => - (α : ℝ) / (n α) * Real.log (1 + ratio α p))
        (-(α : ℝ) / (n α) * (ratio_deriv α 1 / (1 + ratio α 1))) 1 := by
    simpa [neg_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (hlog_one_add_ratio.const_mul (-(α : ℝ) / (n α) : ℝ))
  have hall_raw :
      HasDerivAt
        ((fun _p : ℝ => (α : ℝ) / (n α) * Real.log 2) +
          ((fun p : ℝ => -((1 / n α) * Real.log (ratio α p))) +
            fun p : ℝ => -((α : ℝ) / (n α) * Real.log (1 + ratio α p))))
        (0 +
          (-(1 / n α) * (ratio_deriv α 1 / ratio α 1) +
            (-(α : ℝ) / (n α) * (ratio_deriv α 1 / (1 + ratio α 1)))))
        1 := by
    -- Avoid `simpa` on `HasDerivAt` goals: simp can erase additive constants.
    have hterm2' :
        HasDerivAt (fun p : ℝ => -((1 / n α) * Real.log (ratio α p)))
          (-(1 / n α) * (ratio_deriv α 1 / ratio α 1)) 1 := by
      -- `-((c) * f p) = (-c) * f p`
      have hEq :
          (fun p : ℝ => -((1 / n α) * Real.log (ratio α p))) =
            fun p : ℝ => - (1 / n α) * Real.log (ratio α p) := by
        funext p
        simp [neg_mul]
      exact hterm2.congr_of_eventuallyEq hEq.eventuallyEq
    have hterm3' :
        HasDerivAt (fun p : ℝ => -((α : ℝ) / (n α) * Real.log (1 + ratio α p)))
          (-(α : ℝ) / (n α) * (ratio_deriv α 1 / (1 + ratio α 1))) 1 := by
      have hEq :
          (fun p : ℝ => -((α : ℝ) / (n α) * Real.log (1 + ratio α p))) =
            fun p : ℝ => -(α : ℝ) / (n α) * Real.log (1 + ratio α p) := by
        funext p
        simp [neg_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      exact hterm3.congr_of_eventuallyEq hEq.eventuallyEq
    exact hconst1.add (hterm2'.add hterm3')
  have hall :
      HasDerivAt (log_x_res α)
        (0 +
          (-(1 / n α) * (ratio_deriv α 1 / ratio α 1) +
            (-(α : ℝ) / (n α) * (ratio_deriv α 1 / (1 + ratio α 1)))))
        1 := by
    have hfun :
        log_x_res α =
          ((fun _p : ℝ => (α : ℝ) / (n α) * Real.log 2) +
            ((fun p : ℝ => -((1 / n α) * Real.log (ratio α p))) +
              fun p : ℝ => -((α : ℝ) / (n α) * Real.log (1 + ratio α p)))) := by
      funext p
      simp [log_x_res, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    -- Avoid `simpa` here: `simp` can erase additive constants under `HasDerivAt`.
    exact hall_raw.congr_of_eventuallyEq (hfun.eventuallyEq)
  -- rewrite everything at the point using `ratio_one`, `deriv_ratio_one`
  have hr1 : ratio α 1 = 1 := ratio_one α
  have hdr1 : ratio_deriv α 1 = n α / 2 := by
    -- from `deriv_ratio_one` and `HasDerivAt` at 1
    have : deriv (ratio α) 1 = ratio_deriv α 1 := hratio.deriv
    -- `deriv_ratio_one` gives `deriv (ratio α) 1 = n/2`
    have : ratio_deriv α 1 = n α / 2 := by
      -- avoid rewriting pitfalls by using calc
      calc
        ratio_deriv α 1 = deriv (ratio α) 1 := by simpa using this.symm
        _ = n α / 2 := deriv_ratio_one α
    exact this
  rw [hall.deriv]
  -- simplify
  have hn : (n α) ≠ 0 := by
    have : (0 : ℝ) < n α := by
      -- `n α = α + 2`
      simpa [n] using (by nlinarith : (0 : ℝ) < (α : ℝ) + 2)
    exact ne_of_gt this
  simp [hr1, hdr1] at *
  -- now it's a field identity in `ℝ`
  field_simp [hn]
  simp [n]
  ring


lemma ratio_deriv_one (α : ℕ) : ratio_deriv α 1 = n α / 2 := by
  have hratio : HasDerivAt (ratio α) (ratio_deriv α 1) 1 :=
    hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)
  calc
    ratio_deriv α 1 = deriv (ratio α) 1 := by simpa using hratio.deriv.symm
    _ = n α / 2 := deriv_ratio_one α

/-- Closed-form derivative of `log_x_res α` (where the logarithmic-derivative denominators are nonzero). -/
def log_x_res_deriv (α : ℕ) (p : ℝ) : ℝ :=
  - (1 / (n α)) * (ratio_deriv α p / ratio α p)
    - (α : ℝ) / (n α) * (ratio_deriv α p / (1 + ratio α p))

lemma hasDerivAt_log_x_res (α : ℕ) {p : ℝ} (hp : 0 < p)
    (hr : ratio α p ≠ 0) (h1 : 1 + ratio α p ≠ 0) :
    HasDerivAt (log_x_res α) (log_x_res_deriv α p) p := by
  have hratio : HasDerivAt (ratio α) (ratio_deriv α p) p :=
    hasDerivAt_ratio α hp
  have hlog_ratio :
      HasDerivAt (fun q => Real.log (ratio α q)) (ratio_deriv α p / ratio α p) p :=
    (hratio.log hr)
  have hlog_one_add_ratio :
      HasDerivAt (fun q => Real.log (1 + ratio α q)) (ratio_deriv α p / (1 + ratio α p)) p := by
    have hone_add :
        HasDerivAt (fun q => 1 + ratio α q) (0 + ratio_deriv α p) p :=
      (hasDerivAt_const p (1 : ℝ)).add hratio
    have hlog := hone_add.log h1
    simpa [add_assoc, add_left_comm, add_comm] using hlog
  have hconst1 : HasDerivAt (fun _q : ℝ => (α : ℝ) / (n α) * Real.log 2) 0 p :=
    hasDerivAt_const p ((α : ℝ) / (n α) * Real.log 2)
  have hterm2 :
      HasDerivAt (fun q : ℝ => - (1 / (n α)) * Real.log (ratio α q))
        (- (1 / (n α)) * (ratio_deriv α p / ratio α p)) p := by
    simpa [neg_mul] using (hlog_ratio.const_mul (- (1 / (n α)) : ℝ))
  have hterm3 :
      HasDerivAt (fun q : ℝ => - (α : ℝ) / (n α) * Real.log (1 + ratio α q))
        (-(α : ℝ) / (n α) * (ratio_deriv α p / (1 + ratio α p))) p := by
    simpa [neg_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (hlog_one_add_ratio.const_mul (-(α : ℝ) / (n α) : ℝ))
  have hall_raw :
      HasDerivAt
        ((fun _q : ℝ => (α : ℝ) / (n α) * Real.log 2) +
          ((fun q : ℝ => - (1 / (n α)) * Real.log (ratio α q)) +
            fun q : ℝ => - (α : ℝ) / (n α) * Real.log (1 + ratio α q)))
        (0 + (- (1 / (n α)) * (ratio_deriv α p / ratio α p) +
          (-(α : ℝ) / (n α) * (ratio_deriv α p / (1 + ratio α p))))) p := by
    exact hconst1.add (hterm2.add hterm3)
  have hfun :
      log_x_res α =
        ((fun _q : ℝ => (α : ℝ) / (n α) * Real.log 2) +
          ((fun q : ℝ => - (1 / (n α)) * Real.log (ratio α q)) +
            fun q : ℝ => - (α : ℝ) / (n α) * Real.log (1 + ratio α q))) := by
    funext q
    simp only [log_x_res, Pi.add_apply, neg_mul, neg_div]
    ring
  have hall :
      HasDerivAt (log_x_res α)
        (0 + (- (1 / (n α)) * (ratio_deriv α p / ratio α p) +
          (-(α : ℝ) / (n α) * (ratio_deriv α p / (1 + ratio α p))))) p :=
    hall_raw.congr_of_eventuallyEq hfun.eventuallyEq
  -- rewrite to the bundled definition
  refine hall.congr_deriv ?_
  simp only [log_x_res_deriv, one_div, neg_mul, neg_div]
  ring

lemma deriv_log_x_res_eq (α : ℕ) {p : ℝ} (hp : 0 < p)
    (hr : ratio α p ≠ 0) (h1 : 1 + ratio α p ≠ 0) :
    deriv (log_x_res α) p = log_x_res_deriv α p :=
  (hasDerivAt_log_x_res α hp hr h1).deriv

lemma log_x_res_deriv_one (α : ℕ) : log_x_res_deriv α 1 = -(n α) / 4 := by
  have hr : ratio α 1 = 1 := ratio_one α
  have hdr : ratio_deriv α 1 = n α / 2 := ratio_deriv_one α
  simp [log_x_res_deriv, hr, hdr]
  -- field arithmetic
  have hn : n α ≠ 0 := by
    have : (0 : ℝ) < n α := by
      simpa [n] using (by nlinarith : (0 : ℝ) < (α : ℝ) + 2)
    exact ne_of_gt this
  field_simp [hn]
  simp [n]
  ring

lemma hasDerivAt_log_x_res_deriv_one (α : ℕ) :
    HasDerivAt (log_x_res_deriv α) (n α * (6 - n α) / 16) 1 := by
  have hratio : HasDerivAt (ratio α) (n α / 2) 1 := by
    have h := hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)
    exact h.congr_deriv (ratio_deriv_one α)
  have hratio_deriv : HasDerivAt (ratio_deriv α) (n α * (n α - 2) / 4) 1 :=
    hasDerivAt_ratio_deriv_one α
  have hratio1 : ratio α 1 ≠ 0 := by
    simp [ratio_one]
  have hratio1_add : 1 + ratio α 1 ≠ 0 := by
    simp [ratio_one]

  -- u(p) = ratio_deriv/ratio
  have hu :
      HasDerivAt (fun p : ℝ => ratio_deriv α p / ratio α p)
        (((n α * (n α - 2) / 4) * (ratio α 1) - ratio_deriv α 1 * (n α / 2)) / (ratio α 1) ^ 2) 1 := by
    exact hratio_deriv.div hratio hratio1
  -- v(p) = ratio_deriv/(1+ratio)
  have hone_add : HasDerivAt (fun p : ℝ => 1 + ratio α p) (0 + n α / 2) 1 :=
    (hasDerivAt_const 1 (1 : ℝ)).add hratio
  have hv :
      HasDerivAt (fun p : ℝ => ratio_deriv α p / (1 + ratio α p))
        (((n α * (n α - 2) / 4) * (1 + ratio α 1) - ratio_deriv α 1 * (0 + n α / 2)) / (1 + ratio α 1) ^ 2)
        1 := by
    exact hratio_deriv.div hone_add hratio1_add

  -- assemble log_x_res_deriv = c1*u + c2*v
  have hterm1 :
      HasDerivAt (fun p : ℝ => - (1 / n α) * (ratio_deriv α p / ratio α p))
        (- (1 / n α) * (((n α * (n α - 2) / 4) * (ratio α 1) - ratio_deriv α 1 * (n α / 2)) / (ratio α 1) ^ 2))
        1 := by
    simpa [neg_mul] using (hu.const_mul (- (1 / n α) : ℝ))
  have hterm2_raw :
      HasDerivAt (fun p : ℝ => - (α : ℝ) / (n α) * (ratio_deriv α p / (1 + ratio α p)))
        (-(α : ℝ) / (n α) *
            (((n α * (n α - 2) / 4) * (1 + ratio α 1) - ratio_deriv α 1 * (0 + n α / 2)) / (1 + ratio α 1) ^ 2))
        1 := by
    simpa [neg_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (hv.const_mul (-(α : ℝ) / (n α) : ℝ))
  have hterm2 :
      HasDerivAt (fun p : ℝ => -((α : ℝ) / (n α) * (ratio_deriv α p / (1 + ratio α p))))
        (-(α : ℝ) / (n α) *
            (((n α * (n α - 2) / 4) * (1 + ratio α 1) - ratio_deriv α 1 * (0 + n α / 2)) / (1 + ratio α 1) ^ 2))
        1 := by
    have hEq :
        (fun p : ℝ => -((α : ℝ) / (n α) * (ratio_deriv α p / (1 + ratio α p)))) =
          fun p : ℝ => - (α : ℝ) / (n α) * (ratio_deriv α p / (1 + ratio α p)) := by
      funext p
      ring
    exact hterm2_raw.congr_of_eventuallyEq hEq.eventuallyEq
  have hsum :
      HasDerivAt (log_x_res_deriv α)
        (- (1 / n α) *
              (((n α * (n α - 2) / 4) * (ratio α 1) - ratio_deriv α 1 * (n α / 2)) / (ratio α 1) ^ 2) +
            (-(α : ℝ) / (n α) *
              (((n α * (n α - 2) / 4) * (1 + ratio α 1) - ratio_deriv α 1 * (0 + n α / 2)) / (1 + ratio α 1) ^ 2)))
        1 := by
    -- Avoid `simpa`: `simp` can rewrite `HasDerivAt` goals by removing additive constants.
    have hraw :
        HasDerivAt
          (fun p : ℝ =>
            - (1 / n α) * (ratio_deriv α p / ratio α p) +
              -((α : ℝ) / (n α) * (ratio_deriv α p / (1 + ratio α p))))
          (- (1 / n α) *
                (((n α * (n α - 2) / 4) * (ratio α 1) - ratio_deriv α 1 * (n α / 2)) / (ratio α 1) ^ 2) +
              (-(α : ℝ) / (n α) *
                (((n α * (n α - 2) / 4) * (1 + ratio α 1) - ratio_deriv α 1 * (0 + n α / 2)) /
                    (1 + ratio α 1) ^ 2)))
          1 :=
      hterm1.add hterm2
    have hfun :
        log_x_res_deriv α =
          fun p : ℝ =>
            - (1 / n α) * (ratio_deriv α p / ratio α p) +
              -((α : ℝ) / (n α) * (ratio_deriv α p / (1 + ratio α p))) := by
      funext p
      simp only [log_x_res_deriv, one_div, neg_mul, neg_div]
      ring
    exact hraw.congr_of_eventuallyEq hfun.eventuallyEq

  -- simplify the resulting constant expression
  refine hsum.congr_deriv ?_
  have hr1 : ratio α 1 = 1 := ratio_one α
  have hdr1 : ratio_deriv α 1 = n α / 2 := ratio_deriv_one α
  simp only [hr1, hdr1]
  -- remaining field arithmetic
  have hn : n α ≠ 0 := by
    have : (0 : ℝ) < n α := by
      simpa [n] using (by nlinarith : (0 : ℝ) < (α : ℝ) + 2)
    exact ne_of_gt this
  field_simp [hn]
  -- Expand n α = α + 2 to solve the ring equation
  simp only [n]
  ring

lemma deriv_log_x_res_deriv_one (α : ℕ) : deriv (log_x_res_deriv α) 1 = n α * (6 - n α) / 16 :=
  (hasDerivAt_log_x_res_deriv_one α).deriv

lemma deriv2_log_x_res_one (α : ℕ) : deriv (deriv (log_x_res α)) 1 = n α * (6 - n α) / 16 := by
  have hpos : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), 0 < p :=
    Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hratio_ne : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), ratio α p ≠ 0 := by
    have hcont : ContinuousAt (ratio α) 1 :=
      (hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)).continuousAt
    have hne : ratio α 1 ≠ (0 : ℝ) := by
      simp [ratio_one]
    exact hcont.eventually_ne hne
  have h1_ne : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), 1 + ratio α p ≠ 0 := by
    have hcont : ContinuousAt (fun p : ℝ => 1 + ratio α p) 1 :=
      (continuousAt_const.add (hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)).continuousAt)
    have hne : (1 + ratio α 1) ≠ (0 : ℝ) := by
      simp [ratio_one]
    exact hcont.eventually_ne hne
  have hEq :
      deriv (log_x_res α) =ᶠ[𝓝 (1 : ℝ)] fun p => log_x_res_deriv α p := by
    filter_upwards [hpos, hratio_ne, h1_ne] with p hp hr h1
    exact deriv_log_x_res_eq α hp hr h1
  calc
    deriv (deriv (log_x_res α)) 1 = deriv (fun p => log_x_res_deriv α p) 1 := by
      simpa using (Filter.EventuallyEq.deriv_eq hEq)
    _ = n α * (6 - n α) / 16 := deriv_log_x_res_deriv_one α

/-! ## Impermanent loss: `IL''(1) = - n / 8` -/

/-- A convenient name for the post-arbitrage `x`-reserve derivative formula. -/
def x_res_deriv_formula (α : ℕ) (p : ℝ) : ℝ := x_res α p * log_x_res_deriv α p

lemma x_res_deriv_formula_one (α : ℕ) : x_res_deriv_formula α 1 = -(n α) / 4 := by
  simp [x_res_deriv_formula, x_res_one, log_x_res_deriv_one]

lemma hasDerivAt_x_res_one (α : ℕ) : HasDerivAt (x_res α) (-(n α) / 4) 1 := by
  have hp : (0 : ℝ) < 1 := by norm_num
  have hr : ratio α 1 ≠ 0 := by simp [ratio_one]
  have h1 : 1 + ratio α 1 ≠ 0 := by simp [ratio_one]
  have hlog : HasDerivAt (log_x_res α) (log_x_res_deriv α 1) 1 :=
    hasDerivAt_log_x_res α hp hr h1
  have hx : HasDerivAt (x_res α) (x_res α 1 * log_x_res_deriv α 1) 1 := by
    simpa [x_res] using hlog.exp
  refine hx.congr_deriv ?_
  simp [x_res_one, log_x_res_deriv_one]

lemma deriv_x_res_one (α : ℕ) : deriv (x_res α) 1 = -(n α) / 4 :=
  (hasDerivAt_x_res_one α).deriv

lemma deriv_x_res_eq (α : ℕ) {p : ℝ} (hp : 0 < p)
    (hr : ratio α p ≠ 0) (h1 : 1 + ratio α p ≠ 0) :
    deriv (x_res α) p = x_res_deriv_formula α p := by
  have hlog : HasDerivAt (log_x_res α) (log_x_res_deriv α p) p :=
    hasDerivAt_log_x_res α hp hr h1
  have hx :
      HasDerivAt (x_res α) (Real.exp (log_x_res α p) * log_x_res_deriv α p) p := by
    simpa [x_res] using hlog.exp
  -- `Real.exp (log_x_res α p)` is `x_res α p`
  simpa [x_res, x_res_deriv_formula] using hx.deriv

lemma hasDerivAt_x_res_deriv_formula_one (α : ℕ) :
    HasDerivAt (x_res_deriv_formula α) (3 * n α / 8) 1 := by
  have hx : HasDerivAt (x_res α) (-(n α) / 4) 1 := hasDerivAt_x_res_one α
  have hlog' : HasDerivAt (log_x_res_deriv α) (n α * (6 - n α) / 16) 1 :=
    hasDerivAt_log_x_res_deriv_one α
  have hprod : HasDerivAt (fun p : ℝ => x_res α p * log_x_res_deriv α p)
      ((-(n α) / 4) * log_x_res_deriv α 1 + x_res α 1 * (n α * (6 - n α) / 16)) 1 :=
    hx.mul hlog'
  refine hprod.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · -- pointwise equality: `fun p => x_res α p * log_x_res_deriv α p` is the definition
    exact (by
      refine (Eq.eventuallyEq ?_)
      rfl)
  · simp [x_res_deriv_formula, x_res_one, log_x_res_deriv_one, n]
    ring

lemma deriv2_x_res_one (α : ℕ) : deriv (deriv (x_res α)) 1 = 3 * n α / 8 := by
  have hpos : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), 0 < p :=
    Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hratio_ne : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), ratio α p ≠ 0 := by
    have hcont : ContinuousAt (ratio α) 1 :=
      (hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)).continuousAt
    have hne : ratio α 1 ≠ (0 : ℝ) := by simp [ratio_one]
    exact hcont.eventually_ne hne
  have h1_ne : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), 1 + ratio α p ≠ 0 := by
    have hcont : ContinuousAt (fun p : ℝ => 1 + ratio α p) 1 :=
      (continuousAt_const.add (hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)).continuousAt)
    have hne : (1 + ratio α 1) ≠ (0 : ℝ) := by simp [ratio_one]
    exact hcont.eventually_ne hne
  have hEq : deriv (x_res α) =ᶠ[𝓝 (1 : ℝ)] fun p => x_res_deriv_formula α p := by
    filter_upwards [hpos, hratio_ne, h1_ne] with p hp hr h1
    exact deriv_x_res_eq α hp hr h1
  calc
    deriv (deriv (x_res α)) 1 = deriv (fun p => x_res_deriv_formula α p) 1 := by
      simpa using (Filter.EventuallyEq.deriv_eq hEq)
    _ = 3 * n α / 8 := (hasDerivAt_x_res_deriv_formula_one α).deriv

/-- Convenience function: `g(p) := p + ratio α p`. -/
def g (α : ℕ) (p : ℝ) : ℝ := p + ratio α p

/-- Convenience function: `g'(p) := 1 + ratio_deriv α p`. -/
def g_deriv (α : ℕ) (p : ℝ) : ℝ := 1 + ratio_deriv α p

lemma g_one (α : ℕ) : g α 1 = 2 := by
  simp [g, ratio_one]
  norm_num

lemma g_deriv_one (α : ℕ) : g_deriv α 1 = 1 + n α / 2 := by
  simp [g_deriv, ratio_deriv_one]

lemma hasDerivAt_g_one (α : ℕ) :
    HasDerivAt (g α) (1 + n α / 2) 1 := by
  have hratio : HasDerivAt (ratio α) (n α / 2) 1 := by
    have h := hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)
    exact h.congr_deriv (ratio_deriv_one α)
  have hid : HasDerivAt (fun p : ℝ => p) 1 1 := hasDerivAt_id 1
  have hadd : HasDerivAt (fun p : ℝ => p + ratio α p) (1 + n α / 2) 1 := hid.add hratio
  simpa [g] using hadd

lemma hasDerivAt_g_deriv_one (α : ℕ) :
    HasDerivAt (g_deriv α) (n α * (n α - 2) / 4) 1 := by
  have hratio' : HasDerivAt (ratio_deriv α) (n α * (n α - 2) / 4) 1 :=
    hasDerivAt_ratio_deriv_one α
  have hconst : HasDerivAt (fun _p : ℝ => (1 : ℝ)) 0 1 := hasDerivAt_const 1 (1 : ℝ)
  have hadd : HasDerivAt (fun p : ℝ => 1 + ratio_deriv α p) (0 + n α * (n α - 2) / 4) 1 :=
    hconst.add hratio'
  -- Avoid `simpa` on `HasDerivAt`: simp can erase additive constants.
  have hfun : g_deriv α =ᶠ[𝓝 (1 : ℝ)] (fun p : ℝ => 1 + ratio_deriv α p) :=
    (Eq.eventuallyEq (by rfl))
  have h' : HasDerivAt (g_deriv α) (0 + n α * (n α - 2) / 4) 1 :=
    hadd.congr_of_eventuallyEq hfun.symm
  simpa using h'

/-- Derivative formula for `lp_value` (valid where the `log_x_res` derivative formula is valid). -/
def lp_value_deriv_formula (α : ℕ) (p : ℝ) : ℝ :=
  x_res_deriv_formula α p * g α p + x_res α p * g_deriv α p

lemma deriv_lp_value_eq (α : ℕ) {p : ℝ} (hp : 0 < p)
    (hr : ratio α p ≠ 0) (h1 : 1 + ratio α p ≠ 0) :
    deriv (lp_value α) p = lp_value_deriv_formula α p := by
  have hx : HasDerivAt (x_res α) (x_res_deriv_formula α p) p := by
    -- from the derivative of `log_x_res`
    have hlog : HasDerivAt (log_x_res α) (log_x_res_deriv α p) p :=
      hasDerivAt_log_x_res α hp hr h1
    simpa [x_res, x_res_deriv_formula] using hlog.exp
  have hg : HasDerivAt (g α) (g_deriv α p) p := by
    have hratio : HasDerivAt (ratio α) (ratio_deriv α p) p :=
      hasDerivAt_ratio α hp
    have hid : HasDerivAt (fun q : ℝ => q) 1 p := hasDerivAt_id p
    have hadd : HasDerivAt (fun q : ℝ => q + ratio α q) (1 + ratio_deriv α p) p :=
      hid.add hratio
    simpa [g, g_deriv] using hadd
  have hmul : HasDerivAt (lp_value α)
      (x_res_deriv_formula α p * g α p + x_res α p * g_deriv α p) p := by
    simpa [lp_value, g, g_deriv, lp_value_deriv_formula] using (hx.mul hg)
  exact hmul.deriv

lemma hasDerivAt_lp_value_one (α : ℕ) : HasDerivAt (lp_value α) 1 1 := by
  have hx : HasDerivAt (x_res α) (-(n α) / 4) 1 := hasDerivAt_x_res_one α
  have hg : HasDerivAt (g α) (1 + n α / 2) 1 := hasDerivAt_g_one α
  have hmul : HasDerivAt (lp_value α) ((-(n α) / 4) * g α 1 + x_res α 1 * (1 + n α / 2)) 1 := by
    simpa [lp_value, g] using (hx.mul hg)
  -- simplify the derivative value to `1`
  refine hmul.congr_deriv ?_
  simp [g_one, x_res_one, n]
  ring

lemma deriv_lp_value_one (α : ℕ) : deriv (lp_value α) 1 = 1 :=
  (hasDerivAt_lp_value_one α).deriv

lemma hasDerivAt_lp_value_deriv_formula_one (α : ℕ) :
    HasDerivAt (lp_value_deriv_formula α) (-(n α) / 4) 1 := by
  -- split the derivative formula into two products and differentiate each
  have hxd : HasDerivAt (x_res_deriv_formula α) (3 * n α / 8) 1 :=
    hasDerivAt_x_res_deriv_formula_one α
  have hg : HasDerivAt (g α) (1 + n α / 2) 1 := hasDerivAt_g_one α
  have hx : HasDerivAt (x_res α) (-(n α) / 4) 1 := hasDerivAt_x_res_one α
  have hgd : HasDerivAt (g_deriv α) (n α * (n α - 2) / 4) 1 := hasDerivAt_g_deriv_one α

  have hterm1 :
      HasDerivAt (fun p : ℝ => x_res_deriv_formula α p * g α p)
        ((3 * n α / 8) * g α 1 + x_res_deriv_formula α 1 * (1 + n α / 2)) 1 := by
    exact (hxd.mul hg)
  have hterm2 :
      HasDerivAt (fun p : ℝ => x_res α p * g_deriv α p)
        ((-(n α) / 4) * g_deriv α 1 + x_res α 1 * (n α * (n α - 2) / 4)) 1 := by
    exact (hx.mul hgd)
  have hsum :
      HasDerivAt (lp_value_deriv_formula α)
        (((3 * n α / 8) * g α 1 + x_res_deriv_formula α 1 * (1 + n α / 2)) +
          ((-(n α) / 4) * g_deriv α 1 + x_res α 1 * (n α * (n α - 2) / 4))) 1 := by
    simpa [lp_value_deriv_formula] using (hterm1.add hterm2)
  refine hsum.congr_deriv ?_
  simp [g_one, g_deriv_one, x_res_one, x_res_deriv_formula_one, n]
  ring

lemma deriv2_lp_value_one (α : ℕ) : deriv (deriv (lp_value α)) 1 = -(n α) / 4 := by
  have hpos : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), 0 < p :=
    Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hratio_ne : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), ratio α p ≠ 0 := by
    have hcont : ContinuousAt (ratio α) 1 :=
      (hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)).continuousAt
    have hne : ratio α 1 ≠ (0 : ℝ) := by simp [ratio_one]
    exact hcont.eventually_ne hne
  have h1_ne : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), 1 + ratio α p ≠ 0 := by
    have hcont : ContinuousAt (fun p : ℝ => 1 + ratio α p) 1 :=
      (continuousAt_const.add (hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)).continuousAt)
    have hne : (1 + ratio α 1) ≠ (0 : ℝ) := by simp [ratio_one]
    exact hcont.eventually_ne hne
  have hEq : deriv (lp_value α) =ᶠ[𝓝 (1 : ℝ)] fun p => lp_value_deriv_formula α p := by
    filter_upwards [hpos, hratio_ne, h1_ne] with p hp hr h1
    exact deriv_lp_value_eq α hp hr h1
  calc
    deriv (deriv (lp_value α)) 1 = deriv (fun p => lp_value_deriv_formula α p) 1 := by
      simpa using (Filter.EventuallyEq.deriv_eq hEq)
    _ = -(n α) / 4 := (hasDerivAt_lp_value_deriv_formula_one α).deriv

/-! ### `il''(1)` -/

/-- Convenience: `inv(p) := (p + 1)⁻¹`. -/
def inv_one_plus (p : ℝ) : ℝ := (p + 1)⁻¹

/-- Convenience: derivative formula `inv'(p) := -((p+1)^2)⁻¹`. -/
def inv_one_plus_deriv (p : ℝ) : ℝ := -((p + 1) ^ 2)⁻¹

lemma inv_one_plus_one : inv_one_plus 1 = (1 / 2 : ℝ) := by
  simp [inv_one_plus]
  norm_num

lemma inv_one_plus_deriv_one : inv_one_plus_deriv 1 = (- (1 / 4 : ℝ)) := by
  simp [inv_one_plus_deriv]
  norm_num

lemma hasDerivAt_inv_one_plus_one : HasDerivAt inv_one_plus (- (1 / 4 : ℝ)) 1 := by
  have hlin : HasDerivAt (fun p : ℝ => p + 1) 1 1 := by
    simpa [add_comm, add_left_comm, add_assoc] using (hasDerivAt_id 1).add_const (1 : ℝ)
  have hne : (1 + 1 : ℝ) ≠ 0 := by norm_num
  have hinv : HasDerivAt inv_one_plus (-(1 : ℝ) / (1 + 1) ^ 2) 1 := by
    simpa [inv_one_plus] using (hlin.inv (by simpa using hne))
  have : (-(1 : ℝ) / (1 + 1) ^ 2 : ℝ) = (- (1 / 4 : ℝ)) := by norm_num
  simpa [this] using hinv

lemma deriv_inv_one_plus_one : deriv inv_one_plus 1 = - (1 / 4 : ℝ) :=
  (hasDerivAt_inv_one_plus_one).deriv

lemma deriv_inv_one_plus_eq (p : ℝ) (hp : p ≠ -1) : deriv inv_one_plus p = inv_one_plus_deriv p := by
  have hlin : HasDerivAt (fun q : ℝ => q + 1) 1 p := by
    simpa [add_comm, add_left_comm, add_assoc] using (hasDerivAt_id p).add_const (1 : ℝ)
  have hne : (p + 1 : ℝ) ≠ 0 := by
    -- `p ≠ -1` iff `p+1 ≠ 0`
    intro h
    apply hp
    linarith
  have hinv : HasDerivAt inv_one_plus (-(1 : ℝ) / (p + 1) ^ 2) p := by
    simpa [inv_one_plus] using (hlin.inv (by simpa using hne))
  -- rewrite the derivative value into `inv_one_plus_deriv p`
  have : (-(1 : ℝ) / (p + 1) ^ 2 : ℝ) = inv_one_plus_deriv p := by
    simp [inv_one_plus_deriv, div_eq_mul_inv]
  simpa [this] using hinv.deriv

lemma hasDerivAt_inv_one_plus_deriv_one : HasDerivAt inv_one_plus_deriv (1 / 4 : ℝ) 1 := by
  -- inv_one_plus_deriv(p) = -((p+1)^2)⁻¹; differentiate via `inv` on `d(p)=(p+1)^2`
  have hadd : HasDerivAt (fun p : ℝ => p + 1) 1 1 := by
    simpa [add_comm, add_left_comm, add_assoc] using (hasDerivAt_id 1).add_const (1 : ℝ)
  have hpow : HasDerivAt (fun p : ℝ => (p + 1) ^ 2) (2 * (1 + 1)) 1 := by
    -- derivative of `(p+1)^2` at 1 is `2*(p+1)` evaluated at 1
    simpa [pow_two] using (hadd.fun_pow 2)
  have hne : ((1 + 1 : ℝ) ^ 2) ≠ 0 := by norm_num
  have hinv : HasDerivAt (fun p : ℝ => ((p + 1) ^ 2)⁻¹) (-(2 * (1 + 1)) / ((1 + 1) ^ 2) ^ 2) 1 :=
    (hpow.inv (by
      -- (p+1)^2 at 1 is nonzero
      have : ((1 + 1 : ℝ) ^ 2) ≠ 0 := by norm_num
      simpa using this))
  have hneg : HasDerivAt inv_one_plus_deriv (- (-(2 * (1 + 1)) / ((1 + 1) ^ 2) ^ 2)) 1 := by
    simpa [inv_one_plus_deriv] using hinv.neg
  have : (- (-(2 * (1 + 1)) / ((1 + 1) ^ 2) ^ 2) : ℝ) = (1 / 4 : ℝ) := by norm_num
  simpa [this] using hneg

lemma deriv2_inv_one_plus_one : deriv (deriv inv_one_plus) 1 = (1 / 4 : ℝ) := by
  have hEq : deriv inv_one_plus =ᶠ[𝓝 (1 : ℝ)] fun p => inv_one_plus_deriv p := by
    -- near 1 we have `p ≠ -1`
    have hne : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), p ≠ (-1 : ℝ) :=
      (continuousAt_id.eventually_ne (by norm_num : (1 : ℝ) ≠ (-1 : ℝ)))
    filter_upwards [hne] with p hp
    exact deriv_inv_one_plus_eq p hp
  calc
    deriv (deriv inv_one_plus) 1 = deriv (fun p => inv_one_plus_deriv p) 1 := by
      simpa using (Filter.EventuallyEq.deriv_eq hEq)
    _ = (1 / 4 : ℝ) := (hasDerivAt_inv_one_plus_deriv_one).deriv

/-- `lp_value'` formula at the balanced point. -/
lemma lp_value_deriv_formula_one (α : ℕ) : lp_value_deriv_formula α 1 = 1 := by
  simp [lp_value_deriv_formula, x_res_deriv_formula_one, g_one, x_res_one, g_deriv_one, n]
  ring

/-- `il'` formula (valid where both factor-derivative formulas are valid). -/
def il_deriv_formula (α : ℕ) (p : ℝ) : ℝ :=
  lp_value_deriv_formula α p * inv_one_plus p + lp_value α p * inv_one_plus_deriv p

lemma hasDerivAt_inv_one_plus (p : ℝ) (hp : p ≠ (-1 : ℝ)) :
    HasDerivAt inv_one_plus (inv_one_plus_deriv p) p := by
  have hlin : HasDerivAt (fun q : ℝ => q + 1) 1 p := by
    simpa [add_comm, add_left_comm, add_assoc] using (hasDerivAt_id p).add_const (1 : ℝ)
  have hne : (p + 1 : ℝ) ≠ 0 := by
    intro h
    apply hp
    linarith
  have hinv : HasDerivAt inv_one_plus (-(1 : ℝ) / (p + 1) ^ 2) p := by
    simpa [inv_one_plus] using (hlin.inv (by simpa using hne))
  have hval : (-(1 : ℝ) / (p + 1) ^ 2 : ℝ) = inv_one_plus_deriv p := by
    simp [inv_one_plus_deriv, div_eq_mul_inv]
  exact hinv.congr_deriv hval

lemma hasDerivAt_il_deriv_formula_one (α : ℕ) :
    HasDerivAt (il_deriv_formula α) (-(n α) / 8) 1 := by
  have hterm1 :
      HasDerivAt (fun p : ℝ => lp_value_deriv_formula α p * inv_one_plus p)
        (-(n α) / 8 - (1 / 4 : ℝ)) 1 := by
    have hf : HasDerivAt (lp_value_deriv_formula α) (-(n α) / 4) 1 :=
      hasDerivAt_lp_value_deriv_formula_one α
    have hg : HasDerivAt inv_one_plus (- (1 / 4 : ℝ)) 1 :=
      hasDerivAt_inv_one_plus_one
    have hmul :
        HasDerivAt (fun p : ℝ => lp_value_deriv_formula α p * inv_one_plus p)
          ((-(n α) / 4) * inv_one_plus 1 + lp_value_deriv_formula α 1 * (- (1 / 4 : ℝ))) 1 :=
      hf.mul hg
    refine hmul.congr_deriv ?_
    simp [inv_one_plus_one, lp_value_deriv_formula_one]
    ring
  have hterm2 :
      HasDerivAt (fun p : ℝ => lp_value α p * inv_one_plus_deriv p) (1 / 4 : ℝ) 1 := by
    have hf : HasDerivAt (lp_value α) 1 1 := hasDerivAt_lp_value_one α
    have hg : HasDerivAt inv_one_plus_deriv (1 / 4 : ℝ) 1 := hasDerivAt_inv_one_plus_deriv_one
    have hmul :
        HasDerivAt (fun p : ℝ => lp_value α p * inv_one_plus_deriv p)
          (1 * inv_one_plus_deriv 1 + lp_value α 1 * (1 / 4 : ℝ)) 1 :=
      hf.mul hg
    refine hmul.congr_deriv ?_
    simp [inv_one_plus_deriv_one, lp_value_one]
    ring
  have hadd :
      HasDerivAt (il_deriv_formula α) (-(n α) / 8 - (1 / 4 : ℝ) + (1 / 4 : ℝ)) 1 := by
    simpa [il_deriv_formula] using hterm1.add hterm2
  refine hadd.congr_deriv ?_
  ring

lemma deriv2_il_one (α : ℕ) : deriv (deriv (il α)) 1 = -(n α) / 8 := by
  -- rewrite `il` as a product with `(p+1)⁻¹`
  have hil : il α = fun p : ℝ => lp_value α p * inv_one_plus p - 1 := by
    funext p
    simp [il, inv_one_plus, lp_value, div_eq_mul_inv]
  have hpos : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), 0 < p :=
    Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hratio_ne : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), ratio α p ≠ 0 := by
    have hcont : ContinuousAt (ratio α) 1 :=
      (hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)).continuousAt
    have hne : ratio α 1 ≠ (0 : ℝ) := by simp [ratio_one]
    exact hcont.eventually_ne hne
  have h1_ne : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), 1 + ratio α p ≠ 0 := by
    have hcont : ContinuousAt (fun p : ℝ => 1 + ratio α p) 1 :=
      continuousAt_const.add (hasDerivAt_ratio α (by norm_num : (0 : ℝ) < 1)).continuousAt
    have hne : (1 + ratio α 1) ≠ (0 : ℝ) := by simp [ratio_one]
    exact hcont.eventually_ne hne
  have hm1 : ∀ᶠ p : ℝ in 𝓝 (1 : ℝ), p ≠ (-1 : ℝ) :=
    continuousAt_id.eventually_ne (by norm_num : (1 : ℝ) ≠ (-1 : ℝ))
  have hEq : deriv (il α) =ᶠ[𝓝 (1 : ℝ)] fun p => il_deriv_formula α p := by
    filter_upwards [hpos, hratio_ne, h1_ne, hm1] with p hp hr h1 hpm1
    have hLp : HasDerivAt (lp_value α) (lp_value_deriv_formula α p) p := by
      -- re-run the `lp_value` derivative proof at `p`
      have hx : HasDerivAt (x_res α) (x_res_deriv_formula α p) p := by
        have hlog : HasDerivAt (log_x_res α) (log_x_res_deriv α p) p :=
          hasDerivAt_log_x_res α hp hr h1
        simpa [x_res, x_res_deriv_formula] using hlog.exp
      have hg : HasDerivAt (g α) (g_deriv α p) p := by
        have hratio : HasDerivAt (ratio α) (ratio_deriv α p) p :=
          hasDerivAt_ratio α hp
        have hid : HasDerivAt (fun q : ℝ => q) 1 p := hasDerivAt_id p
        have hadd : HasDerivAt (fun q : ℝ => q + ratio α q) (1 + ratio_deriv α p) p :=
          hid.add hratio
        simpa [g, g_deriv] using hadd
      simpa [lp_value, g, g_deriv, lp_value_deriv_formula] using (hx.mul hg)
    have hInv : HasDerivAt inv_one_plus (inv_one_plus_deriv p) p :=
      hasDerivAt_inv_one_plus p hpm1
    have hProd :
        HasDerivAt (fun q : ℝ => lp_value α q * inv_one_plus q)
          (lp_value_deriv_formula α p * inv_one_plus p + lp_value α p * inv_one_plus_deriv p) p :=
      hLp.mul hInv
    have hIl : HasDerivAt (il α) (il_deriv_formula α p) p := by
      -- use the rewritten form `hil`
      have hIl' :
          HasDerivAt (fun q : ℝ => lp_value α q * inv_one_plus q - 1) (il_deriv_formula α p) p := by
        simpa [il_deriv_formula] using (hProd.sub_const (1 : ℝ))
      simpa [hil] using hIl'
    exact hIl.deriv
  calc
    deriv (deriv (il α)) 1 = deriv (fun p => il_deriv_formula α p) 1 := by
      simpa using (Filter.EventuallyEq.deriv_eq hEq)
    _ = -(n α) / 8 := (hasDerivAt_il_deriv_formula_one α).deriv

/-- `n α` is strictly positive. -/
lemma n_pos (α : ℕ) : (0 : ℝ) < n α := by
  simp [n]
  nlinarith

lemma n_ne_zero (α : ℕ) : n α ≠ 0 :=
  ne_of_gt (n_pos α)

/-- Local slippage coefficient at balance: inverse slope of `ratio` at `p=1`. -/
def slippage_coeff (α : ℕ) : ℝ :=
  (deriv (ratio α) 1)⁻¹

lemma slippage_coeff_eq (α : ℕ) : slippage_coeff α = 2 / n α := by
  have hn : n α ≠ 0 := n_ne_zero α
  unfold slippage_coeff
  rw [deriv_ratio_one α]
  field_simp [hn]

/-- Local IL curvature coefficient: `-IL''(1)/2` (the positive quadratic coefficient of the Taylor expansion). -/
def il_coeff (α : ℕ) : ℝ :=
  -(deriv (deriv (il α)) 1) / 2

lemma il_coeff_eq (α : ℕ) : il_coeff α = n α / 16 := by
  simp [il_coeff, deriv2_il_one α]
  ring

lemma tradeoff_coeff (α : ℕ) : slippage_coeff α * il_coeff α = (1 / 8 : ℝ) := by
  have hn : n α ≠ 0 := n_ne_zero α
  simp [slippage_coeff_eq, il_coeff_eq, div_eq_mul_inv]
  field_simp [hn]
  norm_num

lemma slippage_coeff_lt_cpmm {α : ℕ} (hα : 0 < α) : slippage_coeff α < slippage_coeff 0 := by
  have hα' : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hlt : (2 : ℝ) < (α : ℝ) + 2 := by nlinarith [hα']
  have h : (2 : ℝ) / ((α : ℝ) + 2) < (2 : ℝ) / 2 :=
    div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < (2 : ℝ)) hlt
  have hz : slippage_coeff 0 = 1 := by
    simp [slippage_coeff_eq, n]
  have : slippage_coeff α < 1 := by
    simpa [slippage_coeff_eq, n] using (h.trans_eq (by norm_num : (2 : ℝ) / 2 = 1))
  simpa [hz] using this

lemma il_coeff_gt_cpmm {α : ℕ} (hα : 0 < α) : il_coeff 0 < il_coeff α := by
  have hα' : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hlt : (2 : ℝ) < (α : ℝ) + 2 := by nlinarith [hα']
  have h : (2 : ℝ) / (16 : ℝ) < ((α : ℝ) + 2) / (16 : ℝ) :=
    div_lt_div_of_pos_right hlt (by norm_num : (0 : ℝ) < (16 : ℝ))
  -- rewrite both sides into `il_coeff`
  simpa [il_coeff_eq, n] using h

theorem tradeoff_vs_cpmm {α : ℕ} (hα : 0 < α) :
    slippage_coeff α < slippage_coeff 0 ∧ il_coeff 0 < il_coeff α :=
  ⟨slippage_coeff_lt_cpmm hα, il_coeff_gt_cpmm hα⟩


end

end Impossibility
end TauSwap
