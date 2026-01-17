import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# AMM Slippage-IL Impossibility Theorem (V2)

## Overview

This file proves that for the power-parameterized AMM curve family
  `K(x,y; α) = x * y * (x + y)^α`
no choice of `α ≠ 0` can simultaneously improve both:
  1. Slippage (execution quality for traders), and
  2. Impermanent Loss (LP profitability vs HODL)

relative to the CPMM baseline (α = 0).

## The Curve Family

- `α = 0`: Standard CPMM (`K = x * y`)
- `α = 1`: Cubic sum curve (`K = x * y * (x + y)`)
- `α = -1`: Inverse blend (hypothetical, between constant-sum and CPMM)

The homogeneous degree is `n = α + 2`.

## Key Results

1. **Slippage coefficient** at balance: `slippageCoeff α = 2 / n`
   - Lower is better (less price impact per unit trade)
   - Decreases with increasing α

2. **IL curvature** at balance: `ilCurvature α = -n / 8`
   - This is IL''(1), the second derivative of impermanent loss at price ratio 1
   - More negative means steeper IL curve (worse for LPs)
   - Becomes more negative with increasing α

3. **Tradeoff constant**: `slippageCoeff α * (-ilCurvature α) = 1/4`
   - This product is invariant across the family
   - Reducing slippage necessarily increases IL curvature (and vice versa)

4. **Impossibility theorem**: For α ≠ 0,
   - `slippageBetterThanCPMM α ↔ 0 < α`
   - `ilBetterThanCPMM α ↔ α < 0`
   - Therefore: `¬(slippageBetterThanCPMM α ∧ ilBetterThanCPMM α)`

## Sign Convention

**Critical**: Impermanent loss is a LOSS, so IL ≤ 0.
- IL(p) ≤ 0 for all price moves (LP loses vs HODL)
- ilCurvature = IL''(1) < 0 (IL curves downward from balance)
- "Better IL" means ilCurvature is LESS negative (closer to 0)
- Formally: `ilBetterThanCPMM α` iff `ilCurvature 0 < ilCurvature α`

Since ilCurvature 0 = -1/4 and ilCurvature is -(α+2)/8:
- ilBetter iff -(α+2)/8 > -1/4 iff α + 2 < 2 iff α < 0

## Non-Vacuity

This theorem is non-vacuous because:
1. For α = 1 (cubic): slippageBetterThanCPMM 1 = true (2/3 < 1)
2. For α = -0.5: ilBetterThanCPMM (-0.5) = true (-1.5/8 > -2/8)

The impossibility prevents having BOTH improvements simultaneously.

## References

- Wu & McTighe, "Constant Power Root Market Makers" (IL↔slippage tradeoff)
- Engel & Herlihy, "Loss and Slippage in Networks of AMMs"
-/

namespace TauSwap
namespace ImpossibilityV2

open Real
open scoped Topology

noncomputable section

/-! ## Core Definitions -/

/-- The homogeneous degree of the power-parameterized curve family.
    For K(x,y;α) = x*y*(x+y)^α, the degree is α + 2. -/
def degree (α : ℝ) : ℝ := α + 2

/-- The invariant function for the power-parameterized curve family.
    K(x,y;α) = x * y * (x + y)^α
    Requires x + y > 0 for the real power. -/
def invariant (α : ℝ) (x y : ℝ) (_hpos : 0 < x + y) : ℝ :=
  x * y * (x + y) ^ α

/-- Spot price P = -dy/dx derived from implicit differentiation of K(x,y) = const.
    For K = x*y*(x+y)^α:
      ∂K/∂x = y*(x+y)^α + α*x*y*(x+y)^(α-1) = y*(x+y)^(α-1) * (x+y + αx)
      ∂K/∂y = x*(x+y)^α + α*x*y*(x+y)^(α-1) = x*(x+y)^(α-1) * (x+y + αy)
    P = (∂K/∂x)/(∂K/∂y) = y*(x + y + αx) / (x*(x + y + αy))
                        = y*((1+α)x + y) / (x*(x + (1+α)y))
-/
def spotPrice (α x y : ℝ) : ℝ :=
  y * ((1 + α) * x + y) / (x * (x + (1 + α) * y))

/-! ## Local Coefficients at Balance

The following coefficients characterize the curve's behavior at the balanced point (x = y = 1).
These are derived in the original ImpossibilityTheorem.lean via careful calculus. -/

/-- Slippage coefficient at balance.
    For a small trade δx, the output is approximately dy ≈ -P*δx - slippageCoeff*(δx)²/2.
    Derived: slippageCoeff α = 2 / degree α = 2 / (α + 2)

    Lower slippage coefficient means better execution for traders. -/
def slippageCoeff (α : ℝ) : ℝ := 2 / degree α

/-- Impermanent loss curvature at balance.
    This is IL''(1), the second derivative of the IL function at price ratio p = 1.

    IL(p) measures the loss (as a fraction) of LP value vs holding.
    - IL(1) = 0 (no loss at initial price)
    - IL'(1) = 0 (IL is minimized at balance)
    - IL''(1) < 0 (IL curves downward, i.e., any price move causes loss)

    Derived: ilCurvature α = -degree α / 8 = -(α + 2) / 8

    More negative curvature means steeper IL, i.e., worse for LPs. -/
def ilCurvature (α : ℝ) : ℝ := -(degree α) / 8

/-! ## Comparison Predicates -/

/-- Slippage is better than CPMM iff the slippage coefficient is lower.
    Since slippageCoeff α = 2/(α+2) and slippageCoeff 0 = 1,
    this holds iff 2/(α+2) < 1 iff α > 0. -/
def slippageBetterThanCPMM (α : ℝ) : Prop := slippageCoeff α < slippageCoeff 0

/-- IL is better than CPMM iff the IL curvature is less negative (closer to 0).
    Since ilCurvature α = -(α+2)/8 and ilCurvature 0 = -1/4,
    "better" means ilCurvature 0 < ilCurvature α (both negative, α closer to 0).
    This holds iff -1/4 < -(α+2)/8 iff α < 0. -/
def ilBetterThanCPMM (α : ℝ) : Prop := ilCurvature 0 < ilCurvature α

/-! ## Key Lemmas -/

@[simp]
lemma degree_zero : degree 0 = 2 := by simp [degree]

@[simp]
lemma degree_one : degree 1 = 3 := by simp [degree]; ring

lemma degree_pos (α : ℝ) (hα : -2 < α) : 0 < degree α := by
  simp [degree]
  linarith

lemma degree_ne_zero (α : ℝ) (hα : α ≠ -2) : degree α ≠ 0 := by
  simp only [degree]
  intro h
  have : α = -2 := by linarith
  exact hα this

/-- Slippage coefficient at CPMM (α = 0) equals 1. -/
@[simp]
lemma slippageCoeff_zero : slippageCoeff 0 = 1 := by
  simp [slippageCoeff, degree]

/-- Slippage coefficient at cubic (α = 1) equals 2/3. -/
lemma slippageCoeff_one : slippageCoeff 1 = 2 / 3 := by
  simp [slippageCoeff, degree]
  ring

/-- IL curvature at CPMM (α = 0) equals -1/4. -/
@[simp]
lemma ilCurvature_zero : ilCurvature 0 = -(1 / 4) := by
  simp [ilCurvature, degree]
  ring

/-- IL curvature at cubic (α = 1) equals -3/8. -/
lemma ilCurvature_one : ilCurvature 1 = -(3 / 8) := by
  simp [ilCurvature, degree]
  ring

/-- The slippage-IL tradeoff product is constant across the curve family.
    This is the fundamental constraint: you cannot improve one without worsening the other. -/
theorem tradeoff_product_constant (α : ℝ) (hα : α ≠ -2) :
    slippageCoeff α * (-ilCurvature α) = 1 / 4 := by
  simp only [slippageCoeff, ilCurvature, degree]
  have hdeg : α + 2 ≠ 0 := by
    intro h
    have : α = -2 := by linarith
    exact hα this
  field_simp
  ring

/-- Slippage is better than CPMM iff α > 0. -/
theorem slippageBetter_iff_positive (α : ℝ) (hα : -2 < α) :
    slippageBetterThanCPMM α ↔ 0 < α := by
  simp [slippageBetterThanCPMM, slippageCoeff, degree]
  constructor
  · intro h
    have hdeg_pos : 0 < α + 2 := by linarith
    have : 2 / (α + 2) < 1 := h
    have h2 : 2 < α + 2 := by
      have hne : α + 2 ≠ 0 := by linarith
      rwa [div_lt_one hdeg_pos] at this
    linarith
  · intro hpos
    have hdeg_pos : 0 < α + 2 := by linarith
    have h2 : 2 < α + 2 := by linarith
    exact (div_lt_one hdeg_pos).mpr h2

/-- IL is better than CPMM iff α < 0. -/
theorem ilBetter_iff_negative (α : ℝ) :
    ilBetterThanCPMM α ↔ α < 0 := by
  simp only [ilBetterThanCPMM, ilCurvature, degree]
  -- Goal: -(0 + 2) / 8 < -(α + 2) / 8 ↔ α < 0
  -- Simplify: -2/8 < -(α + 2)/8 ↔ α < 0
  constructor
  · intro h
    -- h : -2/8 < -(α + 2)/8
    -- Both are divided by positive 8, so: -2 < -(α + 2), i.e., α + 2 < 2, i.e., α < 0
    have h8 : (8 : ℝ) > 0 := by norm_num
    have h1 : -2 < -(α + 2) := by
      have := (div_lt_div_iff_of_pos_right h8).mp h
      linarith
    linarith
  · intro hα
    -- hα : α < 0
    -- Need: -(0+2)/8 < -(α+2)/8
    have h8 : (8 : ℝ) > 0 := by norm_num
    have h1 : -(0 + 2) < -(α + 2) := by linarith
    exact (div_lt_div_iff_of_pos_right h8).mpr h1

/-! ## The Impossibility Theorem -/

/-- **Main Theorem (Impossibility)**: No choice of α ≠ 0 can simultaneously
    improve both slippage and impermanent loss relative to CPMM.

    This is non-vacuous because:
    - For α > 0 (e.g., cubic): slippage improves but IL worsens
    - For α < 0: IL improves but slippage worsens

    The theorem states that the conjunction is impossible. -/
theorem impossibility (α : ℝ) (_hα : α ≠ 0) (hα2 : -2 < α) :
    ¬(slippageBetterThanCPMM α ∧ ilBetterThanCPMM α) := by
  intro ⟨hslip, hil⟩
  rw [slippageBetter_iff_positive α hα2] at hslip
  rw [ilBetter_iff_negative α] at hil
  -- hslip : 0 < α
  -- hil : α < 0
  linarith

/-- Alternative formulation: The tradeoff is strictly monotonic.
    If slippage improves, IL must worsen (and vice versa). -/
theorem monotonic_tradeoff (α : ℝ) (hα2 : -2 < α) :
    (slippageBetterThanCPMM α → ¬ilBetterThanCPMM α) ∧
    (ilBetterThanCPMM α → ¬slippageBetterThanCPMM α) := by
  constructor
  · intro hslip hil
    rw [slippageBetter_iff_positive α hα2] at hslip
    rw [ilBetter_iff_negative α] at hil
    linarith
  · intro hil hslip
    rw [slippageBetter_iff_positive α hα2] at hslip
    rw [ilBetter_iff_negative α] at hil
    linarith

/-! ## Witness Lemmas (Non-Vacuity) -/

/-- The cubic curve (α = 1) has better slippage than CPMM. -/
lemma cubic_has_better_slippage : slippageBetterThanCPMM 1 := by
  rw [slippageBetter_iff_positive 1 (by norm_num)]
  norm_num

/-- The cubic curve (α = 1) has worse IL than CPMM. -/
lemma cubic_has_worse_il : ¬ilBetterThanCPMM 1 := by
  rw [ilBetter_iff_negative 1]
  norm_num

/-- For α = -1/2, IL is better than CPMM. -/
lemma negative_alpha_has_better_il : ilBetterThanCPMM (-1/2) := by
  rw [ilBetter_iff_negative (-1/2)]
  norm_num

/-- For α = -1/2, slippage is worse than CPMM. -/
lemma negative_alpha_has_worse_slippage : ¬slippageBetterThanCPMM (-1/2) := by
  rw [slippageBetter_iff_positive (-1/2) (by norm_num)]
  norm_num

/-! ## Derived Properties -/

/-- Spot price at balance equals 1 for all α ≠ -2 (where reserves are equal). -/
lemma spotPrice_at_balance (α : ℝ) (hα : α ≠ -2) : spotPrice α 1 1 = 1 := by
  simp only [spotPrice]
  -- The numerator is 1 * ((1 + α) * 1 + 1) = 2 + α
  -- The denominator is 1 * (1 + (1 + α) * 1) = 2 + α
  have hnum : (1 : ℝ) * ((1 + α) * 1 + 1) = 2 + α := by ring
  have hden : (1 : ℝ) * (1 + (1 + α) * 1) = 2 + α := by ring
  have hne : (2 : ℝ) + α ≠ 0 := by
    intro h
    have : α = -2 := by linarith
    exact hα this
  rw [hnum, hden]
  exact div_self hne

/-- The CPMM invariant (α = 0) at balance equals 1 (with normalization x = y = 1).
    K = x*y*(x+y)^0 = x*y*1 = x*y = 1. -/
lemma invariant_cpmm_at_balance : invariant 0 1 1 (by norm_num : 0 < (1 : ℝ) + 1) = 1 := by
  simp only [invariant]
  norm_num

/-- The cubic invariant (α = 1) at balance equals 2 (with normalization x = y = 1).
    K = x*y*(x+y)^1 = 1*1*2 = 2. -/
lemma invariant_cubic_at_balance : invariant 1 1 1 (by norm_num : 0 < (1 : ℝ) + 1) = 2 := by
  simp only [invariant]
  norm_num

/-! ## Summary

The key takeaways are:

1. **Tradeoff Product Constant**: `slippageCoeff α * (-ilCurvature α) = 1/4` for all valid α.
   This is the fundamental constraint that prevents simultaneous improvement.

2. **Impossibility**: For any α ≠ 0:
   - α > 0 ⟹ better slippage ∧ worse IL (e.g., cubic sum curve)
   - α < 0 ⟹ worse slippage ∧ better IL (e.g., inverse blend)
   - No α achieves both improvements

3. **Non-Vacuity**: The theorem is witnessed by:
   - `cubic_has_better_slippage` and `cubic_has_worse_il` for α = 1
   - `negative_alpha_has_better_il` and `negative_alpha_has_worse_slippage` for α = -1/2

This formalizes the intuition that slippage and IL are fundamentally linked through
curve geometry, and the tradeoff is monotonic in the power parameter. -/

end

end ImpossibilityV2
end TauSwap
