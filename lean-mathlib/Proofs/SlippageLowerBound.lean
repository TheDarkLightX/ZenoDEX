import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# CPMM Slippage Formula and Lower-Bound Schema

This file proves exact rational CPMM slippage formulas and a reusable
lower-bound schema. It does not encode arbitrary market mechanisms, so it should
not be cited as a universal information-theoretic optimality theorem without an
external model proving that every admissible mechanism has slippage at least
`x / (M + x)`.

## Main Results

1. **CPMM Slippage Formula** (`cpmm_slippage`): The relative slippage of a
   CPMM trade of size x with reserve M is `x / (M + x)`.

2. **CPMM Slippage Fraction Bounds** (`cpmm_slippage_fraction_bounds`): The
   candidate floor `x / (M + x)` lies in `(0, 1]`.

3. **CPMM Matches Assumed Floor** (`cpmm_slippage_matches_assumed_floor`): If
   a separate model establishes `x / (M + x)` as a lower-bound floor, CPMM
   matches it exactly.

4. **Slippage Scales as x/M** (`slippage_linear_regime`): For small trades
   (x ≤ M), slippage is at least x/(2M), confirming the linear regime.

5. **CPMM Positive Slippage** (`cpmm_positive_slippage`): CPMM slippage is
   positive for positive trade size and reserve.

## Why This Matters

These lemmas are useful as a CPMM certificate and as a proof target for a
future universal lower-bound model. The universal model remains a separate
obligation.
-/

namespace Proofs
namespace SlippageLowerBound

/-! ## Section 1: CPMM Slippage Formula -/

def cpmmOutput (M K x : ℚ) : ℚ := K * x / (M + x)
def cpmmMarginalPrice (M K : ℚ) : ℚ := K / M
def cpmmAveragePrice (M K x : ℚ) : ℚ := cpmmOutput M K x / x
def relativeSlippage (M K x : ℚ) : ℚ := 1 - cpmmAveragePrice M K x / cpmmMarginalPrice M K

/-- The CPMM relative slippage equals `x / (M + x)`. -/
theorem cpmm_slippage (M K x : ℚ) (hM : 0 < M) (hK : 0 < K) (hx : 0 < x) :
    relativeSlippage M K x = x / (M + x) := by
  unfold relativeSlippage cpmmAveragePrice cpmmOutput cpmmMarginalPrice
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hMx_ne : M + x ≠ 0 := ne_of_gt (by linarith [hM, hx])
  have hx_ne : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

/-! ## Section 2: Slippage Lower Bound -/

/-- The CPMM slippage floor candidate lies in `(0, 1]`. -/
theorem cpmm_slippage_fraction_bounds (M x : ℚ) (hM : 0 < M) (hx : 0 < x) :
    x / (M + x) ≤ 1 ∧ 0 < x / (M + x) := by
  have hMx : 0 < M + x := by linarith [hM, hx]
  constructor
  · rw [div_le_iff₀ hMx]
    linarith [hM]
  · rw [lt_div_iff₀ hMx]
    linarith [hx]

/-! ## Section 3: CPMM Slippage is Optimal -/

/-- CPMM exactly matches the candidate floor `x/(M+x)`. If a separate model
    proves every admissible mechanism has slippage at least this floor, this
    theorem is the CPMM-side achievability witness. -/
theorem cpmm_slippage_matches_assumed_floor (M K x : ℚ) (hM : 0 < M) (hK : 0 < K) (hx : 0 < x) :
    relativeSlippage M K x = x / (M + x) ∧
    ∀ (s : ℚ), s ≥ x / (M + x) → s ≥ relativeSlippage M K x := by
  have h_slippage := cpmm_slippage M K x hM hK hx
  constructor
  · exact h_slippage
  · intro s hs
    rw [h_slippage]
    exact hs

/-! ## Section 4: Slippage Scales as x/M -/

/-- For small trades (x ≤ M), the slippage is at least x / (2M). -/
theorem slippage_linear_regime (M x : ℚ) (hM : 0 < M) (hx : 0 < x) (hx' : x ≤ M) :
    x / (M + x) ≥ x / (2 * M) := by
  have hMx : 0 < M + x := by linarith [hM, hx]
  have h2M : 0 < 2 * M := by linarith [hM]
  show x / (2 * M) ≤ x / (M + x)
  rw [div_le_div_iff₀ h2M hMx]
  nlinarith [hM, hx, hx']

/-- For small trades (x ≤ M/10), slippage ≥ 10x/(11M) ≈ x/M. -/
theorem slippage_small_trade_approx (M x : ℚ) (_hM : 0 < M) (hx : 0 < x) (hx' : x ≤ M/10) :
    x / (M + x) ≥ 10 * x / (11 * M) := by
  have hMpos : 0 < M := by nlinarith [hx, hx']
  have hMx : 0 < M + x := by linarith [hMpos, hx]
  have h11M : 0 < 11 * M := by linarith [hMpos]
  show 10 * x / (11 * M) ≤ x / (M + x)
  rw [div_le_div_iff₀ h11M hMx]
  nlinarith [hx, hx']

/-! ## Section 5: Positive CPMM Slippage -/

/-- CPMM slippage is positive for positive reserve and trade size. -/
theorem cpmm_positive_slippage (M x : ℚ) (hM : 0 < M) (hx : 0 < x) :
    0 < x / (M + x) := by
  have hMx : 0 < M + x := by linarith [hM, hx]
  rw [lt_div_iff₀ hMx]
  linarith [hx]

/-- Slippage is strictly increasing in trade size. -/
theorem slippage_increasing (M x₁ x₂ : ℚ) (hM : 0 < M) (hx₁ : 0 < x₁) (_hx₂ : 0 < x₂)
    (h : x₁ < x₂) :
    x₁ / (M + x₁) < x₂ / (M + x₂) := by
  have hMx₁ : 0 < M + x₁ := by linarith [hM, hx₁]
  have hMx₂ : 0 < M + x₂ := by linarith [hM, h]
  rw [div_lt_div_iff₀ hMx₁ hMx₂]
  nlinarith [h, hM, hx₁]

/-! ## Section 6: Concrete Witnesses -/

/-- Witness: pool with M=10000, trade x=100.
    Slippage = 100/10100 ≈ 0.99%, approximately x/M = 1%. -/
theorem witness_slippage_1pct :
    relativeSlippage 10000 10000 100 = 100 / (10000 + 100) ∧
    100 / (10000 + 100) ≥ 100 / (2 * 10000) := by
  have hM : (0 : ℚ) < 10000 := by norm_num
  have hK : (0 : ℚ) < 10000 := by norm_num
  have hx : (0 : ℚ) < 100 := by norm_num
  constructor
  · exact cpmm_slippage 10000 10000 100 hM hK hx
  · norm_num

/-- Witness: pool with M=1000000, trade x=1000.
    Slippage = 1000/1001000 ≈ 0.1%, confirming slippage ≈ x/M for large pools. -/
theorem witness_slippage_large_pool :
    relativeSlippage 1000000 1000000 1000 = 1000 / (1000000 + 1000) ∧
    1000 / (1000000 + 1000) ≥ 1000 / (2 * 1000000) := by
  have hM : (0 : ℚ) < 1000000 := by norm_num
  have hK : (0 : ℚ) < 1000000 := by norm_num
  have hx : (0 : ℚ) < 1000 := by norm_num
  constructor
  · exact cpmm_slippage 1000000 1000000 1000 hM hK hx
  · norm_num

/-! ## Section 7: Slippage and Liquidity Tradeoff -/

/-- Increasing liquidity reduces slippage for the same trade size. -/
theorem slippage_decreases_with_liquidity (M x : ℚ) (hM : 0 < M) (hx : 0 < x) :
    x / (2 * M + x) ≤ x / (M + x) := by
  have hMx : 0 < M + x := by linarith [hM, hx]
  have h2Mx : 0 < 2 * M + x := by linarith [hM, hx]
  rw [div_le_div_iff₀ h2Mx hMx]
  nlinarith [hM, hx]

/-- For small x, doubling liquidity approximately halves slippage. -/
theorem slippage_halves_approx (M x : ℚ) (hM : 0 < M) (hx : 0 < x) (hx' : x ≤ M/10) :
    x / (2 * M + x) ≤ 11 / 20 * (x / (M + x)) := by
  have hMx : 0 < M + x := by linarith [hM, hx]
  have h2Mx : 0 < 2 * M + x := by linarith [hM, hx]
  rw [show 11 / 20 * (x / (M + x)) = 11 * x / (20 * (M + x)) by field_simp]
  rw [div_le_div_iff₀ h2Mx (by linarith [hM, hx] : (0:ℚ) < 20 * (M + x))]
  nlinarith [hM, hx, hx']

end SlippageLowerBound
end Proofs
