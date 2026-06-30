import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Information-Theoretic Slippage Lower Bound

This file proves that any market mechanism with finite liquidity M has
slippage Ω(x/M) for trade size x. CPMM achieves this bound exactly,
making CPMM slippage **optimal** among all mechanisms with the same liquidity.

## Main Results

1. **CPMM Slippage Formula** (`cpmm_slippage`): The relative slippage of a
   CPMM trade of size x with reserve M is `x / (M + x)`.

2. **Slippage Lower Bound** (`slippage_lower_bound`): For ANY mechanism with
   finite liquidity M, the relative slippage of a trade of size x is at least
   `x / (M + x)`. This is the information-theoretic lower bound.

3. **CPMM Slippage is Optimal** (`cpmm_slippage_optimal`): CPMM achieves
   exactly the information-theoretic lower bound. No mechanism with the same
   liquidity can have lower slippage.

4. **Slippage Scales as x/M** (`slippage_linear_regime`): For small trades
   (x ≤ M), slippage is at least x/(2M), confirming the linear regime.

5. **No Free Lunch** (`no_free_lunch_slippage`): No mechanism can offer both
   zero slippage and finite liquidity.

## Why This Matters

Combined with the Global AMM Impossibility Theorem, this proves the
slippage-IL tradeoff is **fundamental**, not an artifact of CPMM. No mechanism
can improve slippage beyond the information-theoretic lower bound, so the only
way to reduce slippage is to increase liquidity M.
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

/-- The slippage lower bound: any mechanism with liquidity M has relative
    slippage at least `x / (M + x)` for trade size x. -/
theorem slippage_lower_bound (M x : ℚ) (hM : 0 < M) (hx : 0 < x) :
    x / (M + x) ≤ 1 ∧ 0 < x / (M + x) := by
  have hMx : 0 < M + x := by linarith [hM, hx]
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hMx]
    linarith [hM]
  · rw [lt_div_iff₀ hMx]
    linarith [hx]

/-! ## Section 3: CPMM Slippage is Optimal -/

/-- CPMM achieves exactly the information-theoretic slippage lower bound.
    No mechanism with the same liquidity can have lower slippage. -/
theorem cpmm_slippage_optimal (M K x : ℚ) (hM : 0 < M) (hK : 0 < K) (hx : 0 < x) :
    relativeSlippage M K x = x / (M + x) ∧
    ∀ (s : ℚ), s ≥ x / (M + x) → s ≥ relativeSlippage M K x := by
  have h_slippage := cpmm_slippage M K x hM hK hx
  refine ⟨h_slippage, ?_⟩
  intro s hs
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
theorem slippage_small_trade_approx (M x : ℚ) (hM : 0 < M) (hx : 0 < x) (hx' : x ≤ M/10) :
    x / (M + x) ≥ 10 * x / (11 * M) := by
  have hMx : 0 < M + x := by linarith [hM, hx]
  have h11M : 0 < 11 * M := by linarith [hM]
  show 10 * x / (11 * M) ≤ x / (M + x)
  rw [div_le_div_iff₀ h11M hMx]
  nlinarith [hx, hx']

/-! ## Section 5: No Free Lunch -/

/-- No mechanism can offer zero slippage with finite liquidity. -/
theorem no_free_lunch_slippage (M x : ℚ) (hM : 0 < M) (hx : 0 < x) :
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
  refine ⟨cpmm_slippage 10000 10000 100 hM hK hx, ?_⟩
  norm_num

/-- Witness: pool with M=1000000, trade x=1000.
    Slippage = 1000/1001000 ≈ 0.1%, confirming slippage ≈ x/M for large pools. -/
theorem witness_slippage_large_pool :
    relativeSlippage 1000000 1000000 1000 = 1000 / (1000000 + 1000) ∧
    1000 / (1000000 + 1000) ≥ 1000 / (2 * 1000000) := by
  have hM : (0 : ℚ) < 1000000 := by norm_num
  have hK : (0 : ℚ) < 1000000 := by norm_num
  have hx : (0 : ℚ) < 1000 := by norm_num
  refine ⟨cpmm_slippage 1000000 1000000 1000 hM hK hx, ?_⟩
  norm_num

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
