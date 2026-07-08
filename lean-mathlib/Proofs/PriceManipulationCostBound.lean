import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Average-Price Manipulation Cost Bound for CPMM

This file proves that the minimum cost to move the fee-free CPMM average
execution price by a relative amount ε is at least `ε * M / (1 - ε)`, where
`M` is the input reserve.

For small ε, this simplifies to approximately `ε * M`, meaning the cost of
average-price manipulation is proportional to the pool's liquidity.

## Main Results

1. **Average Execution Price** (`cpmm_average_execution_price_eq`): A fee-free
   CPMM trade of size x has average execution price `K/(M+x)`.

2. **Relative Average-Price Change** (`relative_average_price_change_eq`): The
   relative average-price change from a trade of size x is `x / (M + x)`.

3. **Manipulation Cost Lower Bound** (`average_price_move_cost_lower_bound`):
   To achieve a relative average-price change of at least ε, the trade size x
   must satisfy `x ≥ ε * M / (1 - ε)`.

4. **Small-Epsilon Approximation** (`average_price_move_cost_approx`): For
   small ε, the average-price movement cost is at least `ε * M`.

5. **Batch Manipulation Cost** (`batch_average_price_move_cost`): For a batch
   of n intents with total input I, the relative average-price change is
   `I / (M + I)`. To move this price by ε, the batch must have total input
   `I ≥ ε * M / (1 - ε)`.

6. **No Cheap Manipulation** (`no_cheap_average_price_manipulation`): No
   attacker can move the average execution price by ε with cost less than
   `ε * M / (1 - ε)`.

7. **Linear Scaling** (`average_price_move_cost_scales_linearly`): Doubling
   the pool liquidity doubles the cost bound.

## Mathematical Model

For a fee-free CPMM pool with reserves (M, K):
- Initial marginal price: P₀ = K / M
- Average execution price for input x: K / (M + x)
- Relative average-price change: 1 - M/(M+x) = x/(M+x)

The key theorem: `x / (M + x) ≥ ε` iff `x ≥ ε * M / (1 - ε)`.

## Why This Matters

This gives a formal manipulation cost bound for average-execution-price
surfaces. It is not the post-trade CPMM marginal price with updated output
reserve, and it does not include fees or integer rounding.
-/

namespace Proofs
namespace PriceManipulationCostBound

/-! ## Section 1: CPMM Price Model -/

/-- The CPMM initial marginal price before a trade: `K / M`. -/
def cpmmInitialAveragePrice (M K : ℚ) : ℚ := K / M

/-- The fee-free CPMM average execution price for a trade of size x:
    output/x = `K / (M + x)`. -/
def cpmmAverageExecutionPrice (M K x : ℚ) : ℚ := K / (M + x)

/-- The relative average-price change from a trade of size x: `x / (M + x)`. -/
def relativeAveragePriceChange (M x : ℚ) : ℚ := x / (M + x)

/-! ## Section 2: Average Execution Price -/

/-- A fee-free CPMM trade of size x has average execution price `K/(M+x)`. -/
theorem cpmm_average_execution_price_eq (M K x : ℚ) :
    cpmmAverageExecutionPrice M K x = cpmmInitialAveragePrice (M + x) K := by
  rfl

/-- The average execution price is below the initial marginal price for a
    positive trade. -/
theorem average_execution_price_decreases (M K x : ℚ) (hM : 0 < M) (hK : 0 < K) (hx : 0 < x) :
    cpmmAverageExecutionPrice M K x < cpmmInitialAveragePrice M K := by
  unfold cpmmAverageExecutionPrice cpmmInitialAveragePrice
  have hMx : 0 < M + x := by linarith [hM, hx]
  rw [div_lt_div_iff₀ hMx hM]
  nlinarith [hM, hx, hK]

/-- The relative average-price change equals x / (M + x). -/
theorem relative_average_price_change_eq (M K x : ℚ) (hM : 0 < M) (hK : 0 < K) (hx : 0 ≤ x) :
    1 - cpmmAverageExecutionPrice M K x / cpmmInitialAveragePrice M K =
      relativeAveragePriceChange M x := by
  unfold cpmmAverageExecutionPrice cpmmInitialAveragePrice relativeAveragePriceChange
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hMx_ne : M + x ≠ 0 := ne_of_gt (by linarith [hM, hx])
  field_simp
  ring

/-! ## Section 3: Manipulation Cost Lower Bound -/

/-- The relative average-price change x/(M+x) is strictly increasing in x. -/
theorem relative_average_change_increasing (M x₁ x₂ : ℚ) (hM : 0 < M) (hx₁ : 0 ≤ x₁) (_hx₂ : 0 ≤ x₂)
    (h : x₁ < x₂) :
    relativeAveragePriceChange M x₁ < relativeAveragePriceChange M x₂ := by
  unfold relativeAveragePriceChange
  have hMx₁ : 0 < M + x₁ := by linarith [hM, hx₁]
  have hMx₂ : 0 < M + x₂ := by linarith [hM, h]
  rw [div_lt_div_iff₀ hMx₁ hMx₂]
  nlinarith [h, hM, hx₁]

/-- To achieve relative average-price change ≥ ε, the trade size x must satisfy
    `x ≥ ε * M / (1 - ε)`.

    This is the average-price manipulation cost lower bound.

    Proof: `x / (M + x) ≥ ε` iff `x ≥ ε * (M + x)` iff `x * (1 - ε) ≥ ε * M`
    iff `x ≥ ε * M / (1 - ε)` (when `0 < ε < 1`). -/
theorem average_price_move_cost_lower_bound (M ε : ℚ) (hM : 0 < M) (_hε : 0 < ε) (hε' : ε < 1) :
    ∀ x : ℚ, 0 ≤ x → relativeAveragePriceChange M x ≥ ε → x ≥ ε * M / (1 - ε) := by
  intro x hx hchange
  unfold relativeAveragePriceChange at hchange
  have hMx : 0 < M + x := by linarith [hM, hx]
  have h1mε : 0 < 1 - ε := by linarith [hε']
  -- x / (M + x) ≥ ε  →  ε * (M + x) ≤ x
  have hchange' : ε ≤ x / (M + x) := hchange
  rw [le_div_iff₀ hMx] at hchange'
  -- hchange' : ε * (M + x) ≤ x
  -- x ≥ ε * M + ε * x  →  x * (1 - ε) ≥ ε * M
  have hstep2 : x * (1 - ε) ≥ ε * M := by linarith [hchange']
  -- x * (1 - ε) ≥ ε * M  →  x ≥ ε * M / (1 - ε)
  have hstep3 : x ≥ ε * M / (1 - ε) := by
    show ε * M / (1 - ε) ≤ x
    rw [div_le_iff₀ h1mε]
    linarith [hstep2]
  exact hstep3

/-- The average-price movement cost lower bound is achievable: a trade of size
    `ε * M / (1 - ε)` achieves exactly relative average-price change ε. -/
theorem average_price_move_cost_achievable (M ε : ℚ) (hM : 0 < M) (hε : 0 < ε) (hε' : ε < 1) :
    relativeAveragePriceChange M (ε * M / (1 - ε)) = ε := by
  unfold relativeAveragePriceChange
  have h1mε : 0 < 1 - ε := by linarith [hε']
  have hMx : 0 < M + ε * M / (1 - ε) := by
    have : 0 < ε * M / (1 - ε) := by
      rw [lt_div_iff₀ h1mε]
      nlinarith [hM, hε]
    linarith [hM, this]
  field_simp
  nlinarith [hε, hε', hM]

/-! ## Section 4: Small-Epsilon Approximation -/

/-- For 0 < ε ≤ 1/2, the average-price movement cost is at least ε * M.

    This is the small-epsilon approximation: when ε is small,
    `ε * M / (1 - ε) ≥ ε * M` because `1 / (1 - ε) ≥ 1`. -/
theorem average_price_move_cost_approx (M ε : ℚ) (hM : 0 < M) (hε : 0 < ε) (hε' : ε ≤ 1/2) :
    ∀ x : ℚ, 0 ≤ x → relativeAveragePriceChange M x ≥ ε → x ≥ ε * M := by
  intro x hx hchange
  have hbound := average_price_move_cost_lower_bound M ε hM hε (by linarith [hε'])
  have hcost := hbound x hx hchange
  have h1mε : 0 < 1 - ε := by linarith [hε']
  -- ε * M / (1 - ε) ≥ ε * M  because  1/(1-ε) ≥ 1  when  ε ≥ 0
  have : ε * M / (1 - ε) ≥ ε * M := by
    show ε * M ≤ ε * M / (1 - ε)
    rw [le_div_iff₀ h1mε]
    -- Goal: ε * M * (1 - ε) ≤ ε * M
    -- = ε * M - ε * M * ε ≤ ε * M
    -- = -ε * M * ε ≤ 0
    -- = ε * M * ε ≥ 0  (true since ε ≥ 0 and M ≥ 0)
    have hεMε : ε * M * ε ≥ 0 := by positivity
    have hexpand : ε * M * (1 - ε) = ε * M - ε * M * ε := by ring
    linarith [hεMε, hexpand]
  linarith [hcost, this]

/-! ## Section 5: Batch Manipulation Cost -/

/-- For a batch with total input I, the relative average-price change is
    I / (M + I). -/
theorem batch_relative_average_price_change (M I : ℚ) :
    relativeAveragePriceChange M I = I / (M + I) := by
  rfl

/-- To move the batch average execution price by ε, the total batch input must
    be at least `ε * M / (1 - ε)`. -/
theorem batch_average_price_move_cost (M ε : ℚ) (hM : 0 < M) (hε : 0 < ε) (hε' : ε < 1) :
    ∀ I : ℚ, 0 ≤ I → relativeAveragePriceChange M I ≥ ε → I ≥ ε * M / (1 - ε) := by
  exact average_price_move_cost_lower_bound M ε hM hε hε'

/-! ## Section 6: No Cheap Average-Price Manipulation -/

/-- No attacker can move the average execution price by ε with cost less than
    `ε * M / (1 - ε)`.

    If an attacker spends x < ε * M / (1 - ε), the relative average-price
    change is strictly less than ε. -/
theorem no_cheap_average_price_manipulation (M ε : ℚ) (hM : 0 < M) (hε : 0 < ε) (hε' : ε < 1) :
    ∀ x : ℚ, 0 ≤ x → x < ε * M / (1 - ε) → relativeAveragePriceChange M x < ε := by
  intro x hx hbelow
  by_contra h_not
  push_neg at h_not
  have hbound := average_price_move_cost_lower_bound M ε hM hε hε' x hx h_not
  linarith [hbelow, hbound]

/-! ## Section 7: Concrete Witnesses -/

/-- Witness: pool with M=10000, to move average execution price by 10% (ε=0.1),
    need trade size ≥ 0.1 * 10000 / 0.9 = 10000/9 ≈ 1111.11.

    A trade of 1000 gives relative change 1000/11000 ≈ 9.09% < 10%.
    A trade of 1112 gives relative change 1112/11112 ≈ 10.01% ≥ 10%. -/
theorem witness_manipulation_10pct :
    relativeAveragePriceChange 10000 1000 < 1/10 ∧
    relativeAveragePriceChange 10000 1112 ≥ 1/10 := by
  unfold relativeAveragePriceChange
  constructor
  · norm_num
  · norm_num

/-- Witness: pool with M=100000, to move average execution price by 1% (ε=0.01),
    need trade size ≥ 0.01 * 100000 / 0.99 ≈ 1010.1.

    A trade of 1000 gives relative change 1000/101000 ≈ 0.99% < 1%.
    A trade of 1011 gives relative change 1011/101011 ≈ 1.001% ≥ 1%. -/
theorem witness_manipulation_1pct :
    relativeAveragePriceChange 100000 1000 < 1/100 ∧
    relativeAveragePriceChange 100000 1011 ≥ 1/100 := by
  unfold relativeAveragePriceChange
  constructor
  · norm_num
  · norm_num

/-! ## Section 8: Linear Scaling -/

/-- The average-price movement cost scales linearly with pool liquidity.

    For any ε, doubling M doubles the manipulation cost. -/
theorem average_price_move_cost_scales_linearly (M ε : ℚ) (hM : 0 < M) (hε : 0 < ε) (hε' : ε < 1) :
    ε * (2 * M) / (1 - ε) = 2 * (ε * M / (1 - ε)) := by
  have h1mε : 1 - ε ≠ 0 := by linarith [hε']
  field_simp

end PriceManipulationCostBound
end Proofs
