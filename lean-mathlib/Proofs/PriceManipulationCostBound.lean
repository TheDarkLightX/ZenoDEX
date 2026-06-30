import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Price Manipulation Cost Bound for CPMM

This file proves that the minimum cost to move the CPMM clearing price by a
relative amount ε is at least `ε * M / (1 - ε)`, where `M` is the input reserve.

For small ε, this simplifies to approximately `ε * M`, meaning the cost of
price manipulation is proportional to the pool's liquidity.

## Main Results

1. **Price After Trade** (`cpmm_price_after_trade`): After a trade of size x
   in a CPMM pool with reserves (M, K), the price drops from `K/M` to `K/(M+x)`.

2. **Relative Price Change** (`relative_price_change_eq`): The relative price
   change from a trade of size x is `x / (M + x)`.

3. **Manipulation Cost Lower Bound** (`manipulation_cost_lower_bound`): To
   achieve a relative price change of at least ε, the trade size x must
   satisfy `x ≥ ε * M / (1 - ε)`.

4. **Small-Epsilon Approximation** (`manipulation_cost_approx`): For small ε,
   the manipulation cost is at least `ε * M`.

5. **Batch Manipulation Cost** (`batch_manipulation_cost`): For a batch of n
   intents with total input I, the relative price change is `I / (M + I)`.
   To move the price by ε, the batch must have total input `I ≥ ε * M / (1 - ε)`.

6. **No Cheap Manipulation** (`no_cheap_manipulation`): No attacker can move
   the price by ε with cost less than `ε * M / (1 - ε)`.

7. **Linear Scaling** (`manipulation_cost_scales_linearly`): Doubling the pool
   liquidity doubles the manipulation cost.

## Mathematical Model

For a CPMM pool with reserves (M, K):
- Pre-trade price: P₀ = K / M
- After trade of size x: price = K / (M + x) (marginal price drops)
- Relative price change: 1 - M/(M+x) = x/(M+x)

The key theorem: `x / (M + x) ≥ ε` iff `x ≥ ε * M / (1 - ε)`.

## Why This Matters

This gives a formal price manipulation cost bound, the key security guarantee
for oracles and TWAP calculations that read from the DEX. An attacker who
wants to move the price by ε must spend at least `ε * M / (1 - ε)`,
proportional to the pool's liquidity. Larger pools are harder to manipulate.
-/

namespace Proofs
namespace PriceManipulationCostBound

/-! ## Section 1: CPMM Price Model -/

/-- The CPMM marginal price before a trade: `K / M`. -/
def cpmmPrice (M K : ℚ) : ℚ := K / M

/-- The CPMM marginal price after a trade of size x: `K / (M + x)`. -/
def cpmmPriceAfter (M K x : ℚ) : ℚ := K / (M + x)

/-- The relative price change from a trade of size x: `x / (M + x)`. -/
def relativePriceChange (M x : ℚ) : ℚ := x / (M + x)

/-! ## Section 2: Price After Trade -/

/-- After a trade of size x, the price drops from K/M to K/(M+x). -/
theorem cpmm_price_after_trade (M K x : ℚ) :
    cpmmPriceAfter M K x = cpmmPrice (M + x) K := by
  rfl

/-- The price strictly decreases after a positive trade. -/
theorem price_decreases_after_trade (M K x : ℚ) (hM : 0 < M) (hK : 0 < K) (hx : 0 < x) :
    cpmmPriceAfter M K x < cpmmPrice M K := by
  unfold cpmmPriceAfter cpmmPrice
  have hMx : 0 < M + x := by linarith [hM, hx]
  rw [div_lt_div_iff₀ hMx hM]
  nlinarith [hM, hx, hK]

/-- The relative price change equals x / (M + x). -/
theorem relative_price_change_eq (M K x : ℚ) (hM : 0 < M) (hK : 0 < K) (hx : 0 ≤ x) :
    1 - cpmmPriceAfter M K x / cpmmPrice M K = relativePriceChange M x := by
  unfold cpmmPriceAfter cpmmPrice relativePriceChange
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hMx_ne : M + x ≠ 0 := ne_of_gt (by linarith [hM, hx])
  field_simp
  ring

/-! ## Section 3: Manipulation Cost Lower Bound -/

/-- The relative price change x/(M+x) is strictly increasing in x. -/
theorem relative_change_increasing (M x₁ x₂ : ℚ) (hM : 0 < M) (hx₁ : 0 ≤ x₁) (_hx₂ : 0 ≤ x₂)
    (h : x₁ < x₂) :
    relativePriceChange M x₁ < relativePriceChange M x₂ := by
  unfold relativePriceChange
  have hMx₁ : 0 < M + x₁ := by linarith [hM, hx₁]
  have hMx₂ : 0 < M + x₂ := by linarith [hM, h]
  rw [div_lt_div_iff₀ hMx₁ hMx₂]
  nlinarith [h, hM, hx₁]

/-- To achieve relative price change ≥ ε, the trade size x must satisfy
    `x ≥ ε * M / (1 - ε)`.

    This is the **manipulation cost lower bound**: the minimum cost to move
    the price by ε is `ε * M / (1 - ε)`.

    Proof: `x / (M + x) ≥ ε` iff `x ≥ ε * (M + x)` iff `x * (1 - ε) ≥ ε * M`
    iff `x ≥ ε * M / (1 - ε)` (when `0 < ε < 1`). -/
theorem manipulation_cost_lower_bound (M ε : ℚ) (hM : 0 < M) (_hε : 0 < ε) (hε' : ε < 1) :
    ∀ x : ℚ, 0 ≤ x → relativePriceChange M x ≥ ε → x ≥ ε * M / (1 - ε) := by
  intro x hx hchange
  unfold relativePriceChange at hchange
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

/-- The manipulation cost lower bound is achievable: a trade of size
    `ε * M / (1 - ε)` achieves exactly relative price change ε. -/
theorem manipulation_cost_achievable (M ε : ℚ) (hM : 0 < M) (hε : 0 < ε) (hε' : ε < 1) :
    relativePriceChange M (ε * M / (1 - ε)) = ε := by
  unfold relativePriceChange
  have h1mε : 0 < 1 - ε := by linarith [hε']
  have hMx : 0 < M + ε * M / (1 - ε) := by
    have : 0 < ε * M / (1 - ε) := by
      rw [lt_div_iff₀ h1mε]
      nlinarith [hM, hε]
    linarith [hM, this]
  field_simp
  nlinarith [hε, hε', hM]

/-! ## Section 4: Small-Epsilon Approximation -/

/-- For 0 < ε ≤ 1/2, the manipulation cost is at least ε * M.

    This is the small-epsilon approximation: when ε is small,
    `ε * M / (1 - ε) ≥ ε * M` because `1 / (1 - ε) ≥ 1`. -/
theorem manipulation_cost_approx (M ε : ℚ) (hM : 0 < M) (hε : 0 < ε) (hε' : ε ≤ 1/2) :
    ∀ x : ℚ, 0 ≤ x → relativePriceChange M x ≥ ε → x ≥ ε * M := by
  intro x hx hchange
  have hbound := manipulation_cost_lower_bound M ε hM hε (by linarith [hε'])
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

/-- For a batch with total input I, the relative price change is I / (M + I). -/
theorem batch_relative_price_change (M I : ℚ) :
    relativePriceChange M I = I / (M + I) := by
  rfl

/-- To move the batch clearing price by ε, the total batch input must be
    at least `ε * M / (1 - ε)`. -/
theorem batch_manipulation_cost (M ε : ℚ) (hM : 0 < M) (hε : 0 < ε) (hε' : ε < 1) :
    ∀ I : ℚ, 0 ≤ I → relativePriceChange M I ≥ ε → I ≥ ε * M / (1 - ε) := by
  exact manipulation_cost_lower_bound M ε hM hε hε'

/-! ## Section 6: No Cheap Manipulation -/

/-- No attacker can move the price by ε with cost less than `ε * M / (1 - ε)`.

    If an attacker spends x < ε * M / (1 - ε), the relative price change
    is strictly less than ε. -/
theorem no_cheap_manipulation (M ε : ℚ) (hM : 0 < M) (hε : 0 < ε) (hε' : ε < 1) :
    ∀ x : ℚ, 0 ≤ x → x < ε * M / (1 - ε) → relativePriceChange M x < ε := by
  intro x hx hbelow
  by_contra h_not
  push_neg at h_not
  have hbound := manipulation_cost_lower_bound M ε hM hε hε' x hx h_not
  linarith [hbelow, hbound]

/-! ## Section 7: Concrete Witnesses -/

/-- Witness: pool with M=10000, to move price by 10% (ε=0.1),
    need trade size ≥ 0.1 * 10000 / 0.9 = 10000/9 ≈ 1111.11.

    A trade of 1000 gives relative change 1000/11000 ≈ 9.09% < 10%.
    A trade of 1112 gives relative change 1112/11112 ≈ 10.01% ≥ 10%. -/
theorem witness_manipulation_10pct :
    relativePriceChange 10000 1000 < 1/10 ∧
    relativePriceChange 10000 1112 ≥ 1/10 := by
  unfold relativePriceChange
  constructor
  · norm_num
  · norm_num

/-- Witness: pool with M=100000, to move price by 1% (ε=0.01),
    need trade size ≥ 0.01 * 100000 / 0.99 ≈ 1010.1.

    A trade of 1000 gives relative change 1000/101000 ≈ 0.99% < 1%.
    A trade of 1011 gives relative change 1011/101011 ≈ 1.001% ≥ 1%. -/
theorem witness_manipulation_1pct :
    relativePriceChange 100000 1000 < 1/100 ∧
    relativePriceChange 100000 1011 ≥ 1/100 := by
  unfold relativePriceChange
  constructor
  · norm_num
  · norm_num

/-! ## Section 8: Linear Scaling -/

/-- The manipulation cost scales linearly with pool liquidity.

    For any ε, doubling M doubles the manipulation cost. -/
theorem manipulation_cost_scales_linearly (M ε : ℚ) (hM : 0 < M) (hε : 0 < ε) (hε' : ε < 1) :
    ε * (2 * M) / (1 - ε) = 2 * (ε * M / (1 - ε)) := by
  have h1mε : 1 - ε ≠ 0 := by linarith [hε']
  field_simp

end PriceManipulationCostBound
end Proofs
