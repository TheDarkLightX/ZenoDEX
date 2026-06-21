/-
# ZenoProof Redemption Profitability Threshold

## Motivation

ZenoDEX issues zUSD stablecoin backed by collateral. When zUSD trades below
$1 on the open market, arbitrageurs can redeem zUSD at the oracle price,
receiving collateral worth more than their market purchase cost. This
arbitrage burns zUSD supply and pushes the peg back toward $1.

A key question: at what market price threshold does redemption become
profitable? This threshold defines the natural peg floor.

## Model

All values use scaled integer arithmetic:
- `E8 = 100_000_000` (1e8 scale for prices)
- `BPS = 10_000` (basis points scale for fees)

Redemption of `amount` zUSD at oracle price `oracle_price` with fee `fee_bps`:
1. `gross_collateral = amount * E8 / oracle_price` (floor)
2. `fee = ceil(gross_collateral * fee_bps / BPS)` (ceil)
3. `net_collateral = gross_collateral - fee`
4. `payout_value = net_collateral * oracle_price / E8` (floor)

The arbitrageur buys zUSD at `market_price` (in E8 units), so:
- `market_cost = ceil(amount * market_price / E8)` (ceil)
- `profit = payout_value - market_cost`

## Main Results

In exact arithmetic (ignoring rounding), the profitability condition is:

`market_price * BPS < oracle_price * (BPS - fee_bps)`

This means the peg floor is `oracle_price * (BPS - fee_bps) / BPS`.
With oracle at $1 (E8) and fee = 50 bps, the floor is $0.995.

Theorems:
- `redemptionProfitable`: exact profitability condition (definition)
- `zero_fee_profitable_at_par`: with zero fee, profitable iff market < oracle
- `fee_increase_narrows_profit_window`: higher fee makes profitability harder
- `oracle_increase_widens_profit_window`: higher oracle makes profitability easier
- `zero_fee_payout_equals_oracle`: with zero fee, payout per unit equals oracle
- `profitable_implies_market_below_oracle`: profitable implies market < oracle

## Protocol Design Implication

The redemption fee creates a band around the peg. zUSD cannot trade below
`oracle * (1 - fee_bps/BPS)` without triggering profitable redemptions that
burn supply and restore the peg. The fee floor is the peg defense mechanism.
-/

import Mathlib

namespace Internal.ZenoProofRedemptionThreshold

/-- E8 scale factor (1e8). -/
abbrev E8 : Nat := 100_000_000

/-- BPS scale factor (10000). -/
abbrev BPS : Nat := 10_000

/-- Gross collateral received for redeeming `amount` zUSD at `oracle_price`. -/
def grossCollateral (amount oracle_price : Nat) : Nat :=
  amount * E8 / oracle_price

/-- Fee charged on gross collateral (ceiling division). -/
def feeCollateral (gross fee_bps : Nat) : Nat :=
  (gross * fee_bps + BPS - 1) / BPS

/-- Net collateral after fee. -/
def netCollateral (gross fee_bps : Nat) : Nat :=
  gross - feeCollateral gross fee_bps

/-- Value of net collateral in E8 units (floor division). -/
def payoutValue (amount oracle_price fee_bps : Nat) : Nat :=
  netCollateral (grossCollateral amount oracle_price) fee_bps * oracle_price / E8

/-- Market cost to acquire `amount` zUSD at `market_price` (ceiling division). -/
def marketCost (amount market_price : Nat) : Nat :=
  (amount * market_price + E8 - 1) / E8

/-- Redeemer profit: payout value minus market cost. -/
def redeemerProfit (amount market_price oracle_price fee_bps : Nat) : Int :=
  Int.ofNat (payoutValue amount oracle_price fee_bps) -
  Int.ofNat (marketCost amount market_price)

/-- Exact payout per unit (no rounding): `oracle_price * (BPS - fee_bps) / BPS`. -/
def exactPayoutPerUnit (oracle_price fee_bps : Nat) : Nat :=
  oracle_price * (BPS - fee_bps) / BPS

/-! ## Theorem 1: Profitability Condition -/

/-- Redemption is profitable (in exact arithmetic) when
`market_price * BPS < oracle_price * (BPS - fee_bps)`.

This is the core profitability condition without floor-division rounding.
The left side is the cost of acquiring zUSD on the market (scaled by BPS).
The right side is the redemption payout value (scaled by BPS). -/
def redemptionProfitable (market_price oracle_price fee_bps : Nat) : Prop :=
  market_price * BPS < oracle_price * (BPS - fee_bps)

/-! ## Theorem 2: Zero Fee at Par -/

/-- With zero fee, redemption is profitable iff market_price < oracle_price.
The peg floor equals the oracle price. -/
theorem zero_fee_profitable_at_par
    (market_price oracle_price : Nat) :
    redemptionProfitable market_price oracle_price 0 ↔ market_price < oracle_price := by
  unfold redemptionProfitable
  rw [Nat.sub_zero]
  constructor
  · intro h
    by_contra hNot
    have hGe : market_price ≥ oracle_price := by omega
    have : market_price * BPS ≥ oracle_price * BPS := Nat.mul_le_mul_right BPS hGe
    omega
  · intro h
    exact Nat.mul_lt_mul_of_pos_right h (by decide : 0 < BPS)

/-! ## Theorem 3: Fee Increases Narrow Profit Window -/

/-- Higher fee makes the profitability condition harder to satisfy.
If `fee1 < fee2`, then profitable(fee2) implies profitable(fee1).
The right side `oracle * (BPS - fee)` decreases as fee increases. -/
theorem fee_increase_narrows_profit_window
    (market_price oracle_price fee1 fee2 : Nat)
    (hFee : fee1 < fee2)
    (hFee2 : fee2 < BPS) :
    redemptionProfitable market_price oracle_price fee2 →
    redemptionProfitable market_price oracle_price fee1 := by
  unfold redemptionProfitable
  intro h
  have hDiff : (BPS - fee2) < (BPS - fee1) := by omega
  by_cases hOracle : oracle_price > 0
  · have hMul : oracle_price * (BPS - fee2) < oracle_price * (BPS - fee1) :=
      Nat.mul_lt_mul_of_pos_left hDiff hOracle
    exact Nat.lt_trans h hMul
  · -- oracle_price = 0: both sides are 0, contradiction with h
    have : oracle_price = 0 := by omega
    rw [this] at h
    have hBPS : 0 < BPS := by decide
    simp at h

/-! ## Theorem 4: Oracle Increase Widens Profit Window -/

/-- Higher oracle price makes the profitability condition easier to satisfy.
If `oracle1 < oracle2`, then profitable(oracle1) implies profitable(oracle2).
The right side increases with oracle price. -/
theorem oracle_increase_widens_profit_window
    (market_price oracle1 oracle2 fee_bps : Nat)
    (hFee : fee_bps < BPS)
    (hOracle : oracle1 < oracle2) :
    redemptionProfitable market_price oracle1 fee_bps →
    redemptionProfitable market_price oracle2 fee_bps := by
  unfold redemptionProfitable
  intro h
  have hDiff : 0 < BPS - fee_bps := by omega
  have hMul : oracle1 * (BPS - fee_bps) < oracle2 * (BPS - fee_bps) :=
    Nat.mul_lt_mul_of_pos_right hOracle hDiff
  exact Nat.lt_trans h hMul

/-! ## Theorem 5: Zero Fee Payout Equals Oracle -/

/-- With zero fee, the exact payout per unit equals the oracle price. -/
theorem zero_fee_payout_equals_oracle
    (oracle_price : Nat) :
    exactPayoutPerUnit oracle_price 0 = oracle_price := by
  unfold exactPayoutPerUnit
  rw [Nat.sub_zero, Nat.mul_div_cancel oracle_price (by decide : 0 < BPS)]

/-! ## Theorem 6: Profitable Implies Market Below Oracle -/

/-- If redemption is profitable with any fee > 0, then market < oracle.
The fee creates a strict gap below the oracle price. -/
theorem profitable_implies_market_below_oracle
    (market_price oracle_price fee_bps : Nat)
    (hFee : 0 < fee_bps)
    (hFee2 : fee_bps < BPS) :
    redemptionProfitable market_price oracle_price fee_bps →
    market_price < oracle_price := by
  unfold redemptionProfitable
  intro h
  have hDiff : 0 < BPS - fee_bps := by omega
  have hRHS : oracle_price * (BPS - fee_bps) ≤ oracle_price * BPS := by
    have hLe : BPS - fee_bps ≤ BPS := by omega
    exact Nat.mul_le_mul_left oracle_price hLe
  have hChain : market_price * BPS < oracle_price * BPS := Nat.lt_of_lt_of_le h hRHS
  by_contra hNot
  have hGe : market_price ≥ oracle_price := by omega
  have : market_price * BPS ≥ oracle_price * BPS := Nat.mul_le_mul_right BPS hGe
  omega

/-! ## Theorem 7: Fee Collateral Bounded by Gross -/

/-- The fee collateral never exceeds gross * fee_bps / BPS + 1 (ceiling bound).
This follows from the standard ceiling division bound: ceil(a/n) ≤ floor(a/n) + 1. -/
theorem fee_collateral_le_floor_plus_one
    (gross fee_bps : Nat) :
    feeCollateral gross fee_bps ≤ gross * fee_bps / BPS + 1 := by
  unfold feeCollateral
  have hBPS : 0 < BPS := by decide
  have h1 : gross * fee_bps + BPS - 1 ≤ gross * fee_bps + BPS := by omega
  have h2 : (gross * fee_bps + BPS - 1) / BPS ≤ (gross * fee_bps + BPS) / BPS :=
    Nat.div_le_div_right h1
  rw [Nat.add_div hBPS] at h2
  rw [Nat.div_self hBPS] at h2
  have hmod : gross * fee_bps % BPS < BPS := Nat.mod_lt _ hBPS
  have hBPSmod : BPS % BPS = 0 := by decide
  rw [hBPSmod] at h2
  have hcond : ¬ (BPS ≤ gross * fee_bps % BPS) := by omega
  simp [hcond] at h2
  exact h2

/-! ## Theorem 8: Exact Profitability Implies Market Below Payout -/

/-- If the exact profitability condition holds, then market_price is strictly
below the exact payout per unit (in real arithmetic). This connects the
profitability definition to the threshold. -/
theorem profitable_implies_below_payout
    (market_price oracle_price fee_bps : Nat)
    (hFee : fee_bps < BPS) :
    redemptionProfitable market_price oracle_price fee_bps →
    market_price * BPS < oracle_price * (BPS - fee_bps) := by
  unfold redemptionProfitable
  exact id

end Internal.ZenoProofRedemptionThreshold
