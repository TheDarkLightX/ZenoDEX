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

In exact arithmetic, the oracle price cancels in the round-trip:
  payout = (amount * E8 / oracle) * (BPS - fee) / BPS * oracle / E8
         = amount * (BPS - fee) / BPS

So the payout per unit is `E8 * (BPS - fee_bps) / BPS`, independent of oracle.

The arbitrageur buys zUSD at `market_price` (in E8 units), so:
- `market_cost = ceil(amount * market_price / E8)` (ceil)
- `profit = payout_value - market_cost`

## Main Results

In exact arithmetic (ignoring rounding), the profitability condition is:

`market_price * BPS < E8 * (BPS - fee_bps)`

This means the peg floor is `E8 * (BPS - fee_bps) / BPS`.
With fee = 50 bps, the floor is $0.995 (E8 * 9995 / 10000).

Theorems:
- `redemptionProfitable`: exact profitability condition (definition)
- `zero_fee_profitable_at_par`: with zero fee, profitable iff market < E8
- `fee_increase_narrows_profit_window`: higher fee makes profitability harder
- `zero_fee_payout_equals_par`: with zero fee, payout per unit equals E8
- `profitable_implies_market_below_par`: profitable implies market < E8
- `fee_collateral_le_floor_plus_one`: ceiling division bound
- `net_collateral_le_gross`: net collateral never exceeds gross
- `fee_collateral_nonneg`: fee collateral is non-negative

The redemption fee creates a band around par ($1 = E8). zUSD cannot trade below
`E8 * (1 - fee_bps/BPS)` without triggering profitable redemptions that
burn supply and restore the peg. The fee floor is the peg defense mechanism.
The threshold is independent of the collateral oracle price because the
oracle cancels in the round-trip: zUSD -> collateral -> value.

## Scope

This file formalizes the EXACT profitability threshold (no rounding).
The theorems prove properties of the exact condition
`market_price * BPS < E8 * (BPS - fee_bps)`.
Rounded execution (floor/ceil division) can disagree with the exact
threshold for small amounts due to compounding rounding errors.
The Python verifier reports both `exact_profitable` and `rounded_profitable`
to distinguish the two cases.
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

/-- Exact payout per unit (no rounding): `E8 * (BPS - fee_bps) / BPS`.
Independent of oracle price because oracle cancels in the round-trip. -/
def exactPayoutPerUnit (fee_bps : Nat) : Nat :=
  E8 * (BPS - fee_bps) / BPS

/-! ## Theorem 1: Profitability Condition -/

/-- Redemption is profitable (in exact arithmetic) when
`market_price * BPS < E8 * (BPS - fee_bps)`.

This is the core profitability condition without floor-division rounding.
The left side is the cost of acquiring zUSD on the market (scaled by BPS).
The right side is the redemption payout value (scaled by BPS).
The oracle price cancels in the round-trip, so the threshold is
independent of the collateral oracle. -/
def redemptionProfitable (market_price fee_bps : Nat) : Prop :=
  market_price * BPS < E8 * (BPS - fee_bps)

/-! ## Theorem 2: Zero Fee at Par -/

/-- With zero fee, redemption is profitable iff market_price < E8 (par).
The peg floor equals E8 ($1). -/
theorem zero_fee_profitable_at_par
    (market_price : Nat) :
    redemptionProfitable market_price 0 ↔ market_price < E8 := by
  unfold redemptionProfitable
  rw [Nat.sub_zero]
  constructor
  · intro h
    by_contra hNot
    have hGe : market_price ≥ E8 := by omega
    have : market_price * BPS ≥ E8 * BPS := Nat.mul_le_mul_right BPS hGe
    omega
  · intro h
    exact Nat.mul_lt_mul_of_pos_right h (by decide : 0 < BPS)

/-! ## Theorem 3: Fee Increases Narrow Profit Window -/

/-- Higher fee makes the profitability condition harder to satisfy.
If `fee1 < fee2`, then profitable(fee2) implies profitable(fee1).
The right side `E8 * (BPS - fee)` decreases as fee increases. -/
theorem fee_increase_narrows_profit_window
    (market_price fee1 fee2 : Nat)
    (hFee : fee1 < fee2)
    (hFee2 : fee2 < BPS) :
    redemptionProfitable market_price fee2 →
    redemptionProfitable market_price fee1 := by
  unfold redemptionProfitable
  intro h
  have hDiff : (BPS - fee2) < (BPS - fee1) := by omega
  have hE8 : 0 < E8 := by decide
  have hMul : E8 * (BPS - fee2) < E8 * (BPS - fee1) :=
    Nat.mul_lt_mul_of_pos_left hDiff hE8
  exact Nat.lt_trans h hMul

/-! ## Theorem 4: Zero Fee Payout Equals Par -/

/-- With zero fee, the exact payout per unit equals E8 (par = $1). -/
theorem zero_fee_payout_equals_par :
    exactPayoutPerUnit 0 = E8 := by
  unfold exactPayoutPerUnit
  rw [Nat.sub_zero, Nat.mul_div_cancel E8 (by decide : 0 < BPS)]

/-! ## Theorem 5: Profitable Implies Market Below Par -/

/-- If redemption is profitable with any fee > 0, then market < E8 (par).
The fee creates a strict gap below par. -/
theorem profitable_implies_market_below_par
    (market_price fee_bps : Nat)
    (hFee : 0 < fee_bps)
    (hFee2 : fee_bps < BPS) :
    redemptionProfitable market_price fee_bps →
    market_price < E8 := by
  unfold redemptionProfitable
  intro h
  have hDiff : 0 < BPS - fee_bps := by omega
  have hRHS : E8 * (BPS - fee_bps) ≤ E8 * BPS := by
    have hLe : BPS - fee_bps ≤ BPS := by omega
    exact Nat.mul_le_mul_left E8 hLe
  have hChain : market_price * BPS < E8 * BPS := Nat.lt_of_lt_of_le h hRHS
  by_contra hNot
  have hGe : market_price ≥ E8 := by omega
  have : market_price * BPS ≥ E8 * BPS := Nat.mul_le_mul_right BPS hGe
  omega

/-! ## Theorem 6: Fee Collateral Bounded by Gross -/

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

/-! ## Theorem 7: Fee Collateral Non-Negative -/

/-- The fee collateral is always non-negative (trivially true for Nat division). -/
theorem fee_collateral_nonneg
    (gross fee_bps : Nat) :
    0 ≤ feeCollateral gross fee_bps := by
  unfold feeCollateral
  apply Nat.zero_le

/-! ## Theorem 8: Net Collateral Never Exceeds Gross -/

/-- The net collateral after fee deduction is at most the gross collateral.
In Nat arithmetic, subtraction never underflows below 0, so
`gross - fee ≤ gross` holds unconditionally. -/
theorem net_collateral_le_gross
    (gross fee_bps : Nat) :
    netCollateral gross fee_bps ≤ gross := by
  unfold netCollateral
  exact Nat.sub_le gross (feeCollateral gross fee_bps)

end Internal.ZenoProofRedemptionThreshold
