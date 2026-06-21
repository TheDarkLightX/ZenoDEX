import Mathlib

/-!
# ZenoDEX Self-Liquidation Bound

## Motivation

A self-liquidation attack occurs when a borrower liquidates their own vault to
capture the liquidator compensation. If the compensation exceeds the collateral
the borrower would have kept by repaying the debt at fair market price, the
attack is profitable.

The protocol parameters are:
- `mcr_bps`: minimum collateral ratio in basis points (e.g., 13000 = 130%)
- `gas_comp_bps`: liquidator compensation in basis points of liquidated collateral

## Attack Model

1. Attacker opens a vault at exactly MCR with collateral `C`, debt `D`, price `P`.
2. Price drops slightly so the vault is just under MCR (eligible for liquidation).
3. Attacker liquidates their own vault.
4. As liquidator: receives `liquidator_comp = C * gas_comp_bps / BPS` collateral.
5. As borrower: debt `D` cleared, collateral `C` taken.

Without self-liquidation, the attacker would repay `D` zUSD and recover `C`
collateral. The collateral kept after fair repayment is `C - D * E8 / P`.

Self-liquidation is profitable iff:
```text
liquidator_comp > C - D * E8 / P
```

## Main Result

At the MCR boundary (`C * P * BPS = D * mcr * E8`), self-liquidation is
unprofitable iff:

```text
gas_comp_bps * mcr_bps ≤ BPS * (mcr_bps - BPS)
```

Plain reading: the liquidator compensation (in bps) times the MCR must not
exceed the basis scale times the spread between MCR and 100%. Equivalently:

```text
gas_comp_bps ≤ BPS * (1 - BPS / mcr_bps)
```

For `mcr = 13000` (130%): `gas_comp_bps ≤ 10000 * 3000 / 13000 ≈ 2307` (23.07%).

## Scope

Deterministic, single-vault, full-liquidation at MCR boundary. Does not model
partial liquidation, stability pool dynamics, or oracle manipulation. The bound
is the binding case: vaults above MCR have more collateral, making
self-liquidation less profitable.
-/

namespace Internal
namespace ZenoProofSelfLiquidationBound

/-- Basis points scale (10000 = 100%). -/
def BPS : Nat := 10000

/-- E8 scale (1e8) for price representation. -/
def E8 : Nat := 100_000_000

/-! ## Attack Model

We model the self-liquidation attack with explicit collateral `C`, debt `D`,
and price `P`. The vault is at the MCR boundary: `C * P * BPS = D * mcr * E8`.

The liquidator receives compensation `C * gas_comp_bps / BPS` (integer floor).
Without self-liquidation, the borrower repays debt `D` and recovers collateral
`C - D * E8 / P` (integer floor). Self-liquidation is unprofitable when the
compensation does not exceed the recovered collateral.

To avoid integer division floor effects in the proof, we work with the
cross-multiplied form: `C * gas_comp * P + BPS * D * E8 ≤ BPS * P * C`.
This is the exact algebraic condition that implies the floored form.
-/

/-- Liquidator compensation: `C * gas_comp_bps / BPS` (integer floor). -/
def liquidatorComp (C gas_comp_bps : Nat) : Nat :=
  C * gas_comp_bps / BPS

/-- Collateral recovered by fair repayment: `C - D * E8 / P` (integer floor). -/
def fairRepayment (C D P : Nat) : Nat :=
  C - D * E8 / P

/-- Self-liquidation unprofitability (cross-multiplied form, no division).

This is the exact algebraic condition: the liquidator compensation times `P`,
plus the debt value times `BPS`, does not exceed the collateral times `BPS * P`.
At the MCR boundary, this reduces to the parameter bound. -/
def selfLiquidationUnprofitableCross (C D P gas_comp_bps : Nat) : Prop :=
  C * gas_comp_bps * P + BPS * D * E8 ≤ BPS * P * C

/-- Self-liquidation unprofitability condition (parameter form).

At the MCR boundary, this is equivalent to the cross-multiplied attack model.
The bound is purely a function of protocol parameters `gas_comp_bps` and `mcr_bps`. -/
def selfLiquidationUnprofitable (gas_comp_bps mcr_bps : Nat) : Prop :=
  gas_comp_bps * mcr_bps ≤ BPS * (mcr_bps - BPS)

/-- The parameter-only bound (alias for `selfLiquidationUnprofitable`). -/
def paramBound (gas_comp_bps mcr_bps : Nat) : Prop :=
  gas_comp_bps * mcr_bps ≤ BPS * (mcr_bps - BPS)

/-! ## Main Theorem: Attack Model Reduces to Parameter Bound -/

/-- **Self-Liquidation Bound Theorem**: at the MCR boundary
(`C * P * BPS = D * mcr_bps * E8`), the cross-multiplied attack model with
collateral `C`, debt `D`, and price `P` is equivalent to the pure parameter
bound `gas_comp_bps * mcr_bps ≤ BPS * (mcr_bps - BPS)`.

Forward (model => paramBound): Multiply the model by `mcr`, then the goal
`gas_comp * mcr + BPS^2 ≤ BPS * mcr` multiplied by `C * P > 0` follows by
`linear_combination hModelMcr + BPS * hBoundary` (no Nat subtraction in goal
or hypotheses). Cancel `C * P > 0`, then convert to paramBound form via `omega`.

Backward (paramBound => model): Rearrange paramBound to
`gas_comp * mcr + BPS^2 ≤ BPS * mcr`, then the goal multiplied by `mcr > 0`
follows by `linear_combination C * P * hRearr - BPS * hBoundary`. Cancel `mcr`. -/
theorem self_liquidation_unprofitable_iff_param_bound
    (C D P gas_comp_bps mcr_bps : Nat)
    (hC : 0 < C) (hP : 0 < P) (hMCR : BPS < mcr_bps)
    (hBoundary : C * P * BPS = D * mcr_bps * E8) :
    selfLiquidationUnprofitableCross C D P gas_comp_bps ↔
    paramBound gas_comp_bps mcr_bps := by
  unfold selfLiquidationUnprofitableCross paramBound
  have hMCRPos : 0 < mcr_bps := by omega
  have hCP : 0 < C * P := by nlinarith [hC, hP]
  -- Additive identity: BPS * (mcr - BPS) + BPS * BPS = BPS * mcr
  have hDistrib : BPS * (mcr_bps - BPS) + BPS * BPS = BPS * mcr_bps := by
    have hSplit : mcr_bps = (mcr_bps - BPS) + BPS := by omega
    conv_rhs => rw [hSplit, Nat.mul_add]
  constructor
  · -- Forward: model => paramBound
    intro hModel
    have hModelMcr : (C * gas_comp_bps * P + BPS * D * E8) * mcr_bps ≤
        BPS * P * C * mcr_bps := Nat.mul_le_mul_right mcr_bps hModel
    -- Prove: C*P*(gas_comp*mcr + BPS^2) ≤ C*P*(BPS*mcr) via linear_combination
    have hGoalMult : C * P * (gas_comp_bps * mcr_bps + BPS * BPS) ≤
        C * P * (BPS * mcr_bps) := by
      linear_combination hModelMcr + BPS * hBoundary
    -- Cancel C*P > 0: gas_comp*mcr + BPS^2 ≤ BPS*mcr
    have hCancelled : gas_comp_bps * mcr_bps + BPS * BPS ≤ BPS * mcr_bps :=
      Nat.le_of_mul_le_mul_left hGoalMult hCP
    -- Convert to paramBound form: gas_comp*mcr ≤ BPS*(mcr-BPS)
    -- Using hDistrib: BPS*mcr = BPS*(mcr-BPS) + BPS^2, so cancel BPS^2
    nlinarith [hDistrib]
  · -- Backward: paramBound => model
    intro hParam
    -- Rearrange paramBound: gas_comp*mcr + BPS^2 ≤ BPS*mcr
    have hRearr : gas_comp_bps * mcr_bps + BPS * BPS ≤ BPS * mcr_bps := by nlinarith [hDistrib]
    -- Prove: (C*gas_comp*P + BPS*D*E8)*mcr ≤ BPS*P*C*mcr via linear_combination
    have hGoalMult : (C * gas_comp_bps * P + BPS * D * E8) * mcr_bps ≤
        BPS * P * C * mcr_bps := by
      linear_combination C * P * hRearr - BPS * hBoundary
    -- Cancel mcr > 0
    exact Nat.le_of_mul_le_mul_right hGoalMult hMCRPos

/-- **MCR Must Exceed 100%**: for self-liquidation unprofitability to be
achievable with positive compensation, the MCR must exceed 100% (BPS). If
`mcr_bps ≤ BPS`, the RHS `BPS * (mcr_bps - BPS)` is zero (Nat truncation), so
only `gas_comp_bps = 0` is unprofitable. Any positive compensation enables
self-liquidation. Requires `0 < mcr_bps` (MCR is always positive in practice). -/
theorem mcr_must_exceed_100pct
    (gas_comp_bps mcr_bps : Nat) (hGas : 0 < gas_comp_bps) (hMCRPos : 0 < mcr_bps)
    (hUnprofit : selfLiquidationUnprofitable gas_comp_bps mcr_bps) :
    BPS < mcr_bps := by
  unfold selfLiquidationUnprofitable at hUnprofit
  by_contra hNot
  push_neg at hNot
  by_cases hEq : mcr_bps = BPS
  · rw [hEq] at hUnprofit
    have hSub : BPS - BPS = 0 := by omega
    rw [hSub] at hUnprofit
    have hZero : gas_comp_bps * BPS = 0 := Nat.le_antisymm hUnprofit (Nat.zero_le _)
    have hBPS : BPS = 10000 := rfl
    rw [hBPS] at hZero
    nlinarith
  · have hLt : mcr_bps < BPS := by omega
    have hSub : mcr_bps - BPS = 0 := by omega
    rw [hSub] at hUnprofit
    have hZero : gas_comp_bps * mcr_bps = 0 := Nat.le_antisymm hUnprofit (Nat.zero_le _)
    nlinarith

/-- **Max Safe Gas Compensation**: the maximum `gas_comp_bps` that keeps
self-liquidation unprofitable is `BPS * (mcr_bps - BPS) / mcr_bps` (integer
floor). Any compensation above this enables self-liquidation. -/
theorem max_safe_gas_comp
    (mcr_bps : Nat) (_hMCR : BPS < mcr_bps) :
    BPS * (mcr_bps - BPS) / mcr_bps * mcr_bps ≤ BPS * (mcr_bps - BPS) := by
  exact Nat.div_mul_le_self (BPS * (mcr_bps - BPS)) mcr_bps

/-- **Maximality of Safe Gas Compensation**: the floor
`BPS * (mcr_bps - BPS) / mcr_bps` is the maximum safe compensation. Any
compensation strictly above this floor enables self-liquidation.

Proof: Let `n = BPS * (mcr - BPS)` and `floor = n / mcr`. The division
remainder `r = n % mcr` satisfies `r < mcr` (standard mod property) and
`n = floor * mcr + r` (division decomposition). So
`(floor + 1) * mcr = floor * mcr + mcr > floor * mcr + r = n`,
proving `floor + 1` is unsafe. -/
/- **Helper: `(A / m + 1) * m > A` for `m > 0`** (Euclidean division
maximality). The successor of the quotient times the divisor strictly
exceeds the dividend, because the remainder is strictly less than the
divisor. -/
private lemma succ_div_mul_not_le_self (A m : Nat) (hm : 0 < m) :
    ¬ (A / m + 1) * m ≤ A := by
  have hr : A % m < m := Nat.mod_lt A hm
  have hdecomp : A = m * (A / m) + A % m :=
    (Nat.div_add_mod A m).symm
  have hsucc : (A / m + 1) * m = m * (A / m) + m := by
    rw [Nat.succ_mul, Nat.mul_comm (A / m) m]
  intro h
  conv at h => lhs; rw [hsucc]
  conv at h => rhs; rw [hdecomp]
  exact (not_le_of_gt hr) (Nat.add_le_add_iff_left.mp h)

/- **Maximality of Safe Gas Compensation**: the floor
`BPS * (mcr_bps - BPS) / mcr_bps` is the maximum safe compensation. Any
compensation strictly above this floor enables self-liquidation.

Proof: Let `A = BPS * (mcr - BPS)` and `floor = A / mcr`. By
`succ_div_mul_not_le_self`, `(floor + 1) * mcr > A`, so `floor + 1`
violates the unprofitability condition. -/
theorem max_safe_gas_comp_maximal
    (mcr_bps : Nat) (hMCR : BPS < mcr_bps) :
    ¬ (BPS * (mcr_bps - BPS) / mcr_bps + 1) * mcr_bps ≤
      BPS * (mcr_bps - BPS) := by
  have hBPSPos : 0 < BPS := by norm_num [BPS]
  exact succ_div_mul_not_le_self (BPS * (mcr_bps - BPS)) mcr_bps
    (lt_trans hBPSPos hMCR)

/-- **Maximality in terms of `selfLiquidationUnprofitable`**: the direct
maximality theorem above implies that `floor + 1` violates the
`selfLiquidationUnprofitable` condition. -/
theorem max_safe_gas_comp_maximal_unprofitable
    (mcr_bps : Nat) (hMCR : BPS < mcr_bps) :
    ¬ selfLiquidationUnprofitable (BPS * (mcr_bps - BPS) / mcr_bps + 1) mcr_bps :=
  max_safe_gas_comp_maximal mcr_bps hMCR

/- **Greatest Safe Gas Compensation**: if `gas_comp_bps` is safe at
`mcr_bps`, then `gas_comp_bps ≤ max_safe = BPS * (mcr - BPS) / mcr`.

This is the all-gases maximality theorem. Combined with
`max_safe_gas_comp` (floor is safe) and `max_safe_gas_comp_maximal`
(floor+1 is unsafe), this establishes that `max_safe` is the greatest
safe gas compensation.

Proof: `safe gas` means `gas * mcr ≤ BPS * (mcr - BPS)`. Dividing by
`mcr > 0` gives `gas ≤ BPS * (mcr - BPS) / mcr = max_safe`. -/
theorem max_safe_gas_comp_greatest
    (gas_comp_bps mcr_bps : Nat) (hMCR : BPS < mcr_bps)
    (hSafe : selfLiquidationUnprofitable gas_comp_bps mcr_bps) :
    gas_comp_bps ≤ BPS * (mcr_bps - BPS) / mcr_bps := by
  have hMCRPos : 0 < mcr_bps := by omega
  -- hSafe: gas * mcr ≤ BPS * (mcr - BPS)
  -- Divide both sides by mcr > 0
  exact (Nat.le_div_iff_mul_le hMCRPos).mpr hSafe

/-- **Cross-Multiplied Model Implies Floored Model**: if the cross-multiplied
condition `C * gas_comp * P + BPS * D * E8 ≤ BPS * P * C` holds, then the
floored condition `liquidatorComp C gas_comp ≤ fairRepayment C D P` also holds.

This establishes that the parameter bound (equivalent to the cross-multiplied
model at MCR) is sufficient for the integer-floor execution model.

Proof: From the cross-multiplied condition and floor properties
`C * gas_comp / BPS * BPS ≤ C * gas_comp` and `D * E8 / P * P ≤ D * E8`,
we derive `(C * gas_comp / BPS) * BPS * P + (D * E8 / P) * P * BPS ≤
BPS * P * C`. Dividing by `BPS * P > 0` gives
`C * gas_comp / BPS + D * E8 / P ≤ C`. -/
theorem cross_implies_floored
    (C D P gas_comp_bps : Nat)
    (_hC : 0 < C) (hP : 0 < P)
    (hCross : selfLiquidationUnprofitableCross C D P gas_comp_bps) :
    liquidatorComp C gas_comp_bps ≤ fairRepayment C D P := by
  have hFloorGas : C * gas_comp_bps / BPS * BPS ≤ C * gas_comp_bps :=
    Nat.div_mul_le_self (C * gas_comp_bps) BPS
  have hFloorDE8 : D * E8 / P * P ≤ D * E8 :=
    Nat.div_mul_le_self (D * E8) P
  have hBPSPos : 0 < BPS := by norm_num [BPS]
  have hBPSP : 0 < BPS * P := by positivity
  -- (C * gas_comp / BPS) * BPS * P ≤ C * gas_comp * P
  have hLHS1 : C * gas_comp_bps / BPS * BPS * P ≤ C * gas_comp_bps * P :=
    Nat.mul_le_mul_right P hFloorGas
  -- (D * E8 / P) * P * BPS ≤ BPS * D * E8
  have hLHS2 : D * E8 / P * P * BPS ≤ BPS * D * E8 := by
    have hLe : D * E8 / P * P * BPS ≤ D * E8 * BPS :=
      Nat.mul_le_mul_right BPS hFloorDE8
    have hComm : D * E8 * BPS = BPS * D * E8 := by ac_rfl
    exact hLe.trans_eq hComm
  -- Combined: (C * gas_comp / BPS) * BPS * P + (D * E8 / P) * P * BPS ≤ BPS * P * C
  have hCombined : C * gas_comp_bps / BPS * BPS * P + D * E8 / P * P * BPS ≤
      BPS * P * C := (Nat.add_le_add hLHS1 hLHS2).trans hCross
  -- Factor: (C * gas_comp / BPS + D * E8 / P) * (BPS * P) ≤ BPS * P * C
  have hFactored : (C * gas_comp_bps / BPS + D * E8 / P) * (BPS * P) ≤
      BPS * P * C := by
    have hDistrib : (C * gas_comp_bps / BPS + D * E8 / P) * (BPS * P) =
        C * gas_comp_bps / BPS * BPS * P + D * E8 / P * P * BPS := by
      rw [Nat.add_mul]
      ac_rfl
    rw [hDistrib]; exact hCombined
  -- Divide: C * gas_comp / BPS + D * E8 / P ≤ BPS * P * C / (BPS * P)
  have hDivLe : C * gas_comp_bps / BPS + D * E8 / P ≤
      BPS * P * C / (BPS * P) :=
    (Nat.le_div_iff_mul_le hBPSP).mpr hFactored
  -- BPS * P * C / (BPS * P) = C (exact division)
  have hExact : BPS * P * C / (BPS * P) = C := Nat.mul_div_cancel_left _ hBPSP
  -- C * gas_comp / BPS + D * E8 / P ≤ C
  -- Hence C * gas_comp / BPS ≤ C - D * E8 / P
  have hGoal : C * gas_comp_bps / BPS ≤ C - D * E8 / P := by omega
  exact hGoal

/- **Exact Tightness of the Floored Bound**: the parameter bound
`max_safe = BPS * (mcr - BPS) / mcr` is not merely sufficient for the
floored execution model, but also necessary. There exists a boundary
vault (`C = mcr * BPS`, `D = 1`, `P = 1`) where `max_safe + 1` is
profitable in the actual floored model.

This closes the gap between the cross-multiplied maximality proof and
the floored execution semantics. The witness uses `E8 = BPS^2`, so all
divisions are exact and the floor does not add slack. -/
theorem exists_profitable_floored_at_succ_max
    (mcr_bps : Nat) (hMCR : BPS < mcr_bps) :
    ∃ C D P,
      C * P * BPS = D * mcr_bps * E8 ∧
      0 < C ∧ 0 < D ∧ 0 < P ∧
      fairRepayment C D P < liquidatorComp C (BPS * (mcr_bps - BPS) / mcr_bps + 1) := by
  have hBPSPos : 0 < BPS := by norm_num [BPS]
  have hE8 : E8 = BPS * BPS := by norm_num [BPS, E8]
  have hMCRPos : 0 < mcr_bps := lt_trans hBPSPos hMCR
  -- Witness: C = mcr * BPS, D = 1, P = 1
  -- Boundary: C * P * BPS = mcr * BPS * BPS = mcr * BPS^2 = mcr * E8 = D * mcr * E8
  -- liquidatorComp = mcr * BPS * (maxSafe+1) / BPS = mcr * (maxSafe+1) (exact)
  -- fairRepayment = mcr * BPS - E8/1 = mcr * BPS - BPS^2 = BPS * (mcr - BPS)
  -- Profitable iff BPS * (mcr - BPS) < mcr * (maxSafe+1)
  -- which is the contrapositive of max_safe_gas_comp_maximal
  let C := mcr_bps * BPS
  let D := 1
  let P := 1
  refine ⟨C, D, P, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  -- Boundary: C * P * BPS = D * mcr * E8
  · rw [hE8]
    show mcr_bps * BPS * 1 * BPS = 1 * mcr_bps * (BPS * BPS)
    rw [Nat.mul_one, Nat.one_mul, Nat.mul_assoc]
  -- 0 < C
  · exact Nat.mul_pos hMCRPos hBPSPos
  -- 0 < D
  · norm_num
  -- 0 < P
  · norm_num
  -- fairRepayment < liquidatorComp at maxSafe + 1
  · -- liquidatorComp C (maxSafe+1) = C * (maxSafe+1) / BPS
    -- C = mcr * BPS, so = mcr * BPS * (maxSafe+1) / BPS = mcr * (maxSafe+1)
    have hLiqExact : liquidatorComp C (BPS * (mcr_bps - BPS) / mcr_bps + 1) =
        mcr_bps * (BPS * (mcr_bps - BPS) / mcr_bps + 1) := by
      show mcr_bps * BPS * (BPS * (mcr_bps - BPS) / mcr_bps + 1) / BPS =
        mcr_bps * (BPS * (mcr_bps - BPS) / mcr_bps + 1)
      -- (mcr * BPS) * X / BPS = BPS * (mcr * X) / BPS = mcr * X
      rw [Nat.mul_comm mcr_bps BPS, Nat.mul_assoc, Nat.mul_div_cancel_left _ hBPSPos]
    -- fairRepayment C D P = C - D * E8 / P
    -- C = mcr * BPS, D = 1, P = 1, E8 = BPS^2
    -- = mcr * BPS - 1 * BPS^2 / 1 = mcr * BPS - BPS^2 = BPS * (mcr - BPS)
    have hFairExact : fairRepayment C D P = BPS * (mcr_bps - BPS) := by
      show mcr_bps * BPS - 1 * E8 / 1 = BPS * (mcr_bps - BPS)
      rw [hE8, Nat.div_one, Nat.one_mul, Nat.mul_sub, Nat.mul_comm mcr_bps BPS]
    -- Goal: fairRepayment < liquidatorComp
    -- i.e., BPS * (mcr - BPS) < mcr * (maxSafe + 1)
    -- This is the contrapositive of max_safe_gas_comp_maximal
    rw [hFairExact, hLiqExact]
    -- BPS * (mcr - BPS) < mcr * (BPS * (mcr - BPS) / mcr + 1)
    have hMax := max_safe_gas_comp_maximal mcr_bps hMCR
    -- hMax: ¬ (maxSafe+1) * mcr ≤ BPS * (mcr - BPS)
    -- i.e., BPS * (mcr - BPS) < (maxSafe+1) * mcr
    have hComm : mcr_bps * (BPS * (mcr_bps - BPS) / mcr_bps + 1) =
        (BPS * (mcr_bps - BPS) / mcr_bps + 1) * mcr_bps := Nat.mul_comm _ _
    rw [hComm]
    exact Nat.lt_of_not_le hMax

/-! ## Non-Vacuity Witnesses -/

/-- Witness: `mcr = 13000` (130%), `gas_comp = 2307`.
`2307 * 13000 = 29991000 ≤ 10000 * 3000 = 30000000`. Unprofitable. -/
theorem witness_safe_compensation :
    selfLiquidationUnprofitable 2307 13000 := by
  unfold selfLiquidationUnprofitable BPS
  decide

/-- Witness: `mcr = 13000`, `gas_comp = 2308`.
`2308 * 13000 = 30004000 > 30000000`. Profitable (self-liquidation enabled). -/
theorem witness_unsafe_compensation :
    ¬ selfLiquidationUnprofitable 2308 13000 := by
  unfold selfLiquidationUnprofitable BPS
  decide

/-- Witness: `mcr = 15000` (150%), `gas_comp = 3333`.
`3333 * 15000 = 49995000 ≤ 10000 * 5000 = 50000000`. Unprofitable.
Higher MCR allows higher safe compensation. -/
theorem witness_higher_mcr_allows_higher_comp :
    selfLiquidationUnprofitable 3333 15000 := by
  unfold selfLiquidationUnprofitable BPS
  decide

/-- Witness: `mcr = 11000` (110%), `gas_comp = 909`.
`909 * 11000 = 9999000 ≤ 10000 * 1000 = 10000000`. Unprofitable.
Lower MCR means lower safe compensation. -/
theorem witness_lower_mcr_lower_comp :
    selfLiquidationUnprofitable 909 11000 := by
  unfold selfLiquidationUnprofitable BPS
  decide

/-- Witness: `mcr = 11000`, `gas_comp = 910`.
`910 * 11000 = 10010000 > 10000000`. Profitable.
At 110% MCR, only ~909 bps (9.09%) compensation is safe. -/
theorem witness_lower_mcr_tight_bound :
    ¬ selfLiquidationUnprofitable 910 11000 := by
  unfold selfLiquidationUnprofitable BPS
  decide

/-! ## Boundary Cases -/

/-- Boundary: zero gas compensation is always unprofitable (trivially). -/
theorem witness_zero_comp_always_safe
    (mcr_bps : Nat) (_hMCR : BPS < mcr_bps) :
    selfLiquidationUnprofitable 0 mcr_bps := by
  unfold selfLiquidationUnprofitable
  simp [BPS]

/-- Boundary: at MCR = 20000 (200%), the safe compensation is up to 5000 bps
(50%). `5000 * 20000 = 100000000 = 10000 * 10000`. Exact boundary. -/
theorem witness_200pct_boundary :
    selfLiquidationUnprofitable 5000 20000 := by
  unfold selfLiquidationUnprofitable BPS
  decide

/-- Boundary: one unit above the 200% boundary is unsafe.
`5001 * 20000 = 100020000 > 100000000`. -/
theorem witness_200pct_one_above_unsafe :
    ¬ selfLiquidationUnprofitable 5001 20000 := by
  unfold selfLiquidationUnprofitable BPS
  decide

/-- **Monotonicity in MCR**: higher MCR allows higher safe compensation.
If `gas_comp_bps ≤ BPS` (compensation is a fraction of collateral) and the
compensation is safe at `mcr1`, it is also safe at `mcr2 ≥ mcr1`. The LHS grows
by `gas_comp * (mcr2 - mcr1)` while the RHS grows by `BPS * (mcr2 - mcr1)`, so
the inequality is preserved when `gas_comp ≤ BPS`. -/
theorem mcr_monotonicity
    (gas_comp_bps mcr1 mcr2 : Nat) (_hMCR1 : BPS < mcr1) (_hMCR2 : BPS < mcr2)
    (hGas : gas_comp_bps ≤ BPS) (hLe : mcr1 ≤ mcr2)
    (hSafe1 : selfLiquidationUnprofitable gas_comp_bps mcr1) :
    selfLiquidationUnprofitable gas_comp_bps mcr2 := by
  unfold selfLiquidationUnprofitable at *
  have hLHSGrow : gas_comp_bps * (mcr2 - mcr1) ≤ BPS * (mcr2 - mcr1) := by
    apply Nat.mul_le_mul_right
    exact hGas
  have hEq1 : gas_comp_bps * mcr2 = gas_comp_bps * mcr1 + gas_comp_bps * (mcr2 - mcr1) := by
    have hSplit : mcr2 = mcr1 + (mcr2 - mcr1) := by omega
    conv_lhs => rw [hSplit]
    exact Nat.mul_add gas_comp_bps mcr1 (mcr2 - mcr1)
  have hEq2 : BPS * (mcr2 - BPS) = BPS * (mcr1 - BPS) + BPS * (mcr2 - mcr1) := by
    have hSplit : mcr2 - BPS = (mcr1 - BPS) + (mcr2 - mcr1) := by omega
    conv_lhs => rw [hSplit]
    exact Nat.mul_add BPS (mcr1 - BPS) (mcr2 - mcr1)
  rw [hEq1, hEq2]
  exact Nat.add_le_add hSafe1 hLHSGrow

end ZenoProofSelfLiquidationBound
end Internal
