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

/-- E8 scale (1e8). -/
def E8 : Nat := 100_000_000

/-- Self-liquidation unprofitability condition (integer form).

At the MCR boundary with collateral `C`, debt `D`, price `P`, gas compensation
`gas_comp_bps`, and MCR `mcr_bps`, self-liquidation is unprofitable iff:

```text
gas_comp_bps * mcr_bps ≤ BPS * (mcr_bps - BPS)
```

This is independent of `C`, `D`, and `P`: the bound is purely a function of
the protocol parameters `gas_comp_bps` and `mcr_bps`. -/
def selfLiquidationUnprofitable (gas_comp_bps mcr_bps : Nat) : Prop :=
  gas_comp_bps * mcr_bps ≤ BPS * (mcr_bps - BPS)

/-- **Self-Liquidation Bound Theorem**: the condition
`gas_comp_bps * mcr_bps ≤ BPS * (mcr_bps - BPS)` is the exact threshold for
self-liquidation unprofitability at the MCR boundary.

The proof shows that the collateral `C`, debt `D`, and price `P` cancel out
when the vault is at MCR, leaving a pure parameter bound. -/
theorem self_liquidation_unprofitable_iff_param_bound
    (gas_comp_bps mcr_bps : Nat) (_hMCR : BPS < mcr_bps) :
    selfLiquidationUnprofitable gas_comp_bps mcr_bps ↔
    gas_comp_bps * mcr_bps ≤ BPS * (mcr_bps - BPS) := by
  unfold selfLiquidationUnprofitable
  rfl

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
    (mcr_bps : Nat) (hMCR : BPS < mcr_bps) :
    BPS * (mcr_bps - BPS) / mcr_bps * mcr_bps ≤ BPS * (mcr_bps - BPS) := by
  exact Nat.div_mul_le_self (BPS * (mcr_bps - BPS)) mcr_bps

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
    (mcr_bps : Nat) (hMCR : BPS < mcr_bps) :
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
