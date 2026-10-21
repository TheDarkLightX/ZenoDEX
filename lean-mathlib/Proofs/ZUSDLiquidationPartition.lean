import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Liquity V1 Stability-Pool Offset And Redistribution Partition

This file proves the unbounded natural-number arithmetic used by the pure
zUSD liquidation partition.  Eligibility, target selection, gas compensation,
Recovery Mode branches, redistribution accumulators, and runtime binding are
outside the theorem surface.
-/

namespace ZenoDEX
namespace ZUSDLiquidationPartition

def debtToOffset (debt stabilityPoolPrincipal : Nat) : Nat :=
  min debt stabilityPoolPrincipal

def collateralToStabilityPool
    (debt postKeeperCollateral stabilityPoolPrincipal : Nat) : Nat :=
  postKeeperCollateral * debtToOffset debt stabilityPoolPrincipal / debt

def debtToRedistribute (debt stabilityPoolPrincipal : Nat) : Nat :=
  debt - debtToOffset debt stabilityPoolPrincipal

def collateralToRedistribute
    (debt postKeeperCollateral stabilityPoolPrincipal : Nat) : Nat :=
  postKeeperCollateral -
    collateralToStabilityPool debt postKeeperCollateral stabilityPoolPrincipal

theorem debtToOffset_le_debt (debt stabilityPoolPrincipal : Nat) :
    debtToOffset debt stabilityPoolPrincipal ≤ debt := by
  exact min_le_left debt stabilityPoolPrincipal

theorem debt_partition (debt stabilityPoolPrincipal : Nat) :
    debtToOffset debt stabilityPoolPrincipal +
      debtToRedistribute debt stabilityPoolPrincipal = debt := by
  unfold debtToRedistribute
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel (debtToOffset_le_debt debt stabilityPoolPrincipal)

theorem collateralToStabilityPool_le_collateral
    (debt postKeeperCollateral stabilityPoolPrincipal : Nat)
    (hDebt : 0 < debt) :
    collateralToStabilityPool debt postKeeperCollateral stabilityPoolPrincipal
      ≤ postKeeperCollateral := by
  unfold collateralToStabilityPool
  have hOffset := debtToOffset_le_debt debt stabilityPoolPrincipal
  have hMul :
      postKeeperCollateral * debtToOffset debt stabilityPoolPrincipal
        ≤ postKeeperCollateral * debt :=
    Nat.mul_le_mul_left postKeeperCollateral hOffset
  have hDiv :
      postKeeperCollateral * debtToOffset debt stabilityPoolPrincipal / debt
        ≤ postKeeperCollateral * debt / debt :=
    Nat.div_le_div_right hMul
  have hCancel :
      postKeeperCollateral * debt / debt = postKeeperCollateral := by
    rw [Nat.mul_comm postKeeperCollateral debt]
    exact Nat.mul_div_right postKeeperCollateral hDebt
  exact le_trans hDiv (le_of_eq hCancel)

theorem collateral_partition
    (debt postKeeperCollateral stabilityPoolPrincipal : Nat)
    (hDebt : 0 < debt) :
    collateralToStabilityPool debt postKeeperCollateral stabilityPoolPrincipal
      + collateralToRedistribute debt postKeeperCollateral stabilityPoolPrincipal
      = postKeeperCollateral := by
  unfold collateralToRedistribute
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel
    (collateralToStabilityPool_le_collateral
      debt postKeeperCollateral stabilityPoolPrincipal hDebt)

theorem full_redistribution_when_pool_empty
    (debt postKeeperCollateral : Nat) :
    debtToOffset debt 0 = 0 ∧
      collateralToStabilityPool debt postKeeperCollateral 0 = 0 ∧
      debtToRedistribute debt 0 = debt ∧
      collateralToRedistribute debt postKeeperCollateral 0 =
        postKeeperCollateral := by
  simp [debtToOffset, collateralToStabilityPool, debtToRedistribute,
    collateralToRedistribute]

theorem full_offset_when_debt_le_principal
    (debt postKeeperCollateral stabilityPoolPrincipal : Nat)
    (hDebt : 0 < debt)
    (hCapacity : debt ≤ stabilityPoolPrincipal) :
    debtToOffset debt stabilityPoolPrincipal = debt ∧
      collateralToStabilityPool debt postKeeperCollateral
        stabilityPoolPrincipal = postKeeperCollateral ∧
      debtToRedistribute debt stabilityPoolPrincipal = 0 ∧
      collateralToRedistribute debt postKeeperCollateral
        stabilityPoolPrincipal = 0 := by
  have hMin : min debt stabilityPoolPrincipal = debt := min_eq_left hCapacity
  simp [debtToOffset, collateralToStabilityPool, debtToRedistribute,
    collateralToRedistribute, hMin, hDebt]

end ZUSDLiquidationPartition
end ZenoDEX
