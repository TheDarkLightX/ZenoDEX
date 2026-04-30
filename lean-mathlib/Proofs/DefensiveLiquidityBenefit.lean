import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Defensive Liquidity Benefit

A bounded local witness language for liquidity-side rewards in a post-AGI setting.

The design target is deliberately smaller than "global market quality":
- do not pay passive depth just for existing
- do not pay self-generated flow
- only pay classes that actually serve external flow or defended depth
- subtract recapturable terms before allowing positive reward
-/

namespace Proofs
namespace DefensiveLiquidityBenefit

inductive LiquidityServiceClass where
  | passive
  | postedDepth
  | externalFlowServed
  | defendedDepth
  | oracleSafeDefendedDepth
  deriving DecidableEq, Repr

/-- Exact bounded class rank used for local service ordering. -/
def serviceRank : LiquidityServiceClass -> Nat
  | .passive => 0
  | .postedDepth => 1
  | .externalFlowServed => 2
  | .defendedDepth => 3
  | .oracleSafeDefendedDepth => 4

/-- External-flow service begins only once the venue actually serves unaffiliated flow. -/
def externalServiceEnabled : LiquidityServiceClass -> Prop
  | .externalFlowServed | .defendedDepth | .oracleSafeDefendedDepth => True
  | _ => False

/-- Defensive service is stronger than merely serving external flow. -/
def defensiveServiceEnabled : LiquidityServiceClass -> Prop
  | .defendedDepth | .oracleSafeDefendedDepth => True
  | _ => False

/-- Oracle-safe defended depth is the strongest bounded local class. -/
def oracleSafeServiceEnabled : LiquidityServiceClass -> Prop
  | .oracleSafeDefendedDepth => True
  | _ => False

/-- Liquidity-side net benefit after subtracting recapturable terms. -/
def liquidityNetBenefit
    (externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin : Int) : Int :=
  externalFee + safetyLift - selfFlow - inventoryRecycle - overlap - safetyMargin

/-- Local rewardability shell for liquidity service. -/
def rewardableLiquidity
    (cls : LiquidityServiceClass)
    (externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin reward : Int) : Prop :=
  externalServiceEnabled cls /\
    0 < reward /\
    reward <= liquidityNetBenefit externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin

@[simp] theorem external_service_enabled_iff
    (c : LiquidityServiceClass) :
    externalServiceEnabled c <->
      c = .externalFlowServed \/ c = .defendedDepth \/ c = .oracleSafeDefendedDepth := by
  cases c <;> simp [externalServiceEnabled]

@[simp] theorem defensive_service_enabled_iff
    (c : LiquidityServiceClass) :
    defensiveServiceEnabled c <-> c = .defendedDepth \/ c = .oracleSafeDefendedDepth := by
  cases c <;> simp [defensiveServiceEnabled]

@[simp] theorem oracle_safe_service_enabled_iff
    (c : LiquidityServiceClass) :
    oracleSafeServiceEnabled c <-> c = .oracleSafeDefendedDepth := by
  cases c <;> simp [oracleSafeServiceEnabled]

/-- Oracle-safe defended service implies defended service. -/
theorem oracle_safe_implies_defensive
    {c : LiquidityServiceClass} :
    oracleSafeServiceEnabled c -> defensiveServiceEnabled c := by
  cases c <;> simp [oracleSafeServiceEnabled, defensiveServiceEnabled]

/-- Defensive service implies external-flow service. -/
theorem defensive_implies_external_service
    {c : LiquidityServiceClass} :
    defensiveServiceEnabled c -> externalServiceEnabled c := by
  cases c <;> simp [defensiveServiceEnabled, externalServiceEnabled]

/-- Any rewardable liquidity claim must be attached to external service. -/
theorem rewardable_liquidity_implies_external_service
    (cls : LiquidityServiceClass)
    (externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin reward : Int)
    (hReward : rewardableLiquidity cls externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin reward) :
    externalServiceEnabled cls := by
  exact hReward.1

/-- Passive depth and merely posted depth are not rewardable liquidity classes. -/
theorem not_rewardable_without_external_service
    (cls : LiquidityServiceClass)
    (externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin reward : Int)
    (hNoExternal : ¬ externalServiceEnabled cls) :
    ¬ rewardableLiquidity cls externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin reward := by
  intro h
  exact hNoExternal h.1

/-- Positive liquidity reward requires strict external or safety surplus after subtracting
    self-flow, inventory recycling, overlap, and safety reserve. -/
theorem positive_liquidity_reward_requires_surplus
    (cls : LiquidityServiceClass)
    (externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin reward : Int)
    (hReward : rewardableLiquidity cls externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin reward) :
    selfFlow + inventoryRecycle + overlap + safetyMargin < externalFee + safetyLift := by
  rcases hReward with ⟨_hClass, hPos, hUpper⟩
  unfold liquidityNetBenefit at hUpper
  linarith

/-- If recapturable terms dominate external fee plus safety lift, a non-negative
    liquidity reward must collapse to zero. -/
theorem liquidity_reward_zero_if_recapturable_dominates
    (_cls : LiquidityServiceClass)
    (externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin reward : Int)
    (hDom : externalFee + safetyLift <= selfFlow + inventoryRecycle + overlap + safetyMargin)
    (hLower : 0 <= reward)
    (hUpper : reward <= liquidityNetBenefit externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin) :
    reward = 0 := by
  unfold liquidityNetBenefit at hUpper
  linarith

/-- Positive reward on an oracle-safe class implies the class is at least defensive. -/
theorem rewardable_oracle_safe_service_is_defensive
    (cls : LiquidityServiceClass)
    (externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin reward : Int)
    (hOracleSafe : oracleSafeServiceEnabled cls)
    (_hReward : rewardableLiquidity cls externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin reward) :
    defensiveServiceEnabled cls := by
  exact oracle_safe_implies_defensive hOracleSafe

/-- Positive reward on defended depth implies the class also serves external flow. -/
theorem rewardable_defensive_service_is_external
    (cls : LiquidityServiceClass)
    (externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin reward : Int)
    (hDef : defensiveServiceEnabled cls)
    (_hReward : rewardableLiquidity cls externalFee safetyLift selfFlow inventoryRecycle overlap safetyMargin reward) :
    externalServiceEnabled cls := by
  exact defensive_implies_external_service hDef

/-- Concrete witness: defended depth with external fees and safety lift is rewardable. -/
theorem witness_rewardable_defensive_service :
    rewardableLiquidity .defendedDepth 8 4 3 1 1 1 2 := by
  unfold rewardableLiquidity externalServiceEnabled liquidityNetBenefit
  norm_num

/-- Concrete witness: passive depth is not rewardable even if a positive reward is proposed. -/
theorem witness_passive_depth_blocked :
    ¬ rewardableLiquidity .passive 10 0 0 0 0 0 1 := by
  unfold rewardableLiquidity externalServiceEnabled
  norm_num

/-- Concrete witness: self-flow domination blocks non-negative payout. -/
theorem witness_recapturable_dominates :
    liquidityNetBenefit 4 1 3 1 1 1 = -1 := by
  norm_num [liquidityNetBenefit]

end DefensiveLiquidityBenefit
end Proofs
