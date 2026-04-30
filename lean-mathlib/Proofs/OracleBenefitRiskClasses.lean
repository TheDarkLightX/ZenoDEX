import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Oracle Benefit Risk Classes

A bounded oracle benefit language for the post-AGI mechanism discussion.

The core idea is to replace vague "oracle quality improved" claims with a finite
risk-class transition system. A positive rewardable transition must strictly move
from a lower class to a higher class after subtracting recapturable terms.
-/

namespace Proofs
namespace OracleBenefitRiskClasses

inductive OracleRiskClass where
  | stale
  | freshUnsynced
  | freshSynced
  | freshSyncedBounded
  | freshSyncedBoundedRiskyOps
  deriving DecidableEq, Repr

/-- Exact bounded rank used for local transition reasoning. -/
def riskRank : OracleRiskClass → Nat
  | .stale => 0
  | .freshUnsynced => 1
  | .freshSynced => 2
  | .freshSyncedBounded => 3
  | .freshSyncedBoundedRiskyOps => 4

/-- Quote generation is only admissible once the update is at least fresh. -/
def quoteEnabled : OracleRiskClass → Prop
  | .stale => False
  | _ => True

/-- Settlement is only admissible once the update is synced. -/
def settlementEnabled : OracleRiskClass → Prop
  | .freshSynced | .freshSyncedBounded | .freshSyncedBoundedRiskyOps => True
  | _ => False

/-- Risky operations are only admissible in the strongest class. -/
def riskyOpsEnabled : OracleRiskClass → Prop
  | .freshSyncedBoundedRiskyOps => True
  | _ => False

/-- Strict class improvement in the bounded lattice. -/
def classImprovement (before after : OracleRiskClass) : Prop :=
  riskRank before < riskRank after

/-- Integer-valued transition delta used by local payout laws. -/
def classDelta (before after : OracleRiskClass) : Int :=
  Int.ofNat (riskRank after) - Int.ofNat (riskRank before)

/-- Net transition benefit after subtracting recapturable terms and safety reserve. -/
def transitionNetBenefit
    (before after : OracleRiskClass)
    (sameUpdatePnL spamValue overlap safetyMargin : Int) : Int :=
  classDelta before after - sameUpdatePnL - spamValue - overlap - safetyMargin

/-- Local rewardability shell for a single oracle-state transition. -/
def rewardableTransition
    (before after : OracleRiskClass)
    (sameUpdatePnL spamValue overlap safetyMargin reward : Int) : Prop :=
  0 < reward ∧
    reward ≤ transitionNetBenefit before after sameUpdatePnL spamValue overlap safetyMargin

@[simp] theorem risky_ops_enabled_iff
    (c : OracleRiskClass) :
    riskyOpsEnabled c ↔ c = .freshSyncedBoundedRiskyOps := by
  match c with
  | .freshSyncedBoundedRiskyOps => simp [riskyOpsEnabled]
  | .stale | .freshUnsynced | .freshSynced | .freshSyncedBounded => simp [riskyOpsEnabled]

@[simp] theorem settlement_enabled_iff
    (c : OracleRiskClass) :
    settlementEnabled c ↔
      c = .freshSynced ∨ c = .freshSyncedBounded ∨ c = .freshSyncedBoundedRiskyOps := by
  match c with
  | .stale => simp [settlementEnabled]
  | .freshUnsynced => simp [settlementEnabled]
  | .freshSynced => simp [settlementEnabled]
  | .freshSyncedBounded => simp [settlementEnabled]
  | .freshSyncedBoundedRiskyOps => simp [settlementEnabled]

@[simp] theorem quote_enabled_iff
    (c : OracleRiskClass) :
    quoteEnabled c ↔ c ≠ .stale := by
  match c with
  | .stale => simp [quoteEnabled]
  | .freshUnsynced | .freshSynced | .freshSyncedBounded | .freshSyncedBoundedRiskyOps =>
      simp [quoteEnabled]

/-- Risky-ops-enabled classes are exactly the top class in the bounded lattice. -/
theorem risky_ops_enabled_eq_top
    {c : OracleRiskClass} :
    riskyOpsEnabled c → c = .freshSyncedBoundedRiskyOps := by
  intro h
  exact (risky_ops_enabled_iff c).1 h

/-- Risky-ops admissibility is stronger than settlement admissibility. -/
theorem risky_ops_implies_settlement_enabled
    {c : OracleRiskClass} :
    riskyOpsEnabled c → settlementEnabled c := by
  intro hRisky
  rcases (risky_ops_enabled_iff c).1 hRisky with rfl
  simp [settlementEnabled]

/-- Settlement admissibility is stronger than quote admissibility. -/
theorem settlement_implies_quote_enabled
    {c : OracleRiskClass} :
    settlementEnabled c → quoteEnabled c := by
  intro hSettle
  rcases (settlement_enabled_iff c).1 hSettle with rfl | rfl | rfl <;> simp [quoteEnabled]

/-- Positive class delta is exactly strict class improvement. -/
theorem positive_class_delta_iff_improves
    (before after : OracleRiskClass) :
    0 < classDelta before after ↔ classImprovement before after := by
  unfold classDelta classImprovement
  constructor
  · intro hDelta
    have hInt : Int.ofNat (riskRank before) < Int.ofNat (riskRank after) := by
      linarith
    exact Int.ofNat_lt.mp hInt
  · intro hImprove
    have hInt : Int.ofNat (riskRank before) < Int.ofNat (riskRank after) := by
      exact Int.ofNat_lt.mpr hImprove
    linarith

/-- Any positive rewardable transition forces a positive class delta before
recapturable terms are even considered as a rank witness. -/
theorem rewardable_transition_requires_positive_class_delta
    (before after : OracleRiskClass)
    (sameUpdatePnL spamValue overlap safetyMargin reward : Int)
    (hPnL : 0 ≤ sameUpdatePnL)
    (hSpam : 0 ≤ spamValue)
    (hOverlap : 0 ≤ overlap)
    (hMargin : 0 ≤ safetyMargin)
    (hReward :
      rewardableTransition
        before
        after
        sameUpdatePnL
        spamValue
        overlap
        safetyMargin
        reward) :
    0 < classDelta before after := by
  rcases hReward with ⟨hPos, hUpper⟩
  unfold transitionNetBenefit at hUpper
  linarith

/-- Improvement in the bounded lattice is transitive. -/
theorem class_improvement_transitive
    {a b c : OracleRiskClass}
    (hab : classImprovement a b)
    (hbc : classImprovement b c) :
    classImprovement a c := by
  unfold classImprovement at hab hbc ⊢
  omega

/-- A positive rewardable transition requires strict risk-class improvement
    once recapturable terms are known non-negative. -/
theorem rewardable_transition_requires_improvement
    (before after : OracleRiskClass)
    (sameUpdatePnL spamValue overlap safetyMargin reward : Int)
    (hPnL : 0 ≤ sameUpdatePnL)
    (hSpam : 0 ≤ spamValue)
    (hOverlap : 0 ≤ overlap)
    (hMargin : 0 ≤ safetyMargin)
    (hReward :
      rewardableTransition
        before
        after
        sameUpdatePnL
        spamValue
        overlap
        safetyMargin
        reward) :
    classImprovement before after := by
  have hDeltaPos :=
    rewardable_transition_requires_positive_class_delta
      before
      after
      sameUpdatePnL
      spamValue
      overlap
      safetyMargin
      reward
      hPnL
      hSpam
      hOverlap
      hMargin
      hReward
  exact (positive_class_delta_iff_improves before after).1 hDeltaPos

/-- Strictly improving into the top class means the source was not already top. -/
theorem class_improvement_into_risky_ops_requires_not_top
    {before : OracleRiskClass}
    (hImprove : classImprovement before .freshSyncedBoundedRiskyOps) :
    before ≠ .freshSyncedBoundedRiskyOps := by
  intro hEq
  subst hEq
  simp [classImprovement, riskRank] at hImprove

/-- If the target state enables risky operations and the transition is rewardable,
    the source state was not already risky-ops-enabled. This blocks paying twice
    for an already-enabled exact class. -/
theorem rewardable_transition_into_risky_ops_requires_not_already_enabled
    (before : OracleRiskClass)
    (sameUpdatePnL spamValue overlap safetyMargin reward : Int)
    (hPnL : 0 ≤ sameUpdatePnL)
    (hSpam : 0 ≤ spamValue)
    (hOverlap : 0 ≤ overlap)
    (hMargin : 0 ≤ safetyMargin)
    (hReward :
      rewardableTransition
        before
        .freshSyncedBoundedRiskyOps
        sameUpdatePnL
        spamValue
        overlap
        safetyMargin
        reward) :
    ¬ riskyOpsEnabled before := by
  have hImprove := rewardable_transition_requires_improvement
    before .freshSyncedBoundedRiskyOps sameUpdatePnL spamValue overlap safetyMargin reward
    hPnL hSpam hOverlap hMargin hReward
  intro hRisky
  have hTop : before = .freshSyncedBoundedRiskyOps := risky_ops_enabled_eq_top hRisky
  exact class_improvement_into_risky_ops_requires_not_top hImprove hTop

/-- Rewardable settlement-enabling transitions must land in a quote-enabled class. -/
theorem rewardable_transition_to_settlement_implies_quote_enabled_target
    (before after : OracleRiskClass)
    (sameUpdatePnL spamValue overlap safetyMargin reward : Int)
    (hSettle : settlementEnabled after)
    (_hReward : rewardableTransition before after sameUpdatePnL spamValue overlap safetyMargin reward) :
    quoteEnabled after := by
  exact settlement_implies_quote_enabled hSettle

/-- Concrete witness: stale → freshSyncedBounded yields positive class delta 3. -/
theorem witness_transition_gain :
    classDelta .stale .freshSyncedBounded = 3 := by
  native_decide

/-- Concrete witness: positive rewardable transition with zero recapturable terms. -/
theorem witness_rewardable_transition :
    rewardableTransition .stale .freshSyncedBounded 0 0 0 0 1 := by
  unfold rewardableTransition transitionNetBenefit classDelta riskRank
  norm_num

/-- Concrete witness: no positive reward exists without strict class improvement. -/
theorem witness_nonimproving_transition_blocked :
    ¬ rewardableTransition .freshSyncedBounded .freshSyncedBounded 0 0 0 0 1 := by
  unfold rewardableTransition transitionNetBenefit classDelta riskRank
  norm_num

end OracleBenefitRiskClasses
end Proofs
