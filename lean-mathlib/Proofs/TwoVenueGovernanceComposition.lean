import Proofs.TwoVenueComposition
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Two-Venue Governance Composition

A small checked bridge from two-venue composition to governance-timed extraction.

The intended reading is:
- venue A sees venue B's realized take plus governance-side extraction as external recapture
- venue B sees venue A's realized take plus governance-side extraction as external recapture
- if either side's budget is exhausted by that combined externalized value, the pair is blocked

This still does not solve strategic governance timing in full.
It proves the first exact local theorem that adds governance-side value to the
two-venue composition surface.
-/

namespace Proofs
namespace TwoVenueGovernanceComposition

open AgentCapabilityBounds
open CrossSurfaceBenefitBudget
open CrossProtocolRecaptureGate
open TwoVenueComposition

/-- External recapture seen by one venue: the other venue's realized take plus
governance-side extracted value. -/
def venuePlusGovernanceRecapture
    (rewardSettlementOther rewardLiquidityOther rewardOracleOther governanceTransferOther governanceTransferG : Int) : Int :=
  venueTake rewardSettlementOther rewardLiquidityOther rewardOracleOther governanceTransferOther + governanceTransferG

/-- One principal is admissible across two venues with governance timing if both venues
pass the cross-protocol gate after charging the other venue's take plus governance extraction
as external recapture. -/
def twoVenueGovernanceAdmissible
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int)
    (governanceTransferG : Int) : Prop :=
  crossProtocolReleaseAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      (venuePlusGovernanceRecapture rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB governanceTransferG) ∧
    crossProtocolReleaseAdmissible
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
      (venuePlusGovernanceRecapture rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA governanceTransferG)

/-- Venue A still needs explicit live-execution capability. -/
theorem two_venue_governance_requires_live_capability_a
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int)
    (governanceTransferG : Int)
    (h : twoVenueGovernanceAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
      governanceTransferG) :
    capA.liveExecutionAllowed = true := by
  exact cross_protocol_release_requires_live_execution_capability
    capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
    settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
    (venuePlusGovernanceRecapture rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB governanceTransferG)
    h.1

/-- Venue B still needs explicit live-execution capability. -/
theorem two_venue_governance_requires_live_capability_b
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int)
    (governanceTransferG : Int)
    (h : twoVenueGovernanceAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
      governanceTransferG) :
    capB.liveExecutionAllowed = true := by
  exact cross_protocol_release_requires_live_execution_capability
    capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
    settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
    (venuePlusGovernanceRecapture rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA governanceTransferG)
    h.2

/-- Venue A can stay admissible only if venue B's take plus governance extraction stays
strictly below venue A's shared verified budget. -/
theorem two_venue_governance_requires_b_take_plus_gov_lt_a_budget
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int)
    (governanceTransferG : Int)
    (h : twoVenueGovernanceAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
      governanceTransferG) :
    venuePlusGovernanceRecapture rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB governanceTransferG <
      sharedVerifiedBudget settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA := by
  have hAdjPos :
      0 <
        adjustedSharedBudget settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
          (venuePlusGovernanceRecapture rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB governanceTransferG) := by
    exact cross_protocol_release_requires_positive_adjusted_budget
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      (venuePlusGovernanceRecapture rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB governanceTransferG)
      h.1
  have hStrict :
      totalCrossSurfaceTake rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB + governanceTransferG <
        sharedVerifiedBudget settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA := by
    unfold adjustedSharedBudget venuePlusGovernanceRecapture venueTake at hAdjPos
    linarith
  simpa [venuePlusGovernanceRecapture, venueTake] using hStrict

/-- Venue B can stay admissible only if venue A's take plus governance extraction stays
strictly below venue B's shared verified budget. -/
theorem two_venue_governance_requires_a_take_plus_gov_lt_b_budget
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int)
    (governanceTransferG : Int)
    (h : twoVenueGovernanceAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
      governanceTransferG) :
    venuePlusGovernanceRecapture rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA governanceTransferG <
      sharedVerifiedBudget settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB := by
  have hAdjPos :
      0 <
        adjustedSharedBudget settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
          (venuePlusGovernanceRecapture rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA governanceTransferG) := by
    exact cross_protocol_release_requires_positive_adjusted_budget
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
      (venuePlusGovernanceRecapture rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA governanceTransferG)
      h.2
  have hStrict :
      totalCrossSurfaceTake rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA + governanceTransferG <
        sharedVerifiedBudget settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB := by
    unfold adjustedSharedBudget venuePlusGovernanceRecapture venueTake at hAdjPos
    linarith
  simpa [venuePlusGovernanceRecapture, venueTake] using hStrict

/-- If venue B's take plus governance extraction exhausts venue A's budget, the pair is blocked. -/
theorem b_take_plus_gov_exhausts_a_budget_blocks
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int)
    (governanceTransferG : Int)
    (hExhaust :
      sharedVerifiedBudget settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA ≤
        venuePlusGovernanceRecapture rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB governanceTransferG) :
    ¬ twoVenueGovernanceAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
      governanceTransferG := by
  intro h
  exact external_recapture_exhausts_budget_blocks_release
    capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
    settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
    (venuePlusGovernanceRecapture rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB governanceTransferG)
    hExhaust h.1

/-- Governance extraction alone can block venue A if it already reaches venue A's budget.
The reason is that venue B's own admissibility forces venue B's take to be strictly positive. -/
theorem governance_alone_reaching_a_budget_blocks
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int)
    (governanceTransferG : Int)
    (hGovExhaust :
      sharedVerifiedBudget settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA ≤ governanceTransferG) :
    ¬ twoVenueGovernanceAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
      governanceTransferG := by
  intro h
  have hBTakePos :
      0 < venueTake rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB := by
    rcases h with ⟨_, hB⟩
    rcases hB with ⟨_, _, _, _, hTakePos⟩
    have :
        0 < totalCrossSurfaceTake rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB := by
      exact hTakePos
    simpa [venueTake] using this
  have hLt :
      venuePlusGovernanceRecapture rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB governanceTransferG <
        sharedVerifiedBudget settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA := by
    exact two_venue_governance_requires_b_take_plus_gov_lt_a_budget
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
      governanceTransferG h
  have hGe :
      sharedVerifiedBudget settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA ≤
        venuePlusGovernanceRecapture rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB governanceTransferG := by
    have hBTakePos' :
        0 < totalCrossSurfaceTake rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB := by
      simpa [venueTake] using hBTakePos
    unfold venuePlusGovernanceRecapture venueTake
    linarith
  exact not_lt_of_ge hGe hLt

/-- Concrete witness: modest governance extraction still leaves both venues admissible. -/
theorem witness_two_venue_governance_admissible :
    twoVenueGovernanceAdmissible
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 5 }
      { authority := .execute, requestedLoss := 1, liveExecution := true }
      1 0 0 0
      5 0 0 0 0
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 5 }
      { authority := .execute, requestedLoss := 1, liveExecution := true }
      1 0 0 0
      5 0 0 0 0
      1 := by
  unfold twoVenueGovernanceAdmissible
  unfold crossProtocolReleaseAdmissible actionAllowed authorityRank
  unfold adjustedSharedBudget venuePlusGovernanceRecapture venueTake
  norm_num [totalCrossSurfaceTake, sharedVerifiedBudget]

/-- Concrete witness: governance extraction can block the pair once it reaches venue A's budget. -/
theorem witness_governance_blocks_pair :
    ¬ twoVenueGovernanceAdmissible
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 5 }
      { authority := .execute, requestedLoss := 1, liveExecution := true }
      1 0 0 0
      1 0 0 0 0
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 5 }
      { authority := .execute, requestedLoss := 1, liveExecution := true }
      1 0 0 0
      5 0 0 0 0
      1 := by
  apply governance_alone_reaching_a_budget_blocks
  norm_num [sharedVerifiedBudget]

end TwoVenueGovernanceComposition
end Proofs
