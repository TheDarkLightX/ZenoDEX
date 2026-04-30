import Proofs.CrossProtocolRecaptureGate
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Two-Venue Composition

A small checked bridge from local release gates to explicit two-venue composition.

The intended reading is:
- venue B's realized take can act as venue A's external recapture term
- if the same principal still passes venue A's cross-protocol gate, venue B's take
  must be strictly smaller than venue A's shared verified budget
- if venue B's take exhausts venue A's shared budget, the combined posture is blocked

This still does not solve the whole cross-venue equilibrium.
It proves the first exact local theorem that turns "cross-protocol recapture"
into an explicit second-venue object.
-/

namespace Proofs
namespace TwoVenueComposition

open AgentCapabilityBounds
open CrossSurfaceBenefitBudget
open RoleCollapseReleaseGate
open CrossProtocolRecaptureGate

/-- Canonical surface take for one venue. -/
def venueTake
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int) : Int :=
  totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer

/-- One principal is admissible across two venues if:
- venue A passes the cross-protocol gate using venue B's take as its external recapture term
- venue B passes the simpler internal role-collapse gate on its own shared budget -/
def twoVenuePrincipalAdmissible
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int) : Prop :=
  crossProtocolReleaseAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      (venueTake rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB) ∧
    roleCollapseReleaseAdmissible
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB

/-- Any two-venue-admissible principal needs explicit live-execution capability on venue A. -/
theorem two_venue_requires_live_capability_a
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int)
    (h : twoVenuePrincipalAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB) :
    capA.liveExecutionAllowed = true := by
  exact cross_protocol_release_requires_live_execution_capability
    capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
    settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
    (venueTake rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB)
    h.1

/-- Any two-venue-admissible principal needs explicit live-execution capability on venue B. -/
theorem two_venue_requires_live_capability_b
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int)
    (h : twoVenuePrincipalAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB) :
    capB.liveExecutionAllowed = true := by
  exact release_admissible_requires_live_execution_capability
    capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
    settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
    h.2

/-- If venue A is still admissible after treating venue B's take as external recapture,
then venue B's take must be strictly smaller than venue A's shared verified budget. -/
theorem two_venue_admissible_requires_b_take_lt_a_shared_budget
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int)
    (h : twoVenuePrincipalAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB) :
    venueTake rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB <
      sharedVerifiedBudget settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA := by
  have hAdjPos :
      0 <
        adjustedSharedBudget settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
          (venueTake rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB) := by
    exact cross_protocol_release_requires_positive_adjusted_budget
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      (venueTake rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB)
      h.1
  have hStrict :
      totalCrossSurfaceTake rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB <
        sharedVerifiedBudget settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA := by
    unfold adjustedSharedBudget venueTake at hAdjPos
    linarith
  simpa [venueTake] using hStrict

/-- If venue B's take exhausts venue A's shared budget, the two-venue posture is blocked. -/
theorem venue_b_take_exhausts_a_budget_blocks_two_venue_admissibility
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int)
    (hExhaust :
      sharedVerifiedBudget settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA ≤
        venueTake rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB) :
    ¬ twoVenuePrincipalAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB := by
  intro h
  exact external_recapture_exhausts_budget_blocks_release
    capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
    settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
    (venueTake rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB)
    hExhaust h.1

/-- Venue B itself must still have positive shared verified budget. -/
theorem two_venue_admissible_requires_positive_budget_b
    (capA : Capability) (actA : RequestedAction)
    (rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA : Int)
    (settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA : Int)
    (capB : Capability) (actB : RequestedAction)
    (rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB : Int)
    (settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB : Int)
    (h : twoVenuePrincipalAdmissible
      capA actA rewardSettlementA rewardLiquidityA rewardOracleA governanceTransferA
      settlementBenefitA liquidityBenefitA oracleBenefitA governanceBenefitA overlapA
      capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
      settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB) :
    0 < sharedVerifiedBudget settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB := by
  exact release_admissible_requires_positive_shared_budget
    capB actB rewardSettlementB rewardLiquidityB rewardOracleB governanceTransferB
    settlementBenefitB liquidityBenefitB oracleBenefitB governanceBenefitB overlapB
    h.2

/-- Concrete witness: a small venue-B take still leaves enough budget on venue A. -/
theorem witness_two_venue_admissible :
    twoVenuePrincipalAdmissible
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 5 }
      { authority := .execute, requestedLoss := 1, liveExecution := true }
      1 0 0 0
      5 0 0 0 0
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 5 }
      { authority := .execute, requestedLoss := 1, liveExecution := true }
      1 0 0 0
      2 0 0 0 0 := by
  unfold twoVenuePrincipalAdmissible
  unfold crossProtocolReleaseAdmissible roleCollapseReleaseAdmissible
  unfold actionAllowed authorityRank adjustedSharedBudget venueTake
  norm_num [totalCrossSurfaceTake, sharedVerifiedBudget]

/-- Concrete witness: venue B can exhaust venue A's budget and block the pair. -/
theorem witness_two_venue_blocked_by_b_take :
    ¬ twoVenuePrincipalAdmissible
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 5 }
      { authority := .execute, requestedLoss := 1, liveExecution := true }
      1 0 0 0
      1 0 0 0 0
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 5 }
      { authority := .execute, requestedLoss := 1, liveExecution := true }
      1 0 0 0
      2 0 0 0 0 := by
  apply venue_b_take_exhausts_a_budget_blocks_two_venue_admissibility
  norm_num [venueTake, sharedVerifiedBudget, totalCrossSurfaceTake]

end TwoVenueComposition
end Proofs
