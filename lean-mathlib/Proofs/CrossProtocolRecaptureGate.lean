import Proofs.RoleCollapseReleaseGate
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Cross-Protocol Recapture Gate

A small checked accounting gate for post-AGI cross-venue composability.

The intended reading is:
- internal release budget is not just shared verified benefit
- it must be reduced by value the same principal can recapture outside the venue
- if external recapture exhausts the adjusted budget, positive internal release is blocked

This still does not solve the whole cross-protocol ecology.
It proves the first local arithmetic obligations that any tighter external
composability law would need to satisfy.
-/

namespace Proofs
namespace CrossProtocolRecaptureGate

open AgentCapabilityBounds
open CrossSurfaceBenefitBudget
open RoleCollapseReleaseGate

/-- Shared verified budget after subtracting value the same principal can recapture
outside the venue from the same event. -/
def adjustedSharedBudget
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture : Int) : Int :=
  sharedVerifiedBudget
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap -
    externalRecapture

/-- Execute-class release gate with external recapture accounted for. -/
def crossProtocolReleaseAdmissible
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture : Int) : Prop :=
  actionAllowed cap act ∧
    act.authority = .execute ∧
    0 ≤ externalRecapture ∧
    totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer ≤
      adjustedSharedBudget
        settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
        externalRecapture ∧
    0 < totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer

/-- Increasing external recapture can only shrink the adjusted budget. -/
theorem adjusted_budget_antitone_in_external_recapture
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture₁ externalRecapture₂ : Int)
    (hRecapture : externalRecapture₁ ≤ externalRecapture₂) :
    adjustedSharedBudget
        settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
        externalRecapture₂ ≤
      adjustedSharedBudget
        settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
        externalRecapture₁ := by
  unfold adjustedSharedBudget
  linarith

/-- Zero external recapture recovers the original shared verified budget. -/
theorem adjusted_budget_eq_shared_when_no_external_recapture
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int) :
    adjustedSharedBudget
        settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap 0 =
      sharedVerifiedBudget
        settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
  unfold adjustedSharedBudget
  ring

/-- Cross-protocol admissibility implies the simpler internal role-collapse gate. -/
theorem cross_protocol_release_implies_role_collapse_release
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture : Int)
    (h : crossProtocolReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture) :
    roleCollapseReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.2⟩
  have hBudgetLe :
      adjustedSharedBudget
          settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
          externalRecapture ≤
        sharedVerifiedBudget
          settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
    have hRecaptureNonneg : 0 ≤ externalRecapture := h.2.2.1
    unfold adjustedSharedBudget
    linarith
  exact le_trans h.2.2.2.1 hBudgetLe

/-- Any cross-protocol release-admissible action requires explicit live-execution capability. -/
theorem cross_protocol_release_requires_live_execution_capability
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture : Int)
    (h : crossProtocolReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture) :
    cap.liveExecutionAllowed = true := by
  exact release_admissible_requires_live_execution_capability
    cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
    settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
    (cross_protocol_release_implies_role_collapse_release
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture h)

/-- Any positive internal take under cross-protocol accounting requires
strictly positive adjusted budget. -/
theorem cross_protocol_release_requires_positive_adjusted_budget
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture : Int)
    (h : crossProtocolReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture) :
    0 < adjustedSharedBudget
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture := by
  have hBound :
      totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer ≤
        adjustedSharedBudget
          settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
          externalRecapture := by
    exact h.2.2.2.1
  have hTakePos :
      0 <
        totalCrossSurfaceTake
          rewardSettlement rewardLiquidity rewardOracle governanceTransfer := by
    exact h.2.2.2.2
  linarith

/-- A positive cross-protocol release is admissible only before external
recapture exhausts the original shared verified budget. -/
theorem cross_protocol_release_requires_external_recapture_below_shared_budget
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture : Int)
    (h : crossProtocolReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture) :
    externalRecapture <
      sharedVerifiedBudget
        settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
  have hBudgetPos :
      0 < adjustedSharedBudget
        settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
        externalRecapture := by
    exact cross_protocol_release_requires_positive_adjusted_budget
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture h
  unfold adjustedSharedBudget at hBudgetPos
  linarith

/-- If adjusted budget is non-positive after external recapture, positive
internal release is blocked. -/
theorem nonpositive_adjusted_budget_blocks_release
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture : Int)
    (hBudgetNonpos :
      adjustedSharedBudget
        settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
        externalRecapture ≤ 0) :
    ¬ crossProtocolReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture := by
  intro h
  have hBudgetPos :
      0 < adjustedSharedBudget
        settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
        externalRecapture := by
    exact cross_protocol_release_requires_positive_adjusted_budget
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap externalRecapture h
  linarith

/-- If external recapture is at least as large as the original shared budget,
the adjusted budget is non-positive and release is blocked. -/
theorem external_recapture_exhausts_budget_blocks_release
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture : Int)
    (hExhaust :
      sharedVerifiedBudget
        settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap ≤
      externalRecapture) :
    ¬ crossProtocolReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap
      externalRecapture := by
  apply nonpositive_adjusted_budget_blocks_release
  unfold adjustedSharedBudget
  linarith

/-- Concrete witness: without external recapture the adjusted budget admits a
small execute action. -/
theorem witness_cross_protocol_release_without_external_recapture :
    crossProtocolReleaseAdmissible
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 5 }
      { authority := .execute, requestedLoss := 1, liveExecution := true }
      1 0 0 0
      4 0 0 0 0 0 := by
  unfold crossProtocolReleaseAdmissible
  unfold actionAllowed authorityRank adjustedSharedBudget
  norm_num [totalCrossSurfaceTake, sharedVerifiedBudget]

/-- Concrete witness: enough external recapture exhausts the adjusted budget and blocks release. -/
theorem witness_external_recapture_blocks_release :
    ¬ crossProtocolReleaseAdmissible
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 5 }
      { authority := .execute, requestedLoss := 1, liveExecution := true }
      1 0 0 0
      4 0 0 0 0 4 := by
  apply external_recapture_exhausts_budget_blocks_release
  norm_num [sharedVerifiedBudget]

end CrossProtocolRecaptureGate
end Proofs
