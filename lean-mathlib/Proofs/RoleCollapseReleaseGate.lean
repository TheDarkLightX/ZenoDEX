import Proofs.AgentCapabilityBounds
import Proofs.CrossSurfaceBenefitBudget
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Role-Collapse Release Gate

A small composed release-style gate for delegated post-AGI actions.

The purpose is to join two local contracts that were proved separately:
- delegated actions need explicit authority and live-execution permission
- one principal with multi-surface take needs positive shared verified budget

This still does not solve the whole equilibrium. It proves the first local
release-style facts needed for a role-collapse gate.
-/

namespace Proofs
namespace RoleCollapseReleaseGate

open AgentCapabilityBounds
open CrossSurfaceBenefitBudget

/-- A delegated execute-class action is release-admissible only if:
1. the requested action fits inside the declared capability
2. the combined settlement/liquidity/oracle/governance take is bounded by one
   shared verified-benefit budget
3. the combined take is strictly positive, so the gate is about real extraction
   rather than the degenerate zero-take case. -/
def roleCollapseReleaseAdmissible
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int) : Prop :=
  actionAllowed cap act ∧
    act.authority = .execute ∧
    totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer ≤
      sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap ∧
    0 < totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer

/-- Any release-admissible role-collapse action is live-executing. -/
theorem release_admissible_requires_live_execution
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int)
    (h : roleCollapseReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap) :
    act.liveExecution = true := by
  exact allowed_execute_requires_live_execution cap act h.1 h.2.1

/-- Any release-admissible role-collapse action requires explicit live-execution capability. -/
theorem release_admissible_requires_live_execution_capability
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int)
    (h : roleCollapseReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap) :
    cap.liveExecutionAllowed = true := by
  have hLive : act.liveExecution = true := release_admissible_requires_live_execution
    cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
    settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap h
  exact allowed_live_execution_requires_capability cap act h.1 hLive

/-- Any release-admissible positive multi-surface take requires strictly positive shared verified budget. -/
theorem release_admissible_requires_positive_shared_budget
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int)
    (h : roleCollapseReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap) :
    0 < sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
  have hBound :
      totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer ≤
        sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
    exact h.2.2.1
  have hTakePos :
      0 < totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer := by
    exact h.2.2.2
  linarith

/-- A non-positive shared budget blocks execute-class role-collapse release. -/
theorem nonpositive_shared_budget_blocks_release
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int)
    (hBudgetNonpos :
      sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap ≤ 0) :
    ¬ roleCollapseReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
  intro h
  have hBudgetPos :
      0 < sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
    exact release_admissible_requires_positive_shared_budget
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap h
  linarith

/-- If live execution is forbidden in the capability, release is blocked. -/
theorem no_release_when_live_execution_forbidden
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int)
    (hCap : cap.liveExecutionAllowed = false) :
    ¬ roleCollapseReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
  intro h
  exact no_execute_when_live_execution_forbidden cap hCap act h.2.1 h.1

/-- Stage-only capability cannot pass the execute-class release gate. -/
theorem stage_capability_blocks_release
    (maxLoss : Int)
    (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int)
    (hExec : act.authority = .execute) :
    ¬ roleCollapseReleaseAdmissible
      { maxAuthority := .stage, liveExecutionAllowed := true, maxLoss := maxLoss }
      act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
  intro h
  exact stage_capability_cannot_authorize_execute maxLoss act hExec h.1

/-- Advisory-only capability cannot pass the execute-class release gate. -/
theorem advisory_capability_blocks_release
    (liveAllowed : Bool) (maxLoss : Int)
    (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int)
    (hExec : act.authority = .execute) :
    ¬ roleCollapseReleaseAdmissible
      { maxAuthority := .advisory, liveExecutionAllowed := liveAllowed, maxLoss := maxLoss }
      act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
  intro h
  have hStronger : authorityRank .advisory < authorityRank act.authority := by
    simp [hExec, authorityRank]
  exact advisory_capability_cannot_authorize_stronger_action liveAllowed maxLoss act hStronger h.1

/-- Zero-loss capability blocks any release attempt with positive requested loss. -/
theorem zero_loss_capability_blocks_positive_loss_release
    (cap : Capability) (act : RequestedAction)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int)
    (hZero : cap.maxLoss = 0)
    (hPosLoss : 0 < act.requestedLoss) :
    ¬ roleCollapseReleaseAdmissible
      cap act rewardSettlement rewardLiquidity rewardOracle governanceTransfer
      settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
  intro h
  exact zero_loss_capability_blocks_positive_loss cap hZero act hPosLoss h.1

/-- Concrete witness: an execute-capable bounded-loss action with positive shared budget
    passes the release gate. -/
theorem witness_release_admissible :
    roleCollapseReleaseAdmissible
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 5 }
      { authority := .execute, requestedLoss := 1, liveExecution := true }
      1 0 0 0
      4 0 0 0 0 := by
  unfold roleCollapseReleaseAdmissible
  unfold actionAllowed authorityRank
  norm_num [totalCrossSurfaceTake, sharedVerifiedBudget]

/-- Concrete witness: non-positive shared budget blocks release even when the action
    itself is execute-capable. -/
theorem witness_nonpositive_budget_blocks_release :
    ¬ roleCollapseReleaseAdmissible
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 5 }
      { authority := .execute, requestedLoss := 1, liveExecution := true }
      1 0 0 0
      1 0 0 0 2 := by
  apply nonpositive_shared_budget_blocks_release
  norm_num [sharedVerifiedBudget]

end RoleCollapseReleaseGate
end Proofs
