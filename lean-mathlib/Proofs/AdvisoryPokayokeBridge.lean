import Proofs.AgentCapabilityBounds
import Proofs.PokayokeSafety

/-!
# Advisory-to-poka-yoke bridge

This file connects the advisory capability model to the generic poka-yoke submit
contract.  The point is deliberately narrow: an advisory, non-live capability is
not an execution authority, and dangerous unshielded submit paths are still
blocked by the interlock predicate.
-/

namespace Proofs
namespace AdvisoryPokayokeBridge

open AgentCapabilityBounds
open TauSwap.PokayokeSafety

/-- Canonical non-authoritative capability for advisory KRR / automation
surfaces. -/
def advisoryNonLiveCapability (maxLoss : Int) : Capability where
  maxAuthority := .advisory
  liveExecutionAllowed := false
  maxLoss := maxLoss

/-- Advisory non-live capability blocks execute-class requests before the
poka-yoke submit predicate is even relevant. -/
theorem advisory_execute_request_blocked
    (maxLoss : Int)
    (act : RequestedAction)
    (hExec : act.authority = .execute) :
    ¬ actionAllowed (advisoryNonLiveCapability maxLoss) act := by
  simpa [advisoryNonLiveCapability] using
    advisory_non_authoritative_blocks_execute maxLoss act hExec

/-- Advisory non-live capability blocks live-execution requests before the
poka-yoke submit predicate is even relevant. -/
theorem advisory_live_request_blocked
    (maxLoss : Int)
    (act : RequestedAction)
    (hLive : act.liveExecution = true) :
    ¬ actionAllowed (advisoryNonLiveCapability maxLoss) act := by
  simpa [advisoryNonLiveCapability] using
    advisory_non_authoritative_blocks_live_execution maxLoss act hLive

/-- There is no path where an advisory non-live capability both authorizes an
execute-class action and the generic submit predicate says yes. -/
theorem advisory_execute_request_cannot_be_authorized_and_submitted
    (maxLoss : Int)
    (act : RequestedAction)
    (status : RiskStatus)
    (i : InterlockState)
    (hExec : act.authority = .execute) :
    ¬ (actionAllowed (advisoryNonLiveCapability maxLoss) act ∧
      submitAllowed status i = true) := by
  rintro ⟨haction, _hsubmit⟩
  exact advisory_execute_request_blocked maxLoss act hExec haction

/-- If the action requests live execution, there is no path where advisory
non-live authority and the generic submit predicate jointly authorize it. -/
theorem advisory_live_request_cannot_be_authorized_and_submitted
    (maxLoss : Int)
    (act : RequestedAction)
    (status : RiskStatus)
    (i : InterlockState)
    (hLive : act.liveExecution = true) :
    ¬ (actionAllowed (advisoryNonLiveCapability maxLoss) act ∧
      submitAllowed status i = true) := by
  rintro ⟨haction, _hsubmit⟩
  exact advisory_live_request_blocked maxLoss act hLive haction

/-- A dangerous unshielded execute request is blocked at both boundaries:
capability admission rejects the execute authority, and poka-yoke submit rejects
the missing interlock. -/
theorem advisory_execute_dangerous_without_interlock_blocked_at_both_boundaries
    (maxLoss : Int)
    (act : RequestedAction)
    (status : RiskStatus)
    (i : InterlockState)
    (hExec : act.authority = .execute)
    (hdanger : dangerous status = true)
    (hinterlock : interlockSatisfied i = false) :
    (¬ actionAllowed (advisoryNonLiveCapability maxLoss) act) ∧
      submitAllowed status i = false := by
  constructor
  · exact advisory_execute_request_blocked maxLoss act hExec
  · exact dangerous_without_interlock_blocks status i hdanger hinterlock

/-- A dangerous unshielded live request is also blocked at both boundaries:
capability admission rejects the live execution request, and poka-yoke submit
rejects the missing interlock. -/
theorem advisory_live_dangerous_without_interlock_blocked_at_both_boundaries
    (maxLoss : Int)
    (act : RequestedAction)
    (status : RiskStatus)
    (i : InterlockState)
    (hLive : act.liveExecution = true)
    (hdanger : dangerous status = true)
    (hinterlock : interlockSatisfied i = false) :
    (¬ actionAllowed (advisoryNonLiveCapability maxLoss) act) ∧
      submitAllowed status i = false := by
  constructor
  · exact advisory_live_request_blocked maxLoss act hLive
  · exact dangerous_without_interlock_blocks status i hdanger hinterlock

end AdvisoryPokayokeBridge
end Proofs
