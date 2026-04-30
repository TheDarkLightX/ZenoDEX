import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Agent Capability Bounds

A bounded authority contract for delegated AGI agents.

The design goal is not to model all market behavior. It is to prove the first
local facts needed for a post-AGI delegation surface:
- actions have explicit authority levels
- live execution needs explicit permission
- requested loss must fit inside a declared loss ceiling
- zero-loss capability excludes positive-loss execution
-/

namespace Proofs
namespace AgentCapabilityBounds

inductive AuthorityLevel where
  | advisory
  | stage
  | execute
  deriving DecidableEq, Repr

/-- Total authority rank. -/
def authorityRank : AuthorityLevel → Nat
  | .advisory => 0
  | .stage => 1
  | .execute => 2

structure Capability where
  maxAuthority : AuthorityLevel
  liveExecutionAllowed : Bool
  maxLoss : Int
  deriving DecidableEq, Repr

structure RequestedAction where
  authority : AuthorityLevel
  requestedLoss : Int
  liveExecution : Bool
  deriving DecidableEq, Repr

/-- Local admission predicate for delegated actions. -/
def actionAllowed (cap : Capability) (act : RequestedAction) : Prop :=
  authorityRank act.authority ≤ authorityRank cap.maxAuthority ∧
    0 ≤ act.requestedLoss ∧
    act.requestedLoss ≤ cap.maxLoss ∧
    (act.liveExecution = true → cap.liveExecutionAllowed = true) ∧
    (act.authority = .execute → act.liveExecution = true)

@[simp] theorem authority_rank_monotone_cases :
    authorityRank .advisory < authorityRank .stage ∧
    authorityRank .stage < authorityRank .execute := by
  decide

/-- Execute authority is strictly stronger than stage or advisory. -/
theorem execute_not_le_stage :
    ¬ authorityRank .execute ≤ authorityRank .stage := by
  decide

theorem execute_not_le_advisory :
    ¬ authorityRank .execute ≤ authorityRank .advisory := by
  decide

/-- If an action is allowed and requests live execution, the capability explicitly allows it. -/
theorem allowed_live_execution_requires_capability
    (cap : Capability) (act : RequestedAction)
    (h : actionAllowed cap act)
    (hLive : act.liveExecution = true) :
    cap.liveExecutionAllowed = true := by
  exact h.2.2.2.1 hLive

/-- Any allowed execute-class action must be live-executing. -/
theorem allowed_execute_requires_live_execution
    (cap : Capability) (act : RequestedAction)
    (h : actionAllowed cap act)
    (hExec : act.authority = .execute) :
    act.liveExecution = true := by
  exact h.2.2.2.2 hExec

/-- If live execution is forbidden, no execute-class action can be allowed. -/
theorem no_execute_when_live_execution_forbidden
    (cap : Capability) (hCap : cap.liveExecutionAllowed = false)
    (act : RequestedAction)
    (hExec : act.authority = .execute) :
    ¬ actionAllowed cap act := by
  intro h
  have hLive : act.liveExecution = true := allowed_execute_requires_live_execution cap act h hExec
  have hAllowed : cap.liveExecutionAllowed = true := allowed_live_execution_requires_capability cap act h hLive
  rw [hCap] at hAllowed
  contradiction

/-- Stage capability cannot authorize execute-class actions. -/
theorem stage_capability_cannot_authorize_execute
    (maxLoss : Int)
    (act : RequestedAction)
    (hExec : act.authority = .execute) :
    ¬ actionAllowed { maxAuthority := .stage, liveExecutionAllowed := true, maxLoss := maxLoss } act := by
  intro h
  have hRank : authorityRank .execute ≤ authorityRank .stage := by
    simpa [hExec] using h.1
  exact execute_not_le_stage hRank

/-- Advisory capability cannot authorize stage or execute actions if the request exceeds advisory rank. -/
theorem advisory_capability_cannot_authorize_stronger_action
    (liveAllowed : Bool) (maxLoss : Int)
    (act : RequestedAction)
    (hStronger : authorityRank .advisory < authorityRank act.authority) :
    ¬ actionAllowed { maxAuthority := .advisory, liveExecutionAllowed := liveAllowed, maxLoss := maxLoss } act := by
  intro h
  have hRank : authorityRank act.authority ≤ authorityRank .advisory := by
    simpa using h.1
  omega

/-- Advisory-only, non-live capabilities cannot authorize any live execution
request, even if the requested action labels itself as advisory. -/
theorem advisory_non_authoritative_blocks_live_execution
    (maxLoss : Int)
    (act : RequestedAction)
    (hLive : act.liveExecution = true) :
    ¬ actionAllowed
      { maxAuthority := .advisory, liveExecutionAllowed := false, maxLoss := maxLoss }
      act := by
  intro h
  have hAllowedLive :
      ({ maxAuthority := .advisory, liveExecutionAllowed := false, maxLoss := maxLoss } :
        Capability).liveExecutionAllowed = true :=
    allowed_live_execution_requires_capability _ _ h hLive
  contradiction

/-- Advisory-only, non-live capabilities cannot authorize execute-class
requests.  This is the direct non-authoritative boundary used by advisory AI
or KRR shells: advice may exist, but execution requires a different capability. -/
theorem advisory_non_authoritative_blocks_execute
    (maxLoss : Int)
    (act : RequestedAction)
    (hExec : act.authority = .execute) :
    ¬ actionAllowed
      { maxAuthority := .advisory, liveExecutionAllowed := false, maxLoss := maxLoss }
      act := by
  exact no_execute_when_live_execution_forbidden
    { maxAuthority := .advisory, liveExecutionAllowed := false, maxLoss := maxLoss }
    rfl act hExec

/-- Allowed actions respect the declared loss ceiling. -/
theorem allowed_action_respects_loss_ceiling
    (cap : Capability) (act : RequestedAction)
    (h : actionAllowed cap act) :
    act.requestedLoss ≤ cap.maxLoss := by
  exact h.2.2.1

/-- A zero-loss capability cannot authorize an action with positive requested loss. -/
theorem zero_loss_capability_blocks_positive_loss
    (cap : Capability)
    (hZero : cap.maxLoss = 0)
    (act : RequestedAction)
    (hPos : 0 < act.requestedLoss) :
    ¬ actionAllowed cap act := by
  intro h
  have hLe : act.requestedLoss ≤ 0 := by simpa [hZero] using allowed_action_respects_loss_ceiling cap act h
  linarith

/-- Concrete witness: advisory-only zero-loss capability admits an advisory zero-loss action. -/
theorem witness_advisory_zero_loss_allowed :
    actionAllowed
      { maxAuthority := .advisory, liveExecutionAllowed := false, maxLoss := 0 }
      { authority := .advisory, requestedLoss := 0, liveExecution := false } := by
  unfold actionAllowed authorityRank
  simp

/-- Concrete witness: execute action is blocked under stage-only capability. -/
theorem witness_stage_blocks_execute :
    ¬ actionAllowed
      { maxAuthority := .stage, liveExecutionAllowed := true, maxLoss := 10 }
      { authority := .execute, requestedLoss := 1, liveExecution := true } := by
  unfold actionAllowed authorityRank
  norm_num

/-- Concrete witness: positive-loss execution is blocked by a zero-loss execute capability. -/
theorem witness_zero_loss_blocks_positive_execution :
    ¬ actionAllowed
      { maxAuthority := .execute, liveExecutionAllowed := true, maxLoss := 0 }
      { authority := .execute, requestedLoss := 1, liveExecution := true } := by
  unfold actionAllowed authorityRank
  norm_num

end AgentCapabilityBounds
end Proofs
