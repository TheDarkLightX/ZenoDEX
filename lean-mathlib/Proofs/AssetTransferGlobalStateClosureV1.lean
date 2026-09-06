import Proofs.AssetTransferGlobalSuccessorV1

/-!
# State closure of the restricted custody-transfer global construction

The continuation state uses the actual custody-complete module state and the
actual global step. It carries policies and economic state together, including
the new global height and replay registry. An accepted transfer preserves the
nine initial-state obligations needed by the next transfer. A rejected leaf
retains the exact initial state.

State preservation supplies no next-command authority. New occurrence context,
bounded next height, replay freshness, root bindings, command bounds and fee
eligibility remain explicit input requirements. In particular a state at maximum
height can satisfy StateInvariant while having no admitted height successor.

This is a mathematical composition boundary. It implements no runtime admission
checker and proves no encoding, hashing, authenticated snapshot, receipt or
publication claim. The inherited restricted lane/reserve/terminal/outbox scope
is preserved, and the previous proof statements and runtime semantics are unchanged.
-/

set_option warningAsError true

namespace Proofs
namespace AssetTransferGlobalStateClosureV1

open GlobalSettlementCoreV2

namespace X
export AssetTransferGlobalSuccessorV1
  (Input Admitted result result_post result_post_frame result_reserves result_terminal
   successor step step_accepted step_rejected_exact successor_verified SingleEnabledLane
   FeeEligible pre)
end X

namespace K
export AssetTransferPolicySelectionV1
  (State Input StateAdmitted step reject lift rejected_step_noop step_preserves_state_admitted)
end K

namespace G
export GlobalEconomicStateRefinementV2
  (GlobalState StateQuantitiesAdmitted OwnedMatchesSupply ClaimantLiabilitiesBacked
   OccurrenceContextMatches Verified)
end G

namespace T
export AssetTransferRefinementV1 (CommandWellFormed RejectCode)
end T

/-- Carry the actual module result and global successor in one existing state value. -/
def continuedState (input : X.Input) : K.State :=
  { (X.result input).post with economic := (X.step input).post }

/-- The inherited state obligations, separate from each new command's requirements. -/
structure StateInvariant (value : K.State) : Prop where
  state : K.StateAdmitted value
  quantities : G.StateQuantitiesAdmitted value.economic
  owned : G.OwnedMatchesSupply value.economic
  backed : G.ClaimantLiabilitiesBacked value.economic
  reservesEmpty : value.economic.reserves = []
  terminalEmpty : value.economic.terminalObligations = []
  outboxEmpty : value.economic.outbox = []
  singleLane : X.SingleEnabledLane value.economic
  release : value.economic.laneReleaseIds .assetTransfer = value.moduleReleaseId

/-- Fresh facts for the next input. No desired output property is assumed. -/
structure ContinuationRequirements (carried : K.State) (next : X.Input) : Prop where
  pre : next.transfer.pre = carried
  context : G.OccurrenceContextMatches carried.economic next.occurrence
  height : next.occurrence.height = carried.economic.height + 1
  heightFits : FitsU64 (carried.economic.height + 1)
  freshReplay : carried.economic.replayState next.occurrence.replayId = none
  freshOccurrence : ∀ replayId prior,
    carried.economic.replayState replayId = some prior → prior ≠ next.occurrence.occurrenceId
  preLaneRoot : next.privatePortPreRoot = carried.economic.laneRoots .assetTransfer
  laneRootChanged : next.postLaneRoot ≠ carried.economic.laneRoots .assetTransfer
  commandWellFormed : T.CommandWellFormed next.transfer.command
  feeEligible : X.FeeEligible next

private theorem result_static_frame (input : X.Input) :
    (X.result input).post.moduleReleaseId = input.transfer.pre.moduleReleaseId ∧
    (X.result input).post.policies = input.transfer.pre.policies := by
  rw [X.result_post]
  unfold K.step
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

/-- Module release and policy rows come from the actual module transition. -/
theorem continuedState_static_frame (input : X.Input) :
    (continuedState input).moduleReleaseId = input.transfer.pre.moduleReleaseId ∧
    (continuedState input).policies = input.transfer.pre.policies :=
  result_static_frame input

theorem continuedState_accepted {input : X.Input}
    (accepted : (K.step input.transfer).verdict = .accepted) :
    continuedState input = { (X.result input).post with economic := X.successor input } := by
  simp only [continuedState, X.step_accepted accepted]

theorem continuedState_rejected {input : X.Input} {code : T.RejectCode}
    (rejected : (K.step input.transfer).verdict = .rejected code) :
    continuedState input = input.transfer.pre := by
  unfold continuedState
  rw [X.step_rejected_exact rejected, X.result_post, (K.rejected_step_noop rejected).1]
  rfl

theorem invariant_of_admitted {input : X.Input} (admitted : X.Admitted input) :
    StateInvariant input.transfer.pre :=
  ⟨admitted.state, admitted.quantities, admitted.owned, admitted.backed,
   admitted.reservesEmpty, admitted.terminalEmpty, admitted.outboxEmpty,
   admitted.singleLane, admitted.release⟩

/-- Acceptance carries newly constructed global metadata; rejection carries the exact pre. -/
theorem continuedState_invariant {input : X.Input} (admitted : X.Admitted input) :
    StateInvariant (continuedState input) := by
  cases verdict : (K.step input.transfer).verdict with
  | rejected code =>
      rw [continuedState_rejected verdict]
      exact invariant_of_admitted admitted
  | accepted =>
      rw [continuedState_accepted verdict]
      have verified := X.successor_verified admitted verdict
      have moduleAdmitted := K.step_preserves_state_admitted admitted.state
      rw [← X.result_post input] at moduleAdmitted
      have frame := X.result_post_frame input
      refine ⟨?_, verified.postQuantities, verified.ownedSupplyPost,
        verified.liabilitiesPost, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [K.StateAdmitted, X.successor] using moduleAdmitted
      · simpa only [X.successor, X.result_reserves] using admitted.reservesEmpty
      · simpa only [X.successor, X.result_terminal] using admitted.terminalEmpty
      · change (X.result input).post.economic.outbox = []
        rw [congrArg (fun s : G.GlobalState => s.outbox) frame]
        exact admitted.outboxEmpty
      · change X.SingleEnabledLane (X.successor input)
        unfold X.SingleEnabledLane
        change ∀ lane, (X.result input).post.economic.laneEnabled lane = true ↔
          lane = .assetTransfer
        rw [congrArg (fun s : G.GlobalState => s.laneEnabled) frame]
        exact admitted.singleLane
      · change (X.result input).post.economic.laneReleaseIds .assetTransfer =
          (X.result input).post.moduleReleaseId
        rw [congrArg (fun s : G.GlobalState => s.laneReleaseIds) frame,
          (result_static_frame input).1]
        exact admitted.release

/-- Combine inherited state safety with the next input's independently supplied guards. -/
theorem admitted_of_invariant {carried : K.State} {next : X.Input}
    (invariant : StateInvariant carried)
    (requirements : ContinuationRequirements carried next) : X.Admitted next where
  state := by simpa only [requirements.pre] using invariant.state
  quantities := by simpa only [X.pre, requirements.pre] using invariant.quantities
  owned := by simpa only [X.pre, requirements.pre] using invariant.owned
  backed := by simpa only [X.pre, requirements.pre] using invariant.backed
  reservesEmpty := by simpa only [X.pre, requirements.pre] using invariant.reservesEmpty
  terminalEmpty := by simpa only [X.pre, requirements.pre] using invariant.terminalEmpty
  outboxEmpty := by simpa only [X.pre, requirements.pre] using invariant.outboxEmpty
  singleLane := by simpa only [X.pre, requirements.pre] using invariant.singleLane
  release := by simpa only [X.pre, requirements.pre] using invariant.release
  context := by simpa only [X.pre, requirements.pre] using requirements.context
  height := by simpa only [X.pre, requirements.pre] using requirements.height
  heightFits := by simpa only [X.pre, requirements.pre] using requirements.heightFits
  freshReplay := by simpa only [X.pre, requirements.pre] using requirements.freshReplay
  freshOccurrence := by simpa only [X.pre, requirements.pre] using requirements.freshOccurrence
  preLaneRoot := by simpa only [X.pre, requirements.pre] using requirements.preLaneRoot
  laneRootChanged := by simpa only [X.pre, requirements.pre] using requirements.laneRootChanged
  commandWellFormed := requirements.commandWellFormed
  feeEligible := requirements.feeEligible

theorem continuation_admitted {input next : X.Input} (admitted : X.Admitted input)
    (requirements : ContinuationRequirements (continuedState input) next) : X.Admitted next :=
  admitted_of_invariant (continuedState_invariant admitted) requirements

theorem continuation_verified {input next : X.Input} (admitted : X.Admitted input)
    (requirements : ContinuationRequirements (continuedState input) next)
    (accepted : (K.step next.transfer).verdict = .accepted) :
    G.Verified (X.pre next) (X.result next).plan ⟨[]⟩ ⟨[]⟩ [next.occurrence]
      (X.successor next) :=
  X.successor_verified (continuation_admitted admitted requirements) accepted

theorem continuation_preserves_invariant {input next : X.Input} (admitted : X.Admitted input)
    (requirements : ContinuationRequirements (continuedState input) next) :
    StateInvariant (continuedState next) :=
  continuedState_invariant (continuation_admitted admitted requirements)

end AssetTransferGlobalStateClosureV1
end Proofs
