import Init

/-!
The current PROOF_REWARDS lane has no selected UP-09 funding, claimant,
nullifier, payout, or terminal policy.  This model therefore has one empty
state and a total policy rejection for each of the six normative capabilities.

Nonclaims: this proves no reward eligibility, reserve funding, proof receipt,
claimant identity, nullifier construction, payout, terminal policy, runtime
refinement, mounted release, or value-moving authority.
-/

namespace Proofs
namespace ProofRewardsPolicyBlockedLaneV1

inductive ProofRewardCapability where
  | rewardReserve
  | verifiedResultBinding
  | claimantBinding
  | claimNullifier
  | rewardPayout
  | taskTerminalState
  deriving DecidableEq, Repr

def allCapabilities : List ProofRewardCapability :=
  [ .rewardReserve, .verifiedResultBinding, .claimantBinding,
    .claimNullifier, .rewardPayout, .taskTerminalState ]

theorem all_capabilities_length : allCapabilities.length = 6 := rfl

theorem all_capabilities_complete (capability : ProofRewardCapability) :
    capability ∈ allCapabilities := by
  cases capability <;> decide

structure PolicyBlockedState where
  rewardReserves : List String := []
  tasks : List String := []
  claimNullifiers : List String := []
  terminalObligations : List String := []
  reservesEmpty : rewardReserves = [] := by rfl
  tasksEmpty : tasks = [] := by rfl
  nullifiersEmpty : claimNullifiers = [] := by rfl
  obligationsEmpty : terminalObligations = [] := by rfl
  deriving Repr

inductive RejectCode where
  | policyReject
  deriving DecidableEq, Repr

structure Rejection where
  code : RejectCode
  preState : PolicyBlockedState
  postState : PolicyBlockedState
  effects : List String

def transition
    (preState : PolicyBlockedState)
    (_capability : ProofRewardCapability) : Rejection :=
  { code := .policyReject, preState := preState, postState := preState,
    effects := [] }

theorem every_capability_rejects_policy
    (state : PolicyBlockedState) (capability : ProofRewardCapability) :
    (transition state capability).code = .policyReject := rfl

theorem rejection_preserves_exact_state
    (state : PolicyBlockedState) (capability : ProofRewardCapability) :
    (transition state capability).postState =
      (transition state capability).preState := rfl

theorem rejection_has_no_effects
    (state : PolicyBlockedState) (capability : ProofRewardCapability) :
    (transition state capability).effects = [] := rfl

theorem blocked_state_has_no_reserve (state : PolicyBlockedState) :
    state.rewardReserves = [] := state.reservesEmpty

theorem blocked_state_has_no_task (state : PolicyBlockedState) :
    state.tasks = [] := state.tasksEmpty

theorem blocked_state_has_no_nullifier (state : PolicyBlockedState) :
    state.claimNullifiers = [] := state.nullifiersEmpty

theorem blocked_state_has_no_terminal_obligation (state : PolicyBlockedState) :
    state.terminalObligations = [] := state.obligationsEmpty

end ProofRewardsPolicyBlockedLaneV1
end Proofs
