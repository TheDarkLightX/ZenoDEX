import Proofs.LaneCapabilityRegistryV1

/-!
The current profile has a total fail-closed outcome for every capability in
the twelve-lane registry. Cross-lane state/command pairs reject as invalid
context. External-custody capabilities are disabled. Every other capability
is policy-blocked until governed economics and release bindings exist.

Nonclaims: this proves only the abstract current-profile rejection function.
It does not implement any rejected feature, validate a concrete state root,
establish Python or Rust refinement, authenticate a command, verify a receipt,
mount a release, or authorize value movement.
-/

namespace Proofs
namespace CurrentProfileLaneGateV1

open LaneCapabilityRegistryV1

structure State where
  lane : LaneId
  stateRoot : String
  deriving Repr

inductive RejectCode where
  | disabledFeature
  | invalidContext
  | policyReject
  deriving DecidableEq, Repr

structure Rejection where
  code : RejectCode
  preState : State
  postState : State
  effects : List String
  deriving Repr

def rejectionCode (stateLane commandLane : LaneId) : RejectCode :=
  if stateLane != commandLane then .invalidContext
  else if commandLane = .externalCustody then .disabledFeature
  else .policyReject

def transition (state : State) (capability : Capability) : Rejection :=
  { code := rejectionCode state.lane capability.lane
    preState := state
    postState := state
    effects := [] }

theorem every_capability_rejects (state : State) (capability : Capability) :
    ∃ rejection, transition state capability = rejection := by
  exact ⟨transition state capability, rfl⟩

theorem rejection_preserves_exact_state
    (state : State) (capability : Capability) :
    (transition state capability).postState =
      (transition state capability).preState := rfl

theorem rejection_has_no_effects (state : State) (capability : Capability) :
    (transition state capability).effects = [] := rfl

theorem external_capabilities_are_disabled
    (state : State) (capability : Capability)
    (stateExternal : state.lane = .externalCustody)
    (commandExternal : capability.lane = .externalCustody) :
    (transition state capability).code = .disabledFeature := by
  simp [transition, rejectionCode, stateExternal, commandExternal]

theorem non_external_capabilities_are_policy_blocked
    (state : State) (capability : Capability)
    (lanesMatch : state.lane = capability.lane)
    (notExternal : capability.lane ≠ .externalCustody) :
    (transition state capability).code = .policyReject := by
  simp [transition, rejectionCode, lanesMatch, notExternal]

end CurrentProfileLaneGateV1
end Proofs
