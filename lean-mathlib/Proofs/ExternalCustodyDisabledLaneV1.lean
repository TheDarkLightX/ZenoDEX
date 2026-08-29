import Init

/-!
The current M6 external lane has an empty destination registry.  This file
models that exact disabled profile: all nine registered command forms produce
the same typed disabled rejection, preserve the state exactly, and emit no
effects.

Nonclaims: this proves no external adapter, chain finality, lock, burn,
release, mint, refund, outbox delivery, receipt, runtime refinement, mounted
release, or value-moving authority.  Enabling any destination requires a new
profile and separate transition, terminal-lifecycle, and refinement proofs.
-/

namespace Proofs
namespace ExternalCustodyDisabledLaneV1

inductive ExternalCommand where
  | registeredExternalLock
  | registeredExternalBurn
  | registeredExternalRelease
  | registeredExternalMint
  | externalFinality
  | externalTimeout
  | externalRefund
  | outboxAcknowledgment
  | destinationIdempotency
  deriving DecidableEq, Repr

def allExternalCommands : List ExternalCommand :=
  [ .registeredExternalLock, .registeredExternalBurn,
    .registeredExternalRelease, .registeredExternalMint, .externalFinality,
    .externalTimeout, .externalRefund, .outboxAcknowledgment,
    .destinationIdempotency ]

theorem all_external_commands_length : allExternalCommands.length = 9 := rfl

theorem all_external_commands_complete (command : ExternalCommand) :
    command ∈ allExternalCommands := by
  cases command <;> decide

structure DisabledState where
  registryEntries : List String := []
  pendingExternalObligations : List String := []
  outboxAcknowledgments : List String := []
  registryEmpty : registryEntries = [] := by rfl
  pendingEmpty : pendingExternalObligations = [] := by rfl
  acknowledgmentsEmpty : outboxAcknowledgments = [] := by rfl
  deriving Repr

inductive RejectCode where
  | disabledFeature
  deriving DecidableEq, Repr

structure Rejection where
  code : RejectCode
  preState : DisabledState
  postState : DisabledState
  effects : List String

def transition (preState : DisabledState) (_command : ExternalCommand) : Rejection :=
  { code := .disabledFeature, preState := preState, postState := preState,
    effects := [] }

theorem every_command_rejects_disabled
    (state : DisabledState) (command : ExternalCommand) :
    (transition state command).code = .disabledFeature := rfl

theorem every_rejection_preserves_exact_state
    (state : DisabledState) (command : ExternalCommand) :
    (transition state command).postState =
      (transition state command).preState := rfl

theorem every_rejection_has_empty_effects
    (state : DisabledState) (command : ExternalCommand) :
    (transition state command).effects = [] := rfl

theorem disabled_state_has_no_registered_destination (state : DisabledState) :
    state.registryEntries = [] := state.registryEmpty

theorem disabled_state_has_no_pending_external_obligation (state : DisabledState) :
    state.pendingExternalObligations = [] := state.pendingEmpty

theorem disabled_state_has_no_outbox_acknowledgment (state : DisabledState) :
    state.outboxAcknowledgments = [] := state.acknowledgmentsEmpty

end ExternalCustodyDisabledLaneV1
end Proofs
