import Init

/-!
This file models the writer-authority portion of the research-only M6
migration lifecycle implemented by `m6_migration_lifecycle_v1.py`.  States are
constructed canonically from a closed phase.  The transition admits only the
declared forward edge, permits rollback only before authority switch, and
turns a post-switch validation failure into a terminal state with both writer
sets disabled.

Nonclaims: roots, object classification, economic-state refinement, receipt
authentication, durable publication, crash recovery, and Python/Rust runtime
refinement are outside this theorem.  This file grants no migration, release,
settlement, production, or value-moving authority.
-/

namespace Proofs
namespace GovernanceMigrationLifecycleV1

inductive Phase where
  | legacy
  | shadowReplay
  | dualCheck
  | quiesced
  | authoritySwitch
  | postSwitchValidation
  | postSwitchFailed
  | legacyDisabled
  deriving DecidableEq, Repr

inductive Step where
  | shadowReplay
  | dualCheck
  | quiesce
  | authoritySwitch
  | postSwitchValidation
  | postSwitchFailStop
  | legacyDisable
  | rollback
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  branchGeneration : Nat
  targetAuthorityActive : Bool
  legacyWritesEnabled : Bool
  targetWritesEnabled : Bool
  deriving DecidableEq, Repr

def canonicalState (phase : Phase) (branchGeneration : Nat) : State :=
  match phase with
  | .legacy | .shadowReplay | .dualCheck =>
      { phase, branchGeneration, targetAuthorityActive := false,
        legacyWritesEnabled := true, targetWritesEnabled := false }
  | .quiesced =>
      { phase, branchGeneration, targetAuthorityActive := false,
        legacyWritesEnabled := false, targetWritesEnabled := false }
  | .authoritySwitch | .postSwitchValidation | .legacyDisabled =>
      { phase, branchGeneration, targetAuthorityActive := true,
        legacyWritesEnabled := false, targetWritesEnabled := true }
  | .postSwitchFailed =>
      { phase, branchGeneration, targetAuthorityActive := true,
        legacyWritesEnabled := false, targetWritesEnabled := false }

@[simp] theorem canonical_state_phase (phase : Phase) (branch : Nat) :
    (canonicalState phase branch).phase = phase := by
  cases phase <;> rfl

@[simp] theorem canonical_state_branch (phase : Phase) (branch : Nat) :
    (canonicalState phase branch).branchGeneration = branch := by
  cases phase <;> rfl

def WellFormed (state : State) : Prop :=
  state = canonicalState state.phase state.branchGeneration

def WriterSafe (state : State) : Prop :=
  state.legacyWritesEnabled = false ∨ state.targetWritesEnabled = false

inductive RejectCode where
  | phaseMismatch
  | rollbackForbidden
  | legacyAlreadyDisabled
  deriving DecidableEq, Repr

inductive Outcome where
  | accepted (postState : State)
  | rejected (code : RejectCode) (preState : State)
  deriving DecidableEq, Repr

def Outcome.postState : Outcome → State
  | .accepted state => state
  | .rejected _ state => state

def Outcome.acceptedFlag : Outcome → Bool
  | .accepted _ => true
  | .rejected _ _ => false

def reject (state : State) (code : RejectCode) : Outcome :=
  .rejected code state

def transition (state : State) (step : Step) : Outcome :=
  match state.phase, step with
  | .legacy, .shadowReplay =>
      .accepted (canonicalState .shadowReplay state.branchGeneration)
  | .shadowReplay, .dualCheck =>
      .accepted (canonicalState .dualCheck state.branchGeneration)
  | .dualCheck, .quiesce =>
      .accepted (canonicalState .quiesced state.branchGeneration)
  | .quiesced, .authoritySwitch =>
      .accepted (canonicalState .authoritySwitch state.branchGeneration)
  | .authoritySwitch, .postSwitchValidation =>
      .accepted (canonicalState .postSwitchValidation state.branchGeneration)
  | .postSwitchValidation, .legacyDisable =>
      .accepted (canonicalState .legacyDisabled state.branchGeneration)
  | .authoritySwitch, .postSwitchFailStop =>
      .accepted (canonicalState .postSwitchFailed state.branchGeneration)
  | .postSwitchValidation, .postSwitchFailStop =>
      .accepted (canonicalState .postSwitchFailed state.branchGeneration)
  | .shadowReplay, .rollback | .dualCheck, .rollback | .quiesced, .rollback =>
      .accepted (canonicalState .legacy (state.branchGeneration + 1))
  | .legacyDisabled, .rollback => reject state .legacyAlreadyDisabled
  | .legacy, .rollback | .authoritySwitch, .rollback |
      .postSwitchValidation, .rollback | .postSwitchFailed, .rollback =>
      reject state .rollbackForbidden
  | _, _ => reject state .phaseMismatch

theorem canonical_state_well_formed (phase : Phase) (branch : Nat) :
    WellFormed (canonicalState phase branch) := by
  cases phase <;> rfl

theorem canonical_state_writer_safe (phase : Phase) (branch : Nat) :
    WriterSafe (canonicalState phase branch) := by
  cases phase <;> simp [WriterSafe, canonicalState]

theorem rejected_transition_is_exact_noop
    (state : State) (step : Step) (code : RejectCode)
    (h : transition state step = .rejected code state) :
    (transition state step).postState = state := by
  rw [h]
  rfl

theorem transition_preserves_well_formed
    (state : State) (step : Step) (h : WellFormed state) :
    WellFormed (transition state step).postState := by
  cases state with
  | mk phase branch targetActive legacyEnabled targetEnabled =>
      cases phase <;> cases step <;>
        simp_all [WellFormed, transition, reject, Outcome.postState,
          canonicalState]

theorem transition_preserves_writer_safety
    (state : State) (step : Step) (h : WellFormed state) :
    WriterSafe (transition state step).postState := by
  have postWellFormed := transition_preserves_well_formed state step h
  rw [postWellFormed]
  exact canonical_state_writer_safe
    (transition state step).postState.phase
    (transition state step).postState.branchGeneration

theorem authority_switch_selects_only_target_writer (branch : Nat) :
    transition (canonicalState .quiesced branch) .authoritySwitch =
      .accepted (canonicalState .authoritySwitch branch) := rfl

theorem post_switch_fail_stop_disables_both_writers (branch : Nat) :
    let outcome :=
      transition (canonicalState .authoritySwitch branch) .postSwitchFailStop
    outcome.postState.legacyWritesEnabled = false ∧
      outcome.postState.targetWritesEnabled = false := by
  simp [transition, Outcome.postState, canonicalState]

theorem rollback_before_switch_restores_source_and_rotates_branch (branch : Nat) :
    transition (canonicalState .quiesced branch) .rollback =
      .accepted (canonicalState .legacy (branch + 1)) := rfl

theorem rollback_after_switch_is_forbidden (branch : Nat) :
    transition (canonicalState .authoritySwitch branch) .rollback =
      .rejected .rollbackForbidden (canonicalState .authoritySwitch branch) := rfl

def happyPath (branch : Nat) : Outcome :=
  let s1 := (transition (canonicalState .legacy branch) .shadowReplay).postState
  let s2 := (transition s1 .dualCheck).postState
  let s3 := (transition s2 .quiesce).postState
  let s4 := (transition s3 .authoritySwitch).postState
  let s5 := (transition s4 .postSwitchValidation).postState
  transition s5 .legacyDisable

theorem happy_path_disables_legacy_writer (branch : Nat) :
    happyPath branch = .accepted (canonicalState .legacyDisabled branch) := rfl

theorem legacy_disabled_cannot_restore_legacy_writer (branch : Nat) :
    (transition (canonicalState .legacyDisabled branch) .rollback).postState =
      canonicalState .legacyDisabled branch := rfl

end GovernanceMigrationLifecycleV1
end Proofs
