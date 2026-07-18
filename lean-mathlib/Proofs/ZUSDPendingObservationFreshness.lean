import Mathlib

/-!
# zUSD pending-observation freshness

This module models the epoch-only kernel shared by zUSD oracle commit and
liquidation admission.  Admission requires an observation from the present or
past whose age is within the configured maximum.  An accepted commit preserves
the observation epoch as the active oracle epoch.

The model covers epoch ordering, age arithmetic, and the commit epoch update.
Oracle authentication, price validity, collateralization, state encoding, and
atomic shell publication remain separate obligations.
-/

namespace ZenoDEX.ZUSDPendingObservationFreshness

structure Window where
  observedEpoch : Nat
  nowEpoch : Nat
  maxStalenessEpochs : Nat
  deriving DecidableEq, Repr

def Window.Fresh (window : Window) : Prop :=
  window.observedEpoch ≤ window.nowEpoch ∧
    window.nowEpoch - window.observedEpoch ≤ window.maxStalenessEpochs

inductive Operation where
  | commit
  | liquidate
  deriving DecidableEq, Repr

def Admitted : Operation → Window → Prop
  | .commit, window => window.Fresh
  | .liquidate, window => window.Fresh

instance (operation : Operation) (window : Window) :
    Decidable (Admitted operation window) := by
  cases operation <;> unfold Admitted Window.Fresh <;> infer_instance

def admittedBool (operation : Operation) (window : Window) : Bool :=
  decide (Admitted operation window)

theorem admitted_bool_eq_true_iff
    (operation : Operation)
    (window : Window) :
    admittedBool operation window = true ↔ Admitted operation window := by
  simp [admittedBool]

theorem commit_admission_implies_observed_not_future
    (window : Window)
    (hAdmitted : Admitted .commit window) :
    window.observedEpoch ≤ window.nowEpoch := by
  exact hAdmitted.1

theorem commit_admission_implies_age_bounded
    (window : Window)
    (hAdmitted : Admitted .commit window) :
    window.nowEpoch - window.observedEpoch ≤ window.maxStalenessEpochs := by
  exact hAdmitted.2

theorem liquidation_admission_implies_observed_not_future
    (window : Window)
    (hAdmitted : Admitted .liquidate window) :
    window.observedEpoch ≤ window.nowEpoch := by
  exact hAdmitted.1

theorem liquidation_admission_implies_age_bounded
    (window : Window)
    (hAdmitted : Admitted .liquidate window) :
    window.nowEpoch - window.observedEpoch ≤ window.maxStalenessEpochs := by
  exact hAdmitted.2

structure EpochState where
  nowEpoch : Nat
  pendingObservedEpoch : Nat
  lastCommittedObservedEpoch : Nat
  deriving DecidableEq, Repr

def EpochState.pendingWindow
    (state : EpochState)
    (maxStalenessEpochs : Nat) : Window :=
  {
    observedEpoch := state.pendingObservedEpoch
    nowEpoch := state.nowEpoch
    maxStalenessEpochs := maxStalenessEpochs
  }

def applyCommit (state : EpochState) : EpochState :=
  { state with lastCommittedObservedEpoch := state.pendingObservedEpoch }

def commit
    (state : EpochState)
    (maxStalenessEpochs : Nat) : Option EpochState :=
  if Admitted .commit (state.pendingWindow maxStalenessEpochs) then
    some (applyCommit state)
  else
    none

theorem commit_records_observation_epoch
    (state postState : EpochState)
    (maxStalenessEpochs : Nat)
    (hCommit : commit state maxStalenessEpochs = some postState) :
    postState.lastCommittedObservedEpoch = state.pendingObservedEpoch := by
  unfold commit at hCommit
  split at hCommit
  · cases hCommit
    rfl
  · simp at hCommit

theorem commit_does_not_restamp_later_commit_epoch
    (state postState : EpochState)
    (maxStalenessEpochs : Nat)
    (hCommit : commit state maxStalenessEpochs = some postState)
    (hObservedEarlier : state.pendingObservedEpoch < state.nowEpoch) :
    postState.lastCommittedObservedEpoch ≠ state.nowEpoch := by
  rw [commit_records_observation_epoch state postState maxStalenessEpochs hCommit]
  exact Nat.ne_of_lt hObservedEarlier

def boolDigit (value : Bool) : String :=
  if value then "1" else "0"

def admissionRow
    (observedEpoch nowEpoch maxStalenessEpochs : Nat) : String :=
  let window : Window :=
    {
      observedEpoch := observedEpoch
      nowEpoch := nowEpoch
      maxStalenessEpochs := maxStalenessEpochs
    }
  let state : EpochState :=
    {
      nowEpoch := nowEpoch
      pendingObservedEpoch := observedEpoch
      lastCommittedObservedEpoch := 0
    }
  String.intercalate
    ":"
    [
      toString observedEpoch,
      toString nowEpoch,
      toString maxStalenessEpochs,
      boolDigit (admittedBool .commit window),
      boolDigit (admittedBool .liquidate window),
      toString (applyCommit state).lastCommittedObservedEpoch
    ]

def boundedAdmissionRows (bound : Nat) : List String :=
  (List.range bound).flatMap fun observedEpoch =>
    (List.range bound).flatMap fun nowEpoch =>
      (List.range bound).map fun maxStalenessEpochs =>
        admissionRow observedEpoch nowEpoch maxStalenessEpochs

def boundedAdmissionCSV (bound : Nat) : String :=
  String.intercalate "," (boundedAdmissionRows bound)

end ZenoDEX.ZUSDPendingObservationFreshness
