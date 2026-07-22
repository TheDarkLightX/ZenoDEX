import Mathlib

/-!
# zUSD Oracle authority freshness

This module models the distinct epoch authorities used by zUSD Oracle commit
and liquidation admission. Commit reads the pending observation epoch.
Liquidation reads the last finalized observation epoch and also requires the
pending and finalized prices to agree. Both transitions require a canonical
state whose recorded Oracle epochs are not future-dated.

An authenticated fresh pending report can therefore restore finalization after
the previous finalized observation becomes stale. A successful commit records
the pending observation epoch and restores the finalized freshness window.

The model covers epoch-domain validity, freshness arithmetic, authority
selection, pending/finalized agreement, and the commit epoch update. Oracle
authentication, price validity, collateralization, state encoding, and atomic
shell publication remain separate obligations.
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

structure AuthorityState where
  pendingObservedEpoch : Nat
  finalizedObservedEpoch : Nat
  nowEpoch : Nat
  maxStalenessEpochs : Nat
  pendingMatchesFinalized : Bool
  deriving DecidableEq, Repr

def AuthorityState.DomainValid (state : AuthorityState) : Prop :=
  state.pendingObservedEpoch ≤ state.nowEpoch ∧
    state.finalizedObservedEpoch ≤ state.nowEpoch

def AuthorityState.pendingWindow (state : AuthorityState) : Window :=
  {
    observedEpoch := state.pendingObservedEpoch
    nowEpoch := state.nowEpoch
    maxStalenessEpochs := state.maxStalenessEpochs
  }

def AuthorityState.finalizedWindow (state : AuthorityState) : Window :=
  {
    observedEpoch := state.finalizedObservedEpoch
    nowEpoch := state.nowEpoch
    maxStalenessEpochs := state.maxStalenessEpochs
  }

inductive Operation where
  | commit
  | liquidate
  deriving DecidableEq, Repr

def Admitted : Operation → AuthorityState → Prop
  | .commit, state => state.DomainValid ∧ state.pendingWindow.Fresh
  | .liquidate, state =>
      state.DomainValid ∧
        state.pendingMatchesFinalized = true ∧ state.finalizedWindow.Fresh

instance (operation : Operation) (state : AuthorityState) :
    Decidable (Admitted operation state) := by
  cases operation <;>
    unfold Admitted AuthorityState.DomainValid AuthorityState.pendingWindow
      AuthorityState.finalizedWindow Window.Fresh <;>
    infer_instance

def admittedBool (operation : Operation) (state : AuthorityState) : Bool :=
  decide (Admitted operation state)

theorem admitted_bool_eq_true_iff
    (operation : Operation)
    (state : AuthorityState) :
    admittedBool operation state = true ↔ Admitted operation state := by
  simp [admittedBool]

theorem commit_admission_implies_pending_not_future
    (state : AuthorityState)
    (hAdmitted : Admitted .commit state) :
    state.pendingObservedEpoch ≤ state.nowEpoch := by
  exact hAdmitted.2.1

theorem commit_admission_implies_pending_age_bounded
    (state : AuthorityState)
    (hAdmitted : Admitted .commit state) :
    state.nowEpoch - state.pendingObservedEpoch ≤ state.maxStalenessEpochs := by
  exact hAdmitted.2.2

theorem fresh_pending_admits_commit_after_finalized_staleness
    (state : AuthorityState)
    (hPendingNotFuture : state.pendingObservedEpoch ≤ state.nowEpoch)
    (hFinalizedNotFuture : state.finalizedObservedEpoch ≤ state.nowEpoch)
    (hPendingFresh :
      state.nowEpoch - state.pendingObservedEpoch ≤ state.maxStalenessEpochs)
    (_hFinalizedStale :
      state.maxStalenessEpochs <
        state.nowEpoch - state.finalizedObservedEpoch) :
    Admitted .commit state := by
  exact
    ⟨⟨hPendingNotFuture, hFinalizedNotFuture⟩,
      hPendingNotFuture, hPendingFresh⟩

theorem liquidation_admission_implies_pending_matches_finalized
    (state : AuthorityState)
    (hAdmitted : Admitted .liquidate state) :
    state.pendingMatchesFinalized = true := by
  exact hAdmitted.2.1

theorem liquidation_admission_implies_finalized_not_future
    (state : AuthorityState)
    (hAdmitted : Admitted .liquidate state) :
    state.finalizedObservedEpoch ≤ state.nowEpoch := by
  exact hAdmitted.2.2.1

theorem liquidation_admission_implies_finalized_age_bounded
    (state : AuthorityState)
    (hAdmitted : Admitted .liquidate state) :
    state.nowEpoch - state.finalizedObservedEpoch ≤ state.maxStalenessEpochs := by
  exact hAdmitted.2.2.2

def applyCommit (state : AuthorityState) : AuthorityState :=
  {
    state with
    finalizedObservedEpoch := state.pendingObservedEpoch
    pendingMatchesFinalized := true
  }

def commit (state : AuthorityState) : Option AuthorityState :=
  if Admitted .commit state then some (applyCommit state) else none

theorem successful_commit_restores_finalized_freshness
    (state postState : AuthorityState)
    (hCommit : commit state = some postState) :
    postState.finalizedWindow.Fresh := by
  unfold commit at hCommit
  split at hCommit
  · rename_i hAdmitted
    cases hCommit
    simpa [
      applyCommit,
      AuthorityState.finalizedWindow,
      AuthorityState.pendingWindow
    ] using hAdmitted.2
  · simp at hCommit

theorem commit_records_pending_observation_epoch
    (state postState : AuthorityState)
    (hCommit : commit state = some postState) :
    postState.finalizedObservedEpoch = state.pendingObservedEpoch := by
  unfold commit at hCommit
  split at hCommit
  · cases hCommit
    rfl
  · simp at hCommit

theorem commit_does_not_restamp_later_commit_epoch
    (state postState : AuthorityState)
    (hCommit : commit state = some postState)
    (hObservedEarlier : state.pendingObservedEpoch < state.nowEpoch) :
    postState.finalizedObservedEpoch ≠ state.nowEpoch := by
  rw [commit_records_pending_observation_epoch state postState hCommit]
  exact Nat.ne_of_lt hObservedEarlier

def boolDigit (value : Bool) : String :=
  if value then "1" else "0"

def admissionRow
    (pendingObservedEpoch finalizedObservedEpoch nowEpoch maxStalenessEpochs : Nat)
    (pendingMatchesFinalized : Bool) : String :=
  let state : AuthorityState :=
    {
      pendingObservedEpoch := pendingObservedEpoch
      finalizedObservedEpoch := finalizedObservedEpoch
      nowEpoch := nowEpoch
      maxStalenessEpochs := maxStalenessEpochs
      pendingMatchesFinalized := pendingMatchesFinalized
    }
  String.intercalate
    ":"
    [
      toString pendingObservedEpoch,
      toString finalizedObservedEpoch,
      toString nowEpoch,
      toString maxStalenessEpochs,
      boolDigit pendingMatchesFinalized,
      boolDigit (admittedBool .commit state),
      boolDigit (admittedBool .liquidate state),
      toString (applyCommit state).finalizedObservedEpoch
    ]

def boundedAdmissionRows (bound : Nat) : List String :=
  (List.range bound).flatMap fun pendingObservedEpoch =>
    (List.range bound).flatMap fun finalizedObservedEpoch =>
      (List.range bound).flatMap fun nowEpoch =>
        (List.range bound).flatMap fun maxStalenessEpochs =>
          [false, true].map fun pendingMatchesFinalized =>
            admissionRow pendingObservedEpoch finalizedObservedEpoch nowEpoch
              maxStalenessEpochs pendingMatchesFinalized

def boundedAdmissionCSV (bound : Nat) : String :=
  String.intercalate "," (boundedAdmissionRows bound)

end ZenoDEX.ZUSDPendingObservationFreshness
