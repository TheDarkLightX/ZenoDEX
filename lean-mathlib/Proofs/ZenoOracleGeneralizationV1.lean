/-!
# ZenoOracle Generalization V1

Reusable Lean anchors for the ZenoOracle first-shell math lane.

This file promotes the Aristotle generalization packet from bounded examples
to small structural theorems for deviation policy, freshness/sync, reporter
economics, O5 independence, and typed runtime authorization boundaries.
-/

namespace Proofs
namespace ZenoOracleGeneralizationV1

def LowerDeviationBps (lo mid bps : Nat) : Nat :=
  ((mid - lo) * bps) / mid

def UpperDeviationBps (mid hi bps : Nat) : Nat :=
  ((hi - mid) * bps) / mid

def MaxDeviationBpsSorted (lo mid hi bps : Nat) : Nat :=
  max (LowerDeviationBps lo mid bps) (UpperDeviationBps mid hi bps)

def DivergenceBps (left right bps : Nat) : Nat :=
  if left <= right then
    ((right - left) * bps) / right
  else
    ((left - right) * bps) / right

def EpochLag (left right : Nat) : Nat :=
  if left <= right then right - left else left - right

def FreshAt (now observed maxLag : Nat) : Prop :=
  observed <= now ∧ now - observed <= maxLag

def BudgetStepOK (before reward after : Nat) : Prop :=
  after + reward = before

def TwoStepBudgetOK (before reward₁ middle reward₂ after : Nat) : Prop :=
  BudgetStepOK before reward₁ middle ∧ BudgetStepOK middle reward₂ after

structure O5Witness where
  primaryO5Claim : Prop
  distinctVerifiers : Prop
  distinctProofKinds : Prop
  sameInputRoot : Prop
  sameOutputRoot : Prop
  dagClosed : Prop

def O5WitnessOK (w : O5Witness) : Prop :=
  w.primaryO5Claim ∧
    w.distinctVerifiers ∧
      w.distinctProofKinds ∧
        w.sameInputRoot ∧
          w.sameOutputRoot ∧
            w.dagClosed

structure TypedAuthorization where
  consumerModuleMatch : Prop
  actionKindMatch : Prop
  actionIdMatch : Prop
  actionFactsHashMatch : Prop
  preStateHashMatch : Prop
  profileMatch : Prop
  queryMatch : Prop
  valueMatch : Prop
  evidenceAtLeastO3 : Prop
  notExpired : Prop
  receiptGraphClosed : Prop
  economicEnvelopeBound : Prop

def TypedAuthorizationOK (a : TypedAuthorization) : Prop :=
  a.consumerModuleMatch ∧
    a.actionKindMatch ∧
      a.actionIdMatch ∧
        a.actionFactsHashMatch ∧
          a.preStateHashMatch ∧
            a.profileMatch ∧
              a.queryMatch ∧
                a.valueMatch ∧
                  a.evidenceAtLeastO3 ∧
                    a.notExpired ∧
                      a.receiptGraphClosed ∧
                        a.economicEnvelopeBound

def CriticalOracleRuntimeOK (auth : TypedAuthorization) (fresh : Prop) (o5 : O5Witness) : Prop :=
  TypedAuthorizationOK auth ∧ fresh ∧ O5WitnessOK o5

theorem max_deviation_le_iff_components
    (lo mid hi bps cap : Nat) :
    MaxDeviationBpsSorted lo mid hi bps <= cap ↔
      LowerDeviationBps lo mid bps <= cap ∧ UpperDeviationBps mid hi bps <= cap := by
  exact Nat.max_le

theorem max_deviation_exceeds_if_lower_exceeds
    {lo mid hi bps cap : Nat}
    (h : cap < LowerDeviationBps lo mid bps) :
    cap < MaxDeviationBpsSorted lo mid hi bps := by
  exact Nat.lt_of_lt_of_le h (Nat.le_max_left ..)

theorem max_deviation_exceeds_if_upper_exceeds
    {lo mid hi bps cap : Nat}
    (h : cap < UpperDeviationBps mid hi bps) :
    cap < MaxDeviationBpsSorted lo mid hi bps := by
  exact Nat.lt_of_lt_of_le h (Nat.le_max_right ..)

theorem max_deviation_zero_when_all_equal
    (mid bps : Nat) :
    MaxDeviationBpsSorted mid mid mid bps = 0 := by
  simp [MaxDeviationBpsSorted, LowerDeviationBps, UpperDeviationBps, Nat.sub_self]

theorem divergence_self_zero
    (x bps : Nat) :
    DivergenceBps x x bps = 0 := by
  simp [DivergenceBps, Nat.sub_self]

theorem epoch_lag_symmetric
    (left right : Nat) :
    EpochLag left right = EpochLag right left := by
  unfold EpochLag
  split <;> split <;> omega

theorem epoch_lag_zero_iff_eq
    (left right : Nat) :
    EpochLag left right = 0 ↔ left = right := by
  unfold EpochLag
  constructor
  · intro h
    split at h <;> omega
  · intro h
    subst h
    simp

theorem stale_epoch_rejected
    {now observed maxLag : Nat}
    (_hObserved : observed <= now)
    (hStale : maxLag < now - observed) :
    ¬ FreshAt now observed maxLag := by
  intro h
  exact Nat.not_lt_of_ge h.2 hStale

theorem fresh_at_monotone_max_lag
    {now observed smallLag largeLag : Nat}
    (hFresh : FreshAt now observed smallLag)
    (hLe : smallLag <= largeLag) :
    FreshAt now observed largeLag := by
  exact ⟨hFresh.1, Nat.le_trans hFresh.2 hLe⟩

theorem budget_step_reward_le_before
    {before reward after : Nat}
    (h : BudgetStepOK before reward after) :
    reward <= before := by
  unfold BudgetStepOK at h
  omega

theorem budget_step_after_le_before
    {before reward after : Nat}
    (h : BudgetStepOK before reward after) :
    after <= before := by
  unfold BudgetStepOK at h
  omega

theorem positive_reward_strictly_decreases_pool
    {before reward after : Nat}
    (h : BudgetStepOK before reward after)
    (hPositive : 0 < reward) :
    after < before := by
  unfold BudgetStepOK at h
  omega

theorem two_step_budget_conservation
    {before reward₁ middle reward₂ after : Nat}
    (h : TwoStepBudgetOK before reward₁ middle reward₂ after) :
    after + reward₂ + reward₁ = before := by
  obtain ⟨h1, h2⟩ := h
  unfold BudgetStepOK at h1 h2
  omega

theorem o5_witness_ok_requires_distinct_verifiers
    {w : O5Witness}
    (h : O5WitnessOK w) :
    w.distinctVerifiers := by
  exact h.2.1

theorem o5_witness_rejects_missing_dag_closure
    {w : O5Witness}
    (hMissing : ¬ w.dagClosed) :
    ¬ O5WitnessOK w := by
  exact fun h => hMissing h.2.2.2.2.2

theorem typed_authorization_ok_requires_action_binding
    {a : TypedAuthorization}
    (h : TypedAuthorizationOK a) :
    a.actionIdMatch ∧ a.actionFactsHashMatch ∧ a.preStateHashMatch := by
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem typed_authorization_rejects_receipt_borrowing
    {a : TypedAuthorization}
    (hBorrowed : ¬ a.actionIdMatch ∨ ¬ a.preStateHashMatch) :
    ¬ TypedAuthorizationOK a := by
  intro h
  cases hBorrowed with
  | inl hNot => exact hNot h.2.2.1
  | inr hNot => exact hNot h.2.2.2.2.1

theorem critical_runtime_ok_requires_all_boundaries
    {auth : TypedAuthorization}
    {fresh : Prop}
    {o5 : O5Witness}
    (h : CriticalOracleRuntimeOK auth fresh o5) :
    TypedAuthorizationOK auth ∧ fresh ∧ O5WitnessOK o5 := by
  exact h

theorem critical_runtime_rejects_stale_oracle
    {auth : TypedAuthorization}
    {fresh : Prop}
    {o5 : O5Witness}
    (hStale : ¬ fresh) :
    ¬ CriticalOracleRuntimeOK auth fresh o5 := by
  intro h
  exact hStale h.2.1

end ZenoOracleGeneralizationV1
end Proofs
