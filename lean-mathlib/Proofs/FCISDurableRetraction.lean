import Mathlib

namespace FCISDurableRetraction

universe uA uD uE uI uO

/-- A rejected durable layout cannot be reopened as an authorized history. -/
inductive Reject where
  | malformed
  | unauthorized
  deriving DecidableEq, Repr

/-
Runtime-to-formal mapping:
* `A` is the typed `AuthorizedHistoryV1` semantic state.
* `D` is the canonical `DurableSnapshotV1` byte/layout domain.
* `reopen` is the totalized runtime partial function returning `Except Reject A`.
* `encode` is canonical re-encoding; `normalize` is reopen followed by rewrite.
* `CommitResolution` and `ClientObservation` model durable outcome versus transport.
* `CrashView` models the atomic PRE or complete POST publication boundary.
-/

/-- An authorized semantic history is a partial retract of its durable layout. -/
structure DurableRetraction (A : Type uA) (D : Type uD) where
  encode : A → D
  reopen : D → Except Reject A
  reopen_encode : ∀ authorized, reopen (encode authorized) = Except.ok authorized

namespace DurableRetraction

/-- Reopen, then canonically re-encode every durable layout. -/
def normalize {A : Type uA} {D : Type uD} (R : DurableRetraction A D) : D → Except Reject D :=
  fun durable =>
    match R.reopen durable with
    | .error reason => .error reason
    | .ok authorized => .ok (R.encode authorized)

/-- The left-inverse premise is exposed as an explicit successful reopen theorem. -/
theorem reopen_encode_ok
    {A : Type uA}
    {D : Type uD}
    (R : DurableRetraction A D)
    (authorized : A) :
    R.reopen (R.encode authorized) = Except.ok authorized :=
  R.reopen_encode authorized

/-- Canonical durable encoding cannot identify two authorized histories. -/
theorem encode_injective
    {A : Type uA}
    {D : Type uD}
    (R : DurableRetraction A D) :
    Function.Injective R.encode := by
  intro left right sameEncoding
  have reopened : R.reopen (R.encode left) = R.reopen (R.encode right) :=
    congrArg R.reopen sameEncoding
  simpa [R.reopen_encode] using reopened

/-- Every encoded authorized history is a successful fixed point. -/
theorem normalize_encode
    {A : Type uA}
    {D : Type uD}
    (R : DurableRetraction A D)
    (authorized : A) :
    R.normalize (R.encode authorized) = Except.ok (R.encode authorized) := by
  simp [normalize, R.reopen_encode]

/-- Successful normalization is idempotent; failed normalization has no canonical output. -/
theorem normalize_idempotent
    {A : Type uA}
    {D : Type uD}
    (R : DurableRetraction A D)
    (durable canonical : D)
    (success : R.normalize durable = Except.ok canonical) :
    R.normalize canonical = Except.ok canonical := by
  cases reopened : R.reopen durable with
  | error reason =>
      simp [normalize, reopened] at success
  | ok authorized =>
      simp [normalize, reopened] at success
      subst canonical
      simp [normalize, R.reopen_encode]

/-
An exact authoritative layout is a successful reopen whose canonical rewrite is
the exact durable layout. The success premise is part of the characterization.
-/
theorem fixed_iff_in_encode_range
    {A : Type uA}
    {D : Type uD}
    (R : DurableRetraction A D)
    (durable : D) :
    R.normalize durable = Except.ok durable ↔
      ∃ authorized, R.reopen durable = Except.ok authorized ∧ R.encode authorized = durable := by
  constructor
  · intro fixed
    cases reopened : R.reopen durable with
    | error reason =>
        simp [normalize, reopened] at fixed
    | ok authorized =>
        simp [normalize, reopened] at fixed
        exact ⟨authorized, rfl, fixed⟩
  · rintro ⟨authorized, reopened, canonical⟩
    simp [normalize, reopened, canonical]

/-- Equal successful reopens and fixed-point evidence imply equal durable layouts. -/
theorem fixed_extensionality
    {A : Type uA}
    {D : Type uD}
    (R : DurableRetraction A D)
    {left right : D}
    (leftFixed : R.normalize left = Except.ok left)
    (rightFixed : R.normalize right = Except.ok right)
    (sameReopen : R.reopen left = R.reopen right) :
    left = right := by
  have equalOk : (Except.ok left : Except Reject D) = Except.ok right := by
    calc
      Except.ok left = R.normalize left := leftFixed.symm
      _ = R.normalize right := by simp [normalize, sameReopen]
      _ = Except.ok right := rightFixed
  injection equalOk

/-- A successful normalized layout is authoritative and remains successful. -/
theorem normalize_is_fixed
    {A : Type uA}
    {D : Type uD}
    (R : DurableRetraction A D)
    (durable canonical : D)
    (success : R.normalize durable = Except.ok canonical) :
    R.normalize canonical = Except.ok canonical :=
  R.normalize_idempotent durable canonical success

end DurableRetraction

/-- The durable store's exact resolution for one stable commit identity. -/
inductive CommitResolution where
  | newlyCommitted
  | alreadyCommitted
  | absentRetryable
  | staleState
  | definiteRejection
  deriving DecidableEq, Repr

/-- Transport knowledge is distinct from the durable resolution. -/
inductive ClientObservation where
  | confirmedNew
  | confirmedAlready
  | confirmedStale
  | confirmedRejection
  | indeterminate
  deriving DecidableEq, Repr

/-- A compact executable stored-state classifier. -/
def classifyStored
    (commitPresent fingerprintMatches nullifierCollision preStateMatches
      writerAllowed : Bool) :
    CommitResolution :=
  if commitPresent then
    if fingerprintMatches then
      .alreadyCommitted
    else
      .definiteRejection
  else if nullifierCollision then
    .definiteRejection
  else if !preStateMatches then
    .staleState
  else if !writerAllowed then
    .definiteRejection
  else
    .absentRetryable

theorem same_commit_resolves_already :
    classifyStored true true false false false = .alreadyCommitted := by
  rfl

theorem commit_identity_collision_rejects :
    classifyStored true false false true true = .definiteRejection := by
  rfl

theorem nullifier_collision_rejects :
    classifyStored false false true true true = .definiteRejection := by
  rfl

theorem absent_request_on_foreign_head_is_stale :
    classifyStored false false false false true = .staleState := by
  rfl

theorem absent_request_on_current_head_is_retryable :
    classifyStored false false false true true = .absentRetryable := by
  rfl

/-- A head authorization is valid only for the exact snapshot that it names. -/
def HeadAuthorized {Snapshot : Type uD} (tokenHead actualHead : Snapshot) : Prop :=
  tokenHead = actualHead

theorem changed_head_invalidates_old_authorization
    {Snapshot : Type uD}
    {oldHead newHead : Snapshot}
    (changed : oldHead ≠ newHead) :
    ¬ HeadAuthorized oldHead newHead := by
  simpa [HeadAuthorized] using changed

/-- A crash-refined authoritative view contains exactly PRE or exactly POST. -/
inductive CrashView {D : Type uD} (pre post : D) : D → Prop where
  | before : CrashView pre post pre
  | after : CrashView pre post post

theorem crash_view_cases
    {D : Type uD}
    {pre post observed : D}
    (view : CrashView pre post observed) :
    observed = pre ∨ observed = post := by
  cases view with
  | before => exact Or.inl rfl
  | after => exact Or.inr rfl

/-- A verified retry/reopen loop is an observational identity on canonical values. -/
def StutterIdentity {A : Type uA} (step : A → A) : Prop :=
  ∀ value, step value = value

/-- Same-commit identity and client observation remain unchanged on retry. -/
def SameCommitObservation
    {A : Type uA}
    {Identity : Type uI}
    {Observation : Type uO}
    (identity : A → Identity)
    (observe : A → Observation)
    (retry : A → A) :
    Prop :=
  ∀ value, identity (retry value) = identity value ∧ observe (retry value) = observe value

theorem same_commit_retry_is_observational_stutter
    {A : Type uA}
    {Identity : Type uI}
    {Observation : Type uO}
    (identity : A → Identity)
    (observe : A → Observation)
    (retry : A → A)
    (stutter : SameCommitObservation identity observe retry) :
    ∀ value, identity (retry value) = identity value ∧ observe (retry value) = observe value := by
  exact stutter

theorem stutter_comp
    {A : Type uA}
    {left right : A → A}
    (leftStutter : StutterIdentity left)
    (rightStutter : StutterIdentity right) :
    StutterIdentity (right ∘ left) := by
  intro value
  simp [Function.comp_apply, leftStutter value, rightStutter value]

def iterate {A : Type uA} (step : A → A) : Nat → A → A
  | 0, value => value
  | count + 1, value => iterate step count (step value)

theorem stutter_iterate
    {A : Type uA}
    (step : A → A)
    (stutter : StutterIdentity step)
    (count : Nat)
    (value : A) :
    iterate step count value = value := by
  induction count generalizing value with
  | zero => rfl
  | succ count inductionHypothesis =>
      change iterate step count (step value) = value
      exact (inductionHypothesis (step value)).trans (stutter value)

theorem duplicate_effect_identity_is_idempotent
    {EffectState : Type uE}
    (accept : EffectState → EffectState)
    (idempotent : ∀ state, accept (accept state) = accept state)
    (state : EffectState) :
    accept (accept state) = accept state :=
  idempotent state

#print axioms DurableRetraction.reopen_encode_ok
#print axioms DurableRetraction.encode_injective
#print axioms DurableRetraction.normalize_encode
#print axioms DurableRetraction.normalize_idempotent
#print axioms DurableRetraction.fixed_iff_in_encode_range
#print axioms DurableRetraction.fixed_extensionality
#print axioms same_commit_resolves_already
#print axioms commit_identity_collision_rejects
#print axioms nullifier_collision_rejects
#print axioms absent_request_on_foreign_head_is_stale
#print axioms absent_request_on_current_head_is_retryable
#print axioms same_commit_retry_is_observational_stutter
#print axioms changed_head_invalidates_old_authorization
#print axioms crash_view_cases
#print axioms stutter_iterate
#print axioms duplicate_effect_identity_is_idempotent

end FCISDurableRetraction
