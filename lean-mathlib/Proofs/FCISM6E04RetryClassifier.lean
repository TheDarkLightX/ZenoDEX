import Mathlib
import Proofs.FCISDurableRetraction

namespace FCISM6E04RetryClassifier

open FCISDurableRetraction

/-
This file is an abstract Boolean partition artifact only.  It does not model
the Python boundary `reopen : DurableLayout -> Value | Reject`, the typed E04
reopen receipt, or the refinement from a partial reopen verifier into this
classifier.
-/

/-- The retry classifier has four retry results.  `newlyCommitted` is emitted
by the linearizing publication operation, while this function classifies a
request against a canonical stored-state observation. -/
def classifyRetry
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

/-- Every valid stored-state flag tuple receives exactly one retry result. -/
theorem classifyRetry_total
    (commitPresent fingerprintMatches nullifierCollision preStateMatches
      writerAllowed : Bool) :
    classifyRetry commitPresent fingerprintMatches nullifierCollision preStateMatches
        writerAllowed = .alreadyCommitted ∨
      classifyRetry commitPresent fingerprintMatches nullifierCollision preStateMatches
        writerAllowed = .absentRetryable ∨
      classifyRetry commitPresent fingerprintMatches nullifierCollision preStateMatches
        writerAllowed = .staleState ∨
      classifyRetry commitPresent fingerprintMatches nullifierCollision preStateMatches
        writerAllowed = .definiteRejection := by
  simp [classifyRetry]
  aesop

/-- The client-knowledge coordinate is carried through without changing the
durable projection. -/
inductive ClientKnowledge where
  | confirmed
  | indeterminate
  deriving DecidableEq, Repr

def classifyWithKnowledge
    (commitPresent fingerprintMatches nullifierCollision preStateMatches
      writerAllowed : Bool)
    (knowledge : ClientKnowledge) : CommitResolution × ClientKnowledge :=
  (classifyRetry commitPresent fingerprintMatches nullifierCollision preStateMatches writerAllowed,
    knowledge)

theorem knowledge_projection
    (commitPresent fingerprintMatches nullifierCollision preStateMatches
      writerAllowed : Bool)
    (knowledge : ClientKnowledge) :
    (classifyWithKnowledge commitPresent fingerprintMatches nullifierCollision preStateMatches
      writerAllowed knowledge).1 =
      classifyRetry commitPresent fingerprintMatches nullifierCollision preStateMatches
        writerAllowed := by
  rfl

theorem knowledge_does_not_change_durable_result
    (commitPresent fingerprintMatches nullifierCollision preStateMatches
      writerAllowed : Bool) :
    (classifyWithKnowledge commitPresent fingerprintMatches nullifierCollision preStateMatches
      writerAllowed .confirmed).1 =
      (classifyWithKnowledge commitPresent fingerprintMatches nullifierCollision preStateMatches
        writerAllowed .indeterminate).1 := by
  rfl

/-- The taskbook precedence is executable in the formal model. -/
theorem precedence_same_commit_same_fingerprint :
    classifyRetry true true true false false = .alreadyCommitted := by
  rfl

theorem precedence_same_commit_collision :
    classifyRetry true false false true true = .definiteRejection := by
  rfl

theorem precedence_nullifier_collision :
    classifyRetry false false true true true = .definiteRejection := by
  rfl

theorem precedence_stale_head :
    classifyRetry false false false false true = .staleState := by
  rfl

theorem precedence_head_authorization :
    classifyRetry false false false true false = .definiteRejection := by
  rfl

theorem precedence_absent_retryable :
    classifyRetry false false false true true = .absentRetryable := by
  rfl

#print axioms classifyRetry_total
#print axioms knowledge_projection
#print axioms knowledge_does_not_change_durable_result

end FCISM6E04RetryClassifier
