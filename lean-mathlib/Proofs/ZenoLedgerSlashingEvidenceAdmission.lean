/-!
ZenoLedger slashing-evidence admission boundary.

The runtime builder converts checkpoint and watcher-attestation equivocation into
hash-bound evidence packets. This Lean model captures the narrow admission fact:
an admitted packet has a single conflict key, a single slash subject, two
conflicting header hashes, canonical ordering, artifact-hash binding, and
evidence-hash binding.

Bonded slashing execution, penalties, appeals, and governance policy are outside
this theorem surface.
-/

namespace Proofs.ZenoLedgerSlashingEvidenceAdmission

structure SlashingEvidenceAdmission where
  sameChain : Bool
  sameHeight : Bool
  sameSubject : Bool
  headerHashesConflict : Bool
  headerHashesSorted : Bool
  artifactHashesDistinct : Bool
  artifactHashesSorted : Bool
  artifactHashBindingsValid : Bool
  evidenceHashMatches : Bool
deriving DecidableEq, Repr

def Safe (a : SlashingEvidenceAdmission) : Prop :=
  a.sameChain = true ∧
  a.sameHeight = true ∧
  a.sameSubject = true ∧
  a.headerHashesConflict = true ∧
  a.headerHashesSorted = true ∧
  a.artifactHashesDistinct = true ∧
  a.artifactHashesSorted = true ∧
  a.artifactHashBindingsValid = true ∧
  a.evidenceHashMatches = true

def Admitted (a : SlashingEvidenceAdmission) : Prop :=
  Safe a

/--
An admitted slashing-evidence packet has a single conflict key, a single slash
subject, conflicting header hashes, canonical ordering, and both artifact and
evidence hash binding.
-/
theorem admitted_safe
    (a : SlashingEvidenceAdmission)
    (hadmit : Admitted a) :
    Safe a := by
  exact hadmit

theorem admitted_has_conflicting_headers
    (a : SlashingEvidenceAdmission)
    (hadmit : Admitted a) :
    a.headerHashesConflict = true := by
  exact (admitted_safe a hadmit).2.2.2.1

theorem admitted_has_single_subject
    (a : SlashingEvidenceAdmission)
    (hadmit : Admitted a) :
    a.sameSubject = true := by
  exact (admitted_safe a hadmit).2.2.1

theorem admitted_has_artifact_binding
    (a : SlashingEvidenceAdmission)
    (hadmit : Admitted a) :
    a.artifactHashBindingsValid = true := by
  exact (admitted_safe a hadmit).2.2.2.2.2.2.2.1

theorem admitted_has_evidence_hash_binding
    (a : SlashingEvidenceAdmission)
    (hadmit : Admitted a) :
    a.evidenceHashMatches = true := by
  exact (admitted_safe a hadmit).2.2.2.2.2.2.2.2

/--
A packet with non-conflicting header hashes cannot be admitted.
-/
theorem rejects_non_conflicting_headers
    (a : SlashingEvidenceAdmission)
    (hheaders : a.headerHashesConflict = false) :
    ¬ Admitted a := by
  intro hadmit
  have hconflict := admitted_has_conflicting_headers a hadmit
  rw [hheaders] at hconflict
  cases hconflict

/--
A packet that points to different slash subjects cannot be admitted.
-/
theorem rejects_mixed_subjects
    (a : SlashingEvidenceAdmission)
    (hsubject : a.sameSubject = false) :
    ¬ Admitted a := by
  intro hadmit
  have hsame := admitted_has_single_subject a hadmit
  rw [hsubject] at hsame
  cases hsame

/--
A packet with invalid artifact-hash binding cannot be admitted.
-/
theorem rejects_bad_artifact_binding
    (a : SlashingEvidenceAdmission)
    (hbinding : a.artifactHashBindingsValid = false) :
    ¬ Admitted a := by
  intro hadmit
  have hvalid := admitted_has_artifact_binding a hadmit
  rw [hbinding] at hvalid
  cases hvalid

/--
A packet with a mismatched evidence hash cannot be admitted.
-/
theorem rejects_evidence_hash_mismatch
    (a : SlashingEvidenceAdmission)
    (hevidence : a.evidenceHashMatches = false) :
    ¬ Admitted a := by
  intro hadmit
  have hhash := admitted_has_evidence_hash_binding a hadmit
  rw [hevidence] at hhash
  cases hhash

theorem admits_safe_packet
    (a : SlashingEvidenceAdmission)
    (hchain : a.sameChain = true)
    (hheight : a.sameHeight = true)
    (hsubject : a.sameSubject = true)
    (hheaders : a.headerHashesConflict = true)
    (hheaderOrder : a.headerHashesSorted = true)
    (hartifactDistinct : a.artifactHashesDistinct = true)
    (hartifactOrder : a.artifactHashesSorted = true)
    (hartifactBinding : a.artifactHashBindingsValid = true)
    (hevidence : a.evidenceHashMatches = true) :
    Admitted a := by
  unfold Admitted Safe
  exact ⟨
    hchain,
    hheight,
    hsubject,
    hheaders,
    hheaderOrder,
    hartifactDistinct,
    hartifactOrder,
    hartifactBinding,
    hevidence
  ⟩

end Proofs.ZenoLedgerSlashingEvidenceAdmission
