/-!
# ZenoDEX AutoTrader Live Release Certificate

This file formalizes the deterministic shell around the consolidated
AutoTrader live-release certificate.

It proves:

- the release bit is exactly the conjunction of the submit-time gates,
- verifier success is equivalent to equality with the canonical rebuilt
  certificate,
- the verifying certificate is unique for a fixed set of upstream bindings and
  gate bits.

As with the decision-binding shell, this models upstream hashes as deterministic
inputs. It does **not** model canonical JSON or SHA256 concretely.
-/

namespace TauSwap
namespace AutoTrader
namespace LiveReleaseCertificate

structure Inputs where
  policyArtifactHash : Nat
  tauPolicyBundleHash : Nat
  observationHash : Nat
  candidateSetHash : Nat
  decisionHash : Nat
  decisionModelVersion : Nat
deriving DecidableEq, Repr

def releaseOk
    (emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk : Bool) : Bool :=
  emitRequested && liveAdmissionOk && systemComposeOk && submitBundleOk && emitFinalizeOk

def releaseError
    (emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk : Bool)
    (liveAdmissionError systemComposeError submitBundleError emitFinalizeError : Option Nat) :
    Option Nat :=
  if !emitRequested then
    some 5
  else if !liveAdmissionOk then
    match liveAdmissionError with
    | some err => some err
    | none => some 1
  else if !systemComposeOk then
    match systemComposeError with
    | some err => some err
    | none => some 2
  else if !submitBundleOk then
    match submitBundleError with
    | some err => some err
    | none => some 3
  else if !emitFinalizeOk then
    match emitFinalizeError with
    | some err => some err
    | none => some 4
  else if !emitRequested then
    some 5
  else
    none

structure Certificate where
  policyArtifactHash : Nat
  tauPolicyBundleHash : Nat
  observationHash : Nat
  candidateSetHash : Nat
  decisionHash : Nat
  decisionModelVersion : Nat
  emitRequested : Bool
  liveAdmissionOk : Bool
  systemComposeOk : Bool
  submitBundleOk : Bool
  emitFinalizeOk : Bool
  releaseOk : Bool
  releaseError : Option Nat
deriving DecidableEq, Repr

def buildCertificate
    (inputs : Inputs)
    (emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk : Bool)
    (liveAdmissionError systemComposeError submitBundleError emitFinalizeError : Option Nat) :
    Certificate :=
  {
    policyArtifactHash := inputs.policyArtifactHash
    tauPolicyBundleHash := inputs.tauPolicyBundleHash
    observationHash := inputs.observationHash
    candidateSetHash := inputs.candidateSetHash
    decisionHash := inputs.decisionHash
    decisionModelVersion := inputs.decisionModelVersion
    emitRequested := emitRequested
    liveAdmissionOk := liveAdmissionOk
    systemComposeOk := systemComposeOk
    submitBundleOk := submitBundleOk
    emitFinalizeOk := emitFinalizeOk
    releaseOk := releaseOk emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk
    releaseError := releaseError
      emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk
      liveAdmissionError systemComposeError submitBundleError emitFinalizeError
  }

def verifyCertificate
    (inputs : Inputs)
    (emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk : Bool)
    (liveAdmissionError systemComposeError submitBundleError emitFinalizeError : Option Nat)
    (certificate : Certificate) : Prop :=
  certificate =
    buildCertificate
      inputs
      emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk
      liveAdmissionError systemComposeError submitBundleError emitFinalizeError

theorem releaseOk_iff
    (emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk : Bool) :
    releaseOk emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk = true ↔
      emitRequested = true ∧
      liveAdmissionOk = true ∧
      systemComposeOk = true ∧
      submitBundleOk = true ∧
      emitFinalizeOk = true := by
  cases emitRequested <;>
    cases liveAdmissionOk <;>
    cases systemComposeOk <;>
    cases submitBundleOk <;>
    cases emitFinalizeOk <;>
    decide

theorem verifyCertificate_iff
    (inputs : Inputs)
    (emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk : Bool)
    (liveAdmissionError systemComposeError submitBundleError emitFinalizeError : Option Nat)
    (certificate : Certificate) :
    verifyCertificate
      inputs
      emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk
      liveAdmissionError systemComposeError submitBundleError emitFinalizeError
      certificate ↔
    certificate =
      buildCertificate
        inputs
        emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk
        liveAdmissionError systemComposeError submitBundleError emitFinalizeError := by
  rfl

theorem verifyCertificate_of_build
    (inputs : Inputs)
    (emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk : Bool)
    (liveAdmissionError systemComposeError submitBundleError emitFinalizeError : Option Nat) :
    verifyCertificate
      inputs
      emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk
      liveAdmissionError systemComposeError submitBundleError emitFinalizeError
      (buildCertificate
        inputs
        emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk
        liveAdmissionError systemComposeError submitBundleError emitFinalizeError) := by
  rfl

theorem verifyingCertificate_unique
    (inputs : Inputs)
    (emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk : Bool)
    (liveAdmissionError systemComposeError submitBundleError emitFinalizeError : Option Nat)
    {certificate : Certificate}
    (hVerify :
      verifyCertificate
        inputs
        emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk
        liveAdmissionError systemComposeError submitBundleError emitFinalizeError
        certificate) :
    certificate =
      buildCertificate
        inputs
        emitRequested liveAdmissionOk systemComposeOk submitBundleOk emitFinalizeOk
        liveAdmissionError systemComposeError submitBundleError emitFinalizeError := by
  exact hVerify

theorem buildCertificate_releaseError_liveAdmission
    (inputs : Inputs)
    (systemComposeOk submitBundleOk emitFinalizeOk : Bool)
    (liveAdmissionError systemComposeError submitBundleError emitFinalizeError : Option Nat) :
    (buildCertificate
      inputs
      true false systemComposeOk submitBundleOk emitFinalizeOk
      liveAdmissionError systemComposeError submitBundleError emitFinalizeError).releaseError =
      match liveAdmissionError with
      | some err => some err
      | none => some 1 := by
  simp [buildCertificate, releaseError]

theorem buildCertificate_releaseError_emitNotRequested
    (inputs : Inputs) :
    (buildCertificate
      inputs
      false true true true true
      none none none none).releaseError = some 5 := by
  simp [buildCertificate, releaseError]

theorem buildCertificate_releaseError_emitNotRequested_overrides_downstream
    (inputs : Inputs)
    (liveAdmissionError systemComposeError submitBundleError emitFinalizeError : Option Nat) :
    (buildCertificate
      inputs
      false false false false false
      liveAdmissionError systemComposeError submitBundleError emitFinalizeError).releaseError = some 5 := by
  simp [buildCertificate, releaseError]

end LiveReleaseCertificate
end AutoTrader
end TauSwap
