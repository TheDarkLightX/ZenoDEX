/-!
# ZenoDEX AutoTrader Stage Certificate

This file formalizes the deterministic shell around the stage-aware
AutoTrader certificate that can be attached before the full live-release
surface exists.

It proves:

- stage selection is a deterministic function of the available hash surfaces,
- verifier success is equivalent to equality with the canonical rebuilt
  certificate,
- the verifying certificate is unique for a fixed report-shaped input.

As with the other AutoTrader shell proofs, this models hashes as deterministic
inputs. It does **not** model canonical JSON or SHA256 concretely.
-/

namespace TauSwap
namespace AutoTrader
namespace StageCertificate

inductive Stage where
  | signer
  | tauPolicyBundle
  | policyArtifact
  | observation
  | candidateSet
  | decision
  | liveRelease
deriving DecidableEq, Repr

structure Inputs where
  signerPubkey : Nat
  chainId : Nat
  decisionTag : Nat
  tauPolicyBundleHash : Option Nat
  policyArtifactHash : Option Nat
  observationHash : Option Nat
  candidateSetHash : Option Nat
  decisionHash : Option Nat
  blocker : Option Nat
deriving DecidableEq, Repr

def releaseEligible (inputs : Inputs) : Bool :=
  inputs.tauPolicyBundleHash.isSome &&
    inputs.policyArtifactHash.isSome &&
    inputs.observationHash.isSome &&
    inputs.candidateSetHash.isSome &&
    inputs.decisionHash.isSome

def highestStage (inputs : Inputs) : Stage :=
  if releaseEligible inputs then
    Stage.liveRelease
  else if inputs.decisionHash.isSome then
    Stage.decision
  else if inputs.candidateSetHash.isSome then
    Stage.candidateSet
  else if inputs.observationHash.isSome then
    Stage.observation
  else if inputs.policyArtifactHash.isSome then
    Stage.policyArtifact
  else if inputs.tauPolicyBundleHash.isSome then
    Stage.tauPolicyBundle
  else
    Stage.signer

structure Certificate where
  signerPubkey : Nat
  chainId : Nat
  decisionTag : Nat
  tauPolicyBundleHash : Option Nat
  policyArtifactHash : Option Nat
  observationHash : Option Nat
  candidateSetHash : Option Nat
  decisionHash : Option Nat
  highestStage : Stage
  releaseEligible : Bool
  blocker : Option Nat
deriving DecidableEq, Repr

def buildCertificate (inputs : Inputs) : Certificate :=
  {
    signerPubkey := inputs.signerPubkey
    chainId := inputs.chainId
    decisionTag := inputs.decisionTag
    tauPolicyBundleHash := inputs.tauPolicyBundleHash
    policyArtifactHash := inputs.policyArtifactHash
    observationHash := inputs.observationHash
    candidateSetHash := inputs.candidateSetHash
    decisionHash := inputs.decisionHash
    highestStage := highestStage inputs
    releaseEligible := releaseEligible inputs
    blocker := inputs.blocker
  }

def verifyCertificate (inputs : Inputs) (certificate : Certificate) : Prop :=
  certificate = buildCertificate inputs

theorem highestStage_liveRelease_of_releaseEligible
    (inputs : Inputs)
    (h : releaseEligible inputs = true) :
    highestStage inputs = Stage.liveRelease := by
  simp [highestStage, h]

theorem highestStage_signer_of_no_hashes
    (inputs : Inputs)
    (hBundle : inputs.tauPolicyBundleHash = none)
    (hArtifact : inputs.policyArtifactHash = none)
    (hObservation : inputs.observationHash = none)
    (hCandidate : inputs.candidateSetHash = none)
    (hDecision : inputs.decisionHash = none) :
    highestStage inputs = Stage.signer := by
  simp [highestStage, releaseEligible, hBundle, hArtifact, hObservation, hCandidate, hDecision]

theorem verifyCertificate_iff
    (inputs : Inputs)
    (certificate : Certificate) :
    verifyCertificate inputs certificate ↔
      certificate = buildCertificate inputs := by
  rfl

theorem verifyCertificate_of_build
    (inputs : Inputs) :
    verifyCertificate inputs (buildCertificate inputs) := by
  rfl

theorem verifyingCertificate_unique
    (inputs : Inputs)
    {certificate : Certificate}
    (hVerify : verifyCertificate inputs certificate) :
    certificate = buildCertificate inputs := by
  exact hVerify

end StageCertificate
end AutoTrader
end TauSwap
