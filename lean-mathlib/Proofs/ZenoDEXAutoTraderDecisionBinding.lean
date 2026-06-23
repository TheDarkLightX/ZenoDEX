/-!
# ZenoDEX AutoTrader Decision Binding

This file formalizes the deterministic shell around the current binary
AutoTrader decision certificate.

It proves the following, under the same binary frontier used by the shipped
integration code:

- the derived `binding_ok` predicate holds for the canonical rebuilt
  certificate when the candidate set is well-formed,
- verifier success with an explicit kill-switch posture is equivalent to exact
  equality with the canonical rebuilt certificate,
- for a fixed candidate set and kill-switch posture, the verifying certificate
  is unique.

This does **not** model canonical JSON or SHA256 concretely. Instead, it treats
the candidate-set hash as a deterministic function of the unsigned payload and
proves the shell logic around that deterministic binding surface.
-/

namespace TauSwap
namespace AutoTrader
namespace DecisionBinding

inductive CandidateKind where
  | noOp
  | emitCompiledIntent
deriving DecidableEq, Repr

structure DecisionCandidate where
  candidateIndex : Nat
  kind : CandidateKind
  requested : Bool
  admissible : Bool
  candidateKey : Nat
deriving DecidableEq, Repr

structure StrategyCandidateSet where
  policyArtifactHash : Nat
  tauPolicyBundleHash : Nat
  observationHash : Nat
  decisionModelVersion : Nat
  noopCandidate : DecisionCandidate
  emitCandidate : DecisionCandidate
deriving DecidableEq, Repr

abbrev CandidateSetUnsigned :=
  Nat × Nat × Nat × Nat × DecisionCandidate × DecisionCandidate

def candidateSetUnsigned (candidateSet : StrategyCandidateSet) : CandidateSetUnsigned :=
  ( candidateSet.policyArtifactHash,
    candidateSet.tauPolicyBundleHash,
    candidateSet.observationHash,
    candidateSet.decisionModelVersion,
    candidateSet.noopCandidate,
    candidateSet.emitCandidate )

def candidateSetHash (candidateSet : StrategyCandidateSet) : CandidateSetUnsigned :=
  candidateSetUnsigned candidateSet

def canonicalCandidateSetHash (candidateSet : StrategyCandidateSet) : CandidateSetUnsigned :=
  candidateSetUnsigned candidateSet

def candidateShapeOk (candidateSet : StrategyCandidateSet) : Prop :=
  candidateSet.noopCandidate.candidateIndex = 0 ∧
    candidateSet.noopCandidate.kind = CandidateKind.noOp ∧
    candidateSet.emitCandidate.candidateIndex = 1 ∧
    candidateSet.emitCandidate.kind = CandidateKind.emitCompiledIntent

instance (candidateSet : StrategyCandidateSet) : Decidable (candidateShapeOk candidateSet) := by
  unfold candidateShapeOk
  infer_instance

def candidateSetOk (candidateSet : StrategyCandidateSet) : Prop :=
  candidateSet.policyArtifactHash ≠ 0 ∧
    candidateSet.tauPolicyBundleHash ≠ 0 ∧
    candidateSet.observationHash ≠ 0 ∧
    candidateSet.decisionModelVersion ≠ 0 ∧
    candidateShapeOk candidateSet

instance (candidateSet : StrategyCandidateSet) : Decidable (candidateSetOk candidateSet) := by
  unfold candidateSetOk
  infer_instance

def rawEmitKey (candidateSet : StrategyCandidateSet) : Nat :=
  if candidateSet.emitCandidate.requested && candidateSet.emitCandidate.admissible then 1 else 0

def killSwitchOk (killSwitchActive : Bool) : Bool :=
  not killSwitchActive

def effectiveEmitAdmissible
    (candidateSet : StrategyCandidateSet)
    (killSwitchActive : Bool) : Bool :=
  candidateSet.emitCandidate.admissible && killSwitchOk killSwitchActive

def effectiveEmitKey
    (candidateSet : StrategyCandidateSet)
    (killSwitchActive : Bool) : Nat :=
  if candidateSet.emitCandidate.requested &&
      effectiveEmitAdmissible candidateSet killSwitchActive then
    1
  else
    0

def winnerIndex
    (candidateSet : StrategyCandidateSet)
    (killSwitchActive : Bool) : Nat :=
  if candidateSet.emitCandidate.requested &&
      effectiveEmitAdmissible candidateSet killSwitchActive then
    1
  else
    0

def winnerKey
    (candidateSet : StrategyCandidateSet)
    (killSwitchActive : Bool) : Nat :=
  effectiveEmitKey candidateSet killSwitchActive

def winnerKind
    (candidateSet : StrategyCandidateSet)
    (killSwitchActive : Bool) : CandidateKind :=
  if winnerIndex candidateSet killSwitchActive = 0 then
    CandidateKind.noOp
  else
    CandidateKind.emitCompiledIntent

structure ArgmaxStep where
  i1 : Nat
  i2 : Nat
  i3 : Nat
  i4 : Nat
  i5 : Bool
deriving DecidableEq, Repr

def buildArgmaxStep
    (winnerKey winnerIndex candKey candIndex : Nat)
    (bindingOk : Bool) : ArgmaxStep :=
  {
    i1 := winnerKey
    i2 := winnerIndex
    i3 := candKey
    i4 := candIndex
    i5 := bindingOk
  }

def decisionBindingOk
    (candidateSet : StrategyCandidateSet)
    (winnerIndex winnerKey : Nat)
    (killSwitchActive : Bool) : Prop :=
  candidateSetOk candidateSet ∧
    candidateSet.noopCandidate.candidateKey = 0 ∧
    candidateSet.emitCandidate.candidateKey = rawEmitKey candidateSet ∧
    winnerIndex = DecisionBinding.winnerIndex candidateSet killSwitchActive ∧
    winnerKey = DecisionBinding.winnerKey candidateSet killSwitchActive ∧
    candidateSetHash candidateSet = canonicalCandidateSetHash candidateSet

instance
    (candidateSet : StrategyCandidateSet)
    (winnerIndex winnerKey : Nat)
    (killSwitchActive : Bool) :
    Decidable (decisionBindingOk candidateSet winnerIndex winnerKey killSwitchActive) := by
  unfold decisionBindingOk
  infer_instance

structure StrategyDecisionCertificate where
  policyArtifactHash : Nat
  tauPolicyBundleHash : Nat
  observationHash : Nat
  candidateSetHash : CandidateSetUnsigned
  decisionModelVersion : Nat
  winnerIndex : Nat
  winnerKind : CandidateKind
  winnerKey : Nat
  argmaxSteps : List ArgmaxStep
  killSwitchActive : Bool
deriving DecidableEq, Repr

def buildDecisionCertificate
    (candidateSet : StrategyCandidateSet)
    (killSwitchActive : Bool) : StrategyDecisionCertificate :=
  let bindingOk :=
    decide
      (decisionBindingOk
        candidateSet
        (winnerIndex candidateSet killSwitchActive)
        (winnerKey candidateSet killSwitchActive)
        killSwitchActive)
  {
    policyArtifactHash := candidateSet.policyArtifactHash
    tauPolicyBundleHash := candidateSet.tauPolicyBundleHash
    observationHash := candidateSet.observationHash
    candidateSetHash := candidateSetHash candidateSet
    decisionModelVersion := candidateSet.decisionModelVersion
    winnerIndex := winnerIndex candidateSet killSwitchActive
    winnerKind := winnerKind candidateSet killSwitchActive
    winnerKey := winnerKey candidateSet killSwitchActive
    argmaxSteps :=
      [ buildArgmaxStep
          (winnerKey candidateSet killSwitchActive)
          (winnerIndex candidateSet killSwitchActive)
          candidateSet.noopCandidate.candidateKey
          candidateSet.noopCandidate.candidateIndex
          bindingOk,
        buildArgmaxStep
          (winnerKey candidateSet killSwitchActive)
          (winnerIndex candidateSet killSwitchActive)
          (effectiveEmitKey candidateSet killSwitchActive)
          candidateSet.emitCandidate.candidateIndex
          bindingOk ]
    killSwitchActive := killSwitchActive
  }

def verifyDecisionCertificate
    (candidateSet : StrategyCandidateSet)
    (certificate : StrategyDecisionCertificate)
    (expectedKillSwitchActive : Bool) : Prop :=
  certificate = buildDecisionCertificate candidateSet expectedKillSwitchActive

theorem candidateSetHash_eq_canonicalCandidateSetHash
    (candidateSet : StrategyCandidateSet) :
    candidateSetHash candidateSet = canonicalCandidateSetHash candidateSet := by
  rfl

theorem bindingOk_of_wellFormed
    {candidateSet : StrategyCandidateSet}
    (hSet : candidateSetOk candidateSet)
    (hNoopKey : candidateSet.noopCandidate.candidateKey = 0)
    (hEmitKey : candidateSet.emitCandidate.candidateKey = rawEmitKey candidateSet)
    (killSwitchActive : Bool) :
    decisionBindingOk
      candidateSet
      (winnerIndex candidateSet killSwitchActive)
      (winnerKey candidateSet killSwitchActive)
      killSwitchActive := by
  refine ⟨hSet, hNoopKey, hEmitKey, rfl, rfl, ?_⟩
  exact candidateSetHash_eq_canonicalCandidateSetHash candidateSet

theorem buildDecisionCertificate_bindingBit_true
    {candidateSet : StrategyCandidateSet}
    (hSet : candidateSetOk candidateSet)
    (hNoopKey : candidateSet.noopCandidate.candidateKey = 0)
    (hEmitKey : candidateSet.emitCandidate.candidateKey = rawEmitKey candidateSet)
    (killSwitchActive : Bool) :
    (buildDecisionCertificate candidateSet killSwitchActive).argmaxSteps.all ArgmaxStep.i5 = true := by
  have hProof :
      decisionBindingOk
        candidateSet
        (winnerIndex candidateSet killSwitchActive)
        (winnerKey candidateSet killSwitchActive)
        killSwitchActive :=
    bindingOk_of_wellFormed hSet hNoopKey hEmitKey killSwitchActive
  have hBinding :
      decide
        (decisionBindingOk
          candidateSet
          (winnerIndex candidateSet killSwitchActive)
          (winnerKey candidateSet killSwitchActive)
          killSwitchActive) = true := by
    simp [hProof]
  simp [buildDecisionCertificate, hBinding, buildArgmaxStep]

theorem verifyDecisionCertificate_iff
    (candidateSet : StrategyCandidateSet)
    (certificate : StrategyDecisionCertificate)
    (expectedKillSwitchActive : Bool) :
    verifyDecisionCertificate candidateSet certificate expectedKillSwitchActive ↔
      certificate = buildDecisionCertificate candidateSet expectedKillSwitchActive := by
  rfl

theorem verifyDecisionCertificate_of_build
    (candidateSet : StrategyCandidateSet)
    (expectedKillSwitchActive : Bool) :
    verifyDecisionCertificate
      candidateSet
      (buildDecisionCertificate candidateSet expectedKillSwitchActive)
      expectedKillSwitchActive := by
  rfl

theorem verifyingCertificate_unique
    (candidateSet : StrategyCandidateSet)
    (expectedKillSwitchActive : Bool)
    {certificate : StrategyDecisionCertificate}
    (hVerify : verifyDecisionCertificate candidateSet certificate expectedKillSwitchActive) :
    certificate = buildDecisionCertificate candidateSet expectedKillSwitchActive := by
  exact hVerify

theorem buildDecisionCertificate_argmaxShape
    (candidateSet : StrategyCandidateSet)
    (killSwitchActive : Bool) :
    (buildDecisionCertificate candidateSet killSwitchActive).argmaxSteps =
      [ buildArgmaxStep
          (winnerKey candidateSet killSwitchActive)
          (winnerIndex candidateSet killSwitchActive)
          candidateSet.noopCandidate.candidateKey
          candidateSet.noopCandidate.candidateIndex
          (decide
            (decisionBindingOk
              candidateSet
              (winnerIndex candidateSet killSwitchActive)
              (winnerKey candidateSet killSwitchActive)
              killSwitchActive)),
        buildArgmaxStep
          (winnerKey candidateSet killSwitchActive)
          (winnerIndex candidateSet killSwitchActive)
          (effectiveEmitKey candidateSet killSwitchActive)
          candidateSet.emitCandidate.candidateIndex
          (decide
            (decisionBindingOk
              candidateSet
              (winnerIndex candidateSet killSwitchActive)
              (winnerKey candidateSet killSwitchActive)
              killSwitchActive)) ] := by
  rfl

end DecisionBinding
end AutoTrader
end TauSwap
