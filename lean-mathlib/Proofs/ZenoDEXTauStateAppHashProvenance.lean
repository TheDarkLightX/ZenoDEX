/-!
# ZenoDEX Tau State App-Hash Provenance

This file formalizes the exact boolean acceptance relation for the Tau-state
app-hash provenance shell used by the settlement signer-registry loader.

It proves:

- the packet is a deterministic rebuild from the control/data booleans,
- verifier success is equivalent to equality with the canonical rebuilt packet,
- `loaderOk` is exactly the conjunction:
  - `bridgePayloadReady`,
  - `baselineProvenanceOk`,
  - and, when required, `strongTauStateBindingOk`.
-/

namespace TauSwap
namespace TauStateAppHashProvenance

structure Inputs where
  execReq : Bool
  bridgePayloadPresent : Bool
  requestBindingOk : Bool
  anchorBindingOk : Bool
  policyBindingOk : Bool
  strongBindingRequired : Bool
  stateProofPresent : Bool
  stateHashPresent : Bool
  stateProofStable : Bool
  appStatePresent : Bool
  appStateStable : Bool
  appStateHashOk : Bool
  tauStateTransportAvailable : Bool
  tauStatePresent : Bool
  tauStateStable : Bool
  tauStateHashMatchesProof : Bool
  tauStateAppHashPresent : Bool
  tauStateAppHashMatchesAppState : Bool
  deriving DecidableEq, Repr

structure Packet where
  bridgePayloadReady : Bool
  baselineProvenanceOk : Bool
  strongTauStateBindingOk : Bool
  loaderOk : Bool
  deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    bridgePayloadReady :=
      inputs.execReq &&
      inputs.bridgePayloadPresent &&
      inputs.requestBindingOk &&
      inputs.anchorBindingOk &&
      inputs.policyBindingOk
    baselineProvenanceOk :=
      inputs.stateProofPresent &&
      inputs.stateHashPresent &&
      inputs.stateProofStable &&
      inputs.appStatePresent &&
      inputs.appStateStable &&
      inputs.appStateHashOk
    strongTauStateBindingOk :=
      inputs.tauStateTransportAvailable &&
      inputs.tauStatePresent &&
      inputs.tauStateStable &&
      inputs.tauStateHashMatchesProof &&
      inputs.tauStateAppHashPresent &&
      inputs.tauStateAppHashMatchesAppState
    loaderOk :=
      (inputs.execReq &&
       inputs.bridgePayloadPresent &&
       inputs.requestBindingOk &&
       inputs.anchorBindingOk &&
       inputs.policyBindingOk) &&
      (inputs.stateProofPresent &&
       inputs.stateHashPresent &&
       inputs.stateProofStable &&
       inputs.appStatePresent &&
       inputs.appStateStable &&
       inputs.appStateHashOk) &&
      (if inputs.strongBindingRequired then
         inputs.tauStateTransportAvailable &&
         inputs.tauStatePresent &&
         inputs.tauStateStable &&
         inputs.tauStateHashMatchesProof &&
         inputs.tauStateAppHashPresent &&
         inputs.tauStateAppHashMatchesAppState
       else
         true)
  }

def verifyPacket (inputs : Inputs) (packet : Packet) : Prop :=
  packet = buildPacket inputs

theorem verifyPacket_iff (inputs : Inputs) (packet : Packet) :
    verifyPacket inputs packet ↔ packet = buildPacket inputs := by
  rfl

theorem verifyPacket_of_build (inputs : Inputs) :
    verifyPacket inputs (buildPacket inputs) := by
  rfl

theorem verifyingPacket_unique (inputs : Inputs) {packet : Packet}
    (hVerify : verifyPacket inputs packet) :
    packet = buildPacket inputs := by
  exact hVerify

theorem bridgePayloadReady_iff (inputs : Inputs) :
    (buildPacket inputs).bridgePayloadReady = true ↔
      inputs.execReq = true ∧
      inputs.bridgePayloadPresent = true ∧
      inputs.requestBindingOk = true ∧
      inputs.anchorBindingOk = true ∧
      inputs.policyBindingOk = true := by
  cases inputs <;> simp [buildPacket, Bool.and_eq_true, and_assoc]

theorem baselineProvenanceOk_iff (inputs : Inputs) :
    (buildPacket inputs).baselineProvenanceOk = true ↔
      inputs.stateProofPresent = true ∧
      inputs.stateHashPresent = true ∧
      inputs.stateProofStable = true ∧
      inputs.appStatePresent = true ∧
      inputs.appStateStable = true ∧
      inputs.appStateHashOk = true := by
  cases inputs <;> simp [buildPacket, Bool.and_eq_true, and_assoc]

theorem strongTauStateBindingOk_iff (inputs : Inputs) :
    (buildPacket inputs).strongTauStateBindingOk = true ↔
      inputs.tauStateTransportAvailable = true ∧
      inputs.tauStatePresent = true ∧
      inputs.tauStateStable = true ∧
      inputs.tauStateHashMatchesProof = true ∧
      inputs.tauStateAppHashPresent = true ∧
      inputs.tauStateAppHashMatchesAppState = true := by
  cases inputs <;> simp [buildPacket, Bool.and_eq_true, and_assoc]

theorem loaderOk_iff (inputs : Inputs) :
    (buildPacket inputs).loaderOk = true ↔
      inputs.execReq = true ∧
      inputs.bridgePayloadPresent = true ∧
      inputs.requestBindingOk = true ∧
      inputs.anchorBindingOk = true ∧
      inputs.policyBindingOk = true ∧
      inputs.stateProofPresent = true ∧
      inputs.stateHashPresent = true ∧
      inputs.stateProofStable = true ∧
      inputs.appStatePresent = true ∧
      inputs.appStateStable = true ∧
      inputs.appStateHashOk = true ∧
      (inputs.strongBindingRequired = false ∨
        inputs.tauStateTransportAvailable = true ∧
        inputs.tauStatePresent = true ∧
        inputs.tauStateStable = true ∧
        inputs.tauStateHashMatchesProof = true ∧
        inputs.tauStateAppHashPresent = true ∧
        inputs.tauStateAppHashMatchesAppState = true) := by
  cases inputs with
  | mk execReq bridgePayloadPresent requestBindingOk anchorBindingOk policyBindingOk
      strongBindingRequired stateProofPresent stateHashPresent stateProofStable appStatePresent
      appStateStable appStateHashOk tauStateTransportAvailable tauStatePresent tauStateStable
      tauStateHashMatchesProof tauStateAppHashPresent tauStateAppHashMatchesAppState =>
      cases strongBindingRequired <;> simp [buildPacket, Bool.and_eq_true, and_assoc]

theorem loaderOk_iff_strongBindingDisabled (inputs : Inputs)
    (hRequired : inputs.strongBindingRequired = false) :
    (buildPacket inputs).loaderOk = true ↔
      inputs.execReq = true ∧
      inputs.bridgePayloadPresent = true ∧
      inputs.requestBindingOk = true ∧
      inputs.anchorBindingOk = true ∧
      inputs.policyBindingOk = true ∧
      inputs.stateProofPresent = true ∧
      inputs.stateHashPresent = true ∧
      inputs.stateProofStable = true ∧
      inputs.appStatePresent = true ∧
      inputs.appStateStable = true ∧
      inputs.appStateHashOk = true := by
  cases inputs with
  | mk execReq bridgePayloadPresent requestBindingOk anchorBindingOk policyBindingOk
      strongBindingRequired stateProofPresent stateHashPresent stateProofStable appStatePresent
      appStateStable appStateHashOk tauStateTransportAvailable tauStatePresent tauStateStable
      tauStateHashMatchesProof tauStateAppHashPresent tauStateAppHashMatchesAppState =>
      cases hRequired
      simp [buildPacket, Bool.and_eq_true, and_assoc]

theorem loaderOk_iff_strongBindingEnabled (inputs : Inputs)
    (hRequired : inputs.strongBindingRequired = true) :
    (buildPacket inputs).loaderOk = true ↔
      inputs.execReq = true ∧
      inputs.bridgePayloadPresent = true ∧
      inputs.requestBindingOk = true ∧
      inputs.anchorBindingOk = true ∧
      inputs.policyBindingOk = true ∧
      inputs.stateProofPresent = true ∧
      inputs.stateHashPresent = true ∧
      inputs.stateProofStable = true ∧
      inputs.appStatePresent = true ∧
      inputs.appStateStable = true ∧
      inputs.appStateHashOk = true ∧
      inputs.tauStateTransportAvailable = true ∧
      inputs.tauStatePresent = true ∧
      inputs.tauStateStable = true ∧
      inputs.tauStateHashMatchesProof = true ∧
      inputs.tauStateAppHashPresent = true ∧
      inputs.tauStateAppHashMatchesAppState = true := by
  cases inputs with
  | mk execReq bridgePayloadPresent requestBindingOk anchorBindingOk policyBindingOk
      strongBindingRequired stateProofPresent stateHashPresent stateProofStable appStatePresent
      appStateStable appStateHashOk tauStateTransportAvailable tauStatePresent tauStateStable
      tauStateHashMatchesProof tauStateAppHashPresent tauStateAppHashMatchesAppState =>
      cases hRequired
      simp [buildPacket, Bool.and_eq_true, and_assoc]

end TauStateAppHashProvenance
end TauSwap
