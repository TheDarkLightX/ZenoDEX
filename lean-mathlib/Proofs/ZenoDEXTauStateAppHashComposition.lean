import Proofs.ZenoDEXTauStateAppHashProvenance
import Proofs.ZenoDEXTauStateAppHashStableWindow

/-!
# ZenoDEX Tau State App-Hash Composition

This file links the stable transport refinement predicates to the abstract
loader acceptance shell.
-/

namespace TauSwap
namespace TauStateAppHashComposition

open TauStateAppHashProvenance
open TauStateAppHashStableWindow

def toProvenanceInputs (inputs : TauStateAppHashStableWindow.Inputs) :
    TauStateAppHashProvenance.Inputs :=
  {
    execReq := true
    bridgePayloadPresent := inputs.bridgePayloadReady
    bridgePayloadObjectOk := true
    bridgeSchemaOk := true
    bridgeSnapshotPresent := true
    requestBindingOk := true
    anchorBindingOk := true
    policyBindingOk := true
    strongBindingRequired := inputs.strongBindingRequired
    stateProofPresent := inputs.stateProofPresent
    stateHashPresent := inputs.stateHashPresent
    stateProofStable := inputs.stateProofStable
    stateProofErrorFree := true
    appStatePresent := inputs.appStatePresent
    appStateStable := inputs.appStateStable
    appStateHashOk := inputs.appStateHashOk
    tauStateTransportAvailable := inputs.tauStateTransportAvailable
    tauStatePresent := inputs.tauStatePresent
    tauStateStable := inputs.tauStateStable
    tauStateHashMatchesProof := inputs.tauStateHashMatchesProof
    tauStateAppHashPresent := inputs.tauStateAppHashPresent
    tauStateAppHashMatchesAppState := inputs.tauStateAppHashMatchesAppState
  }

theorem transportRefinementImpliesLoaderOk (inputs : TauStateAppHashStableWindow.Inputs)
    (hRefine : transportRefinementOk inputs = true) :
    (buildPacket (toProvenanceInputs inputs)).loaderOk = true := by
  cases inputs with
  | mk bridgePayloadReady strongBindingRequired stateProofPresent stateHashPresent stateProofStable
      appStatePresent appStateStable appStateHashOk tauStateTransportAvailable tauStatePresent
      tauStateStable tauStateHashMatchesProof tauStateAppHashPresent tauStateAppHashMatchesAppState =>
      cases strongBindingRequired
      · simp [
          transportRefinementOk,
          stableWindowOk,
          toProvenanceInputs,
          TauStateAppHashProvenance.buildPacket,
          Bool.and_eq_true,
          and_assoc,
        ] at hRefine ⊢
        simpa [and_assoc, and_left_comm, and_comm] using hRefine
      · simp [
          transportRefinementOk,
          stableWindowOk,
          toProvenanceInputs,
          TauStateAppHashProvenance.buildPacket,
          Bool.and_eq_true,
          and_assoc,
        ] at hRefine ⊢
        simpa [and_assoc, and_left_comm, and_comm] using hRefine

end TauStateAppHashComposition
end TauSwap
