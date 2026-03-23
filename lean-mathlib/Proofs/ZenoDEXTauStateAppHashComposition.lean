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
    requestBindingOk := true
    anchorBindingOk := true
    policyBindingOk := true
    strongBindingRequired := inputs.strongBindingRequired
    stateProofPresent := inputs.stateProofPresent
    stateHashPresent := inputs.stateHashPresent
    stateProofStable := inputs.stateProofStable
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
        rcases hRefine with ⟨hb, hpres, hhash, happ, hah, hps, has⟩
        exact ⟨hb, ⟨hpres, ⟨hhash, ⟨hps, ⟨happ, ⟨has, hah⟩⟩⟩⟩⟩⟩
      · simp [
          transportRefinementOk,
          stableWindowOk,
          toProvenanceInputs,
          TauStateAppHashProvenance.buildPacket,
          Bool.and_eq_true,
          and_assoc,
        ] at hRefine ⊢
        rcases hRefine with ⟨hb, hpres, hhash, happ, hah, hps, has, hts, hta, htp, hth, haph, haeq⟩
        exact
          ⟨hb, ⟨hpres, ⟨hhash, ⟨hps, ⟨happ, ⟨has, ⟨hah, ⟨hta, ⟨htp, ⟨hts, ⟨hth, ⟨haph, haeq⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end TauStateAppHashComposition
end TauSwap
