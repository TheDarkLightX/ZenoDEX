/-!
# ZenoDEX Tau State App-Hash Stable Window

This file formalizes the bounded host-side refinement predicates around the
stable-read window used by the Tau-state/app-hash provenance loader.
-/

namespace TauSwap
namespace TauStateAppHashStableWindow

structure Inputs where
  bridgePayloadReady : Bool
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

def stableWindowOk (inputs : Inputs) : Bool :=
  inputs.stateProofStable &&
  inputs.appStateStable &&
  (if inputs.strongBindingRequired then inputs.tauStateStable else true)

def transportRefinementOk (inputs : Inputs) : Bool :=
  inputs.bridgePayloadReady &&
  inputs.stateProofPresent &&
  inputs.stateHashPresent &&
  inputs.appStatePresent &&
  inputs.appStateHashOk &&
  stableWindowOk inputs &&
  (if inputs.strongBindingRequired then
     inputs.tauStateTransportAvailable &&
     inputs.tauStatePresent &&
     inputs.tauStateHashMatchesProof &&
     inputs.tauStateAppHashPresent &&
     inputs.tauStateAppHashMatchesAppState
   else
     true)

theorem stableWindowOk_iff (inputs : Inputs) :
    stableWindowOk inputs = true ↔
      inputs.stateProofStable = true ∧
      inputs.appStateStable = true ∧
      (inputs.strongBindingRequired = false ∨ inputs.tauStateStable = true) := by
  cases inputs with
  | mk bridgePayloadReady strongBindingRequired stateProofPresent stateHashPresent stateProofStable
      appStatePresent appStateStable appStateHashOk tauStateTransportAvailable tauStatePresent
      tauStateStable tauStateHashMatchesProof tauStateAppHashPresent tauStateAppHashMatchesAppState =>
      cases strongBindingRequired <;> simp [stableWindowOk, Bool.and_eq_true, and_assoc]

theorem transportRefinementOk_iff (inputs : Inputs) :
    transportRefinementOk inputs = true ↔
      inputs.bridgePayloadReady = true ∧
      inputs.stateProofPresent = true ∧
      inputs.stateHashPresent = true ∧
      inputs.appStatePresent = true ∧
      inputs.appStateHashOk = true ∧
      inputs.stateProofStable = true ∧
      inputs.appStateStable = true ∧
      (inputs.strongBindingRequired = false ∨
        (inputs.tauStateStable = true ∧
         inputs.tauStateTransportAvailable = true ∧
         inputs.tauStatePresent = true ∧
         inputs.tauStateHashMatchesProof = true ∧
         inputs.tauStateAppHashPresent = true ∧
         inputs.tauStateAppHashMatchesAppState = true)) := by
  cases inputs with
  | mk bridgePayloadReady strongBindingRequired stateProofPresent stateHashPresent stateProofStable
      appStatePresent appStateStable appStateHashOk tauStateTransportAvailable tauStatePresent
      tauStateStable tauStateHashMatchesProof tauStateAppHashPresent tauStateAppHashMatchesAppState =>
      cases strongBindingRequired <;> simp [transportRefinementOk, stableWindowOk, Bool.and_eq_true, and_assoc]

theorem transportRefinementOk_iff_strongBindingDisabled (inputs : Inputs)
    (hRequired : inputs.strongBindingRequired = false) :
    transportRefinementOk inputs = true ↔
      inputs.bridgePayloadReady = true ∧
      inputs.stateProofPresent = true ∧
      inputs.stateHashPresent = true ∧
      inputs.appStatePresent = true ∧
      inputs.appStateHashOk = true ∧
      inputs.stateProofStable = true ∧
      inputs.appStateStable = true := by
  cases inputs with
  | mk bridgePayloadReady strongBindingRequired stateProofPresent stateHashPresent stateProofStable
      appStatePresent appStateStable appStateHashOk tauStateTransportAvailable tauStatePresent
      tauStateStable tauStateHashMatchesProof tauStateAppHashPresent tauStateAppHashMatchesAppState =>
      cases hRequired
      simp [transportRefinementOk, stableWindowOk, Bool.and_eq_true, and_assoc]

theorem transportRefinementOk_iff_strongBindingEnabled (inputs : Inputs)
    (hRequired : inputs.strongBindingRequired = true) :
    transportRefinementOk inputs = true ↔
      inputs.bridgePayloadReady = true ∧
      inputs.stateProofPresent = true ∧
      inputs.stateHashPresent = true ∧
      inputs.appStatePresent = true ∧
      inputs.appStateHashOk = true ∧
      inputs.stateProofStable = true ∧
      inputs.appStateStable = true ∧
      inputs.tauStateStable = true ∧
      inputs.tauStateTransportAvailable = true ∧
      inputs.tauStatePresent = true ∧
      inputs.tauStateHashMatchesProof = true ∧
      inputs.tauStateAppHashPresent = true ∧
      inputs.tauStateAppHashMatchesAppState = true := by
  cases inputs with
  | mk bridgePayloadReady strongBindingRequired stateProofPresent stateHashPresent stateProofStable
      appStatePresent appStateStable appStateHashOk tauStateTransportAvailable tauStatePresent
      tauStateStable tauStateHashMatchesProof tauStateAppHashPresent tauStateAppHashMatchesAppState =>
      cases hRequired
      simp [transportRefinementOk, stableWindowOk, Bool.and_eq_true, and_assoc]

end TauStateAppHashStableWindow
end TauSwap
