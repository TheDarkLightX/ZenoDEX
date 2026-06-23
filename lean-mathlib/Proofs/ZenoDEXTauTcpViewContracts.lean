/-!
# ZenoDEX Tau TCP View Contracts

This file formalizes the abstract boolean contracts for the typed Tau TCP view
builders. It does not model JSON parsing; it models the typed post-parse
conditions that must hold for the host views to be considered well-formed.
-/

namespace TauSwap
namespace TauTcpViewContracts

structure AppStateInputs where
  responseIsObject : Bool
  appHashFieldOk : Bool
  deriving DecidableEq, Repr

def appStateViewOk (inputs : AppStateInputs) : Bool :=
  inputs.responseIsObject && inputs.appHashFieldOk

theorem appStateViewOk_iff (inputs : AppStateInputs) :
    appStateViewOk inputs = true ↔
      inputs.responseIsObject = true ∧
      inputs.appHashFieldOk = true := by
  cases inputs <;> simp [appStateViewOk, Bool.and_eq_true]

structure StateProofInputs where
  responseIsObject : Bool
  presentFieldIsBool : Bool
  present : Bool
  stateHashFieldOk : Bool
  proofTypeFieldOk : Bool
  proofBytesFieldOk : Bool
  proofSha256FieldOk : Bool
  errorFieldOk : Bool
  deriving DecidableEq, Repr

def stateProofViewOk (inputs : StateProofInputs) : Bool :=
  inputs.responseIsObject &&
  inputs.presentFieldIsBool &&
  ((!inputs.present) || inputs.stateHashFieldOk) &&
  inputs.proofTypeFieldOk &&
  inputs.proofBytesFieldOk &&
  inputs.proofSha256FieldOk &&
  inputs.errorFieldOk

theorem stateProofViewOk_iff (inputs : StateProofInputs) :
    stateProofViewOk inputs = true ↔
      inputs.responseIsObject = true ∧
      inputs.presentFieldIsBool = true ∧
      (inputs.present = false ∨ inputs.stateHashFieldOk = true) ∧
      inputs.proofTypeFieldOk = true ∧
      inputs.proofBytesFieldOk = true ∧
      inputs.proofSha256FieldOk = true ∧
      inputs.errorFieldOk = true := by
  cases inputs <;> simp [stateProofViewOk, Bool.and_eq_true, Bool.or_eq_true, and_assoc]

structure TauStateInputs where
  responseIsObject : Bool
  presentFieldOk : Bool
  present : Bool
  errorFieldOk : Bool
  errorEmpty : Bool
  stateHashFieldOk : Bool
  rulesFieldIsString : Bool
  accountsHashFieldOk : Bool
  appHashFieldOk : Bool
  deriving DecidableEq, Repr

def tauStateViewOk (inputs : TauStateInputs) : Bool :=
  inputs.responseIsObject &&
  inputs.presentFieldOk &&
  inputs.present &&
  inputs.errorFieldOk &&
  inputs.errorEmpty &&
  inputs.stateHashFieldOk &&
  inputs.rulesFieldIsString &&
  inputs.accountsHashFieldOk &&
  inputs.appHashFieldOk

theorem tauStateViewOk_iff (inputs : TauStateInputs) :
    tauStateViewOk inputs = true ↔
      inputs.responseIsObject = true ∧
      inputs.presentFieldOk = true ∧
      inputs.present = true ∧
      inputs.errorFieldOk = true ∧
      inputs.errorEmpty = true ∧
      inputs.stateHashFieldOk = true ∧
      inputs.rulesFieldIsString = true ∧
      inputs.accountsHashFieldOk = true ∧
      inputs.appHashFieldOk = true := by
  cases inputs <;> simp [tauStateViewOk, Bool.and_eq_true, and_assoc]

structure ViewBundleInputs where
  strongBindingRequired : Bool
  appStateViewOk : Bool
  stateProofViewOk : Bool
  tauStateViewOk : Bool
  deriving DecidableEq, Repr

def viewContractsOk (inputs : ViewBundleInputs) : Bool :=
  inputs.appStateViewOk &&
  inputs.stateProofViewOk &&
  (if inputs.strongBindingRequired then inputs.tauStateViewOk else true)

theorem viewContractsOk_iff (inputs : ViewBundleInputs) :
    viewContractsOk inputs = true ↔
      inputs.appStateViewOk = true ∧
      inputs.stateProofViewOk = true ∧
      (inputs.strongBindingRequired = false ∨ inputs.tauStateViewOk = true) := by
  cases inputs with
  | mk strongBindingRequired appStateViewOk stateProofViewOk tauStateViewOk =>
      cases strongBindingRequired <;> simp [viewContractsOk, Bool.and_eq_true, and_assoc]

end TauTcpViewContracts
end TauSwap
