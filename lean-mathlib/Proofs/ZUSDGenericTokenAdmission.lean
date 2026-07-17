import Mathlib.Tactic

/-!
# Canonical zUSD writer-role and custody admission

This module formalizes the complete authority-only policy for canonical zUSD.
Generic token authority cannot mint or burn canonical zUSD. A generic canonical
zUSD transfer cannot target any custody class marked internal and reserved. An
ordinary user transfer is admitted and preserves canonical supply. Every
rejection returns the exact immutable prestate.

Stability Pool escrow is the only currently addressable live internal custody
principal. The additional custody constructors make future addressable reserve,
fee, perps, DEX, and bridge principals fail closed at the policy level. Runtime
registry completeness remains a separate binding obligation.

The model is an admission kernel. It does not prove authentication,
chain-derived identifier binding, registry completeness, balance arithmetic,
monetary-transition correctness, serialization, or atomic shell commit. The
test gate executes this decision table for all 108 typed cases and compares it
with the Python core and generated ESSO reference before claiming refinement.
-/

namespace ZenoDEX.ZUSDGenericTokenAdmission

inductive GenericTokenAction where
  | transfer
  | mint
  | burn
  deriving DecidableEq, Repr

inductive AssetClass where
  | canonicalZUSD
  | other
  deriving DecidableEq, Repr

inductive WriterRole where
  | genericTokenWriter
  | zusdMonetaryAuthority
  deriving DecidableEq, Repr

inductive CustodyClass where
  | ordinaryAccount
  | stabilityPoolEscrow
  | gasReserveLedger
  | protocolFeeReserveLedger
  | stakingFeePoolLedger
  | hostFeePoolLedger
  | perpsQuoteLiabilityLedger
  | dexPoolCustody
  | bridgeEscrow
  deriving DecidableEq, Repr

inductive AdmissionCode where
  | admitted
  | canonicalMintRequiresMonetaryAuthority
  | canonicalBurnRequiresMonetaryAuthority
  | canonicalReservedCustodyRequiresMonetaryAuthority
  | routeToZUSDMonetaryKernel
  deriving DecidableEq, Repr

structure Command where
  action : GenericTokenAction
  asset : AssetClass
  writerRole : WriterRole
  recipientCustody : CustodyClass
  deriving DecidableEq, Repr

structure CanonicalSupplyState where
  totalSupplyUnits : Fin (2 ^ 32)
  deriving DecidableEq, Repr

structure Transition where
  postState : CanonicalSupplyState
  code : AdmissionCode
  deriving DecidableEq, Repr

def CustodyClass.isReserved : CustodyClass → Bool
  | .ordinaryAccount => false
  | _ => true

/-- Complete authority decision for all writer, asset, action, and custody cases. -/
def decide (command : Command) : AdmissionCode :=
  match command.writerRole, command.asset, command.action,
      command.recipientCustody with
  | .zusdMonetaryAuthority, _, _, _ => .routeToZUSDMonetaryKernel
  | .genericTokenWriter, .other, _, _ => .admitted
  | .genericTokenWriter, .canonicalZUSD, .mint, _ =>
      .canonicalMintRequiresMonetaryAuthority
  | .genericTokenWriter, .canonicalZUSD, .burn, _ =>
      .canonicalBurnRequiresMonetaryAuthority
  | .genericTokenWriter, .canonicalZUSD, .transfer, .ordinaryAccount => .admitted
  | .genericTokenWriter, .canonicalZUSD, .transfer, _ =>
      .canonicalReservedCustodyRequiresMonetaryAuthority

/-- Admission is pure: account effects remain outside this policy kernel. -/
def step (preState : CanonicalSupplyState) (command : Command) : Transition :=
  { postState := preState, code := decide command }

def canonicalSupplyDelta
    (preState : CanonicalSupplyState) (transition : Transition) : Int :=
  Int.ofNat transition.postState.totalSupplyUnits.val -
    Int.ofNat preState.totalSupplyUnits.val

def AdmissionCode.toNat : AdmissionCode → Nat
  | .admitted => 0
  | .canonicalMintRequiresMonetaryAuthority => 1
  | .canonicalBurnRequiresMonetaryAuthority => 2
  | .canonicalReservedCustodyRequiresMonetaryAuthority => 3
  | .routeToZUSDMonetaryKernel => 4

def allActions : List GenericTokenAction := [.transfer, .mint, .burn]

def allAssets : List AssetClass := [.canonicalZUSD, .other]

def allWriterRoles : List WriterRole :=
  [.genericTokenWriter, .zusdMonetaryAuthority]

def allCustodyClasses : List CustodyClass :=
  [
    .ordinaryAccount,
    .stabilityPoolEscrow,
    .gasReserveLedger,
    .protocolFeeReserveLedger,
    .stakingFeePoolLedger,
    .hostFeePoolLedger,
    .perpsQuoteLiabilityLedger,
    .dexPoolCustody,
    .bridgeEscrow,
  ]

def exhaustiveCommands : List Command :=
  allActions.flatMap fun action =>
    allAssets.flatMap fun asset =>
      allWriterRoles.flatMap fun writerRole =>
        allCustodyClasses.map fun recipientCustody =>
          ⟨action, asset, writerRole, recipientCustody⟩

/-- Stable executable vector consumed by the cross-language refinement test. -/
def exhaustiveDecisionVector : List Nat :=
  exhaustiveCommands.map fun command => (decide command).toNat

/-- Non-truncating serialization used only by the executable refinement test. -/
def exhaustiveDecisionCSV : String :=
  String.intercalate "," (exhaustiveDecisionVector.map toString)

def sampleSupplyStates : List CanonicalSupplyState :=
  [
    ⟨⟨0, by norm_num⟩⟩,
    ⟨⟨1, by norm_num⟩⟩,
    ⟨⟨2 ^ 32 - 1, by norm_num⟩⟩,
  ]

/-- Boundary-supply transition vector binds decision and no-op semantics. -/
def exhaustiveTransitionVector : List Nat :=
  sampleSupplyStates.flatMap fun preState =>
    exhaustiveCommands.flatMap fun command =>
      let transition := step preState command
      [transition.code.toNat, transition.postState.totalSupplyUnits.val]

def exhaustiveTransitionCSV : String :=
  String.intercalate "," (exhaustiveTransitionVector.map toString)

theorem generic_canonical_mint_rejected (recipient : CustodyClass) :
    decide ⟨.mint, .canonicalZUSD, .genericTokenWriter, recipient⟩ =
      .canonicalMintRequiresMonetaryAuthority := by
  cases recipient <;> rfl

theorem generic_canonical_burn_rejected (recipient : CustodyClass) :
    decide ⟨.burn, .canonicalZUSD, .genericTokenWriter, recipient⟩ =
      .canonicalBurnRequiresMonetaryAuthority := by
  cases recipient <;> rfl

theorem stability_pool_transfer_rejected :
    decide ⟨.transfer, .canonicalZUSD, .genericTokenWriter,
      .stabilityPoolEscrow⟩ =
      .canonicalReservedCustodyRequiresMonetaryAuthority := rfl

theorem every_reserved_custody_rejects_generic_canonical_transfer
    (recipient : CustodyClass) (reserved : recipient.isReserved = true) :
    decide ⟨.transfer, .canonicalZUSD, .genericTokenWriter, recipient⟩ =
      .canonicalReservedCustodyRequiresMonetaryAuthority := by
  cases recipient <;> simp [CustodyClass.isReserved, decide] at reserved ⊢

theorem ordinary_canonical_transfer_admitted :
    decide ⟨.transfer, .canonicalZUSD, .genericTokenWriter,
      .ordinaryAccount⟩ = .admitted := rfl

theorem generic_canonical_admission_iff_ordinary_transfer
    (action : GenericTokenAction) (recipient : CustodyClass) :
    decide ⟨action, .canonicalZUSD, .genericTokenWriter, recipient⟩ = .admitted ↔
      action = .transfer ∧ recipient = .ordinaryAccount := by
  cases action <;> cases recipient <;> simp [decide]

theorem monetary_authority_routes_to_separate_kernel
    (action : GenericTokenAction) (asset : AssetClass) (recipient : CustodyClass) :
    decide ⟨action, asset, .zusdMonetaryAuthority, recipient⟩ =
      .routeToZUSDMonetaryKernel := by
  cases action <;> cases asset <;> cases recipient <;> rfl

theorem every_step_preserves_canonical_supply
    (preState : CanonicalSupplyState) (command : Command) :
    (step preState command).postState = preState := rfl

theorem every_step_has_zero_canonical_supply_delta
    (preState : CanonicalSupplyState) (command : Command) :
    canonicalSupplyDelta preState (step preState command) = 0 := by
  simp [canonicalSupplyDelta, step]

theorem every_rejection_is_exact_prestate_noop
    (preState : CanonicalSupplyState) (command : Command)
    (_rejected : decide command ≠ .admitted) :
    (step preState command).postState = preState := rfl

theorem decision_cases_exhaustive (command : Command) :
    decide command = .admitted ∨
      decide command = .canonicalMintRequiresMonetaryAuthority ∨
      decide command = .canonicalBurnRequiresMonetaryAuthority ∨
      decide command = .canonicalReservedCustodyRequiresMonetaryAuthority ∨
      decide command = .routeToZUSDMonetaryKernel := by
  cases command with
  | mk action asset writerRole recipient =>
      cases action <;> cases asset <;> cases writerRole <;>
        cases recipient <;> simp [decide]

end ZenoDEX.ZUSDGenericTokenAdmission
