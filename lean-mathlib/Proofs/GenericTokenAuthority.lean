import Mathlib.Tactic

/-!
# Generic-token registered supply authority

This module formalizes the pure per-asset supply transition used by the Python
functional core. The decision order is part of the specification: amount
validity, registration, transfer recipient rules, mint authority, then bounded
mint or burn arithmetic.

The model proves exact supply deltas, u32 closure, rejection no-op, mint
authorization prerequisites, exact asset-to-actor registry binding, and
locality of an accepted update to one asset. An exhaustive boundary vector is
compared with the Python implementation by a focused formal regression test.

The final theorem gives an unbounded composition rule for global accounted
units: exact pre-state equality plus equal supply and location deltas implies
exact post-state equality. Its subtraction-free cross-sum premise covers both
increases and decreases over natural numbers.

This module does not prove asset/pubkey text canonicalization, signatures,
runtime projection completeness, non-overlap of represented locations,
serialization, or atomic shell commit.
-/

namespace ZenoDEX.GenericTokenAuthority

def u32Max : Nat := 2 ^ 32 - 1

inductive Action where
  | transfer
  | mint
  | burn
  deriving DecidableEq, Repr

inductive DecisionCode where
  | accepted
  | invalidAmount
  | unregisteredAsset
  | recipientRequired
  | selfTransfer
  | mintDisabled
  | unauthorizedMint
  | supplyOverflow
  | supplyUnderflow
  deriving DecidableEq, Repr

structure State where
  supply : Nat
  deriving DecidableEq, Repr

structure Command where
  action : Action
  amount : Nat
  assetRegistered : Bool
  recipientPresent : Bool
  selfTransfer : Bool
  mintEnabled : Bool
  mintAuthorized : Bool
  deriving DecidableEq, Repr

structure Transition where
  accepted : Bool
  postState : State
  code : DecisionCode
  deriving DecidableEq, Repr

@[simp] def reject (preState : State) (code : DecisionCode) : Transition :=
  ⟨false, preState, code⟩

@[simp] def accept (supplyAfter : Nat) : Transition :=
  ⟨true, ⟨supplyAfter⟩, .accepted⟩

/-- Exact abstract transition matching the Python core's decision order. -/
def step (preState : State) (command : Command) : Transition :=
  if command.amount = 0 ∨ u32Max < command.amount then
    reject preState .invalidAmount
  else if !command.assetRegistered then
    reject preState .unregisteredAsset
  else
    match command.action with
    | .transfer =>
        if !command.recipientPresent then
          reject preState .recipientRequired
        else if command.selfTransfer then
          reject preState .selfTransfer
        else
          accept preState.supply
    | .mint =>
        if !command.mintEnabled then
          reject preState .mintDisabled
        else if !command.mintAuthorized then
          reject preState .unauthorizedMint
        else if preState.supply > u32Max - command.amount then
          reject preState .supplyOverflow
        else
          accept (preState.supply + command.amount)
    | .burn =>
        if command.amount > preState.supply then
          reject preState .supplyUnderflow
        else
          accept (preState.supply - command.amount)

def DecisionCode.toNat : DecisionCode → Nat
  | .accepted => 0
  | .invalidAmount => 1
  | .unregisteredAsset => 2
  | .recipientRequired => 3
  | .selfTransfer => 4
  | .mintDisabled => 5
  | .unauthorizedMint => 6
  | .supplyOverflow => 7
  | .supplyUnderflow => 8

def allActions : List Action := [.transfer, .mint, .burn]

def allBools : List Bool := [false, true]

def sampleSupplies : List Nat := [0, 1, u32Max]

def sampleAmounts : List Nat := [0, 1, 2, u32Max]

def exhaustiveCommands : List Command :=
  allActions.flatMap fun action =>
    sampleAmounts.flatMap fun amount =>
      allBools.flatMap fun assetRegistered =>
        allBools.flatMap fun recipientPresent =>
          allBools.flatMap fun selfTransfer =>
            allBools.flatMap fun mintEnabled =>
              allBools.map fun mintAuthorized =>
                ⟨action, amount, assetRegistered, recipientPresent,
                  selfTransfer, mintEnabled, mintAuthorized⟩

def exhaustiveTransitionVector : List Nat :=
  sampleSupplies.flatMap fun supply =>
    exhaustiveCommands.flatMap fun command =>
      let transition := step ⟨supply⟩ command
      [transition.code.toNat, transition.postState.supply]

def exhaustiveTransitionCSV : String :=
  String.intercalate "," (exhaustiveTransitionVector.map toString)

theorem rejection_is_exact_prestate_noop
    (preState : State) (command : Command)
    (rejected : (step preState command).accepted = false) :
    (step preState command).postState = preState := by
  cases command with
  | mk action amount assetRegistered recipientPresent selfTransfer mintEnabled mintAuthorized =>
      cases action <;>
        simp only [step] at rejected ⊢ <;>
        repeat' first | split | simp_all

theorem accepted_transfer_preserves_supply
    (preState : State) (command : Command)
    (action : command.action = .transfer)
    (accepted : (step preState command).accepted = true) :
    (step preState command).postState.supply = preState.supply := by
  simp only [step, action] at accepted ⊢
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem accepted_mint_has_exact_delta
    (preState : State) (command : Command)
    (action : command.action = .mint)
    (accepted : (step preState command).accepted = true) :
    (step preState command).postState.supply =
      preState.supply + command.amount := by
  simp only [step, action] at accepted ⊢
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem accepted_burn_has_exact_delta
    (preState : State) (command : Command)
    (action : command.action = .burn)
    (accepted : (step preState command).accepted = true) :
    (step preState command).postState.supply =
      preState.supply - command.amount := by
  simp only [step, action] at accepted ⊢
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem accepted_mint_requires_committed_authority
    (preState : State) (command : Command)
    (action : command.action = .mint)
    (accepted : (step preState command).accepted = true) :
    command.assetRegistered = true ∧
      command.mintEnabled = true ∧
      command.mintAuthorized = true := by
  simp only [step, action] at accepted
  split at accepted <;> simp_all
  split at accepted <;> simp_all
  split at accepted <;> simp_all
  split at accepted <;> simp_all

abbrev ExactAssetId := Nat
abbrev ActorId := Nat
abbrev AuthorityRegistry := ExactAssetId → Option ActorId

/-- Exact subject-bound mint request used to derive the abstract guard flags. -/
structure ExactMintCommand where
  asset : ExactAssetId
  actor : ActorId
  amount : Nat
  deriving DecidableEq, Repr

/--
Build the existing arithmetic command from one exact registry lookup. The
registration, enablement, and authorization flags are derived facts rather
than caller-supplied witnesses.
-/
def exactMintAbstractCommand
    (authorityRegistry : AuthorityRegistry) (command : ExactMintCommand) :
    Command :=
  {
    action := .mint
    amount := command.amount
    assetRegistered := (authorityRegistry command.asset).isSome
    recipientPresent := false
    selfTransfer := false
    mintEnabled := (authorityRegistry command.asset).isSome
    mintAuthorized := authorityRegistry command.asset == some command.actor
  }

def exactMintStep
    (authorityRegistry : AuthorityRegistry) (preState : State)
    (command : ExactMintCommand) : Transition :=
  step preState (exactMintAbstractCommand authorityRegistry command)

/-- Accepted mint binds the exact command asset to the exact authenticated actor. -/
theorem accepted_exact_mint_binds_registry
    (authorityRegistry : AuthorityRegistry) (preState : State)
    (command : ExactMintCommand)
    (accepted : (exactMintStep authorityRegistry preState command).accepted = true) :
    authorityRegistry command.asset = some command.actor := by
  have guards := accepted_mint_requires_committed_authority
    preState
    (exactMintAbstractCommand authorityRegistry command)
    rfl
    accepted
  simpa [exactMintAbstractCommand] using guards.2.2

theorem accepted_transition_preserves_u32_bound
    (preState : State) (command : Command)
    (preBound : preState.supply ≤ u32Max)
    (accepted : (step preState command).accepted = true) :
    (step preState command).postState.supply ≤ u32Max := by
  simp only [step] at accepted ⊢
  split <;> simp_all
  split <;> simp_all
  cases command.action <;>
    repeat' first | split | simp_all | omega

abbrev AssetId := Nat

def updateAssetSupply
    (supplies : AssetId → Nat) (target : AssetId) (supplyAfter : Nat) :
    AssetId → Nat :=
  fun asset => if asset = target then supplyAfter else supplies asset

theorem accepted_update_is_asset_local
    (supplies : AssetId → Nat) (target other : AssetId) (supplyAfter : Nat)
    (distinct : other ≠ target) :
    updateAssetSupply supplies target supplyAfter other = supplies other := by
  simp [updateAssetSupply, distinct]

theorem decision_cases_exhaustive (preState : State) (command : Command) :
    (step preState command).code = .accepted ∨
      (step preState command).code = .invalidAmount ∨
      (step preState command).code = .unregisteredAsset ∨
      (step preState command).code = .recipientRequired ∨
      (step preState command).code = .selfTransfer ∨
      (step preState command).code = .mintDisabled ∨
      (step preState command).code = .unauthorizedMint ∨
      (step preState command).code = .supplyOverflow ∨
      (step preState command).code = .supplyUnderflow := by
  simp only [step]
  split <;> simp_all
  split <;> simp_all
  cases command.action <;>
    repeat' first | split | simp_all

/-- Aggregate whole-token units across the represented protocol locations. -/
structure AccountedUnits where
  walletUnits : Nat
  poolLockedUnits : Nat
  perpsLockedUnits : Nat
  stakeLockedUnits : Nat
  deriving DecidableEq, Repr

def AccountedUnits.total (units : AccountedUnits) : Nat :=
  units.walletUnits + units.poolLockedUnits +
    units.perpsLockedUnits + units.stakeLockedUnits

/-!
The delta premise below is written as a cross-sum:

  postAccounted + preSupply = postSupply + preAccounted

This is the natural-number form of matching signed deltas and does not lose
burn cases to truncated subtraction. The theorem assumes that both accounted
totals were computed for the same asset and unit scale. It does not establish
that a runtime projection includes every location exactly once, that a
location effect is authorized, or that state and effects commit atomically.
-/

theorem global_accounting_preserved_of_matching_deltas
    (preSupply postSupply : Nat)
    (preUnits postUnits : AccountedUnits)
    (preExact : preUnits.total = preSupply)
    (matchingDelta :
      postUnits.total + preSupply = postSupply + preUnits.total) :
    postUnits.total = postSupply := by
  omega

end ZenoDEX.GenericTokenAuthority
