import Proofs.AssetTransferRefinementV2

/-!
# Managed-asset lifecycle V2 bounded functional-core model

This file models `transition_managed_asset_lifecycle_v2` from
`src/core/managed_asset_lifecycle_module_v2.py` and its owned V2 values.  The
model has one registered asset, one selected account balance, a projected sum
of all account rows, and one supply value.  The paired `IssueAuthority` mirrors
the Python constructor rule that an issue subject and authorization root are
present together.

The first eighteen failures form the exact authorization prefix.  The source
then computes supply before account balance.  Consequently an issue that would
overflow both reports `SUPPLY_OVERFLOW`, even though the public enum declares
`BALANCE_OVERFLOW` first.  The theorem
`issue_supply_overflow_precedes_balance_overflow_counterexample` pins that
source-level distinction.  Burn supply and balance underflow share the one
`INSUFFICIENT_BALANCE` code.

Acceptance consumes one occurrence, emits no external outbox, uses zero
private-port, terminal-obligation, and Oracle-plan roots, and changes projected
account total and supply by the same signed amount.  The stateful witness runs
an issue, converts the accepted projection into the V2 transfer model, performs
a transfer, converts it back, and burns the transferred amount.

Roots and command-body digests are opaque equality tokens.  This model claims
no hash or codec equivalence, canonical row encoding, runtime mounting,
registry or release/profile authentication, settlement, publication,
migration, or production authority.  It is not a Python or Rust refinement
proof.  The source-pin test only makes drift visible and does not close those
composition gaps.
-/

namespace Proofs
namespace ManagedAssetLifecycleRefinementV2

abbrev Principal := AssetTransferRefinementV2.Principal
abbrev Asset := AssetTransferRefinementV2.Asset
abbrev Root := AssetTransferRefinementV2.Root
abbrev CommandKind := AssetTransferRefinementV2.CommandKind
abbrev AssetClass := AssetTransferRefinementV2.AssetClass

def issueCommandKind : CommandKind := "managed_asset_issue"
def burnCommandKind : CommandKind := "managed_asset_burn"
def productionAuthority : String := "NONE"

theorem production_authority_is_none : productionAuthority = "NONE" := rfl

/-! ## Closed rejection surface -/

inductive RejectCode where
  | missingOccurrence
  | occurrenceBindingMismatch
  | releaseMismatch
  | unknownCommand
  | occurrenceCommandMismatch
  | unknownAsset
  | disabledAsset
  | assetClassMismatch
  | assetDecimalsMismatch
  | unregisteredAsset
  | assetOriginMismatch
  | genericAuthorityForbidden
  | issueDisabled
  | burnDisabled
  | unauthorizedSubject
  | authorizationRootMismatch
  | zeroAmount
  | effectDeltaOverflow
  | insufficientBalance
  | balanceOverflow
  | supplyOverflow
  deriving DecidableEq, Repr

def RejectCode.code : RejectCode → String
  | .missingOccurrence => "MISSING_OCCURRENCE"
  | .occurrenceBindingMismatch => "OCCURRENCE_BINDING_MISMATCH"
  | .releaseMismatch => "RELEASE_MISMATCH"
  | .unknownCommand => "UNKNOWN_COMMAND"
  | .occurrenceCommandMismatch => "OCCURRENCE_COMMAND_MISMATCH"
  | .unknownAsset => "UNKNOWN_ASSET"
  | .disabledAsset => "DISABLED_ASSET"
  | .assetClassMismatch => "ASSET_CLASS_MISMATCH"
  | .assetDecimalsMismatch => "ASSET_DECIMALS_MISMATCH"
  | .unregisteredAsset => "UNREGISTERED_ASSET"
  | .assetOriginMismatch => "ASSET_ORIGIN_MISMATCH"
  | .genericAuthorityForbidden => "GENERIC_AUTHORITY_FORBIDDEN"
  | .issueDisabled => "ISSUE_DISABLED"
  | .burnDisabled => "BURN_DISABLED"
  | .unauthorizedSubject => "UNAUTHORIZED_SUBJECT"
  | .authorizationRootMismatch => "AUTHORIZATION_ROOT_MISMATCH"
  | .zeroAmount => "ZERO_AMOUNT"
  | .effectDeltaOverflow => "EFFECT_DELTA_OVERFLOW"
  | .insufficientBalance => "INSUFFICIENT_BALANCE"
  | .balanceOverflow => "BALANCE_OVERFLOW"
  | .supplyOverflow => "SUPPLY_OVERFLOW"

def RejectCode.rank : RejectCode → Nat
  | .missingOccurrence => 0
  | .occurrenceBindingMismatch => 1
  | .releaseMismatch => 2
  | .unknownCommand => 3
  | .occurrenceCommandMismatch => 4
  | .unknownAsset => 5
  | .disabledAsset => 6
  | .assetClassMismatch => 7
  | .assetDecimalsMismatch => 8
  | .unregisteredAsset => 9
  | .assetOriginMismatch => 10
  | .genericAuthorityForbidden => 11
  | .issueDisabled => 12
  | .burnDisabled => 13
  | .unauthorizedSubject => 14
  | .authorizationRootMismatch => 15
  | .zeroAmount => 16
  | .effectDeltaOverflow => 17
  | .insufficientBalance => 18
  | .balanceOverflow => 19
  | .supplyOverflow => 20

def allRejectCodes : List RejectCode :=
  [ .missingOccurrence, .occurrenceBindingMismatch, .releaseMismatch,
    .unknownCommand, .occurrenceCommandMismatch, .unknownAsset, .disabledAsset,
    .assetClassMismatch, .assetDecimalsMismatch, .unregisteredAsset,
    .assetOriginMismatch, .genericAuthorityForbidden, .issueDisabled,
    .burnDisabled, .unauthorizedSubject, .authorizationRootMismatch,
    .zeroAmount, .effectDeltaOverflow, .insufficientBalance, .balanceOverflow,
    .supplyOverflow ]

def authorizationRejectCodes : List RejectCode := allRejectCodes.take 18

def hasDuplicateCode : List RejectCode → Bool
  | [] => false
  | code :: rest => rest.contains code || hasDuplicateCode rest

theorem all_reject_codes_length : allRejectCodes.length = 21 := rfl

theorem all_reject_codes_wire_order :
    allRejectCodes.map RejectCode.code =
      [ "MISSING_OCCURRENCE", "OCCURRENCE_BINDING_MISMATCH", "RELEASE_MISMATCH",
        "UNKNOWN_COMMAND", "OCCURRENCE_COMMAND_MISMATCH", "UNKNOWN_ASSET",
        "DISABLED_ASSET", "ASSET_CLASS_MISMATCH", "ASSET_DECIMALS_MISMATCH",
        "UNREGISTERED_ASSET", "ASSET_ORIGIN_MISMATCH",
        "GENERIC_AUTHORITY_FORBIDDEN", "ISSUE_DISABLED", "BURN_DISABLED",
        "UNAUTHORIZED_SUBJECT", "AUTHORIZATION_ROOT_MISMATCH", "ZERO_AMOUNT",
        "EFFECT_DELTA_OVERFLOW", "INSUFFICIENT_BALANCE", "BALANCE_OVERFLOW",
        "SUPPLY_OVERFLOW" ] := rfl

theorem all_reject_codes_complete (code : RejectCode) : code ∈ allRejectCodes := by
  cases code <;> decide

theorem all_reject_codes_no_duplicates : hasDuplicateCode allRejectCodes = false := by
  decide

theorem RejectCode.rank_injective {a b : RejectCode} (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact absurd h (by decide)

/-! ## Owned policy, state, and command projections -/

structure IssueAuthority where
  subject : Principal
  authorizationRoot : Root
  deriving DecidableEq, Repr

structure Policy where
  asset : Asset
  assetClass : AssetClass
  assetOriginRoot : Option Root
  atomDecimals : Nat
  issueAuthority : Option IssueAuthority
  burnAuthorizationRoot : Option Root
  enabled : Bool
  deriving DecidableEq, Repr

structure LifecycleState where
  moduleReleaseId : Root
  policy : Policy
  balance : Principal → Int
  supplyAtoms : Int
  /-- Projection of the finite Python account-row sum. -/
  accountTotalAtoms : Int

structure Context where
  moduleReleaseId : Root
  globalPreStateRoot : Root
  occurrence : Option AssetTransferRefinementV2.Occurrence
  deriving DecidableEq, Repr

structure Command where
  commandKind : CommandKind
  commandBodyHash : Root
  asset : Asset
  assetClass : AssetClass
  assetOriginRoot : Option Root
  atomDecimals : Nat
  authorizationRoot : Option Root
  accountOwner : Principal
  amountAtoms : Int
  deriving DecidableEq, Repr

structure PolicyWellFormed (policy : Policy) : Prop where
  decimals : policy.atomDecimals = 8
  protocolHasNoGenericAuthority :
    policy.assetClass ≠ .registeredOrdinaryToken →
      policy.issueAuthority = none ∧ policy.burnAuthorizationRoot = none

structure StateWellFormed (state : LifecycleState) : Prop where
  balances : ∀ p : Principal, AssetTransferRefinementV2.IsU128 (state.balance p)
  supply : AssetTransferRefinementV2.IsU128 state.supplyAtoms
  accountTotal : AssetTransferRefinementV2.IsU128 state.accountTotalAtoms
  accountCover : state.accountTotalAtoms ≤ state.supplyAtoms
  policy : PolicyWellFormed state.policy

structure CommandWellFormed (command : Command) : Prop where
  amount : AssetTransferRefinementV2.IsU128 command.amountAtoms
  decimals : command.atomDecimals = 8

def isIssue (command : Command) : Prop := command.commandKind = issueCommandKind
def isBurn (command : Command) : Prop := command.commandKind = burnCommandKind

instance (command : Command) : Decidable (isIssue command) :=
  inferInstanceAs (Decidable (command.commandKind = issueCommandKind))

instance (command : Command) : Decidable (isBurn command) :=
  inferInstanceAs (Decidable (command.commandKind = burnCommandKind))

def signedAmount (command : Command) : Int :=
  if isIssue command then command.amountAtoms else -command.amountAtoms

def occurrencePasses (ctx : Context) (predicate : AssetTransferRefinementV2.Occurrence → Prop) : Prop :=
  match ctx.occurrence with
  | none => True
  | some occurrence => predicate occurrence

instance occurrencePassesDecidable (ctx : Context)
    (predicate : AssetTransferRefinementV2.Occurrence → Prop) [DecidablePred predicate] :
    Decidable (occurrencePasses ctx predicate) := by
  cases h : ctx.occurrence with
  | none => exact isTrue (by simp [occurrencePasses, h])
  | some occurrence =>
      simpa [occurrencePasses, h] using (inferInstance : Decidable (predicate occurrence))

def originRegistered (pre : LifecycleState) (command : Command) : Prop :=
  pre.policy.assetOriginRoot.isSome = true ∧ command.assetOriginRoot.isSome = true

instance originRegisteredDecidable (pre : LifecycleState) (command : Command) :
    Decidable (originRegistered pre command) :=
  inferInstanceAs (Decidable
    (pre.policy.assetOriginRoot.isSome = true ∧ command.assetOriginRoot.isSome = true))

def expectedAuthorizationRoot (policy : Policy) (command : Command) : Option Root :=
  if isIssue command then policy.issueAuthority.map IssueAuthority.authorizationRoot
  else policy.burnAuthorizationRoot

def effectDeltaAdmitted (command : Command) : Prop :=
  if isIssue command then command.amountAtoms ≤ AssetTransferRefinementV2.i128Max
  else command.amountAtoms ≤ -AssetTransferRefinementV2.i128Min

instance (command : Command) : Decidable (effectDeltaAdmitted command) := by
  unfold effectDeltaAdmitted
  infer_instance

/-! ## Fixed authorization prefix and source-ordered post checks -/

def guardPasses (ctx : Context) (pre : LifecycleState) (command : Command) :
    RejectCode → Prop
  | .missingOccurrence => ctx.occurrence ≠ none
  | .occurrenceBindingMismatch => occurrencePasses ctx fun occurrence =>
      occurrence.preStateRoot = ctx.globalPreStateRoot ∧ occurrence.consumedObjectIds = []
  | .releaseMismatch => ctx.moduleReleaseId = pre.moduleReleaseId
  | .unknownCommand => isIssue command ∨ isBurn command
  | .occurrenceCommandMismatch => occurrencePasses ctx fun occurrence =>
      occurrence.commandKind = command.commandKind ∧
      occurrence.commandBodyHash = command.commandBodyHash
  | .unknownAsset => command.asset = pre.policy.asset
  | .disabledAsset => pre.policy.enabled = true
  | .assetClassMismatch => command.assetClass = pre.policy.assetClass
  | .assetDecimalsMismatch => command.atomDecimals = pre.policy.atomDecimals
  | .unregisteredAsset => originRegistered pre command
  | .assetOriginMismatch => command.assetOriginRoot = pre.policy.assetOriginRoot
  | .genericAuthorityForbidden => pre.policy.assetClass = .registeredOrdinaryToken
  | .issueDisabled => ¬ isIssue command ∨ pre.policy.issueAuthority.isSome = true
  | .burnDisabled => ¬ isBurn command ∨ pre.policy.burnAuthorizationRoot.isSome = true
  | .unauthorizedSubject => occurrencePasses ctx fun occurrence =>
      if isIssue command then
        pre.policy.issueAuthority.map IssueAuthority.subject = some occurrence.subjectId
      else occurrence.subjectId = command.accountOwner
  | .authorizationRootMismatch => occurrencePasses ctx fun occurrence =>
      some occurrence.grantRoot = expectedAuthorizationRoot pre.policy command ∧
      command.authorizationRoot = expectedAuthorizationRoot pre.policy command
  | .zeroAmount => command.amountAtoms ≠ 0
  | .effectDeltaOverflow => effectDeltaAdmitted command
  | .insufficientBalance => True
  | .balanceOverflow => True
  | .supplyOverflow => True

instance guardPassesDecidable (ctx : Context) (pre : LifecycleState) (command : Command) :
    DecidablePred (guardPasses ctx pre command)
  | .missingOccurrence => inferInstanceAs (Decidable (ctx.occurrence ≠ none))
  | .occurrenceBindingMismatch => inferInstanceAs (Decidable (occurrencePasses ctx fun o =>
      o.preStateRoot = ctx.globalPreStateRoot ∧ o.consumedObjectIds = []))
  | .releaseMismatch => inferInstanceAs (Decidable (ctx.moduleReleaseId = pre.moduleReleaseId))
  | .unknownCommand => inferInstanceAs (Decidable (isIssue command ∨ isBurn command))
  | .occurrenceCommandMismatch => inferInstanceAs (Decidable (occurrencePasses ctx fun o =>
      o.commandKind = command.commandKind ∧ o.commandBodyHash = command.commandBodyHash))
  | .unknownAsset => inferInstanceAs (Decidable (command.asset = pre.policy.asset))
  | .disabledAsset => inferInstanceAs (Decidable (pre.policy.enabled = true))
  | .assetClassMismatch => inferInstanceAs (Decidable (command.assetClass = pre.policy.assetClass))
  | .assetDecimalsMismatch => inferInstanceAs (Decidable (command.atomDecimals = pre.policy.atomDecimals))
  | .unregisteredAsset => inferInstanceAs (Decidable (originRegistered pre command))
  | .assetOriginMismatch => inferInstanceAs
      (Decidable (command.assetOriginRoot = pre.policy.assetOriginRoot))
  | .genericAuthorityForbidden => inferInstanceAs
      (Decidable
        (pre.policy.assetClass =
          AssetTransferRefinementV2.AssetClass.registeredOrdinaryToken))
  | .issueDisabled => inferInstanceAs
      (Decidable (¬ isIssue command ∨ pre.policy.issueAuthority.isSome = true))
  | .burnDisabled => inferInstanceAs
      (Decidable (¬ isBurn command ∨ pre.policy.burnAuthorizationRoot.isSome = true))
  | .unauthorizedSubject => inferInstanceAs (Decidable (occurrencePasses ctx fun o =>
      if isIssue command then
        pre.policy.issueAuthority.map IssueAuthority.subject = some o.subjectId
      else o.subjectId = command.accountOwner))
  | .authorizationRootMismatch => inferInstanceAs (Decidable (occurrencePasses ctx fun o =>
      some o.grantRoot = expectedAuthorizationRoot pre.policy command ∧
      command.authorizationRoot = expectedAuthorizationRoot pre.policy command))
  | .zeroAmount => inferInstanceAs (Decidable (command.amountAtoms ≠ 0))
  | .effectDeltaOverflow => inferInstanceAs (Decidable (effectDeltaAdmitted command))
  | .insufficientBalance => inferInstanceAs (Decidable True)
  | .balanceOverflow => inferInstanceAs (Decidable True)
  | .supplyOverflow => inferInstanceAs (Decidable True)

def firstFailing (g : RejectCode → Prop) [DecidablePred g] : List RejectCode → Option RejectCode
  | [] => none
  | code :: rest => if g code then firstFailing g rest else some code

def postStageRejectCode (pre : LifecycleState) (command : Command) : Option RejectCode :=
  if isIssue command then
    if pre.supplyAtoms > AssetTransferRefinementV2.u128Max - command.amountAtoms then some .supplyOverflow
    else if pre.balance command.accountOwner > AssetTransferRefinementV2.u128Max - command.amountAtoms then
      some .balanceOverflow
    else none
  else
    if pre.supplyAtoms < command.amountAtoms then some .insufficientBalance
    else if pre.balance command.accountOwner < command.amountAtoms then
      some .insufficientBalance
    else none

def rejectCode (ctx : Context) (pre : LifecycleState) (command : Command) :
    Option RejectCode :=
  match firstFailing (guardPasses ctx pre command) authorizationRejectCodes with
  | some code => some code
  | none => postStageRejectCode pre command

/-! ## Exact authorization-prefix precedence -/

theorem firstFailing_eq_none_iff (g : RejectCode → Prop) [DecidablePred g] :
    ∀ codes : List RejectCode, firstFailing g codes = none ↔ ∀ c ∈ codes, g c
  | [] => by simp [firstFailing]
  | c :: rest => by
      constructor
      · intro h c' hc'
        by_cases hg : g c
        · simp only [firstFailing, if_pos hg] at h
          rcases List.mem_cons.mp hc' with rfl | hmem
          · exact hg
          · exact (firstFailing_eq_none_iff g rest).mp h c' hmem
        · simp [firstFailing, if_neg hg] at h
      · intro h
        have hg : g c := h c List.mem_cons_self
        simp only [firstFailing, if_pos hg]
        exact (firstFailing_eq_none_iff g rest).mpr
          (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

def RankSorted : List RejectCode → Prop
  | [] => True
  | code :: rest => (∀ later ∈ rest, code.rank < later.rank) ∧ RankSorted rest

instance RankSorted.decidable : ∀ codes : List RejectCode, Decidable (RankSorted codes)
  | [] => inferInstanceAs (Decidable True)
  | _ :: rest =>
      have : Decidable (RankSorted rest) := RankSorted.decidable rest
      inferInstanceAs (Decidable (_ ∧ RankSorted rest))

theorem authorization_codes_rank_sorted : RankSorted authorizationRejectCodes := by decide

theorem authorization_codes_complete {code : RejectCode} (h : code.rank < 18) :
    code ∈ authorizationRejectCodes := by
  cases code <;> simp_all [RejectCode.rank, authorizationRejectCodes, allRejectCodes]

theorem firstFailing_some_spec (g : RejectCode → Prop) [DecidablePred g] :
    ∀ (codes : List RejectCode) (code : RejectCode), RankSorted codes →
      firstFailing g codes = some code →
        code ∈ codes ∧ ¬ g code ∧
          ∀ earlier ∈ codes, earlier.rank < code.rank → g earlier
  | [], _, _, h => by simp [firstFailing] at h
  | head :: rest, code, hs, h => by
      by_cases hg : g head
      · simp only [firstFailing, if_pos hg] at h
        obtain ⟨hmem, hnot, hbefore⟩ := firstFailing_some_spec g rest code hs.2 h
        refine ⟨List.mem_cons_of_mem head hmem, hnot, ?_⟩
        intro earlier hearlier hlt
        rcases List.mem_cons.mp hearlier with rfl | hearlier
        · exact hg
        · exact hbefore earlier hearlier hlt
      · simp only [firstFailing, if_neg hg, Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_self, hg, ?_⟩
        intro earlier hearlier hlt
        rcases List.mem_cons.mp hearlier with rfl | hearlier
        · omega
        · have := hs.1 earlier hearlier
          omega

theorem firstFailing_some_of (g : RejectCode → Prop) [DecidablePred g]
    (codes : List RejectCode) (hs : RankSorted codes) (code : RejectCode)
    (hmem : code ∈ codes) (hnot : ¬ g code)
    (hbefore : ∀ earlier ∈ codes, earlier.rank < code.rank → g earlier) :
    firstFailing g codes = some code := by
  cases hf : firstFailing g codes with
  | none => exact absurd ((firstFailing_eq_none_iff g codes).mp hf code hmem) hnot
  | some found =>
      obtain ⟨hfound, hfoundNot, hfoundBefore⟩ :=
        firstFailing_some_spec g codes found hs hf
      by_cases h1 : found.rank < code.rank
      · exact absurd (hbefore found hfound h1) hfoundNot
      · by_cases h2 : code.rank < found.rank
        · exact absurd (hfoundBefore code hmem h2) hnot
        · have heq : found.rank = code.rank := by omega
          rw [RejectCode.rank_injective heq]

theorem authorization_reject_exact_precedence
    (ctx : Context) (pre : LifecycleState) (command : Command)
    (code : RejectCode) (hcode : code.rank < 18) :
    firstFailing (guardPasses ctx pre command) authorizationRejectCodes = some code ↔
      ¬ guardPasses ctx pre command code ∧
      ∀ earlier, earlier.rank < code.rank → guardPasses ctx pre command earlier := by
  constructor
  · intro h
    obtain ⟨_, hnot, hbefore⟩ :=
      firstFailing_some_spec _ authorizationRejectCodes code
        authorization_codes_rank_sorted h
    exact ⟨hnot, fun earlier hlt =>
      hbefore earlier (authorization_codes_complete (by omega)) hlt⟩
  · intro h
    exact firstFailing_some_of _ authorizationRejectCodes authorization_codes_rank_sorted
      code (authorization_codes_complete hcode) h.1 (fun earlier _ hlt => h.2 earlier hlt)

theorem reject_code_none_parts (ctx : Context) (pre : LifecycleState)
    (command : Command) :
    rejectCode ctx pre command = none ↔
      (∀ code ∈ authorizationRejectCodes, guardPasses ctx pre command code) ∧
      postStageRejectCode pre command = none := by
  unfold rejectCode
  cases h : firstFailing (guardPasses ctx pre command) authorizationRejectCodes with
  | none =>
      exact ⟨
        fun hpost => ⟨(firstFailing_eq_none_iff _ _).mp h, hpost⟩,
        fun pair => pair.2
      ⟩
  | some code =>
      constructor
      · intro impossible
        simp at impossible
      · intro pair
        have hall := (firstFailing_eq_none_iff _ _).mpr pair.1
        rw [h] at hall
        cases hall

theorem issue_supply_overflow_precedes_balance_overflow
    (pre : LifecycleState) (command : Command) (hissue : isIssue command)
    (hsupply : pre.supplyAtoms > AssetTransferRefinementV2.u128Max - command.amountAtoms) :
    postStageRejectCode pre command = some .supplyOverflow := by
  simp [postStageRejectCode, hissue, hsupply]

/-! ## Accepted state, effects, totality, and rejection no-op -/

def acceptedState (pre : LifecycleState) (command : Command) : LifecycleState :=
  { pre with
    balance := fun principal =>
      if principal = command.accountOwner then
        pre.balance principal + signedAmount command
      else pre.balance principal
    supplyAtoms := pre.supplyAtoms + signedAmount command
    accountTotalAtoms := pre.accountTotalAtoms + signedAmount command }

inductive SupplyEffectKind where
  | issue
  | burn
  deriving DecidableEq, Repr

structure LifecyclePayload where
  accountOwner : Principal
  accountDeltaAtoms : Int
  supplyKind : SupplyEffectKind
  supplyDeltaAtoms : Int
  conservation : AssetTransferRefinementV2.ConservationRow
  deriving DecidableEq, Repr

structure RootModel where
  stateRoot : LifecycleState → Root

def lifecyclePayload (pre : LifecycleState) (command : Command) : LifecyclePayload :=
  let issueAtoms := if isIssue command then command.amountAtoms else 0
  let burnAtoms := if isIssue command then 0 else command.amountAtoms
  { accountOwner := command.accountOwner
    accountDeltaAtoms := signedAmount command
    supplyKind := if isIssue command then .issue else .burn
    supplyDeltaAtoms := signedAmount command
    conservation :=
      ⟨pre.accountTotalAtoms, pre.accountTotalAtoms + signedAmount command,
        pre.supplyAtoms, pre.supplyAtoms + signedAmount command,
        issueAtoms, burnAtoms⟩ }

def occurrenceIds (ctx : Context) : List Root :=
  match ctx.occurrence with
  | none => []
  | some occurrence => [occurrence.occurrenceId]

def acceptedEffects (roots : RootModel) (ctx : Context) (pre : LifecycleState)
    (command : Command) : AssetTransferRefinementV2.EffectEnvelope LifecyclePayload :=
  { payload := some (lifecyclePayload pre command)
    laneWrites := [⟨roots.stateRoot pre, roots.stateRoot (acceptedState pre command)⟩]
    occurrenceConsumptions := occurrenceIds ctx
    externalOutbox := []
    externalRoots := AssetTransferRefinementV2.ExternalRoots.zero }

inductive Verdict where
  | accepted
  | rejected (code : RejectCode)
  deriving DecidableEq, Repr

structure TransitionResult where
  verdict : Verdict
  post : LifecycleState
  effects : AssetTransferRefinementV2.EffectEnvelope LifecyclePayload

def reject (code : RejectCode) (pre : LifecycleState) : TransitionResult :=
  ⟨.rejected code, pre, AssetTransferRefinementV2.EffectEnvelope.empty⟩

def transition (roots : RootModel) (ctx : Context)
    (pre : LifecycleState) (command : Command) : TransitionResult :=
  match rejectCode ctx pre command with
  | some code => reject code pre
  | none => ⟨.accepted, acceptedState pre command, acceptedEffects roots ctx pre command⟩

theorem transition_total (roots : RootModel) (ctx : Context)
    (pre : LifecycleState) (command : Command) :
    (∃ code, rejectCode ctx pre command = some code ∧
      transition roots ctx pre command = reject code pre) ∨
    (rejectCode ctx pre command = none ∧
      transition roots ctx pre command =
        ⟨.accepted, acceptedState pre command, acceptedEffects roots ctx pre command⟩) := by
  unfold transition
  cases h : rejectCode ctx pre command with
  | none => exact Or.inr ⟨rfl, rfl⟩
  | some code => exact Or.inl ⟨code, rfl, rfl⟩

theorem accepted_iff_no_reject (roots : RootModel) (ctx : Context)
    (pre : LifecycleState) (command : Command) :
    (transition roots ctx pre command).verdict = .accepted ↔
      rejectCode ctx pre command = none := by
  rcases transition_total roots ctx pre command with ⟨code, hc, heq⟩ | ⟨hn, heq⟩
  · rw [heq, hc]
    simp [reject]
  · rw [heq, hn]
    simp

theorem rejected_post_eq_pre {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command} {code : RejectCode}
    (h : (transition roots ctx pre command).verdict = .rejected code) :
    (transition roots ctx pre command).post = pre := by
  rcases transition_total roots ctx pre command with ⟨code', -, heq⟩ | ⟨-, heq⟩
  · rw [heq]
    rfl
  · rw [heq] at h
    simp at h

theorem rejected_effects_empty {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command} {code : RejectCode}
    (h : (transition roots ctx pre command).verdict = .rejected code) :
    (transition roots ctx pre command).effects = AssetTransferRefinementV2.EffectEnvelope.empty := by
  rcases transition_total roots ctx pre command with ⟨code', -, heq⟩ | ⟨-, heq⟩
  · rw [heq]
    rfl
  · rw [heq] at h
    simp at h

theorem accepted_post_and_effects {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command}
    (h : (transition roots ctx pre command).verdict = .accepted) :
    (transition roots ctx pre command).post = acceptedState pre command ∧
    (transition roots ctx pre command).effects = acceptedEffects roots ctx pre command := by
  rcases transition_total roots ctx pre command with ⟨code, -, heq⟩ | ⟨-, heq⟩
  · rw [heq] at h
    simp [reject] at h
  · rw [heq]
    exact ⟨rfl, rfl⟩

theorem accepted_authorization_guard {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command}
    (h : (transition roots ctx pre command).verdict = .accepted)
    {code : RejectCode} (hmem : code ∈ authorizationRejectCodes) :
    guardPasses ctx pre command code := by
  have hn := (accepted_iff_no_reject roots ctx pre command).mp h
  exact (reject_code_none_parts ctx pre command).mp hn |>.1 code hmem

theorem accepted_consumes_exact_occurrence {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command}
    (h : (transition roots ctx pre command).verdict = .accepted) :
    ∃ occurrence, ctx.occurrence = some occurrence ∧
      (transition roots ctx pre command).effects.occurrenceConsumptions =
        [occurrence.occurrenceId] := by
  have hp := accepted_post_and_effects h
  have hm := accepted_authorization_guard h
    (code := RejectCode.missingOccurrence) (by decide)
  cases ho : ctx.occurrence with
  | none => simp [guardPasses, ho] at hm
  | some occurrence =>
      refine ⟨occurrence, rfl, ?_⟩
      rw [hp.2]
      simp [acceptedEffects, occurrenceIds, ho]

theorem accepted_zero_external_roots {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command}
    (h : (transition roots ctx pre command).verdict = .accepted) :
    (transition roots ctx pre command).effects.externalRoots =
      AssetTransferRefinementV2.ExternalRoots.zero ∧
    (transition roots ctx pre command).effects.externalOutbox = [] := by
  rw [(accepted_post_and_effects h).2]
  exact ⟨rfl, rfl⟩

theorem accepted_conservation_equations {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command}
    (h : (transition roots ctx pre command).verdict = .accepted) :
    (transition roots ctx pre command).post.accountTotalAtoms =
        pre.accountTotalAtoms + signedAmount command ∧
    (transition roots ctx pre command).post.supplyAtoms =
        pre.supplyAtoms + signedAmount command ∧
    (transition roots ctx pre command).effects.payload.map
      (fun payload => payload.conservation) =
      some ⟨pre.accountTotalAtoms, pre.accountTotalAtoms + signedAmount command,
        pre.supplyAtoms, pre.supplyAtoms + signedAmount command,
        (if isIssue command then command.amountAtoms else 0),
        (if isIssue command then 0 else command.amountAtoms)⟩ := by
  rw [(accepted_post_and_effects h).1, (accepted_post_and_effects h).2]
  exact ⟨rfl, rfl, rfl⟩

theorem accepted_effect_delta_i128 {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command}
    (hcmd : CommandWellFormed command)
    (h : (transition roots ctx pre command).verdict = .accepted) :
    AssetTransferRefinementV2.IsI128 (signedAmount command) := by
  have hwidth : effectDeltaAdmitted command :=
    accepted_authorization_guard h (code := RejectCode.effectDeltaOverflow) (by decide)
  unfold AssetTransferRefinementV2.IsI128 signedAmount
  by_cases hissue : isIssue command
  · rw [if_pos hissue]
    unfold effectDeltaAdmitted at hwidth
    rw [if_pos hissue] at hwidth
    have hnonneg := hcmd.amount.1
    unfold AssetTransferRefinementV2.i128Min AssetTransferRefinementV2.i128Max at *
    exact ⟨by omega, hwidth⟩
  · rw [if_neg hissue]
    have hnonneg := hcmd.amount.1
    unfold effectDeltaAdmitted at hwidth
    rw [if_neg hissue] at hwidth
    unfold AssetTransferRefinementV2.i128Min AssetTransferRefinementV2.i128Max at *
    exact ⟨by omega, by omega⟩

theorem accepted_post_supply_u128 {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command}
    (hpre : StateWellFormed pre) (hcmd : CommandWellFormed command)
    (h : (transition roots ctx pre command).verdict = .accepted) :
    AssetTransferRefinementV2.IsU128 (transition roots ctx pre command).post.supplyAtoms := by
  rw [(accepted_post_and_effects h).1]
  have hn := (accepted_iff_no_reject roots ctx pre command).mp h
  have hparts := (reject_code_none_parts ctx pre command).mp hn
  have hpost := hparts.2
  have hkind := hparts.1 RejectCode.unknownCommand (by decide)
  unfold guardPasses at hkind
  unfold postStageRejectCode at hpost
  change AssetTransferRefinementV2.IsU128
    (pre.supplyAtoms + signedAmount command)
  unfold signedAmount AssetTransferRefinementV2.IsU128
  by_cases hissue : isIssue command
  · rw [if_pos hissue]
    simp [hissue] at hpost
    have hsupplyGuard : ¬
        (AssetTransferRefinementV2.u128Max - command.amountAtoms < pre.supplyAtoms) := by
      intro hbad
      rw [if_pos hbad] at hpost
      contradiction
    have hs := hpre.supply
    have ha := hcmd.amount
    unfold AssetTransferRefinementV2.IsU128 at hs ha
    omega
  · rw [if_neg hissue]
    have hburn : isBurn command := hkind.resolve_left hissue
    simp [hissue] at hpost
    have hsupplyGuard : ¬ (pre.supplyAtoms < command.amountAtoms) := by
      intro hbad
      rw [if_pos hbad] at hpost
      contradiction
    have hs := hpre.supply
    have ha := hcmd.amount
    unfold AssetTransferRefinementV2.IsU128 at hs ha
    omega

theorem accepted_post_selected_balance_u128 {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command}
    (hpre : StateWellFormed pre) (hcmd : CommandWellFormed command)
    (h : (transition roots ctx pre command).verdict = .accepted) :
    AssetTransferRefinementV2.IsU128
      ((transition roots ctx pre command).post.balance command.accountOwner) := by
  rw [(accepted_post_and_effects h).1]
  have hn := (accepted_iff_no_reject roots ctx pre command).mp h
  have hparts := (reject_code_none_parts ctx pre command).mp hn
  have hpost := hparts.2
  have hkind := hparts.1 RejectCode.unknownCommand (by decide)
  unfold guardPasses at hkind
  unfold postStageRejectCode at hpost
  unfold acceptedState
  simp only [eq_self, if_true]
  change AssetTransferRefinementV2.IsU128
    (pre.balance command.accountOwner + signedAmount command)
  unfold signedAmount AssetTransferRefinementV2.IsU128
  by_cases hissue : isIssue command
  · rw [if_pos hissue]
    simp [hissue] at hpost
    have hsupplyGuard : ¬
        (AssetTransferRefinementV2.u128Max - command.amountAtoms < pre.supplyAtoms) := by
      intro hbad
      rw [if_pos hbad] at hpost
      contradiction
    have hbalanceGuard : ¬
        (AssetTransferRefinementV2.u128Max - command.amountAtoms <
          pre.balance command.accountOwner) := by
      intro hbad
      rw [if_neg hsupplyGuard, if_pos hbad] at hpost
      contradiction
    have hb := hpre.balances command.accountOwner
    have ha := hcmd.amount
    unfold AssetTransferRefinementV2.IsU128 at hb ha
    omega
  · rw [if_neg hissue]
    have hburn : isBurn command := hkind.resolve_left hissue
    simp [hissue] at hpost
    have hsupplyGuard : ¬ (pre.supplyAtoms < command.amountAtoms) := by
      intro hbad
      rw [if_pos hbad] at hpost
      contradiction
    have hbalanceGuard : ¬
        (pre.balance command.accountOwner < command.amountAtoms) := by
      intro hbad
      rw [if_neg hsupplyGuard, if_pos hbad] at hpost
      contradiction
    have hb := hpre.balances command.accountOwner
    have ha := hcmd.amount
    unfold AssetTransferRefinementV2.IsU128 at hb ha
    omega

/-! ## Exact issue/burn authorization and protocol exclusion -/

theorem accepted_issue_authority_exact {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command}
    (hissue : isIssue command)
    (h : (transition roots ctx pre command).verdict = .accepted) :
    ∃ occurrence authority,
      ctx.occurrence = some occurrence ∧
      pre.policy.issueAuthority = some authority ∧
      occurrence.subjectId = authority.subject ∧
      occurrence.grantRoot = authority.authorizationRoot ∧
      command.authorizationRoot = some authority.authorizationRoot := by
  have hm := accepted_authorization_guard h
    (code := RejectCode.missingOccurrence) (by decide)
  have hi := accepted_authorization_guard h
    (code := RejectCode.issueDisabled) (by decide)
  have hu := accepted_authorization_guard h
    (code := RejectCode.unauthorizedSubject) (by decide)
  have hr := accepted_authorization_guard h
    (code := RejectCode.authorizationRootMismatch) (by decide)
  change (¬ isIssue command ∨ pre.policy.issueAuthority.isSome = true) at hi
  have hisome : pre.policy.issueAuthority.isSome = true := by
    rcases hi with hnot | hisome
    · exact absurd hissue hnot
    · exact hisome
  cases ho : ctx.occurrence with
  | none => simp [guardPasses, ho] at hm
  | some occurrence =>
      cases ha : pre.policy.issueAuthority with
      | none => simp [ha] at hisome
      | some authority =>
          simp [guardPasses, occurrencePasses, ho, hissue, ha,
            expectedAuthorizationRoot] at hu hr
          refine ⟨occurrence, authority, rfl, rfl, ?_, ?_, ?_⟩
          · exact hu.symm
          · exact hr.1
          · exact hr.2

theorem accepted_burn_authority_exact {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command}
    (hburn : isBurn command)
    (h : (transition roots ctx pre command).verdict = .accepted) :
    ∃ occurrence authorizationRoot,
      ctx.occurrence = some occurrence ∧
      pre.policy.burnAuthorizationRoot = some authorizationRoot ∧
      occurrence.subjectId = command.accountOwner ∧
      occurrence.grantRoot = authorizationRoot ∧
      command.authorizationRoot = some authorizationRoot := by
  have hm := accepted_authorization_guard h
    (code := RejectCode.missingOccurrence) (by decide)
  have hb := accepted_authorization_guard h
    (code := RejectCode.burnDisabled) (by decide)
  have hu := accepted_authorization_guard h
    (code := RejectCode.unauthorizedSubject) (by decide)
  have hr := accepted_authorization_guard h
    (code := RejectCode.authorizationRootMismatch) (by decide)
  have hnotIssue : ¬ isIssue command := by
    intro hissue
    unfold isIssue at hissue
    unfold isBurn at hburn
    rw [hissue] at hburn
    exact (by decide : issueCommandKind ≠ burnCommandKind) hburn
  change (¬ isBurn command ∨ pre.policy.burnAuthorizationRoot.isSome = true) at hb
  have hisome : pre.policy.burnAuthorizationRoot.isSome = true := by
    rcases hb with hnot | hisome
    · exact absurd hburn hnot
    · exact hisome
  cases ho : ctx.occurrence with
  | none => simp [guardPasses, ho] at hm
  | some occurrence =>
      cases hroot : pre.policy.burnAuthorizationRoot with
      | none => simp [hroot] at hisome
      | some authorizationRoot =>
          simp [guardPasses, occurrencePasses, ho, hnotIssue,
            expectedAuthorizationRoot, hroot] at hu hr
          refine ⟨occurrence, authorizationRoot, rfl, rfl, ?_, ?_, ?_⟩
          · exact hu
          · exact hr.1
          · exact hr.2

theorem protocol_asset_cannot_be_accepted {roots : RootModel} {ctx : Context}
    {pre : LifecycleState} {command : Command}
    (hclass : pre.policy.assetClass ≠ .registeredOrdinaryToken) :
    (transition roots ctx pre command).verdict ≠ .accepted := by
  intro h
  have hgeneric := accepted_authorization_guard h
    (code := RejectCode.genericAuthorityForbidden) (by decide)
  exact hclass hgeneric

/-! ## Coordinator managed projection and generic envelope rebind -/

def replaceManaged
    (pre : AssetTransferRefinementV2.AssetLaneAggregate LifecycleState) (post : LifecycleState)
    (postAggregateRoot : Root) : AssetTransferRefinementV2.AssetLaneAggregate LifecycleState :=
  { transferProjection := pre.transferProjection
    otherProjection := post
    aggregateRoot := postAggregateRoot }

theorem coordinator_managed_projection_preserves_transfer
    (pre : AssetTransferRefinementV2.AssetLaneAggregate LifecycleState) (post : LifecycleState)
    (postRoot : Root) :
    (replaceManaged pre post postRoot).otherProjection = post ∧
    (replaceManaged pre post postRoot).transferProjection = pre.transferProjection := by
  exact ⟨rfl, rfl⟩

theorem coordinator_managed_projection_and_rebind
    (pre : AssetTransferRefinementV2.AssetLaneAggregate LifecycleState) (post : LifecycleState)
    (postRoot : Root) (leaf : AssetTransferRefinementV2.EffectEnvelope LifecyclePayload) :
    (replaceManaged pre post postRoot).otherProjection = post ∧
    (replaceManaged pre post postRoot).transferProjection = pre.transferProjection ∧
    (AssetTransferRefinementV2.rebindLane pre.aggregateRoot postRoot leaf).laneWrites =
      [⟨pre.aggregateRoot, postRoot⟩] ∧
    (AssetTransferRefinementV2.rebindLane pre.aggregateRoot postRoot leaf).occurrenceConsumptions =
      leaf.occurrenceConsumptions ∧
    (AssetTransferRefinementV2.rebindLane pre.aggregateRoot postRoot leaf).externalOutbox = [] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Stateful and adversarial witnesses -/

def ledger : List (Principal × Int) → Principal → Int := AssetTransferRefinementV2.ledger

def ordinaryPolicy : Policy :=
  { asset := "ORD"
    assetClass := .registeredOrdinaryToken
    assetOriginRoot := some "origin-ord"
    atomDecimals := 8
    issueAuthority := some ⟨"issuer", "issue-grant"⟩
    burnAuthorizationRoot := some "burn-grant"
    enabled := true }

def baseState : LifecycleState :=
  { moduleReleaseId := "release-v2"
    policy := ordinaryPolicy
    balance := ledger []
    supplyAtoms := 0
    accountTotalAtoms := 0 }

def occurrence (kind body subject grant occurrenceId : String) : AssetTransferRefinementV2.Occurrence :=
  { preStateRoot := "global-pre"
    consumedObjectIds := []
    commandKind := kind
    commandBodyHash := body
    subjectId := subject
    grantRoot := grant
    occurrenceId := occurrenceId }

def contextFor (occ : AssetTransferRefinementV2.Occurrence) : Context :=
  { moduleReleaseId := "release-v2"
    globalPreStateRoot := "global-pre"
    occurrence := some occ }

def issueCommand : Command :=
  { commandKind := issueCommandKind
    commandBodyHash := "issue-body"
    asset := "ORD"
    assetClass := .registeredOrdinaryToken
    assetOriginRoot := some "origin-ord"
    atomDecimals := 8
    authorizationRoot := some "issue-grant"
    accountOwner := "alice"
    amountAtoms := 100 }

def issueContext : Context :=
  contextFor (occurrence issueCommandKind "issue-body" "issuer" "issue-grant" "occ-issue")

def lifecycleRoots : RootModel :=
  ⟨fun state => toString state.accountTotalAtoms ++ ":" ++ toString state.supplyAtoms⟩

def issueResult : TransitionResult := transition lifecycleRoots issueContext baseState issueCommand
def issuedState : LifecycleState := issueResult.post

def transferPolicy : AssetTransferRefinementV2.Policy :=
  { asset := "ORD"
    feeOwner := "treasury"
    transferFeeAtoms := 0
    enabled := true
    assetClass := .registeredOrdinaryToken
    assetOriginRoot := some "origin-ord"
    atomDecimals := 8 }

def transferState : AssetTransferRefinementV2.TransferState :=
  { moduleReleaseId := issuedState.moduleReleaseId
    policy := transferPolicy
    balance := issuedState.balance
    supplyAtoms := issuedState.supplyAtoms
    accountTotalAtoms := issuedState.accountTotalAtoms }

def transferCommand : AssetTransferRefinementV2.Command :=
  { commandKind := AssetTransferRefinementV2.assetTransferCommandKind
    commandBodyHash := "transfer-body"
    asset := "ORD"
    sender := "alice"
    recipient := "bob"
    amountAtoms := 40
    maxFeeAtoms := 0
    assetOriginRoot := some "origin-ord" }

def transferContext : AssetTransferRefinementV2.Context :=
  { moduleReleaseId := "release-v2"
    globalPreStateRoot := "global-pre"
    occurrence := some
      (occurrence AssetTransferRefinementV2.assetTransferCommandKind "transfer-body" "alice"
        "unused" "occ-transfer") }

def transferRoots : AssetTransferRefinementV2.RootModel :=
  ⟨fun state =>
    toString (state.balance "alice") ++ ":" ++ toString (state.balance "bob")⟩

def transferResult : AssetTransferRefinementV2.TransitionResult :=
  AssetTransferRefinementV2.transition transferRoots transferContext transferState transferCommand

def burnInputState : LifecycleState :=
  { issuedState with
    balance := transferResult.post.balance
    supplyAtoms := transferResult.post.supplyAtoms
    accountTotalAtoms := transferResult.post.accountTotalAtoms }

def burnCommand : Command :=
  { commandKind := burnCommandKind
    commandBodyHash := "burn-body"
    asset := "ORD"
    assetClass := .registeredOrdinaryToken
    assetOriginRoot := some "origin-ord"
    atomDecimals := 8
    authorizationRoot := some "burn-grant"
    accountOwner := "bob"
    amountAtoms := 40 }

def burnContext : Context :=
  contextFor (occurrence burnCommandKind "burn-body" "bob" "burn-grant" "occ-burn")

def burnResult : TransitionResult :=
  transition lifecycleRoots burnContext burnInputState burnCommand

theorem stateful_issue_transfer_burn_trace :
    issueResult.verdict = .accepted ∧
    issueResult.post.balance "alice" = 100 ∧
    issueResult.post.supplyAtoms = 100 ∧
    transferResult.verdict = .accepted ∧
    transferResult.post.balance "alice" = 60 ∧
    transferResult.post.balance "bob" = 40 ∧
    transferResult.post.supplyAtoms = 100 ∧
    burnResult.verdict = .accepted ∧
    burnResult.post.balance "alice" = 60 ∧
    burnResult.post.balance "bob" = 0 ∧
    burnResult.post.accountTotalAtoms = 60 ∧
    burnResult.post.supplyAtoms = 60 := by decide

def overflowState : LifecycleState :=
  { baseState with
    balance := ledger [("alice", AssetTransferRefinementV2.u128Max)]
    supplyAtoms := AssetTransferRefinementV2.u128Max
    accountTotalAtoms := AssetTransferRefinementV2.u128Max }

def overflowCommand : Command := { issueCommand with amountAtoms := 1 }

def overflowContext : Context := issueContext

theorem issue_supply_overflow_precedes_balance_overflow_counterexample :
    RejectCode.balanceOverflow.rank < RejectCode.supplyOverflow.rank ∧
    overflowState.supplyAtoms > AssetTransferRefinementV2.u128Max - overflowCommand.amountAtoms ∧
    overflowState.balance overflowCommand.accountOwner >
      AssetTransferRefinementV2.u128Max - overflowCommand.amountAtoms ∧
    rejectCode overflowContext overflowState overflowCommand = some .supplyOverflow := by
  constructor
  · decide
  · constructor
    · decide
    · constructor
      · decide
      · rfl

def protocolPolicy : Policy :=
  { ordinaryPolicy with
    asset := "ZDEX"
    assetClass := .zdexProtocolToken
    assetOriginRoot := some "origin-zdex"
    issueAuthority := none
    burnAuthorizationRoot := none }

def protocolState : LifecycleState := { baseState with policy := protocolPolicy }
def protocolCommand : Command :=
  { issueCommand with
    asset := "ZDEX"
    assetClass := .zdexProtocolToken
    assetOriginRoot := some "origin-zdex" }

def protocolContext : Context :=
  contextFor (occurrence issueCommandKind "issue-body" "issuer" "issue-grant" "occ-protocol")

theorem protocol_issue_rejects_generic_authority_counterexample :
    rejectCode protocolContext protocolState protocolCommand =
      some .genericAuthorityForbidden := by rfl

def wrongGrantContext : Context :=
  contextFor (occurrence issueCommandKind "issue-body" "issuer" "wrong-grant" "occ-wrong")

theorem wrong_grant_rejects_and_transition_is_noop :
    (transition lifecycleRoots wrongGrantContext baseState issueCommand).verdict =
      .rejected .authorizationRootMismatch ∧
    (transition lifecycleRoots wrongGrantContext baseState issueCommand).post = baseState ∧
    (transition lifecycleRoots wrongGrantContext baseState issueCommand).effects =
      AssetTransferRefinementV2.EffectEnvelope.empty := by
  have hreject : rejectCode wrongGrantContext baseState issueCommand =
      some .authorizationRootMismatch := by rfl
  simp [transition, hreject, reject]

end ManagedAssetLifecycleRefinementV2
end Proofs
