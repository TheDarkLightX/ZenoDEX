import Proofs.AssetLaneFiniteByteAccountingV2

/-!
Concrete finite managed-leaf outcomes following the existing economic prefix.
All policies, balances, complete supplies and serialized metadata are owned
inputs. Resources are computed from the constructed candidate. Initial typed
admission, external serializer correspondence and cryptographic digest
properties remain separate from this finite-state theorem surface.
-/
set_option warningAsError true

namespace Proofs.ManagedAssetFiniteOutcomeV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open RegisteredSupplySupportV1 RegisteredSupplyUpdateV1

namespace M
export ManagedAssetLifecycleRefinementV2 (Policy IssueAuthority Context Command Root LifecycleState
  RejectCode PolicyWellFormed CommandWellFormed StateWellFormed isIssue isBurn signedAmount
  firstFailing guardPasses authorizationRejectCodes rejectCode occurrencePasses occurrenceIds
  LifecyclePayload SupplyEffectKind)
end M
namespace T
export AssetTransferRefinementV2 (AssetClass EffectEnvelope ExternalRoots IsU128 u128Max)
end T
namespace B
export AssetLaneFiniteByteAccountingV2 (Bytes raw quoted number array leafBytes ValidToken
  BalanceTokens SupplyTokens updateRows_tokens adjustComplete_tokens oldBalanceWeight newBalanceWeight
  oldSupplyCost newSupplyCost emptyBit postEmptyBit)
end B
namespace A
export ManagedAssetFiniteAccountingV2 (project updateRows updateRows_total updateRows_unique
  updateRows_lookup accepted_rows_preserve_accounts)
end A
namespace S
export AssetTransferSparseTablesV1 (Unique PositiveAccounts accountKey accounts balanceWire
  putAmount mem_eraseKey)
end S
namespace C
export CanonicalEpochEconomicRowsV1 (amountKey lookupLast lookupLast_absent sortOn sortOn_perm sortOn_ordered)
end C

attribute [local instance] lexOrd

structure State where
  moduleReleaseId : String
  policies : List M.Policy
  balances : List AmountRow
  supplies : List V1SupplyRow
  deriving DecidableEq, Repr

def schema : String := "zenodex/managed-asset-lifecycle-module/v2"

def optionalString : Option String → B.Bytes
  | none => B.raw "null"
  | some value => B.quoted value

/-- The actual policy fields, including flattened paired issue authority. -/
def policyBytes (policy : M.Policy) : B.Bytes :=
  B.raw "{\"asset\":" ++ B.quoted policy.asset ++
    B.raw ",\"asset_class\":" ++ B.quoted policy.assetClass.code ++
    B.raw ",\"asset_origin_root\":" ++ optionalString policy.assetOriginRoot ++
    B.raw ",\"atom_decimals\":" ++ B.number (Int.ofNat policy.atomDecimals) ++
    B.raw ",\"burn_authorization_root\":" ++ optionalString policy.burnAuthorizationRoot ++
    B.raw ",\"enabled\":" ++ (if policy.enabled then B.raw "true" else B.raw "false") ++
    B.raw ",\"issue_authority_subject\":" ++ optionalString (policy.issueAuthority.map (fun authority => authority.subject)) ++
    B.raw ",\"issue_authorization_root\":" ++
      optionalString (policy.issueAuthority.map (fun authority => authority.authorizationRoot)) ++ B.raw "}"

def stateBytes (state : State) : B.Bytes :=
  B.leafBytes schema state.moduleReleaseId (B.array policyBytes state.policies) state.balances state.supplies

def stateRoot (digest : B.Bytes → M.Root) (state : State) : M.Root := digest (stateBytes state)

def policyFor (state : State) (asset : Asset) : Option M.Policy :=
  state.policies.find? (fun policy => policy.asset == asset)

def project (state : State) (policy : M.Policy) : M.LifecycleState :=
  A.project state.moduleReleaseId policy state.balances (supplyFor (numericRows state.supplies) policy.asset)

/-- Policy-independent guards occur before actual policy-list lookup. -/
def contextRejectCode (ctx : M.Context) (release : String) (command : M.Command) : Option M.RejectCode :=
  if ctx.occurrence ≠ none then
    if M.occurrencePasses ctx (fun o => o.preStateRoot = ctx.globalPreStateRoot ∧ o.consumedObjectIds = []) then
      if ctx.moduleReleaseId = release then
        if M.isIssue command ∨ M.isBurn command then
          if M.occurrencePasses ctx (fun o => o.commandKind = command.commandKind ∧
              o.commandBodyHash = command.commandBodyHash) then none
          else some .occurrenceCommandMismatch
        else some .unknownCommand
      else some .releaseMismatch
    else some .occurrenceBindingMismatch
  else some .missingOccurrence

def economicRejectCode (ctx : M.Context) (pre : State) (command : M.Command) : Option M.RejectCode :=
  match contextRejectCode ctx pre.moduleReleaseId command with
  | some code => some code
  | none => match policyFor pre command.asset with
      | none => some .unknownAsset
      | some policy => M.rejectCode ctx (project pre policy) command

def candidate (pre : State) (command : M.Command) : State :=
  { pre with
    balances := A.updateRows pre.balances command.asset command.accountOwner (M.signedAmount command)
    supplies := adjustComplete command.asset (M.signedAmount command) pre.supplies }

def Resources (state : State) : Prop :=
  state.policies.length ≤ 256 ∧ state.balances.length ≤ 4096 ∧ state.supplies.length ≤ 256 ∧
    (stateBytes state).length ≤ 1048576

instance (state : State) : Decidable (Resources state) :=
  inferInstanceAs (Decidable (state.policies.length ≤ 256 ∧ state.balances.length ≤ 4096 ∧
    state.supplies.length ≤ 256 ∧ (stateBytes state).length ≤ 1048576))

inductive RejectCode where
  | economic (code : M.RejectCode)
  | stateResourceLimit
  deriving DecidableEq, Repr

def RejectCode.code : RejectCode → String
  | .economic code => code.code
  | .stateResourceLimit => "STATE_RESOURCE_LIMIT"

def allRejectCodes : List RejectCode :=
  ManagedAssetLifecycleRefinementV2.allRejectCodes.map RejectCode.economic ++ [.stateResourceLimit]

theorem all_reject_codes_length : allRejectCodes.length = 22 := rfl

theorem all_reject_codes_complete (code : RejectCode) : code ∈ allRejectCodes := by
  cases code with
  | economic code => exact List.mem_append_left _ (List.mem_map.mpr
      ⟨code, ManagedAssetLifecycleRefinementV2.all_reject_codes_complete code, rfl⟩)
  | stateResourceLimit => simp [allRejectCodes]

theorem all_reject_codes_wire_order : allRejectCodes.map RejectCode.code =
    ["MISSING_OCCURRENCE", "OCCURRENCE_BINDING_MISMATCH", "RELEASE_MISMATCH", "UNKNOWN_COMMAND",
     "OCCURRENCE_COMMAND_MISMATCH", "UNKNOWN_ASSET", "DISABLED_ASSET", "ASSET_CLASS_MISMATCH",
     "ASSET_DECIMALS_MISMATCH", "UNREGISTERED_ASSET", "ASSET_ORIGIN_MISMATCH", "GENERIC_AUTHORITY_FORBIDDEN",
     "ISSUE_DISABLED", "BURN_DISABLED", "UNAUTHORIZED_SUBJECT", "AUTHORIZATION_ROOT_MISMATCH", "ZERO_AMOUNT",
     "EFFECT_DELTA_OVERFLOW", "INSUFFICIENT_BALANCE", "BALANCE_OVERFLOW", "SUPPLY_OVERFLOW", "STATE_RESOURCE_LIMIT"] := rfl

theorem all_reject_codes_wire_unique : (allRejectCodes.map RejectCode.code).Nodup := by decide

def payload (pre : State) (command : M.Command) : M.LifecyclePayload :=
  let post := candidate pre command
  { accountOwner := command.accountOwner
    accountDeltaAtoms := M.signedAmount command
    supplyKind := if M.isIssue command then .issue else .burn
    supplyDeltaAtoms := M.signedAmount command
    conservation := ⟨amountForAsset pre.balances command.asset, amountForAsset post.balances command.asset,
      supplyFor (numericRows pre.supplies) command.asset, supplyFor (numericRows post.supplies) command.asset,
      if M.isIssue command then command.amountAtoms else 0, if M.isIssue command then 0 else command.amountAtoms⟩ }

def acceptedEffects (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : State) (command : M.Command) :
    T.EffectEnvelope M.LifecyclePayload :=
  { payload := some (payload pre command)
    laneWrites := [⟨stateRoot digest pre, stateRoot digest (candidate pre command)⟩]
    occurrenceConsumptions := M.occurrenceIds ctx
    externalOutbox := []
    externalRoots := Proofs.AssetTransferRefinementV2.ExternalRoots.zero }

inductive Verdict where
  | accepted
  | rejected (code : RejectCode)
  deriving DecidableEq, Repr

structure Result where
  verdict : Verdict
  post : State
  effects : T.EffectEnvelope M.LifecyclePayload
  deriving DecidableEq, Repr

def reject (code : RejectCode) (pre : State) : Result :=
  ⟨.rejected code, pre, Proofs.AssetTransferRefinementV2.EffectEnvelope.empty⟩

def transition (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : State) (command : M.Command) : Result :=
  match economicRejectCode ctx pre command with
  | some code => reject (.economic code) pre
  | none => if Resources (candidate pre command) then
      ⟨.accepted, candidate pre command, acceptedEffects digest ctx pre command⟩
    else reject .stateResourceLimit pre

theorem accepted_iff (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : State) (command : M.Command) :
    (transition digest ctx pre command).verdict = .accepted ↔
      economicRejectCode ctx pre command = none ∧ Resources (candidate pre command) := by
  unfold transition
  cases code : economicRejectCode ctx pre command with
  | some code => simp [reject]
  | none => by_cases resource : Resources (candidate pre command) <;> simp [resource, reject]

theorem resource_reject_iff (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : State) (command : M.Command) :
    (transition digest ctx pre command).verdict = .rejected .stateResourceLimit ↔
      economicRejectCode ctx pre command = none ∧ ¬ Resources (candidate pre command) := by
  unfold transition
  cases code : economicRejectCode ctx pre command with
  | some code => simp [reject]
  | none => by_cases resource : Resources (candidate pre command) <;> simp [resource, reject]

theorem economic_reject_precedes_resource (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : State)
    (command : M.Command) (code : M.RejectCode) (economic : economicRejectCode ctx pre command = some code) :
    transition digest ctx pre command = reject (.economic code) pre := by
  simp only [transition, economic]

theorem rejected_noop {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : State} {command : M.Command}
    {code : RejectCode} (rejected : (transition digest ctx pre command).verdict = .rejected code) :
    (transition digest ctx pre command).post = pre ∧
      stateRoot digest (transition digest ctx pre command).post = stateRoot digest pre ∧
      (transition digest ctx pre command).effects = Proofs.AssetTransferRefinementV2.EffectEnvelope.empty := by
  unfold transition at rejected ⊢
  cases economic : economicRejectCode ctx pre command with
  | some code => exact ⟨rfl, rfl, rfl⟩
  | none =>
      by_cases resource : Resources (candidate pre command)
      · simp only [economic, if_pos resource] at rejected
        contradiction
      · simp only [if_neg resource]
        exact ⟨rfl, rfl, rfl⟩

theorem accepted_post_effects {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : State} {command : M.Command}
    (accepted : (transition digest ctx pre command).verdict = .accepted) :
    (transition digest ctx pre command).post = candidate pre command ∧
      (transition digest ctx pre command).effects = acceptedEffects digest ctx pre command := by
  have parts := (accepted_iff digest ctx pre command).mp accepted
  simp only [transition, parts.1, if_pos parts.2, and_self]

theorem context_is_scalar_first_five (ctx : M.Context) (pre : State) (policy : M.Policy) (command : M.Command) :
    M.firstFailing (M.guardPasses ctx (project pre policy) command) (M.authorizationRejectCodes.take 5) =
      contextRejectCode ctx pre.moduleReleaseId command := rfl

theorem firstFailing_append (guard : M.RejectCode → Prop) [DecidablePred guard]
    (left right : List M.RejectCode) :
    M.firstFailing guard (left ++ right) =
      match M.firstFailing guard left with | some code => some code | none => M.firstFailing guard right := by
  induction left with
  | nil => rfl
  | cons code rest ih => by_cases pass : guard code <;> simp [M.firstFailing, pass, ih]

theorem scalar_preserves_context_failure (ctx : M.Context) (pre : State) (policy : M.Policy)
    (command : M.Command) (code : M.RejectCode)
    (failure : contextRejectCode ctx pre.moduleReleaseId command = some code) :
    M.rejectCode ctx (project pre policy) command = some code := by
  unfold M.rejectCode
  rw [show M.authorizationRejectCodes = M.authorizationRejectCodes.take 5 ++ M.authorizationRejectCodes.drop 5 by decide,
    firstFailing_append, context_is_scalar_first_five, failure]

theorem economic_matches_selected (ctx : M.Context) (pre : State) (command : M.Command) (policy : M.Policy)
    (selected : policyFor pre command.asset = some policy) :
    economicRejectCode ctx pre command = M.rejectCode ctx (project pre policy) command := by
  unfold economicRejectCode
  cases common : contextRejectCode ctx pre.moduleReleaseId command with
  | none => simp only [selected]
  | some code => exact (scalar_preserves_context_failure ctx pre policy command code common).symm

theorem economic_none_iff_selected (ctx : M.Context) (pre : State) (command : M.Command) :
    economicRejectCode ctx pre command = none ↔
      ∃ policy, policyFor pre command.asset = some policy ∧ M.rejectCode ctx (project pre policy) command = none := by
  constructor
  · intro success
    unfold economicRejectCode at success
    cases common : contextRejectCode ctx pre.moduleReleaseId command with
    | some code => simp only [common] at success; contradiction
    | none =>
        simp only [common] at success
        cases selected : policyFor pre command.asset with
        | none => simp only [selected] at success; contradiction
        | some policy => exact ⟨policy, rfl, by simpa only [selected] using success⟩
  · rintro ⟨policy, selected, success⟩
    rw [economic_matches_selected ctx pre command policy selected]
    exact success

theorem context_precedes_policy_absence (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : State)
    (command : M.Command) (code : M.RejectCode)
    (failure : contextRejectCode ctx pre.moduleReleaseId command = some code) :
    transition digest ctx pre command = reject (.economic code) pre := by
  apply economic_reject_precedes_resource
  simp only [economicRejectCode, failure]

theorem absent_policy_after_context (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : State)
    (command : M.Command) (common : contextRejectCode ctx pre.moduleReleaseId command = none)
    (absent : policyFor pre command.asset = none) :
    transition digest ctx pre command = reject (.economic .unknownAsset) pre := by
  apply economic_reject_precedes_resource
  simp only [economicRejectCode, common, absent]

/-- Structural conditions on actual finite tables. Strict order makes the
explicit uniqueness fields redundant, but they support the reused row API. -/
structure Structural (pre : State) : Prop where
  policyUnique : (pre.policies.map (fun policy => policy.asset)).Nodup
  policyOrdered : pre.policies.Pairwise (fun left right => left.asset < right.asset)
  policyWellFormed : ∀ policy ∈ pre.policies, M.PolicyWellFormed policy
  balanceUnique : S.Unique pre.balances
  balancePositive : S.PositiveAccounts pre.balances
  balanceOrdered : pre.balances.Pairwise (fun left right => compare (S.balanceWire left) (S.balanceWire right) = .lt)
  balanceSupported : ∀ row ∈ pre.balances, row.asset ∈ pre.policies.map (fun policy => policy.asset)
  supplyUnique : SourceAssetKeysUnique pre.supplies
  supplyOrdered : SourceAssetKeysOrdered pre.supplies
  supplyU128 : SourceRowsU128 pre.supplies
  keysAgree : pre.supplies.map V1SupplyRow.asset = pre.policies.map (fun policy => policy.asset)
  accountCover : ∀ asset, amountForAsset pre.balances asset ≤ supplyFor (numericRows pre.supplies) asset
  balanceTokens : B.BalanceTokens pre.balances
  supplyTokens : B.SupplyTokens pre.supplies

/-- Root and namespace predicates are external syntax conditions applied only
to owned immutable metadata. They are not resource or transition-success oracles. -/
def PolicySyntax (rootSyntax : String → Prop) (namespaceSyntax : String → T.AssetClass → Prop)
    (policy : M.Policy) : Prop :=
  B.ValidToken policy.asset ∧ namespaceSyntax policy.asset policy.assetClass ∧
  (∀ value, policy.assetOriginRoot = some value → B.ValidToken value ∧ rootSyntax value) ∧
  (∀ value, policy.burnAuthorizationRoot = some value → B.ValidToken value ∧ rootSyntax value) ∧
  (∀ authority, policy.issueAuthority = some authority →
    B.ValidToken authority.subject ∧ B.ValidToken authority.authorizationRoot ∧ rootSyntax authority.authorizationRoot)

def MetadataAdmission (rootSyntax : String → Prop) (namespaceSyntax : String → T.AssetClass → Prop)
    (pre : State) : Prop :=
  B.ValidToken pre.moduleReleaseId ∧ rootSyntax pre.moduleReleaseId ∧
    ∀ policy ∈ pre.policies, PolicySyntax rootSyntax namespaceSyntax policy

def Admitted (rootSyntax : String → Prop) (namespaceSyntax : String → T.AssetClass → Prop)
    (pre : State) : Prop := Structural pre ∧ MetadataAdmission rootSyntax namespaceSyntax pre ∧ Resources pre

theorem policyFor_spec {pre : State} {asset : Asset} {policy : M.Policy}
    (selected : policyFor pre asset = some policy) : policy ∈ pre.policies ∧ policy.asset = asset := by
  exact ⟨List.mem_of_find?_eq_some selected, by simpa only [beq_iff_eq] using List.find?_some selected⟩

theorem structural_registered {pre : State} {command : M.Command} {policy : M.Policy}
    (admitted : Structural pre) (selected : policyFor pre command.asset = some policy) :
    command.asset ∈ pre.supplies.map V1SupplyRow.asset := by
  rw [admitted.keysAgree]
  exact List.mem_map.mpr ⟨policy, (policyFor_spec selected).1, (policyFor_spec selected).2⟩

theorem supply_lookup_u128 (rows : List V1SupplyRow) (unique : SourceAssetKeysUnique rows)
    (bounded : SourceRowsU128 rows) (asset : Asset) : T.IsU128 (supplyFor (numericRows rows) asset) := by
  rw [supplyFor_numericRows_preserved]
  by_cases present : asset ∈ rows.map V1SupplyRow.asset
  · obtain ⟨row, member, same⟩ := List.mem_map.mp present
    rw [← same, source_supplyFor_eq_member_of_unique unique member]
    exact bounded row member
  · have absent : ∀ row ∈ rows, row.asset ≠ asset := by
      intro row member same
      exact present (List.mem_map.mpr ⟨row, member, same⟩)
    rw [source_supplyFor_zero_of_absent absent]
    constructor <;> decide

theorem balance_lookup_u128 (rows : List AmountRow) (unique : S.Unique rows)
    (positive : S.PositiveAccounts rows) (asset owner : String) :
    T.IsU128 (C.lookupLast (S.accountKey asset owner) rows) := by
  by_cases present : S.accountKey asset owner ∈ rows.map C.amountKey
  · obtain ⟨row, member, same⟩ := List.mem_map.mp present
    rw [← same, AssetLaneFiniteRowGrowthV2.lookupLast_member rows row unique member]
    exact (positive row member).2.1
  · rw [C.lookupLast_absent _ rows present]
    constructor <;> decide

theorem amountForAsset_nonnegative (rows : List AmountRow)
    (nonnegative : ∀ row ∈ rows, 0 ≤ row.amountAtoms) (asset : Asset) : 0 ≤ amountForAsset rows asset := by
  induction rows with
  | nil => exact Int.le_refl 0
  | cons row rows ih =>
      have head := nonnegative row (by simp)
      have tail := ih (fun next member => nonnegative next (by simp [member]))
      change 0 ≤ (if row.asset = asset then row.amountAtoms else 0) + amountForAsset rows asset
      split <;> omega

theorem project_well_formed {pre : State} {policy : M.Policy} (admitted : Structural pre)
    (member : policy ∈ pre.policies) : M.StateWellFormed (project pre policy) := by
  have supply := supply_lookup_u128 pre.supplies admitted.supplyUnique admitted.supplyU128 policy.asset
  have cover := admitted.accountCover policy.asset
  constructor
  · intro owner
    exact balance_lookup_u128 pre.balances admitted.balanceUnique admitted.balancePositive policy.asset owner
  · exact supply
  · exact ⟨amountForAsset_nonnegative pre.balances
      (fun row member => (admitted.balancePositive row member).2.1.1) policy.asset,
        Int.le_trans cover supply.2⟩
  · exact cover
  · exact admitted.policyWellFormed policy member

theorem updateRows_supported (rows : List AmountRow) (assets : List Asset) (asset owner : String) (delta : Int)
    (supported : ∀ row ∈ rows, row.asset ∈ assets) (registered : asset ∈ assets) :
    ∀ row ∈ A.updateRows rows asset owner delta, row.asset ∈ assets := by
  intro row member
  have raw := (C.sortOn_perm S.balanceWire _).mem_iff.mp member
  unfold S.putAmount at raw
  split at raw
  · exact supported row (List.mem_filter.mp raw).1
  · rcases List.mem_cons.mp raw with rfl | raw
    · exact registered
    · exact supported row (List.mem_filter.mp raw).1

theorem updateRows_ordered (rows : List AmountRow) (asset owner : String) (delta : Int)
    (unique : S.Unique rows) (positive : S.PositiveAccounts (A.updateRows rows asset owner delta)) :
    (A.updateRows rows asset owner delta).Pairwise
      (fun left right => compare (S.balanceWire left) (S.balanceWire right) = .lt) := by
  have ordered := C.sortOn_ordered S.balanceWire
    (S.putAmount (S.accountKey asset owner) (C.lookupLast (S.accountKey asset owner) rows + delta) rows)
  have distinct : (A.updateRows rows asset owner delta).Pairwise
      (fun left right => S.balanceWire left ≠ S.balanceWire right) :=
    List.pairwise_map.mp (AssetLaneFiniteRecompositionV2.balance_wire_keys_unique _
      (A.updateRows_unique rows asset owner delta unique) (fun row member => (positive row member).1))
  apply (ordered.and distinct).imp
  intro left right pair
  rcases Ordering.isLE_iff_eq_lt_or_eq_eq.mp pair.1 with lt | eq
  · exact lt
  · exact False.elim (pair.2 (Std.LawfulEqOrd.eq_of_compare eq))

/-- Economic success already derives the concrete candidate's shape and
quantities. No post structure or resource condition is supplied as a premise. -/
theorem economic_candidate_structural {ctx : M.Context} {pre : State} {command : M.Command}
    (admitted : Structural pre) (commandAdmitted : M.CommandWellFormed command)
    (ownerToken : B.ValidToken command.accountOwner)
    (economic : economicRejectCode ctx pre command = none) : Structural (candidate pre command) := by
  obtain ⟨policy, selected, success⟩ := (economic_none_iff_selected ctx pre command).mp economic
  have member := (policyFor_spec selected).1
  have same := (policyFor_spec selected).2
  have registered := structural_registered admitted selected
  have wellFormed := project_well_formed admitted member
  have accepted := (ManagedAssetLifecycleRefinementV2.accepted_iff_no_reject
    ⟨fun _ => ""⟩ ctx (project pre policy) command).mpr success
  have accounts := A.accepted_rows_preserve_accounts admitted.balanceUnique admitted.balancePositive
    wellFormed commandAdmitted accepted
  have supply := ManagedAssetLifecycleRefinementV2.accepted_post_supply_u128 wellFormed commandAdmitted accepted
  rw [(ManagedAssetLifecycleRefinementV2.accepted_post_and_effects accepted).1] at supply
  change T.IsU128 (supplyFor (numericRows pre.supplies) policy.asset + M.signedAmount command) at supply
  rw [same] at supply
  have assetToken : B.ValidToken command.asset := by
    obtain ⟨row, rowMember, sameAsset⟩ := List.mem_map.mp registered
    exact sameAsset ▸ admitted.supplyTokens row rowMember
  constructor
  · exact admitted.policyUnique
  · exact admitted.policyOrdered
  · exact admitted.policyWellFormed
  · exact accounts.1
  · exact accounts.2
  · exact updateRows_ordered pre.balances _ _ _ admitted.balanceUnique accounts.2
  · exact updateRows_supported pre.balances _ _ _ _ admitted.balanceSupported
      (List.mem_map.mpr ⟨policy, member, same⟩)
  · exact adjustComplete_unique admitted.supplyUnique _ _
  · exact adjustComplete_ordered admitted.supplyOrdered _ _
  · exact adjustComplete_u128 pre.supplies _ _ admitted.supplyUnique admitted.supplyU128 supply
  · exact (adjustComplete_keys _ _ _).trans admitted.keysAgree
  · intro asset
    change amountForAsset (A.updateRows pre.balances _ _ _) asset ≤
      supplyFor (numericRows (adjustComplete _ _ pre.supplies)) asset
    rw [A.updateRows_total _ _ _ _ admitted.balanceUnique,
      adjustComplete_lookup _ _ _ admitted.supplyUnique registered]
    have cover := admitted.accountCover asset
    by_cases selectedAsset : command.asset = asset
    · simp only [selectedAsset, if_true]
      omega
    · simp only [if_neg selectedAsset, if_neg (Ne.symm selectedAsset), Int.add_zero]
      exact cover
  · exact B.updateRows_tokens pre.balances _ _ _ admitted.balanceTokens assetToken ownerToken
  · exact B.adjustComplete_tokens pre.supplies _ _ admitted.supplyTokens

theorem accepted_preserves_admission {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} {digest : B.Bytes → M.Root}
    {ctx : M.Context} {pre : State} {command : M.Command}
    (admitted : Admitted rootSyntax namespaceSyntax pre) (commandAdmitted : M.CommandWellFormed command)
    (ownerToken : B.ValidToken command.accountOwner)
    (accepted : (transition digest ctx pre command).verdict = .accepted) :
    Admitted rootSyntax namespaceSyntax (transition digest ctx pre command).post := by
  have parts := (accepted_iff digest ctx pre command).mp accepted
  rw [(accepted_post_effects accepted).1]
  exact ⟨economic_candidate_structural admitted.1 commandAdmitted ownerToken parts.1,
    admitted.2.1, parts.2⟩


theorem candidate_project {pre : State} {command : M.Command} {policy : M.Policy}
    (admitted : Structural pre) (selected : policyFor pre command.asset = some policy) :
    project (candidate pre command) policy =
      ManagedAssetLifecycleRefinementV2.acceptedState (project pre policy) command := by
  have same := (policyFor_spec selected).2
  have registered := structural_registered admitted selected
  unfold project candidate
  simp only
  rw [adjustComplete_lookup _ _ _ admitted.supplyUnique registered policy.asset]
  simp only [same, if_true]
  exact ManagedAssetFiniteAccountingV2.materializes_accepted_state _ _ _ _ _ admitted.balanceUnique same.symm

/-- Every full accepted outcome selects an actual policy and rehydrates the
old economic leaf from the computed finite successor, for any scalar observer. -/
theorem accepted_selected_leaf {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : State}
    {command : M.Command} (roots : ManagedAssetLifecycleRefinementV2.RootModel)
    (admitted : Structural pre) (accepted : (transition digest ctx pre command).verdict = .accepted) :
    ∃ policy, policyFor pre command.asset = some policy ∧
      (ManagedAssetLifecycleRefinementV2.transition roots ctx (project pre policy) command).verdict = .accepted ∧
      project (transition digest ctx pre command).post policy =
        (ManagedAssetLifecycleRefinementV2.transition roots ctx (project pre policy) command).post := by
  obtain ⟨policy, selected, success⟩ := (economic_none_iff_selected ctx pre command).mp
    ((accepted_iff digest ctx pre command).mp accepted).1
  have scalar := (ManagedAssetLifecycleRefinementV2.accepted_iff_no_reject roots ctx _ command).mpr success
  have equal : project (transition digest ctx pre command).post policy =
      (ManagedAssetLifecycleRefinementV2.transition roots ctx (project pre policy) command).post := by
    rw [(accepted_post_effects accepted).1,
      (ManagedAssetLifecycleRefinementV2.accepted_post_and_effects scalar).1]
    exact candidate_project admitted selected
  exact ⟨policy, selected, scalar, equal⟩

theorem accepted_accounting {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : State}
    {command : M.Command} (admitted : Structural pre)
    (accepted : (transition digest ctx pre command).verdict = .accepted) (asset : Asset) :
    amountForAsset (transition digest ctx pre command).post.balances asset =
        amountForAsset pre.balances asset + (if command.asset = asset then M.signedAmount command else 0) ∧
      supplyFor (numericRows (transition digest ctx pre command).post.supplies) asset =
        supplyFor (numericRows pre.supplies) asset + (if asset = command.asset then M.signedAmount command else 0) := by
  obtain ⟨policy, selected, _⟩ := (economic_none_iff_selected ctx pre command).mp
    ((accepted_iff digest ctx pre command).mp accepted).1
  rw [(accepted_post_effects accepted).1]
  exact ⟨A.updateRows_total _ _ _ _ admitted.balanceUnique asset,
    adjustComplete_lookup _ _ _ admitted.supplyUnique (structural_registered admitted selected) asset⟩

theorem accepted_effect_delta_i128 {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : State}
    {command : M.Command} (commandAdmitted : M.CommandWellFormed command)
    (accepted : (transition digest ctx pre command).verdict = .accepted) :
    AssetTransferRefinementV2.IsI128 (M.signedAmount command) := by
  obtain ⟨policy, _, success⟩ := (economic_none_iff_selected ctx pre command).mp
    ((accepted_iff digest ctx pre command).mp accepted).1
  exact ManagedAssetLifecycleRefinementV2.accepted_effect_delta_i128 commandAdmitted
    ((ManagedAssetLifecycleRefinementV2.accepted_iff_no_reject ⟨fun _ => ""⟩ ctx (project pre policy) command).mpr success)

theorem accepted_effects_bind {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : State} {command : M.Command}
    (accepted : (transition digest ctx pre command).verdict = .accepted) :
    (transition digest ctx pre command).effects.payload = some (payload pre command) ∧
      (transition digest ctx pre command).effects.laneWrites =
        [⟨stateRoot digest pre, stateRoot digest (transition digest ctx pre command).post⟩] ∧
      (transition digest ctx pre command).effects.occurrenceConsumptions = M.occurrenceIds ctx ∧
      (transition digest ctx pre command).effects.externalOutbox = [] ∧
      (transition digest ctx pre command).effects.externalRoots = AssetTransferRefinementV2.ExternalRoots.zero := by
  rw [(accepted_post_effects accepted).1, (accepted_post_effects accepted).2]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Remaining authorization and arithmetic decisions precede every resource
failure. Supply-before-balance is exactly the unchanged scalar post-stage. -/
theorem selected_post_stage (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : State)
    (command : M.Command) (policy : M.Policy) (code : M.RejectCode)
    (selected : policyFor pre command.asset = some policy)
    (authorization : ∀ reason ∈ M.authorizationRejectCodes, M.guardPasses ctx (project pre policy) command reason)
    (arithmetic : ManagedAssetLifecycleRefinementV2.postStageRejectCode (project pre policy) command = some code) :
    transition digest ctx pre command = reject (.economic code) pre := by
  apply economic_reject_precedes_resource
  rw [economic_matches_selected ctx pre command policy selected]
  unfold M.rejectCode
  rw [(ManagedAssetLifecycleRefinementV2.firstFailing_eq_none_iff _ _).mpr authorization]
  exact arithmetic

theorem issue_supply_overflow_precedes_resources (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : State)
    (command : M.Command) (policy : M.Policy) (selected : policyFor pre command.asset = some policy)
    (authorization : ∀ reason ∈ M.authorizationRejectCodes, M.guardPasses ctx (project pre policy) command reason)
    (issue : M.isIssue command)
    (overflow : supplyFor (numericRows pre.supplies) policy.asset > T.u128Max - command.amountAtoms) :
    transition digest ctx pre command = reject (.economic .supplyOverflow) pre :=
  selected_post_stage digest ctx pre command policy .supplyOverflow selected authorization
    (ManagedAssetLifecycleRefinementV2.issue_supply_overflow_precedes_balance_overflow _ _ issue overflow)

theorem candidate_byte_equation {pre : State} {command : M.Command}
    (balanceUnique : S.Unique pre.balances) (supplyUnique : SourceAssetKeysUnique pre.supplies)
    (registered : command.asset ∈ pre.supplies.map V1SupplyRow.asset) :
    (stateBytes (candidate pre command)).length + B.oldBalanceWeight pre.balances command.asset command.accountOwner +
        B.oldSupplyCost pre.supplies command.asset + B.emptyBit pre.balances =
      (stateBytes pre).length + B.newBalanceWeight pre.balances command.asset command.accountOwner (M.signedAmount command) +
        B.newSupplyCost pre.supplies command.asset (M.signedAmount command) +
        B.postEmptyBit pre.balances command.asset command.accountOwner (M.signedAmount command) :=
  AssetLaneFiniteByteAccountingV2.framed_update_bytes _ _ _ _ _ _ _ _ balanceUnique supplyUnique registered

/-- Algebraic capacity criterion computed solely from owned PRE rows, metadata
and the command. The balance term includes presence/deletion and decimal/escape
costs; complete supply rows remain present when their new amount is zero. -/
def SourceCapacity (pre : State) (command : M.Command) : Prop :=
  pre.policies.length ≤ 256 ∧ pre.supplies.length ≤ 256 ∧
    pre.balances.length + (if C.lookupLast (S.accountKey command.asset command.accountOwner) pre.balances +
        M.signedAmount command ≠ 0 then 1 else 0) ≤
      4096 + (if S.accountKey command.asset command.accountOwner ∈ pre.balances.map C.amountKey then 1 else 0) ∧
    (stateBytes pre).length + B.newBalanceWeight pre.balances command.asset command.accountOwner (M.signedAmount command) +
        B.newSupplyCost pre.supplies command.asset (M.signedAmount command) +
        B.postEmptyBit pre.balances command.asset command.accountOwner (M.signedAmount command) ≤
      1048576 + B.oldBalanceWeight pre.balances command.asset command.accountOwner +
        B.oldSupplyCost pre.supplies command.asset + B.emptyBit pre.balances

theorem candidate_resources_iff_source_capacity {pre : State} {command : M.Command}
    (balanceUnique : S.Unique pre.balances) (supplyUnique : SourceAssetKeysUnique pre.supplies)
    (registered : command.asset ∈ pre.supplies.map V1SupplyRow.asset) :
    Resources (candidate pre command) ↔ SourceCapacity pre command := by
  have bytes := candidate_byte_equation balanceUnique supplyUnique registered
  have rows := AssetLaneFiniteRowGrowthV2.updateRows_length pre.balances command.asset command.accountOwner
    (M.signedAmount command) balanceUnique
  have supplies : (candidate pre command).supplies.length = pre.supplies.length := List.length_map _
  unfold Resources SourceCapacity
  change pre.policies.length ≤ 256 ∧ (A.updateRows pre.balances _ _ _).length ≤ 4096 ∧
    (candidate pre command).supplies.length ≤ 256 ∧ (stateBytes (candidate pre command)).length ≤ 1048576 ↔ _
  rw [supplies]
  omega

theorem dormant_issue_at_row_cap_rejected {digest : B.Bytes → M.Root} {ctx : M.Context}
    {pre : State} {command : M.Command} (admitted : Structural pre)
    (economic : economicRejectCode ctx pre command = none) (issue : M.isIssue command)
    (positive : 0 < command.amountAtoms)
    (dormant : C.lookupLast (S.accountKey command.asset command.accountOwner) pre.balances = 0)
    (full : pre.balances.length = 4096) :
    (transition digest ctx pre command).verdict = .rejected .stateResourceLimit := by
  apply (resource_reject_iff digest ctx pre command).mpr
  have count := AssetLaneFiniteRowGrowthV2.dormant_issue_length pre.balances command.asset command.accountOwner
    command.amountAtoms admitted.balanceUnique admitted.balancePositive dormant positive
  have tooMany : ¬ Resources (candidate pre command) := by
    intro resource
    have bound := resource.2.1
    change (A.updateRows pre.balances command.asset command.accountOwner (M.signedAmount command)).length ≤ 4096 at bound
    rw [M.signedAmount, if_pos issue, count, full] at bound
    omega
  exact ⟨economic, tooMany⟩


theorem accepted_iff_full_guards_capacity (digest : B.Bytes → M.Root) (ctx : M.Context)
    (pre : State) (command : M.Command) (admitted : Structural pre) :
    (transition digest ctx pre command).verdict = .accepted ↔
      ∃ policy, policyFor pre command.asset = some policy ∧
        (∀ reason ∈ M.authorizationRejectCodes, M.guardPasses ctx (project pre policy) command reason) ∧
        ManagedAssetLifecycleRefinementV2.postStageRejectCode (project pre policy) command = none ∧
        SourceCapacity pre command := by
  rw [accepted_iff]
  constructor
  · rintro ⟨economic, resources⟩
    obtain ⟨policy, selected, success⟩ := (economic_none_iff_selected ctx pre command).mp economic
    have guards := (ManagedAssetLifecycleRefinementV2.reject_code_none_parts ctx _ command).mp success
    exact ⟨policy, selected, guards.1, guards.2,
      (candidate_resources_iff_source_capacity admitted.balanceUnique admitted.supplyUnique
        (structural_registered admitted selected)).mp resources⟩
  · rintro ⟨policy, selected, authorization, arithmetic, capacity⟩
    exact ⟨(economic_none_iff_selected ctx pre command).mpr ⟨policy, selected,
      (ManagedAssetLifecycleRefinementV2.reject_code_none_parts ctx _ command).mpr ⟨authorization, arithmetic⟩⟩,
      (candidate_resources_iff_source_capacity admitted.balanceUnique admitted.supplyUnique
        (structural_registered admitted selected)).mpr capacity⟩

theorem resource_reject_iff_full_guards_capacity (digest : B.Bytes → M.Root) (ctx : M.Context)
    (pre : State) (command : M.Command) (admitted : Structural pre) :
    (transition digest ctx pre command).verdict = .rejected .stateResourceLimit ↔
      ∃ policy, policyFor pre command.asset = some policy ∧
        (∀ reason ∈ M.authorizationRejectCodes, M.guardPasses ctx (project pre policy) command reason) ∧
        ManagedAssetLifecycleRefinementV2.postStageRejectCode (project pre policy) command = none ∧
        ¬ SourceCapacity pre command := by
  rw [resource_reject_iff]
  constructor
  · rintro ⟨economic, resources⟩
    obtain ⟨policy, selected, success⟩ := (economic_none_iff_selected ctx pre command).mp economic
    have guards := (ManagedAssetLifecycleRefinementV2.reject_code_none_parts ctx _ command).mp success
    have capacity := candidate_resources_iff_source_capacity admitted.balanceUnique admitted.supplyUnique
      (structural_registered admitted selected)
    exact ⟨policy, selected, guards.1, guards.2, fun source => resources (capacity.mpr source)⟩
  · rintro ⟨policy, selected, authorization, arithmetic, capacity⟩
    have economic := (economic_none_iff_selected ctx pre command).mpr ⟨policy, selected,
      (ManagedAssetLifecycleRefinementV2.reject_code_none_parts ctx _ command).mpr ⟨authorization, arithmetic⟩⟩
    have resources := candidate_resources_iff_source_capacity admitted.balanceUnique admitted.supplyUnique
      (structural_registered admitted selected)
    exact ⟨economic, fun admitted => capacity (resources.mp admitted)⟩

theorem accepted_supply_identity {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : State}
    {command : M.Command} (admitted : Structural pre)
    (accepted : (transition digest ctx pre command).verdict = .accepted) :
    (transition digest ctx pre command).post.supplies.map V1SupplyRow.asset = pre.supplies.map V1SupplyRow.asset ∧
      numericRows (transition digest ctx pre command).post.supplies =
        adjustSparse command.asset (M.signedAmount command) (numericRows pre.supplies) ∧
      decode ⟨pre.supplies.map V1SupplyRow.asset,
        adjustSparse command.asset (M.signedAmount command) (numericRows pre.supplies)⟩ =
        (transition digest ctx pre command).post.supplies := by
  obtain ⟨policy, selected, _⟩ := (economic_none_iff_selected ctx pre command).mp
    ((accepted_iff digest ctx pre command).mp accepted).1
  have registered := structural_registered admitted selected
  rw [(accepted_post_effects accepted).1]
  exact ⟨adjustComplete_keys _ _ _,
    registered_supply_adjust_commutes _ _ _ admitted.supplyUnique admitted.supplyOrdered registered,
    registered_supply_adjust_roundtrip _ _ _ admitted.supplyUnique admitted.supplyOrdered registered⟩

theorem transition_preserves_admission {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} (digest : B.Bytes → M.Root)
    (ctx : M.Context) (pre : State) (command : M.Command)
    (admitted : Admitted rootSyntax namespaceSyntax pre) (commandAdmitted : M.CommandWellFormed command)
    (ownerToken : B.ValidToken command.accountOwner) :
    Admitted rootSyntax namespaceSyntax (transition digest ctx pre command).post := by
  cases verdict : (transition digest ctx pre command).verdict with
  | accepted => exact accepted_preserves_admission admitted commandAdmitted ownerToken verdict
  | rejected code => rw [(rejected_noop verdict).1]; exact admitted

/-- Each new command observes the finite state returned by the preceding step. -/
def executeTrace (digest : B.Bytes → M.Root) : State → List (M.Context × M.Command) → State
  | pre, [] => pre
  | pre, input :: rest => executeTrace digest (transition digest input.1 pre input.2).post rest

theorem trace_preserves_admission {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} (digest : B.Bytes → M.Root)
    (pre : State) (trace : List (M.Context × M.Command))
    (admitted : Admitted rootSyntax namespaceSyntax pre)
    (commands : ∀ input ∈ trace, M.CommandWellFormed input.2 ∧ B.ValidToken input.2.accountOwner) :
    Admitted rootSyntax namespaceSyntax (executeTrace digest pre trace) := by
  induction trace generalizing pre with
  | nil => exact admitted
  | cons input rest ih =>
      have first := commands input (by simp)
      exact ih _ (transition_preserves_admission digest input.1 pre input.2 admitted first.1 first.2)
        (fun next member => commands next (by simp [member]))

theorem trace_prefixes_admitted {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} (digest : B.Bytes → M.Root)
    (pre : State) (trace : List (M.Context × M.Command))
    (admitted : Admitted rootSyntax namespaceSyntax pre)
    (commands : ∀ input ∈ trace, M.CommandWellFormed input.2 ∧ B.ValidToken input.2.accountOwner)
    (length : Nat) : Admitted rootSyntax namespaceSyntax (executeTrace digest pre (trace.take length)) :=
  trace_preserves_admission digest pre (trace.take length) admitted
    (fun input member => commands input (List.mem_of_mem_take member))

end Proofs.ManagedAssetFiniteOutcomeV2
