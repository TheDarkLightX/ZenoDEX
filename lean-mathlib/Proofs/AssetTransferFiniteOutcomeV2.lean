import Proofs.ManagedAssetFiniteOutcomeV2

/-!
Concrete finite transfer outcomes with owned policy/state serialization.
The existing V2 forward owner scan owns arithmetic rejection precedence.
Resource admission observes only the final materialized table, after every
role update. External type/parser, complete effect/journal codec and hash
correspondence are separate from this finite theorem surface.
-/
set_option warningAsError true

namespace Proofs.AssetTransferFiniteOutcomeV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open RegisteredSupplySupportV1 RegisteredSupplyUpdateV1

namespace T
export AssetTransferRefinementV2 (Policy Context Command Root TransferState RejectCode
  StateWellFormed CommandWellFormed IsU128 IsI128 AssetClass TransferPayload EffectEnvelope
  firstFailing guardPasses preBalanceRejectCodes rejectCode occurrencePasses occurrenceIds
  assetTransferCommandKind orderedRoles roleOrder sortPrincipals insertPrincipal delta
  acceptedPayload movementRows balanceCodeOn)
end T
namespace B
export AssetLaneFiniteByteAccountingV2 (Bytes raw quoted number array leafBytes ValidToken
  BalanceTokens SupplyTokens updateRows_tokens)
end B
namespace F
export AssetTransferFiniteAccountingV2 (project transferRows updateRoles update_roles_unique
  transferRows_unique transferRows_lookup transferRows_totals accepted_distinct
  accepted_rows_preserve_accounts accepted_materialization)
end F
namespace G
export ManagedAssetFiniteOutcomeV2 (supply_lookup_u128 balance_lookup_u128 amountForAsset_nonnegative
  updateRows_supported updateRows_ordered optionalString)
end G
namespace S
export AssetTransferSparseTablesV1 (Unique PositiveAccounts accounts accountKey balanceWire)
end S
namespace C
export CanonicalEpochEconomicRowsV1 (amountKey lookupLast)
end C

attribute [local instance] lexOrd

structure State where
  moduleReleaseId : String
  policies : List T.Policy
  balances : List AmountRow
  supplies : List V1SupplyRow
  deriving DecidableEq, Repr

def schema : String := "zenodex/asset-transfer-module/v2"

def policyBytes (policy : T.Policy) : B.Bytes :=
  B.raw "{\"asset\":" ++ B.quoted policy.asset ++
    B.raw ",\"asset_class\":" ++ B.quoted policy.assetClass.code ++
    B.raw ",\"asset_origin_root\":" ++ G.optionalString policy.assetOriginRoot ++
    B.raw ",\"atom_decimals\":" ++ B.number (Int.ofNat policy.atomDecimals) ++
    B.raw ",\"enabled\":" ++ (if policy.enabled then B.raw "true" else B.raw "false") ++
    B.raw ",\"fee_owner\":" ++ B.quoted policy.feeOwner ++
    B.raw ",\"transfer_fee_atoms\":" ++ B.number policy.transferFeeAtoms ++ B.raw "}"

def stateBytes (state : State) : B.Bytes :=
  B.leafBytes schema state.moduleReleaseId (B.array policyBytes state.policies) state.balances state.supplies

def stateRoot (digest : B.Bytes → T.Root) (state : State) : T.Root := digest (stateBytes state)

def policyFor (state : State) (asset : Asset) : Option T.Policy :=
  state.policies.find? (fun policy => policy.asset == asset)

def project (state : State) (policy : T.Policy) : T.TransferState :=
  F.project state.moduleReleaseId policy state.balances (supplyFor (numericRows state.supplies) policy.asset)

def contextRejectCode (ctx : T.Context) (release : String) (command : T.Command) : Option T.RejectCode :=
  if ctx.occurrence ≠ none then
    if T.occurrencePasses ctx (fun o => o.preStateRoot = ctx.globalPreStateRoot ∧ o.consumedObjectIds = []) then
      if ctx.moduleReleaseId = release then
        if command.commandKind = T.assetTransferCommandKind then
          if T.occurrencePasses ctx (fun o => o.commandKind = command.commandKind ∧
              o.commandBodyHash = command.commandBodyHash) then none
          else some .occurrenceCommandMismatch
        else some .unknownCommand
      else some .releaseMismatch
    else some .occurrenceBindingMismatch
  else some .missingOccurrence

def economicRejectCode (ctx : T.Context) (pre : State) (command : T.Command) : Option T.RejectCode :=
  match contextRejectCode ctx pre.moduleReleaseId command with
  | some code => some code
  | none => match policyFor pre command.asset with
      | none => some .unknownAsset
      | some policy => T.rejectCode ctx (project pre policy) command

def candidateFor (pre : State) (policy : T.Policy) (command : T.Command) : State :=
  { pre with balances := F.transferRows (project pre policy) command pre.balances }

/-- Missing policy leaves the total function at PRE. Economic success proves
that the actual selected-policy branch was taken. -/
def candidate (pre : State) (command : T.Command) : State :=
  match policyFor pre command.asset with
  | none => pre
  | some policy => candidateFor pre policy command

def Resources (state : State) : Prop :=
  state.policies.length ≤ 256 ∧ state.balances.length ≤ 4096 ∧ state.supplies.length ≤ 256 ∧
    (stateBytes state).length ≤ 1048576

instance (state : State) : Decidable (Resources state) :=
  inferInstanceAs (Decidable (state.policies.length ≤ 256 ∧ state.balances.length ≤ 4096 ∧
    state.supplies.length ≤ 256 ∧ (stateBytes state).length ≤ 1048576))

inductive RejectCode where
  | economic (code : T.RejectCode)
  | stateResourceLimit
  deriving DecidableEq, Repr

def RejectCode.code : RejectCode → String
  | .economic code => code.code
  | .stateResourceLimit => "STATE_RESOURCE_LIMIT"

def allRejectCodes : List RejectCode :=
  AssetTransferRefinementV2.allRejectCodes.map RejectCode.economic ++ [.stateResourceLimit]

theorem all_reject_codes_length : allRejectCodes.length = 18 := rfl

theorem all_reject_codes_complete (code : RejectCode) : code ∈ allRejectCodes := by
  cases code with
  | economic code => exact List.mem_append_left _ (List.mem_map.mpr
      ⟨code, AssetTransferRefinementV2.all_reject_codes_complete code, rfl⟩)
  | stateResourceLimit => simp [allRejectCodes]

theorem all_reject_codes_wire_order : allRejectCodes.map RejectCode.code =
    ["MISSING_OCCURRENCE", "OCCURRENCE_BINDING_MISMATCH", "RELEASE_MISMATCH", "UNKNOWN_COMMAND",
     "OCCURRENCE_COMMAND_MISMATCH", "UNKNOWN_ASSET", "DISABLED_ASSET", "UNREGISTERED_ASSET",
     "ASSET_ORIGIN_MISMATCH", "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED", "UNAUTHORIZED_SUBJECT",
     "SELF_TRANSFER", "ZERO_AMOUNT", "FEE_LIMIT_EXCEEDED", "EFFECT_DELTA_OVERFLOW",
     "INSUFFICIENT_BALANCE", "BALANCE_OVERFLOW", "STATE_RESOURCE_LIMIT"] := rfl

theorem all_reject_codes_wire_unique : (allRejectCodes.map RejectCode.code).Nodup := by decide

def payloadFor (pre : State) (policy : T.Policy) (command : T.Command) : T.TransferPayload :=
  { T.acceptedPayload (project pre policy) command with
    conservation := ⟨amountForAsset pre.balances command.asset,
      amountForAsset (candidateFor pre policy command).balances command.asset,
      supplyFor (numericRows pre.supplies) command.asset,
      supplyFor (numericRows (candidateFor pre policy command).supplies) command.asset, 0, 0⟩ }

def acceptedEffects (digest : B.Bytes → T.Root) (ctx : T.Context) (pre : State) (command : T.Command) :
    T.EffectEnvelope T.TransferPayload :=
  { payload := (policyFor pre command.asset).map (fun policy => payloadFor pre policy command)
    laneWrites := [⟨stateRoot digest pre, stateRoot digest (candidate pre command)⟩]
    occurrenceConsumptions := T.occurrenceIds ctx
    externalOutbox := []
    externalRoots := AssetTransferRefinementV2.ExternalRoots.zero }

inductive Verdict where
  | accepted
  | rejected (code : RejectCode)
  deriving DecidableEq, Repr

structure Result where
  verdict : Verdict
  post : State
  effects : T.EffectEnvelope T.TransferPayload
  deriving DecidableEq, Repr

def reject (code : RejectCode) (pre : State) : Result :=
  ⟨.rejected code, pre, AssetTransferRefinementV2.EffectEnvelope.empty⟩

/-- Resources are checked once on the final table. The arithmetic role fold
contains no intermediate resource decision. -/
def transition (digest : B.Bytes → T.Root) (ctx : T.Context) (pre : State) (command : T.Command) : Result :=
  match economicRejectCode ctx pre command with
  | some code => reject (.economic code) pre
  | none => if Resources (candidate pre command) then
      ⟨.accepted, candidate pre command, acceptedEffects digest ctx pre command⟩
    else reject .stateResourceLimit pre

theorem accepted_iff (digest : B.Bytes → T.Root) (ctx : T.Context) (pre : State) (command : T.Command) :
    (transition digest ctx pre command).verdict = .accepted ↔
      economicRejectCode ctx pre command = none ∧ Resources (candidate pre command) := by
  unfold transition
  cases code : economicRejectCode ctx pre command with
  | some code => simp [reject]
  | none => by_cases resource : Resources (candidate pre command) <;> simp [resource, reject]

theorem resource_reject_iff (digest : B.Bytes → T.Root) (ctx : T.Context) (pre : State) (command : T.Command) :
    (transition digest ctx pre command).verdict = .rejected .stateResourceLimit ↔
      economicRejectCode ctx pre command = none ∧ ¬ Resources (candidate pre command) := by
  unfold transition
  cases code : economicRejectCode ctx pre command with
  | some code => simp [reject]
  | none => by_cases resource : Resources (candidate pre command) <;> simp [resource, reject]

theorem economic_reject_precedes_resource (digest : B.Bytes → T.Root) (ctx : T.Context) (pre : State)
    (command : T.Command) (code : T.RejectCode) (economic : economicRejectCode ctx pre command = some code) :
    transition digest ctx pre command = reject (.economic code) pre := by
  simp only [transition, economic]

theorem rejected_noop {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : State} {command : T.Command}
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

theorem accepted_post_effects {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : State} {command : T.Command}
    (accepted : (transition digest ctx pre command).verdict = .accepted) :
    (transition digest ctx pre command).post = candidate pre command ∧
      (transition digest ctx pre command).effects = acceptedEffects digest ctx pre command := by
  have parts := (accepted_iff digest ctx pre command).mp accepted
  simp only [transition, parts.1, if_pos parts.2, and_self]

theorem context_is_scalar_first_five (ctx : T.Context) (pre : State) (policy : T.Policy) (command : T.Command) :
    T.firstFailing (T.guardPasses ctx (project pre policy) command) (T.preBalanceRejectCodes.take 5) =
      contextRejectCode ctx pre.moduleReleaseId command := rfl

theorem firstFailing_append (guard : T.RejectCode → Prop) [DecidablePred guard]
    (left right : List T.RejectCode) :
    T.firstFailing guard (left ++ right) =
      match T.firstFailing guard left with | some code => some code | none => T.firstFailing guard right := by
  induction left with
  | nil => rfl
  | cons code rest ih => by_cases pass : guard code <;> simp [T.firstFailing, pass, ih]

theorem scalar_preserves_context_failure (ctx : T.Context) (pre : State) (policy : T.Policy)
    (command : T.Command) (code : T.RejectCode)
    (failure : contextRejectCode ctx pre.moduleReleaseId command = some code) :
    T.rejectCode ctx (project pre policy) command = some code := by
  unfold T.rejectCode
  rw [show T.preBalanceRejectCodes = T.preBalanceRejectCodes.take 5 ++ T.preBalanceRejectCodes.drop 5 by decide,
    firstFailing_append, context_is_scalar_first_five, failure]

theorem economic_matches_selected (ctx : T.Context) (pre : State) (command : T.Command) (policy : T.Policy)
    (selected : policyFor pre command.asset = some policy) :
    economicRejectCode ctx pre command = T.rejectCode ctx (project pre policy) command := by
  unfold economicRejectCode
  cases common : contextRejectCode ctx pre.moduleReleaseId command with
  | none => simp only [selected]
  | some code => exact (scalar_preserves_context_failure ctx pre policy command code common).symm

theorem economic_none_iff_selected (ctx : T.Context) (pre : State) (command : T.Command) :
    economicRejectCode ctx pre command = none ↔
      ∃ policy, policyFor pre command.asset = some policy ∧ T.rejectCode ctx (project pre policy) command = none := by
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

theorem context_precedes_policy_absence (digest : B.Bytes → T.Root) (ctx : T.Context) (pre : State)
    (command : T.Command) (code : T.RejectCode)
    (failure : contextRejectCode ctx pre.moduleReleaseId command = some code) :
    transition digest ctx pre command = reject (.economic code) pre := by
  apply economic_reject_precedes_resource
  simp only [economicRejectCode, failure]

theorem absent_policy_after_context (digest : B.Bytes → T.Root) (ctx : T.Context) (pre : State)
    (command : T.Command) (common : contextRejectCode ctx pre.moduleReleaseId command = none)
    (absent : policyFor pre command.asset = none) :
    transition digest ctx pre command = reject (.economic .unknownAsset) pre := by
  apply economic_reject_precedes_resource
  simp only [economicRejectCode, common, absent]


/-- Explicit finite input conditions. Uniqueness is partly redundant under
strict order; account cover is an inequality, as in the standalone leaf. -/
structure Structural (pre : State) : Prop where
  policyUnique : (pre.policies.map (fun policy => policy.asset)).Nodup
  policyOrdered : pre.policies.Pairwise (fun left right => left.asset < right.asset)
  policyFee : ∀ policy ∈ pre.policies, T.IsU128 policy.transferFeeAtoms
  policyDecimals : ∀ policy ∈ pre.policies, policy.atomDecimals = 8
  feeOwnerTokens : ∀ policy ∈ pre.policies, B.ValidToken policy.feeOwner
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

def MetadataAdmission (rootSyntax : String → Prop) (namespaceSyntax : String → T.AssetClass → Prop)
    (pre : State) : Prop :=
  B.ValidToken pre.moduleReleaseId ∧ rootSyntax pre.moduleReleaseId ∧
    ∀ policy ∈ pre.policies, B.ValidToken policy.asset ∧ namespaceSyntax policy.asset policy.assetClass ∧
      ∀ value, policy.assetOriginRoot = some value → B.ValidToken value ∧ rootSyntax value

def Admitted (rootSyntax : String → Prop) (namespaceSyntax : String → T.AssetClass → Prop)
    (pre : State) : Prop := Structural pre ∧ MetadataAdmission rootSyntax namespaceSyntax pre ∧ Resources pre

def CommandAdmission (command : T.Command) : Prop :=
  T.CommandWellFormed command ∧ B.ValidToken command.sender ∧ B.ValidToken command.recipient

theorem policyFor_spec {pre : State} {asset : Asset} {policy : T.Policy}
    (selected : policyFor pre asset = some policy) : policy ∈ pre.policies ∧ policy.asset = asset := by
  exact ⟨List.mem_of_find?_eq_some selected, by simpa only [beq_iff_eq] using List.find?_some selected⟩

theorem structural_registered {pre : State} {command : T.Command} {policy : T.Policy}
    (admitted : Structural pre) (selected : policyFor pre command.asset = some policy) :
    command.asset ∈ pre.supplies.map V1SupplyRow.asset := by
  rw [admitted.keysAgree]
  exact List.mem_map.mpr ⟨policy, (policyFor_spec selected).1, (policyFor_spec selected).2⟩

theorem project_well_formed {pre : State} {policy : T.Policy} (admitted : Structural pre)
    (member : policy ∈ pre.policies) : T.StateWellFormed (project pre policy) := by
  have supply := G.supply_lookup_u128 pre.supplies admitted.supplyUnique admitted.supplyU128 policy.asset
  have cover := admitted.accountCover policy.asset
  constructor
  · intro owner
    exact G.balance_lookup_u128 pre.balances admitted.balanceUnique admitted.balancePositive policy.asset owner
  · exact supply
  · exact ⟨G.amountForAsset_nonnegative pre.balances
      (fun row member => (admitted.balancePositive row member).2.1.1) policy.asset,
        Int.le_trans cover supply.2⟩
  · exact cover
  · exact admitted.policyFee policy member
  · exact admitted.policyDecimals policy member

theorem update_roles_supported (rows : List AmountRow) (assets : List Asset) (asset : String)
    (delta : String → Int) (roles : List String)
    (supported : ∀ row ∈ rows, row.asset ∈ assets) (registered : asset ∈ assets) :
    ∀ row ∈ F.updateRoles rows asset delta roles, row.asset ∈ assets := by
  induction roles with
  | nil => exact supported
  | cons owner rest ih => exact G.updateRows_supported _ assets asset owner (delta owner) ih registered

theorem update_roles_tokens (rows : List AmountRow) (asset : String) (delta : String → Int)
    (roles : List String) (tokens : B.BalanceTokens rows) (assetToken : B.ValidToken asset)
    (roleTokens : ∀ owner ∈ roles, B.ValidToken owner) : B.BalanceTokens (F.updateRoles rows asset delta roles) := by
  induction roles with
  | nil => exact tokens
  | cons owner rest ih =>
      exact B.updateRows_tokens _ asset owner _
        (ih (fun next member => roleTokens next (List.mem_cons_of_mem owner member))) assetToken
        (roleTokens owner List.mem_cons_self)

theorem update_roles_ordered (rows : List AmountRow) (asset : String) (delta : String → Int)
    (roles : List String) (unique : S.Unique rows)
    (ordered : rows.Pairwise (fun left right => compare (S.balanceWire left) (S.balanceWire right) = .lt))
    (positive : S.PositiveAccounts (F.updateRoles rows asset delta roles)) :
    (F.updateRoles rows asset delta roles).Pairwise
      (fun left right => compare (S.balanceWire left) (S.balanceWire right) = .lt) := by
  cases roles with
  | nil => exact ordered
  | cons owner rest =>
      exact G.updateRows_ordered _ asset owner _
        (F.update_roles_unique rows asset delta rest unique) positive

theorem ordered_roles_tokens (pre : T.TransferState) (command : T.Command)
    (sender : B.ValidToken command.sender) (recipient : B.ValidToken command.recipient)
    (feeOwner : B.ValidToken pre.policy.feeOwner) :
    ∀ owner ∈ T.orderedRoles pre command, B.ValidToken owner := by
  intro owner member
  rw [T.orderedRoles, AssetTransferRefinementV2.mem_sort_principals] at member
  unfold T.roleOrder at member
  split at member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact sender
    · exact recipient
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact sender
    · exact recipient
    · exact feeOwner

/-- Candidate shape follows from actual economic success and initial finite
conditions; the resource decision is deliberately absent from these premises. -/
theorem economic_candidate_structural {ctx : T.Context} {pre : State} {command : T.Command}
    (admitted : Structural pre) (commandAdmitted : CommandAdmission command)
    (economic : economicRejectCode ctx pre command = none) : Structural (candidate pre command) := by
  obtain ⟨policy, selected, success⟩ := (economic_none_iff_selected ctx pre command).mp economic
  have member := (policyFor_spec selected).1
  have same := (policyFor_spec selected).2
  have wellFormed := project_well_formed admitted member
  have accepted := (AssetTransferRefinementV2.accepted_iff_no_reject
    ⟨fun _ => ""⟩ ctx (project pre policy) command).mpr success
  have accounts := F.accepted_rows_preserve_accounts admitted.balanceUnique admitted.balancePositive wellFormed accepted
  have distinct := F.accepted_distinct accepted
  have assetToken : B.ValidToken command.asset := by
    obtain ⟨row, rowMember, sameAsset⟩ := List.mem_map.mp (structural_registered admitted selected)
    exact sameAsset ▸ admitted.supplyTokens row rowMember
  rw [candidate, selected]
  constructor
  · exact admitted.policyUnique
  · exact admitted.policyOrdered
  · exact admitted.policyFee
  · exact admitted.policyDecimals
  · exact admitted.feeOwnerTokens
  · exact accounts.1
  · exact accounts.2
  · exact update_roles_ordered pre.balances _ _ _ admitted.balanceUnique admitted.balanceOrdered accounts.2
  · exact update_roles_supported pre.balances _ _ _ _ admitted.balanceSupported
      (List.mem_map.mpr ⟨policy, member, same⟩)
  · exact admitted.supplyUnique
  · exact admitted.supplyOrdered
  · exact admitted.supplyU128
  · exact admitted.keysAgree
  · intro asset
    change amountForAsset (F.transferRows (project pre policy) command pre.balances) asset ≤
      supplyFor (numericRows pre.supplies) asset
    rw [F.transferRows_totals _ _ _ admitted.balanceUnique distinct]
    exact admitted.accountCover asset
  · exact update_roles_tokens pre.balances _ _ _ admitted.balanceTokens assetToken
      (ordered_roles_tokens (project pre policy) command commandAdmitted.2.1 commandAdmitted.2.2
        (admitted.feeOwnerTokens policy member))
  · exact admitted.supplyTokens

theorem candidate_immutable (pre : State) (command : T.Command) :
    (candidate pre command).moduleReleaseId = pre.moduleReleaseId ∧
      (candidate pre command).policies = pre.policies ∧ (candidate pre command).supplies = pre.supplies := by
  unfold candidate
  cases policyFor pre command.asset <;> exact ⟨rfl, rfl, rfl⟩

theorem accepted_preserves_admission {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} {digest : B.Bytes → T.Root}
    {ctx : T.Context} {pre : State} {command : T.Command}
    (admitted : Admitted rootSyntax namespaceSyntax pre) (commandAdmitted : CommandAdmission command)
    (accepted : (transition digest ctx pre command).verdict = .accepted) :
    Admitted rootSyntax namespaceSyntax (transition digest ctx pre command).post := by
  have parts := (accepted_iff digest ctx pre command).mp accepted
  have metadata : MetadataAdmission rootSyntax namespaceSyntax (candidate pre command) := by
    unfold MetadataAdmission
    rw [(candidate_immutable pre command).1, (candidate_immutable pre command).2.1]
    exact admitted.2.1
  rw [(accepted_post_effects accepted).1]
  exact ⟨economic_candidate_structural admitted.1 commandAdmitted parts.1, metadata, parts.2⟩

/-- The selected old economic leaf is rehydrated from the actual computed
finite successor. The scalar root observer contributes no authority. -/
theorem accepted_selected_leaf {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : State}
    {command : T.Command} (roots : AssetTransferRefinementV2.RootModel)
    (unique : S.Unique pre.balances) (accepted : (transition digest ctx pre command).verdict = .accepted) :
    ∃ policy, policyFor pre command.asset = some policy ∧
      (AssetTransferRefinementV2.transition roots ctx (project pre policy) command).verdict = .accepted ∧
      project (transition digest ctx pre command).post policy =
        (AssetTransferRefinementV2.transition roots ctx (project pre policy) command).post := by
  obtain ⟨policy, selected, success⟩ := (economic_none_iff_selected ctx pre command).mp
    ((accepted_iff digest ctx pre command).mp accepted).1
  have scalar := (AssetTransferRefinementV2.accepted_iff_no_reject roots ctx _ command).mpr success
  have equal : project (transition digest ctx pre command).post policy =
      (AssetTransferRefinementV2.transition roots ctx (project pre policy) command).post := by
    rw [(accepted_post_effects accepted).1, candidate, selected]
    exact (F.accepted_materialization unique scalar).symm
  exact ⟨policy, selected, scalar, equal⟩

theorem accepted_accounting {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : State}
    {command : T.Command} (unique : S.Unique pre.balances)
    (accepted : (transition digest ctx pre command).verdict = .accepted) (asset : Asset) :
    amountForAsset (transition digest ctx pre command).post.balances asset = amountForAsset pre.balances asset ∧
      (transition digest ctx pre command).post.supplies = pre.supplies := by
  obtain ⟨policy, selected, success⟩ := (economic_none_iff_selected ctx pre command).mp
    ((accepted_iff digest ctx pre command).mp accepted).1
  have scalar := (AssetTransferRefinementV2.accepted_iff_no_reject ⟨fun _ => ""⟩ ctx _ command).mpr success
  rw [(accepted_post_effects accepted).1, candidate, selected]
  exact ⟨F.transferRows_totals _ _ _ unique (F.accepted_distinct scalar) asset, rfl⟩

theorem accepted_lookup {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : State}
    {command : T.Command} {policy : T.Policy} (selected : policyFor pre command.asset = some policy)
    (unique : S.Unique pre.balances) (accepted : (transition digest ctx pre command).verdict = .accepted)
    (asset owner : String) :
    C.lookupLast (S.accountKey asset owner) (transition digest ctx pre command).post.balances =
      C.lookupLast (S.accountKey asset owner) pre.balances +
        (if command.asset = asset then T.delta (project pre policy) command owner else 0) := by
  have success := ((accepted_iff digest ctx pre command).mp accepted).1
  rw [economic_matches_selected ctx pre command policy selected] at success
  have scalar := (AssetTransferRefinementV2.accepted_iff_no_reject ⟨fun _ => ""⟩ ctx _ command).mpr success
  rw [(accepted_post_effects accepted).1, candidate, selected]
  exact F.transferRows_lookup _ _ _ unique (F.accepted_distinct scalar) asset owner


theorem selected_scan_precedes_resources (digest : B.Bytes → T.Root) (ctx : T.Context) (pre : State)
    (command : T.Command) (policy : T.Policy) (code : T.RejectCode)
    (selected : policyFor pre command.asset = some policy)
    (authorization : ∀ reason ∈ T.preBalanceRejectCodes, T.guardPasses ctx (project pre policy) command reason)
    (scan : T.balanceCodeOn (project pre policy) command (T.orderedRoles (project pre policy) command) = some code) :
    transition digest ctx pre command = reject (.economic code) pre := by
  apply economic_reject_precedes_resource
  rw [economic_matches_selected ctx pre command policy selected]
  unfold T.rejectCode
  rw [(AssetTransferRefinementV2.firstFailing_eq_none_iff _ _).mpr authorization]
  exact scan

theorem accepted_iff_full_guards_resources (digest : B.Bytes → T.Root) (ctx : T.Context)
    (pre : State) (command : T.Command) :
    (transition digest ctx pre command).verdict = .accepted ↔
      ∃ policy, policyFor pre command.asset = some policy ∧
        (∀ reason ∈ T.preBalanceRejectCodes, T.guardPasses ctx (project pre policy) command reason) ∧
        T.balanceCodeOn (project pre policy) command (T.orderedRoles (project pre policy) command) = none ∧
        Resources (candidateFor pre policy command) := by
  rw [accepted_iff]
  constructor
  · rintro ⟨economic, resources⟩
    obtain ⟨policy, selected, success⟩ := (economic_none_iff_selected ctx pre command).mp economic
    have guards := (AssetTransferRefinementV2.reject_code_none_parts ctx _ command).mp success
    rw [candidate, selected] at resources
    exact ⟨policy, selected, guards.1, guards.2, resources⟩
  · rintro ⟨policy, selected, authorization, scan, resources⟩
    constructor
    · exact (economic_none_iff_selected ctx pre command).mpr ⟨policy, selected,
        (AssetTransferRefinementV2.reject_code_none_parts ctx _ command).mpr ⟨authorization, scan⟩⟩
    · rw [candidate, selected]
      exact resources

theorem resource_reject_iff_full_guards_resources (digest : B.Bytes → T.Root) (ctx : T.Context)
    (pre : State) (command : T.Command) :
    (transition digest ctx pre command).verdict = .rejected .stateResourceLimit ↔
      ∃ policy, policyFor pre command.asset = some policy ∧
        (∀ reason ∈ T.preBalanceRejectCodes, T.guardPasses ctx (project pre policy) command reason) ∧
        T.balanceCodeOn (project pre policy) command (T.orderedRoles (project pre policy) command) = none ∧
        ¬ Resources (candidateFor pre policy command) := by
  rw [resource_reject_iff]
  constructor
  · rintro ⟨economic, resources⟩
    obtain ⟨policy, selected, success⟩ := (economic_none_iff_selected ctx pre command).mp economic
    have guards := (AssetTransferRefinementV2.reject_code_none_parts ctx _ command).mp success
    rw [candidate, selected] at resources
    exact ⟨policy, selected, guards.1, guards.2, resources⟩
  · rintro ⟨policy, selected, authorization, scan, resources⟩
    constructor
    · exact (economic_none_iff_selected ctx pre command).mpr ⟨policy, selected,
        (AssetTransferRefinementV2.reject_code_none_parts ctx _ command).mpr ⟨authorization, scan⟩⟩
    · rw [candidate, selected]
      exact resources

theorem insertPrincipal_length (owner : String) (roles : List String) :
    (T.insertPrincipal owner roles).length = roles.length + 1 := by
  induction roles with
  | nil => rfl
  | cons head rest ih => unfold T.insertPrincipal; split <;> simp [ih]

theorem sortPrincipals_length (roles : List String) : (T.sortPrincipals roles).length = roles.length := by
  induction roles with
  | nil => rfl
  | cons head rest ih => simp only [T.sortPrincipals, insertPrincipal_length, ih, List.length_cons]

theorem ordered_roles_length_le_three (pre : T.TransferState) (command : T.Command) :
    (T.orderedRoles pre command).length ≤ 3 := by
  rw [T.orderedRoles, sortPrincipals_length]
  unfold T.roleOrder
  split <;> simp only [List.length_cons, List.length_nil] <;> decide

theorem movementRows_length_le (pre : T.TransferState) (command : T.Command) (roles : List String) :
    (T.movementRows pre command roles).length ≤ roles.length := by
  induction roles with
  | nil => exact Nat.le_refl 0
  | cons head rest ih => unfold T.movementRows; split <;> simp only [List.length_cons] <;> omega

theorem movementRows_width (pre : T.TransferState) (command : T.Command) (roles : List String)
    (bounded : ∀ owner, T.IsI128 (T.delta pre command owner)) :
    ∀ row ∈ T.movementRows pre command roles, T.IsI128 row.deltaAtoms ∧ row.deltaAtoms ≠ 0 := by
  induction roles with
  | nil => simp [T.movementRows]
  | cons head rest ih =>
      intro row member
      unfold T.movementRows at member
      split at member
      · exact ih row member
      · rename_i nonzero
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨bounded head, nonzero⟩
        · exact ih row member

/-- These are bounds on the modeled movement/fee payload, not a theorem about
the complete runtime effect-plan serializer or journal constructor. -/
theorem accepted_payload_bounds {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : State}
    {command : T.Command} {policy : T.Policy} (selected : policyFor pre command.asset = some policy)
    (accepted : (transition digest ctx pre command).verdict = .accepted) :
    (payloadFor pre policy command).movements.length ≤ 3 ∧
      (payloadFor pre policy command).feeAllocations.length ≤ 1 ∧
      (∀ row ∈ (payloadFor pre policy command).movements, T.IsI128 row.deltaAtoms ∧ row.deltaAtoms ≠ 0) ∧
      T.IsI128 policy.transferFeeAtoms := by
  have success := ((accepted_iff digest ctx pre command).mp accepted).1
  rw [economic_matches_selected ctx pre command policy selected] at success
  have scalar := (AssetTransferRefinementV2.accepted_iff_no_reject ⟨fun _ => ""⟩ ctx _ command).mpr success
  have width : AssetTransferRefinementV2.widthAdmitted (project pre policy) command :=
    AssetTransferRefinementV2.accepted_pre_balance_guard scalar (code := .effectDeltaOverflow) (by decide)
  constructor
  · exact Nat.le_trans (movementRows_length_le _ _ _) (ordered_roles_length_le_three _ _)
  constructor
  · change (if policy.transferFeeAtoms = 0 then [] else [⟨policy.feeOwner, policy.transferFeeAtoms⟩] :
      List AssetTransferRefinementV2.MovementRow).length ≤ 1
    split <;> simp only [List.length_cons, List.length_nil] <;> decide
  · exact ⟨movementRows_width _ _ _ (AssetTransferRefinementV2.accepted_deltas_i128 scalar), width.1⟩

theorem accepted_effects_bind {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : State} {command : T.Command}
    (accepted : (transition digest ctx pre command).verdict = .accepted) :
    ∃ policy occurrence, policyFor pre command.asset = some policy ∧ ctx.occurrence = some occurrence ∧
      (transition digest ctx pre command).effects.payload = some (payloadFor pre policy command) ∧
      (transition digest ctx pre command).effects.laneWrites =
        [⟨stateRoot digest pre, stateRoot digest (transition digest ctx pre command).post⟩] ∧
      (transition digest ctx pre command).effects.occurrenceConsumptions = [occurrence.occurrenceId] ∧
      (transition digest ctx pre command).effects.externalOutbox = [] ∧
      (transition digest ctx pre command).effects.externalRoots = AssetTransferRefinementV2.ExternalRoots.zero := by
  obtain ⟨policy, selected, success⟩ := (economic_none_iff_selected ctx pre command).mp
    ((accepted_iff digest ctx pre command).mp accepted).1
  have scalar := (AssetTransferRefinementV2.accepted_iff_no_reject ⟨fun _ => ""⟩ ctx _ command).mpr success
  have present : ctx.occurrence ≠ none :=
    AssetTransferRefinementV2.accepted_pre_balance_guard scalar (code := .missingOccurrence) (by decide)
  cases occurrence : ctx.occurrence with
  | none => exact False.elim (present occurrence)
  | some value =>
      rw [(accepted_post_effects accepted).1, (accepted_post_effects accepted).2]
      exact ⟨policy, value, selected, rfl, by simp [acceptedEffects, selected], rfl,
        by simp [acceptedEffects, T.occurrenceIds, occurrence], rfl, rfl⟩

theorem transition_preserves_admission {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} (digest : B.Bytes → T.Root)
    (ctx : T.Context) (pre : State) (command : T.Command)
    (admitted : Admitted rootSyntax namespaceSyntax pre) (commandAdmitted : CommandAdmission command) :
    Admitted rootSyntax namespaceSyntax (transition digest ctx pre command).post := by
  cases verdict : (transition digest ctx pre command).verdict with
  | accepted => exact accepted_preserves_admission admitted commandAdmitted verdict
  | rejected code => rw [(rejected_noop verdict).1]; exact admitted

/-- Each step sees the actual finite result of the preceding step. -/
def executeTrace (digest : B.Bytes → T.Root) : State → List (T.Context × T.Command) → State
  | pre, [] => pre
  | pre, input :: rest => executeTrace digest (transition digest input.1 pre input.2).post rest

theorem trace_preserves_admission {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} (digest : B.Bytes → T.Root)
    (pre : State) (trace : List (T.Context × T.Command))
    (admitted : Admitted rootSyntax namespaceSyntax pre) (commands : ∀ input ∈ trace, CommandAdmission input.2) :
    Admitted rootSyntax namespaceSyntax (executeTrace digest pre trace) := by
  induction trace generalizing pre with
  | nil => exact admitted
  | cons input rest ih =>
      exact ih _ (transition_preserves_admission digest input.1 pre input.2 admitted (commands input (by simp)))
        (fun next member => commands next (by simp [member]))

theorem trace_prefixes_admitted {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} (digest : B.Bytes → T.Root)
    (pre : State) (trace : List (T.Context × T.Command))
    (admitted : Admitted rootSyntax namespaceSyntax pre) (commands : ∀ input ∈ trace, CommandAdmission input.2)
    (length : Nat) : Admitted rootSyntax namespaceSyntax (executeTrace digest pre (trace.take length)) :=
  trace_preserves_admission digest pre (trace.take length) admitted
    (fun input member => commands input (List.mem_of_mem_take member))

end Proofs.AssetTransferFiniteOutcomeV2
