import Mathlib.Data.List.Nodup
import Mathlib.Data.String.Basic

/-!
# Asset-origin registry V2 bounded functional-core model

This file is a source-pinned abstract model of the rejection order and
accepted-state shape of
`transition_asset_origin_registration_v2` in the Python and Rust V2 SHADOW
cores.  On the explicit `ValidState` and `ValidCommand` domain, a successful
transition inserts one Tau-originated asset record while preserving strict
asset order and the registry uniqueness invariants.  It consumes the bound
occurrence once, writes the typed ASSET_TRANSFER lane from the supplied opaque
pre-state-root observation to the supplied opaque post-state-root observation,
and emits no value, outbox, private-port, terminal-obligation, or Oracle-plan
effect.  Every rejection preserves the pre-state and emits an empty effect
shape.

Identifiers and root payloads are abstract strings assumed to have crossed the
typed runtime decode boundary.  `ValidState` and `ValidCommand` expose the
runtime-relevant structural subdomain used by these theorems: ordered unique
assets, unique origins, native uniqueness, fixed record decimals, and native
kind/class consistency.  Token and root syntax, protected asset namespaces,
integer representation bounds, canonical JSON, and cryptographic hashes or
their recomputation remain outside the model.  Python/Rust/Lean execution equivalence
remains outside the model.  Registry authentication, mounting, settlement,
migration, release, and production authority also remain outside the model.  The
aggregate coordinator's 256-asset admission cap and all other resource bounds
are also omitted.  Thus the list-general preservation theorem does not imply
unbounded runtime acceptance.  The paired source-pin test makes drift in the
reviewed Python and Rust source surface visible and does not constitute a
universal refinement proof.
-/

namespace Proofs
namespace AssetOriginRegistryRefinementV2

abbrev Asset := String
abbrev Principal := String
abbrev Root := String
abbrev CommandKind := String

def registrationCommandKind : CommandKind := "register_asset_origin"
def assetAtomDecimals : Nat := 8
def zeroRoot : Root := "0x0000000000000000000000000000000000000000000000000000000000000000"
def productionAuthority : String := "NONE"

inductive OriginKind where
  | native
  | tauOriginated
  deriving DecidableEq, Repr

inductive AssetClass where
  | tauNativeCoin
  | canonicalZusd
  | lpShare
  | zdexProtocolToken
  | sealedBidPaymentOrInventory
  | registeredOrdinaryToken
  deriving DecidableEq, Repr

inductive RejectCode where
  | missingOccurrence
  | occurrenceBindingMismatch
  | releaseMismatch
  | unknownCommand
  | occurrenceCommandMismatch
  | unauthorizedSubject
  | grantMismatch
  | decimalScaleMismatch
  | disabledOriginKind
  | nativeAssetAccountingUnimplemented
  | duplicateAsset
  | duplicateOrigin
  deriving DecidableEq, Repr

def RejectCode.code : RejectCode → String
  | .missingOccurrence => "MISSING_OCCURRENCE"
  | .occurrenceBindingMismatch => "OCCURRENCE_BINDING_MISMATCH"
  | .releaseMismatch => "RELEASE_MISMATCH"
  | .unknownCommand => "UNKNOWN_COMMAND"
  | .occurrenceCommandMismatch => "OCCURRENCE_COMMAND_MISMATCH"
  | .unauthorizedSubject => "UNAUTHORIZED_SUBJECT"
  | .grantMismatch => "GRANT_MISMATCH"
  | .decimalScaleMismatch => "DECIMAL_SCALE_MISMATCH"
  | .disabledOriginKind => "DISABLED_ORIGIN_KIND"
  | .nativeAssetAccountingUnimplemented => "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED"
  | .duplicateAsset => "DUPLICATE_ASSET"
  | .duplicateOrigin => "DUPLICATE_ORIGIN"

def RejectCode.rank : RejectCode → Nat
  | .missingOccurrence => 0
  | .occurrenceBindingMismatch => 1
  | .releaseMismatch => 2
  | .unknownCommand => 3
  | .occurrenceCommandMismatch => 4
  | .unauthorizedSubject => 5
  | .grantMismatch => 6
  | .decimalScaleMismatch => 7
  | .disabledOriginKind => 8
  | .nativeAssetAccountingUnimplemented => 9
  | .duplicateAsset => 10
  | .duplicateOrigin => 11

def allRejectCodes : List RejectCode :=
  [ .missingOccurrence, .occurrenceBindingMismatch, .releaseMismatch,
    .unknownCommand, .occurrenceCommandMismatch, .unauthorizedSubject,
    .grantMismatch, .decimalScaleMismatch, .disabledOriginKind,
    .nativeAssetAccountingUnimplemented, .duplicateAsset, .duplicateOrigin ]

def hasDuplicateCode : List RejectCode → Bool
  | [] => false
  | code :: rest => rest.contains code || hasDuplicateCode rest

theorem all_reject_codes_length : allRejectCodes.length = 12 := rfl

theorem all_reject_codes_wire_order :
    allRejectCodes.map RejectCode.code =
      [ "MISSING_OCCURRENCE", "OCCURRENCE_BINDING_MISMATCH", "RELEASE_MISMATCH",
        "UNKNOWN_COMMAND", "OCCURRENCE_COMMAND_MISMATCH", "UNAUTHORIZED_SUBJECT",
        "GRANT_MISMATCH", "DECIMAL_SCALE_MISMATCH", "DISABLED_ORIGIN_KIND",
        "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED", "DUPLICATE_ASSET",
        "DUPLICATE_ORIGIN" ] := rfl

theorem all_reject_codes_complete (code : RejectCode) : code ∈ allRejectCodes := by
  cases code <;> decide

theorem all_reject_codes_no_duplicates : hasDuplicateCode allRejectCodes = false := by
  decide

theorem RejectCode.rank_injective {a b : RejectCode} (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact absurd h (by decide)

structure Record where
  asset : Asset
  originKind : OriginKind
  originRoot : Root
  transferPolicyRoot : Root
  issuePolicyRoot : Root
  decimals : Nat
  assetClass : AssetClass
  deriving DecidableEq, Repr

structure RegistrationPolicy where
  authoritySubject : Principal
  authorityGrantRoot : Root
  allowNative : Bool
  allowTauOriginated : Bool
  deriving DecidableEq, Repr

structure State where
  moduleReleaseId : Root
  policy : RegistrationPolicy
  assets : List Record
  deriving DecidableEq, Repr

structure Occurrence where
  preStateRoot : Root
  consumedObjectIds : List Root
  commandKind : CommandKind
  commandBodyHash : Root
  subjectId : Principal
  grantRoot : Root
  occurrenceId : Root
  deriving DecidableEq, Repr

structure Context where
  moduleReleaseId : Root
  globalPreStateRoot : Root
  preStateRootObservation : Root
  postStateRootObservation : Root
  occurrence : Option Occurrence
  deriving DecidableEq, Repr

structure Command where
  commandKind : CommandKind
  commandBodyHash : Root
  asset : Asset
  originKind : OriginKind
  originRoot : Root
  transferPolicyRoot : Root
  issuePolicyRoot : Root
  decimals : Nat
  assetClass : AssetClass
  deriving DecidableEq, Repr

inductive LaneId where
  | assetTransfer
  deriving DecidableEq, Repr

structure LaneWrite where
  laneId : LaneId
  preStateRoot : Root
  postStateRoot : Root
  deriving DecidableEq, Repr

structure EffectPlan where
  laneWrites : List LaneWrite
  occurrenceConsumptions : List Root
  valueEffects : List Root
  externalOutbox : List Root
  deriving DecidableEq, Repr

def EffectPlan.empty : EffectPlan where
  laneWrites := []
  occurrenceConsumptions := []
  valueEffects := []
  externalOutbox := []

def commandRecord (command : Command) : Record where
  asset := command.asset
  originKind := command.originKind
  originRoot := command.originRoot
  transferPolicyRoot := command.transferPolicyRoot
  issuePolicyRoot := command.issuePolicyRoot
  decimals := command.decimals
  assetClass := command.assetClass

def hasAsset (state : State) (asset : Asset) : Prop :=
  ∃ row ∈ state.assets, row.asset = asset

def hasOrigin (state : State) (originRoot : Root) : Prop :=
  ∃ row ∈ state.assets, row.originRoot = originRoot

instance hasAssetDecidable (state : State) (asset : Asset) :
    Decidable (hasAsset state asset) := by
  unfold hasAsset
  infer_instance

instance hasOriginDecidable (state : State) (originRoot : Root) :
    Decidable (hasOrigin state originRoot) := by
  unfold hasOrigin
  infer_instance

def kindClassConsistent (originKind : OriginKind) (assetClass : AssetClass) : Prop :=
  (originKind = .native) ↔ assetClass = .tauNativeCoin

def ValidRecord (row : Record) : Prop :=
  row.decimals = assetAtomDecimals ∧ kindClassConsistent row.originKind row.assetClass

def ValidCommand (command : Command) : Prop :=
  kindClassConsistent command.originKind command.assetClass

instance validRecordDecidable (row : Record) : Decidable (ValidRecord row) := by
  unfold ValidRecord kindClassConsistent
  infer_instance

instance validCommandDecidable (command : Command) : Decidable (ValidCommand command) := by
  unfold ValidCommand kindClassConsistent
  infer_instance

def StrictAssetOrder (rows : List Record) : Prop :=
  rows.Pairwise fun left right => left.asset < right.asset

def UniqueAssets (rows : List Record) : Prop :=
  (rows.map Record.asset).Nodup

def UniqueOrigins (rows : List Record) : Prop :=
  (rows.map Record.originRoot).Nodup

def nativeCount (rows : List Record) : Nat :=
  rows.countP fun row => row.originKind == .native

def NativeUnique (rows : List Record) : Prop :=
  nativeCount rows ≤ 1

structure ValidState (state : State) : Prop where
  assetOrder : StrictAssetOrder state.assets
  originUnique : UniqueOrigins state.assets
  nativeUnique : NativeUnique state.assets
  recordsValid : ∀ row ∈ state.assets, ValidRecord row

instance validStateDecidable (state : State) : Decidable (ValidState state) := by
  letI : Decidable (StrictAssetOrder state.assets) := by
    unfold StrictAssetOrder
    infer_instance
  letI : Decidable (UniqueOrigins state.assets) := by
    unfold UniqueOrigins
    infer_instance
  letI : Decidable (NativeUnique state.assets) := by
    unfold NativeUnique nativeCount
    infer_instance
  exact decidable_of_iff
    (StrictAssetOrder state.assets ∧ UniqueOrigins state.assets ∧
      NativeUnique state.assets ∧ List.Forall ValidRecord state.assets)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, List.forall_iff_forall_mem.mp h.2.2.2⟩,
      fun h => ⟨h.assetOrder, h.originUnique, h.nativeUnique,
        List.forall_iff_forall_mem.mpr h.recordsValid⟩⟩

def insertRecord (record : Record) : List Record → List Record
  | [] => [record]
  | head :: rest =>
      if record.asset ≤ head.asset then record :: head :: rest
      else head :: insertRecord record rest

def postState (pre : State) (command : Command) : State where
  moduleReleaseId := pre.moduleReleaseId
  policy := pre.policy
  assets := insertRecord (commandRecord command) pre.assets

theorem mem_insert_record (row record : Record) :
    ∀ rows : List Record, row ∈ insertRecord record rows ↔ row = record ∨ row ∈ rows
  | [] => by simp [insertRecord]
  | head :: rest => by
      by_cases h : record.asset ≤ head.asset
      · simp [insertRecord, h]
      · simp [insertRecord, h, mem_insert_record row record rest, or_left_comm]

theorem command_record_mem_post (pre : State) (command : Command) :
    commandRecord command ∈ (postState pre command).assets := by
  simp [postState, mem_insert_record]

theorem pre_record_mem_post {pre : State} {command : Command} {row : Record}
    (h : row ∈ pre.assets) : row ∈ (postState pre command).assets := by
  simpa [postState, mem_insert_record] using Or.inr h

theorem post_assets_length (pre : State) (command : Command) :
    (postState pre command).assets.length = pre.assets.length + 1 := by
  simp only [postState]
  induction pre.assets with
  | nil => rfl
  | cons head rest ih =>
      by_cases placeFirst : (commandRecord command).asset ≤ head.asset
      · simp [insertRecord, placeFirst]
      · simp [insertRecord, placeFirst, ih]

theorem insertRecord_perm (record : Record) :
    ∀ rows : List Record, (insertRecord record rows).Perm (record :: rows)
  | [] => by
      simp only [insertRecord]
      exact List.Perm.refl [record]
  | head :: rest => by
      by_cases placeFirst : record.asset ≤ head.asset
      · simp only [insertRecord, placeFirst, if_pos]
        exact List.Perm.refl (record :: head :: rest)
      · simp only [insertRecord, placeFirst, if_false]
        exact (List.Perm.cons head (insertRecord_perm record rest)).trans
          (List.Perm.swap record head rest)

theorem insertRecord_preserves_strict_asset_order (record : Record) :
    ∀ rows : List Record,
      StrictAssetOrder rows →
      (∀ row ∈ rows, row.asset ≠ record.asset) →
      StrictAssetOrder (insertRecord record rows)
  | [], _, _ => by simp only [insertRecord, StrictAssetOrder, List.pairwise_singleton]
  | head :: rest, ordered, fresh => by
      have headBefore : ∀ row ∈ rest, head.asset < row.asset :=
        (List.pairwise_cons.mp ordered).1
      have restOrdered : StrictAssetOrder rest := (List.pairwise_cons.mp ordered).2
      by_cases placeFirst : record.asset ≤ head.asset
      · simp only [insertRecord, placeFirst, if_pos, StrictAssetOrder]
        apply List.Pairwise.cons
        · intro row rowMem
          rcases List.mem_cons.mp rowMem with rowEq | rowMem
          · rw [rowEq]
            exact lt_of_le_of_ne placeFirst (Ne.symm (fresh head (by simp)))
          · exact lt_of_le_of_lt placeFirst (headBefore row rowMem)
        · exact ordered
      · simp only [insertRecord, placeFirst, if_false, StrictAssetOrder]
        apply List.Pairwise.cons
        · intro row rowMem
          rcases (mem_insert_record row record rest).mp rowMem with rowEq | rowMem
          · rw [rowEq]
            exact lt_of_not_ge placeFirst
          · exact headBefore row rowMem
        · apply insertRecord_preserves_strict_asset_order record rest restOrdered
          intro row rowMem
          exact fresh row (by simp only [List.mem_cons, rowMem, or_true])

theorem strict_asset_order_implies_unique_assets {rows : List Record}
    (ordered : StrictAssetOrder rows) : UniqueAssets rows := by
  rw [UniqueAssets, List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact ordered.imp fun before => ne_of_lt before

theorem unique_assets_implies_rows_nodup {rows : List Record}
    (unique : UniqueAssets rows) : rows.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  have keyPairwise : rows.Pairwise fun left right => left.asset ≠ right.asset := by
    rw [← List.pairwise_map, ← List.nodup_iff_pairwise_ne]
    exact unique
  apply keyPairwise.imp
  intro left right keysDiffer rowsEqual
  exact keysDiffer (congrArg Record.asset rowsEqual)

theorem insertRecord_preserves_unique_origins (record : Record) (rows : List Record)
    (unique : UniqueOrigins rows)
    (fresh : ∀ row ∈ rows, row.originRoot ≠ record.originRoot) :
    UniqueOrigins (insertRecord record rows) := by
  simp only [UniqueOrigins] at unique ⊢
  have perm := (insertRecord_perm record rows).map Record.originRoot
  apply perm.nodup_iff.mpr
  apply List.Nodup.cons
  · intro rootMem
    rcases List.mem_map.mp rootMem with ⟨row, rowMem, rootEq⟩
    exact fresh row rowMem rootEq
  · exact unique

theorem insertRecord_preserves_native_unique (record : Record) (rows : List Record)
    (tauOriginated : record.originKind = .tauOriginated)
    (unique : NativeUnique rows) : NativeUnique (insertRecord record rows) := by
  unfold NativeUnique at unique ⊢
  calc
    nativeCount (insertRecord record rows) = nativeCount (record :: rows) :=
      by
        unfold nativeCount
        exact (insertRecord_perm record rows).countP_eq
          (fun row : Record => row.originKind == OriginKind.native)
    _ = nativeCount rows := by simp [nativeCount, tauOriginated]
    _ ≤ 1 := unique

theorem insertRecord_preserves_record_validity (record : Record) (rows : List Record)
    (recordValid : ValidRecord record)
    (rowsValid : ∀ row ∈ rows, ValidRecord row) :
    ∀ row ∈ insertRecord record rows, ValidRecord row := by
  intro row rowMem
  rcases (mem_insert_record row record rows).mp rowMem with rfl | rowMem
  · exact recordValid
  · exact rowsValid row rowMem

def occurrencePasses (ctx : Context) (predicate : Occurrence → Prop) : Prop :=
  match ctx.occurrence with
  | none => False
  | some occurrence => predicate occurrence

instance occurrencePassesDecidable (ctx : Context)
    (predicate : Occurrence → Prop) [DecidablePred predicate] :
    Decidable (occurrencePasses ctx predicate) := by
  cases h : ctx.occurrence with
  | none => exact isFalse (by simp [occurrencePasses, h])
  | some occurrence =>
      simpa [occurrencePasses, h] using (inferInstance : Decidable (predicate occurrence))

def originEnabled (policy : RegistrationPolicy) : OriginKind → Bool
  | .native => policy.allowNative
  | .tauOriginated => policy.allowTauOriginated

def guardPasses (ctx : Context) (pre : State) (command : Command) : RejectCode → Prop
  | .missingOccurrence => ctx.occurrence ≠ none
  | .occurrenceBindingMismatch => occurrencePasses ctx fun occurrence =>
      occurrence.preStateRoot = ctx.globalPreStateRoot ∧ occurrence.consumedObjectIds = []
  | .releaseMismatch => ctx.moduleReleaseId = pre.moduleReleaseId
  | .unknownCommand => command.commandKind = registrationCommandKind
  | .occurrenceCommandMismatch => occurrencePasses ctx fun occurrence =>
      occurrence.commandKind = command.commandKind ∧
      occurrence.commandBodyHash = command.commandBodyHash
  | .unauthorizedSubject => occurrencePasses ctx fun occurrence =>
      occurrence.subjectId = pre.policy.authoritySubject
  | .grantMismatch => occurrencePasses ctx fun occurrence =>
      occurrence.grantRoot = pre.policy.authorityGrantRoot
  | .decimalScaleMismatch => command.decimals = assetAtomDecimals
  | .disabledOriginKind => originEnabled pre.policy command.originKind = true
  | .nativeAssetAccountingUnimplemented => command.originKind ≠ .native
  | .duplicateAsset => ¬ hasAsset pre command.asset
  | .duplicateOrigin => ¬ hasOrigin pre command.originRoot

instance guardPassesDecidable (ctx : Context) (pre : State) (command : Command) :
    DecidablePred (guardPasses ctx pre command)
  | .missingOccurrence => inferInstanceAs (Decidable (ctx.occurrence ≠ none))
  | .occurrenceBindingMismatch => inferInstanceAs (Decidable (occurrencePasses ctx fun o =>
      o.preStateRoot = ctx.globalPreStateRoot ∧ o.consumedObjectIds = []))
  | .releaseMismatch => inferInstanceAs
      (Decidable (ctx.moduleReleaseId = pre.moduleReleaseId))
  | .unknownCommand => inferInstanceAs
      (Decidable (command.commandKind = registrationCommandKind))
  | .occurrenceCommandMismatch => inferInstanceAs (Decidable (occurrencePasses ctx fun o =>
      o.commandKind = command.commandKind ∧ o.commandBodyHash = command.commandBodyHash))
  | .unauthorizedSubject => inferInstanceAs (Decidable (occurrencePasses ctx fun o =>
      o.subjectId = pre.policy.authoritySubject))
  | .grantMismatch => inferInstanceAs (Decidable (occurrencePasses ctx fun o =>
      o.grantRoot = pre.policy.authorityGrantRoot))
  | .decimalScaleMismatch => inferInstanceAs
      (Decidable (command.decimals = assetAtomDecimals))
  | .disabledOriginKind => inferInstanceAs
      (Decidable (originEnabled pre.policy command.originKind = true))
  | .nativeAssetAccountingUnimplemented => inferInstanceAs
      (Decidable (command.originKind ≠ OriginKind.native))
  | .duplicateAsset => inferInstanceAs
      (Decidable (¬ hasAsset pre command.asset))
  | .duplicateOrigin => inferInstanceAs
      (Decidable (¬ hasOrigin pre command.originRoot))

def firstFailing (g : RejectCode → Prop) [DecidablePred g] :
    List RejectCode → Option RejectCode
  | [] => none
  | code :: rest => if g code then firstFailing g rest else some code

def rejectCode (ctx : Context) (pre : State) (command : Command) : Option RejectCode :=
  firstFailing (guardPasses ctx pre command) allRejectCodes

theorem firstFailing_eq_none_iff (g : RejectCode → Prop) [DecidablePred g] :
    ∀ codes : List RejectCode, firstFailing g codes = none ↔ ∀ code ∈ codes, g code
  | [] => by simp [firstFailing]
  | head :: rest => by
      by_cases h : g head
      · simp [firstFailing, h, firstFailing_eq_none_iff g rest]
      · simp [firstFailing, h]

theorem firstFailing_some_spec (g : RejectCode → Prop) [DecidablePred g]
    {codes : List RejectCode} {selected : RejectCode}
    (h : firstFailing g codes = some selected) :
    selected ∈ codes ∧ ¬ g selected := by
  induction codes with
  | nil => simp [firstFailing] at h
  | cons head rest ih =>
      by_cases pass : g head
      · simp only [firstFailing, pass, if_pos] at h
        exact ⟨by simp [ih h |>.1], ih h |>.2⟩
      · simp only [firstFailing, pass] at h
        have : head = selected := Option.some.inj h
        subst selected
        exact ⟨by simp, pass⟩

theorem exact_reject_precedence (ctx : Context) (pre : State) (command : Command)
    (selected : RejectCode)
    (hfail : ¬ guardPasses ctx pre command selected)
    (hearlier : ∀ earlier ∈ allRejectCodes,
      earlier.rank < selected.rank → guardPasses ctx pre command earlier) :
    rejectCode ctx pre command = some selected := by
  cases selected <;>
    simp [rejectCode, firstFailing, allRejectCodes, RejectCode.rank, hfail, hearlier]

def acceptedEffectPlan (ctx : Context) (occurrence : Occurrence) : EffectPlan where
  laneWrites := [{
    laneId := .assetTransfer
    preStateRoot := ctx.preStateRootObservation
    postStateRoot := ctx.postStateRootObservation
  }]
  occurrenceConsumptions := [occurrence.occurrenceId]
  valueEffects := []
  externalOutbox := []

structure Accepted where
  post : State
  registered : Record
  effects : EffectPlan
  privatePortRoot : Root
  terminalObligationsRoot : Root
  oraclePlanRoot : Root
  productionAuthority : String
  deriving DecidableEq, Repr

structure Rejected where
  code : RejectCode
  pre : State
  post : State
  effects : EffectPlan
  deriving DecidableEq, Repr

inductive Result where
  | accepted (value : Accepted)
  | rejected (value : Rejected)
  deriving DecidableEq, Repr

def transition (ctx : Context) (pre : State) (command : Command) : Result :=
  match rejectCode ctx pre command with
  | some code => .rejected {
      code := code
      pre := pre
      post := pre
      effects := .empty
    }
  | none =>
      match ctx.occurrence with
      | none => .rejected {
          code := .missingOccurrence
          pre := pre
          post := pre
          effects := .empty
        }
      | some occurrence => .accepted {
          post := postState pre command
          registered := commandRecord command
          effects := acceptedEffectPlan ctx occurrence
          privatePortRoot := zeroRoot
          terminalObligationsRoot := zeroRoot
          oraclePlanRoot := zeroRoot
          productionAuthority := productionAuthority
        }

/-! ## Concrete non-vacuity witnesses -/

def opaqueRootA : Root :=
  "0x1111111111111111111111111111111111111111111111111111111111111111"

def opaqueRootB : Root :=
  "0x2222222222222222222222222222222222222222222222222222222222222222"

def witnessPolicy : RegistrationPolicy where
  authoritySubject := "governance"
  authorityGrantRoot := opaqueRootA
  allowNative := true
  allowTauOriginated := true

def witnessState : State where
  moduleReleaseId := opaqueRootA
  policy := witnessPolicy
  assets := []

def witnessCommand : Command where
  commandKind := registrationCommandKind
  commandBodyHash := opaqueRootA
  asset := "USD"
  originKind := .tauOriginated
  originRoot := opaqueRootA
  transferPolicyRoot := opaqueRootA
  issuePolicyRoot := zeroRoot
  decimals := assetAtomDecimals
  assetClass := .registeredOrdinaryToken

def witnessOccurrence : Occurrence where
  preStateRoot := opaqueRootA
  consumedObjectIds := []
  commandKind := registrationCommandKind
  commandBodyHash := opaqueRootA
  subjectId := "governance"
  grantRoot := opaqueRootA
  occurrenceId := opaqueRootA

def witnessContext : Context where
  moduleReleaseId := opaqueRootA
  globalPreStateRoot := opaqueRootA
  preStateRootObservation := opaqueRootA
  postStateRootObservation := opaqueRootB
  occurrence := some witnessOccurrence

def witnessAccepted : Accepted where
  post := postState witnessState witnessCommand
  registered := commandRecord witnessCommand
  effects := acceptedEffectPlan witnessContext witnessOccurrence
  privatePortRoot := zeroRoot
  terminalObligationsRoot := zeroRoot
  oraclePlanRoot := zeroRoot
  productionAuthority := productionAuthority

theorem acceptance_witness :
    transition witnessContext witnessState witnessCommand = .accepted witnessAccepted := by
  decide

def nativeWitnessCommand : Command := {
  witnessCommand with
  asset := "TAU"
  originKind := .native
  originRoot := opaqueRootB
  assetClass := .tauNativeCoin
}

theorem native_registration_rejection_witness :
    rejectCode witnessContext witnessState nativeWitnessCommand =
      some .nativeAssetAccountingUnimplemented := by
  decide

theorem acceptance_witness_on_valid_domain :
    ValidState witnessState ∧ ValidCommand witnessCommand ∧
      transition witnessContext witnessState witnessCommand = .accepted witnessAccepted := by
  decide

/-! ## Concrete rejection reachability and adjacent-failure precedence -/

def occurrenceWith (command : Command) : Occurrence := {
  witnessOccurrence with
  commandKind := command.commandKind
  commandBodyHash := command.commandBodyHash
}

def contextWith (command : Command) : Context := {
  witnessContext with
  occurrence := some (occurrenceWith command)
}

def duplicateAssetRecord : Record := commandRecord {
  witnessCommand with
  originRoot := opaqueRootB
}

def duplicateOriginRecord : Record := commandRecord {
  witnessCommand with
  asset := "AAA"
}

def populatedState (record : Record) : State := {
  witnessState with
  assets := [record]
}

def disabledTauState : State := {
  witnessState with
  policy := { witnessPolicy with allowTauOriginated := false }
}

def disabledNativeState : State := {
  witnessState with
  policy := { witnessPolicy with allowNative := false }
}

def decimalMismatchCommand : Command := { witnessCommand with decimals := 7 }

def unknownCommand : Command := { witnessCommand with commandKind := "unknown-command" }

def rejectWitnessContext : RejectCode → Context
  | .missingOccurrence => { witnessContext with occurrence := none }
  | .occurrenceBindingMismatch => {
      witnessContext with
      occurrence := some { witnessOccurrence with preStateRoot := opaqueRootB }
    }
  | .releaseMismatch => { witnessContext with moduleReleaseId := opaqueRootB }
  | .unknownCommand => contextWith unknownCommand
  | .occurrenceCommandMismatch => {
      witnessContext with
      occurrence := some { witnessOccurrence with commandBodyHash := opaqueRootB }
    }
  | .unauthorizedSubject => {
      witnessContext with
      occurrence := some { witnessOccurrence with subjectId := "mallory" }
    }
  | .grantMismatch => {
      witnessContext with
      occurrence := some { witnessOccurrence with grantRoot := opaqueRootB }
    }
  | .decimalScaleMismatch => contextWith decimalMismatchCommand
  | .disabledOriginKind => witnessContext
  | .nativeAssetAccountingUnimplemented => contextWith nativeWitnessCommand
  | .duplicateAsset => witnessContext
  | .duplicateOrigin => witnessContext

def rejectWitnessState : RejectCode → State
  | .disabledOriginKind => disabledTauState
  | .duplicateAsset => populatedState duplicateAssetRecord
  | .duplicateOrigin => populatedState duplicateOriginRecord
  | _ => witnessState

def rejectWitnessCommand : RejectCode → Command
  | .unknownCommand => unknownCommand
  | .decimalScaleMismatch => decimalMismatchCommand
  | .nativeAssetAccountingUnimplemented => nativeWitnessCommand
  | _ => witnessCommand

theorem every_reject_code_reachable_on_valid_domain (code : RejectCode) :
    ValidState (rejectWitnessState code) ∧ ValidCommand (rejectWitnessCommand code) ∧
      rejectCode (rejectWitnessContext code) (rejectWitnessState code)
        (rejectWitnessCommand code) = some code := by
  cases code <;> decide

def nextRejectCode : RejectCode → Option RejectCode
  | .missingOccurrence => some .occurrenceBindingMismatch
  | .occurrenceBindingMismatch => some .releaseMismatch
  | .releaseMismatch => some .unknownCommand
  | .unknownCommand => some .occurrenceCommandMismatch
  | .occurrenceCommandMismatch => some .unauthorizedSubject
  | .unauthorizedSubject => some .grantMismatch
  | .grantMismatch => some .decimalScaleMismatch
  | .decimalScaleMismatch => some .disabledOriginKind
  | .disabledOriginKind => some .nativeAssetAccountingUnimplemented
  | .nativeAssetAccountingUnimplemented => some .duplicateAsset
  | .duplicateAsset => some .duplicateOrigin
  | .duplicateOrigin => none

def adjacentFailureContext : RejectCode → Context
  | .missingOccurrence => { witnessContext with occurrence := none }
  | .occurrenceBindingMismatch => {
      witnessContext with
      moduleReleaseId := opaqueRootB
      occurrence := some { witnessOccurrence with preStateRoot := opaqueRootB }
    }
  | .releaseMismatch => { contextWith unknownCommand with moduleReleaseId := opaqueRootB }
  | .unknownCommand => witnessContext
  | .occurrenceCommandMismatch => {
      witnessContext with
      occurrence := some {
        witnessOccurrence with
        commandBodyHash := opaqueRootB
        subjectId := "mallory"
      }
    }
  | .unauthorizedSubject => {
      witnessContext with
      occurrence := some {
        witnessOccurrence with
        subjectId := "mallory"
        grantRoot := opaqueRootB
      }
    }
  | .grantMismatch => {
      contextWith decimalMismatchCommand with
      occurrence := some {
        occurrenceWith decimalMismatchCommand with
        grantRoot := opaqueRootB
      }
    }
  | _ => witnessContext

def adjacentFailureState : RejectCode → State
  | .decimalScaleMismatch => disabledTauState
  | .disabledOriginKind => disabledNativeState
  | .nativeAssetAccountingUnimplemented => populatedState (commandRecord nativeWitnessCommand)
  | .duplicateAsset => populatedState (commandRecord witnessCommand)
  | _ => witnessState

def adjacentFailureCommand : RejectCode → Command
  | .releaseMismatch => unknownCommand
  | .unknownCommand => unknownCommand
  | .grantMismatch => decimalMismatchCommand
  | .decimalScaleMismatch => decimalMismatchCommand
  | .disabledOriginKind => nativeWitnessCommand
  | .nativeAssetAccountingUnimplemented => nativeWitnessCommand
  | _ => witnessCommand

theorem adjacent_double_failure_precedence (earlier : RejectCode) :
    match nextRejectCode earlier with
    | none => True
    | some later =>
        ValidState (adjacentFailureState earlier) ∧
        ValidCommand (adjacentFailureCommand earlier) ∧
        ¬ guardPasses (adjacentFailureContext earlier) (adjacentFailureState earlier)
          (adjacentFailureCommand earlier) earlier ∧
        ¬ guardPasses (adjacentFailureContext earlier) (adjacentFailureState earlier)
          (adjacentFailureCommand earlier) later ∧
        rejectCode (adjacentFailureContext earlier) (adjacentFailureState earlier)
          (adjacentFailureCommand earlier) = some earlier := by
  cases earlier <;> simp only [nextRejectCode] <;> decide

theorem rejected_is_exact_noop {ctx : Context} {pre : State} {command : Command}
    {rejected : Rejected} (h : transition ctx pre command = .rejected rejected) :
    rejected.pre = pre ∧ rejected.post = pre ∧ rejected.effects = .empty := by
  simp only [transition] at h
  split at h
  · cases h
    simp only [and_self]
  · split at h
    · cases h
      simp only [and_self]
    · contradiction

theorem accepted_has_exact_effect_shape {ctx : Context} {pre : State} {command : Command}
    {accepted : Accepted} (h : transition ctx pre command = .accepted accepted) :
    accepted.post = postState pre command ∧
      accepted.registered = commandRecord command ∧
      ∃ occurrence, ctx.occurrence = some occurrence ∧
        accepted.effects = acceptedEffectPlan ctx occurrence ∧
        accepted.effects.laneWrites = [{
          laneId := .assetTransfer
          preStateRoot := ctx.preStateRootObservation
          postStateRoot := ctx.postStateRootObservation
        }] ∧
        accepted.effects.occurrenceConsumptions = [occurrence.occurrenceId] ∧
        accepted.effects.valueEffects = [] ∧ accepted.effects.externalOutbox = [] ∧
        accepted.privatePortRoot = zeroRoot ∧
        accepted.terminalObligationsRoot = zeroRoot ∧
        accepted.oraclePlanRoot = zeroRoot ∧
        accepted.productionAuthority = productionAuthority := by
  simp only [transition] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i occurrence occurrenceEq
      cases h
      exact ⟨rfl, rfl, occurrence, occurrenceEq, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl⟩

theorem accepted_reject_code_is_none {ctx : Context} {pre : State} {command : Command}
    {accepted : Accepted} (h : transition ctx pre command = .accepted accepted) :
    rejectCode ctx pre command = none := by
  simp only [transition] at h
  split at h
  · contradiction
  · assumption

theorem accepted_all_guards_pass {ctx : Context} {pre : State} {command : Command}
    {accepted : Accepted} (h : transition ctx pre command = .accepted accepted) :
    ∀ code ∈ allRejectCodes, guardPasses ctx pre command code :=
  (firstFailing_eq_none_iff (guardPasses ctx pre command) allRejectCodes).mp
    (accepted_reject_code_is_none h)

theorem accepted_consumes_exact_occurrence {ctx : Context} {pre : State}
    {command : Command} {accepted : Accepted}
    (h : transition ctx pre command = .accepted accepted) :
    ∃ occurrence, ctx.occurrence = some occurrence ∧
      accepted.effects.occurrenceConsumptions = [occurrence.occurrenceId] := by
  rcases accepted_has_exact_effect_shape h with
    ⟨_, _, occurrence, occurrenceEq, _, _, consumed, _⟩
  exact ⟨occurrence, occurrenceEq, consumed⟩

theorem accepted_registers_exact_command_record {ctx : Context} {pre : State}
    {command : Command} {accepted : Accepted}
    (h : transition ctx pre command = .accepted accepted) :
    accepted.registered = commandRecord command ∧
      commandRecord command ∈ accepted.post.assets ∧
      accepted.post.assets.length = pre.assets.length + 1 := by
  have shape := accepted_has_exact_effect_shape h
  rw [shape.1]
  exact ⟨shape.2.1, command_record_mem_post pre command, post_assets_length pre command⟩

theorem accepted_requires_authority_and_tau_origin {ctx : Context} {pre : State}
    {command : Command} {accepted : Accepted}
    (h : transition ctx pre command = .accepted accepted) :
    command.originKind = .tauOriginated ∧
      originEnabled pre.policy command.originKind = true ∧
      command.decimals = assetAtomDecimals ∧
      ∃ occurrence, ctx.occurrence = some occurrence ∧
        occurrence.subjectId = pre.policy.authoritySubject ∧
        occurrence.grantRoot = pre.policy.authorityGrantRoot := by
  have allPass := accepted_all_guards_pass h
  have nativeGuard := allPass .nativeAssetAccountingUnimplemented (by decide)
  have enabledGuard := allPass .disabledOriginKind (by decide)
  have decimalGuard := allPass .decimalScaleMismatch (by decide)
  have occurrenceGuard := allPass .missingOccurrence (by decide)
  have subjectGuard := allPass .unauthorizedSubject (by decide)
  have grantGuard := allPass .grantMismatch (by decide)
  cases hoccur : ctx.occurrence with
  | none => exact absurd occurrenceGuard (by simpa [guardPasses] using hoccur)
  | some occurrence =>
      have notNative : command.originKind ≠ .native := by
        simpa [guardPasses] using nativeGuard
      have tau : command.originKind = .tauOriginated := by
        cases hkind : command.originKind with
        | native => exact False.elim (notNative hkind)
        | tauOriginated => rfl
      exact ⟨tau, enabledGuard, decimalGuard, occurrence, rfl,
        by simpa [guardPasses, occurrencePasses, hoccur] using subjectGuard,
        by simpa [guardPasses, occurrencePasses, hoccur] using grantGuard⟩

theorem accepted_preserves_valid_state {ctx : Context} {pre : State} {command : Command}
    {accepted : Accepted} (preValid : ValidState pre)
    (commandValid : ValidCommand command)
    (h : transition ctx pre command = .accepted accepted) : ValidState accepted.post := by
  have allPass := accepted_all_guards_pass h
  have noAsset : ¬ hasAsset pre command.asset := by
    simpa [guardPasses] using allPass .duplicateAsset (by decide)
  have noOrigin : ¬ hasOrigin pre command.originRoot := by
    simpa [guardPasses] using allPass .duplicateOrigin (by decide)
  have decimal : command.decimals = assetAtomDecimals := by
    simpa [guardPasses] using allPass .decimalScaleMismatch (by decide)
  have tau := (accepted_requires_authority_and_tau_origin h).1
  have freshAsset : ∀ row ∈ pre.assets, row.asset ≠ command.asset := by
    intro row rowMem sameAsset
    exact noAsset ⟨row, rowMem, sameAsset⟩
  have freshOrigin : ∀ row ∈ pre.assets, row.originRoot ≠ command.originRoot := by
    intro row rowMem sameOrigin
    exact noOrigin ⟨row, rowMem, sameOrigin⟩
  have newRecordValid : ValidRecord (commandRecord command) := by
    exact ⟨by simpa [commandRecord] using decimal, by simpa [commandRecord] using commandValid⟩
  have postEq := (accepted_has_exact_effect_shape h).1
  rw [postEq]
  exact {
    assetOrder := by
      simpa [postState, commandRecord] using
        insertRecord_preserves_strict_asset_order (commandRecord command) pre.assets
          preValid.assetOrder (by simpa [commandRecord] using freshAsset)
    originUnique := by
      simpa [postState, commandRecord] using
        insertRecord_preserves_unique_origins (commandRecord command) pre.assets
          preValid.originUnique (by simpa [commandRecord] using freshOrigin)
    nativeUnique := by
      simpa [postState, commandRecord] using
        insertRecord_preserves_native_unique (commandRecord command) pre.assets
          (by simpa [commandRecord] using tau) preValid.nativeUnique
    recordsValid := by
      simpa [postState] using
        insertRecord_preserves_record_validity (commandRecord command) pre.assets
          newRecordValid preValid.recordsValid
  }

theorem accepted_preserves_registry_invariants {ctx : Context} {pre : State}
    {command : Command} {accepted : Accepted} (preValid : ValidState pre)
    (commandValid : ValidCommand command)
    (h : transition ctx pre command = .accepted accepted) :
    StrictAssetOrder accepted.post.assets ∧ UniqueAssets accepted.post.assets ∧
      UniqueOrigins accepted.post.assets ∧ NativeUnique accepted.post.assets := by
  have postValid := accepted_preserves_valid_state preValid commandValid h
  exact ⟨postValid.assetOrder, strict_asset_order_implies_unique_assets postValid.assetOrder,
    postValid.originUnique, postValid.nativeUnique⟩

def ExactlyOneRecord (row : Record) (rows : List Record) : Prop :=
  row ∈ rows ∧ rows.Nodup

def ExactlyOneInsertedRecord (row : Record) (before after : List Record) : Prop :=
  row ∉ before ∧ after.Perm (row :: before) ∧ ExactlyOneRecord row after

theorem accepted_inserts_exactly_one_command_record {ctx : Context} {pre : State}
    {command : Command} {accepted : Accepted} (preValid : ValidState pre)
    (commandValid : ValidCommand command)
    (h : transition ctx pre command = .accepted accepted) :
    ExactlyOneInsertedRecord (commandRecord command) pre.assets accepted.post.assets := by
  have postValid := accepted_preserves_valid_state preValid commandValid h
  have registered := accepted_registers_exact_command_record h
  have noAsset : ¬ hasAsset pre command.asset := by
    simpa [guardPasses] using accepted_all_guards_pass h .duplicateAsset (by decide)
  have absent : commandRecord command ∉ pre.assets := by
    intro commandMem
    exact noAsset ⟨commandRecord command, commandMem, rfl⟩
  have postEq := (accepted_has_exact_effect_shape h).1
  exact ⟨absent, by rw [postEq]; exact insertRecord_perm (commandRecord command) pre.assets,
    registered.2.1,
    unique_assets_implies_rows_nodup
      (strict_asset_order_implies_unique_assets postValid.assetOrder)⟩

theorem disabled_native_precedes_native_unimplemented
    (ctx : Context) (pre : State) (command : Command)
    (hkind : command.originKind = .native)
    (hdisabled : pre.policy.allowNative = false)
    (hearlier : ∀ earlier ∈ allRejectCodes,
      earlier.rank < RejectCode.disabledOriginKind.rank →
        guardPasses ctx pre command earlier) :
    rejectCode ctx pre command = some .disabledOriginKind := by
  apply exact_reject_precedence ctx pre command .disabledOriginKind
  · simp [guardPasses, originEnabled, hkind, hdisabled]
  · exact hearlier

theorem duplicate_asset_precedes_duplicate_origin
    (ctx : Context) (pre : State) (command : Command)
    (hasset : hasAsset pre command.asset)
    (horigin : hasOrigin pre command.originRoot)
    (hearlier : ∀ earlier ∈ allRejectCodes,
      earlier.rank < RejectCode.duplicateAsset.rank →
        guardPasses ctx pre command earlier) :
    rejectCode ctx pre command = some .duplicateAsset ∧
      hasOrigin pre command.originRoot := by
  constructor
  · apply exact_reject_precedence ctx pre command .duplicateAsset
    · simp [guardPasses, hasset]
    · exact hearlier
  · exact horigin

end AssetOriginRegistryRefinementV2
end Proofs
