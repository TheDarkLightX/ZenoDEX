/-!
# Asset-origin registry V2 bounded functional-core model

This file models the rejection order and accepted-state shape of
`transition_asset_origin_registration_v2` in the Python and Rust V2 SHADOW
cores.  A successful transition inserts one Tau-originated asset record in
asset order, consumes the bound occurrence once, writes the ASSET_TRANSFER
lane once, and emits no value, outbox, private-port, terminal-obligation, or
Oracle-plan effect.  Every rejection preserves the pre-state and emits an
empty effect shape.

Identifiers and roots are opaque strings.  Runtime constructors, canonical
JSON, cryptographic hashes, Python/Rust/Lean execution equivalence, registry
authentication, mounting, settlement, migration, release, and production authority
remain outside this model.  The paired source-pin test makes drift
in the modeled Python and Rust files visible.
-/

namespace Proofs
namespace AssetOriginRegistryRefinementV2

abbrev Asset := String
abbrev Principal := String
abbrev Root := String
abbrev CommandKind := String

def registrationCommandKind : CommandKind := "register_asset_origin"
def assetAtomDecimals : Nat := 8
def productionAuthority : String := "NONE"

theorem production_authority_is_none : productionAuthority = "NONE" := rfl

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

def commandRecord (command : Command) : Record where
  asset := command.asset
  originKind := command.originKind
  originRoot := command.originRoot
  transferPolicyRoot := command.transferPolicyRoot
  issuePolicyRoot := command.issuePolicyRoot
  decimals := command.decimals
  assetClass := command.assetClass

def hasAsset (state : State) (asset : Asset) : Bool :=
  state.assets.any fun row => row.asset = asset

def hasOrigin (state : State) (originRoot : Root) : Bool :=
  state.assets.any fun row => row.originRoot = originRoot

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
      simp only [insertRecord]
      split <;> simp_all

def occurrencePasses (ctx : Context) (predicate : Occurrence → Prop) : Prop :=
  match ctx.occurrence with
  | none => True
  | some occurrence => predicate occurrence

instance occurrencePassesDecidable (ctx : Context)
    (predicate : Occurrence → Prop) [DecidablePred predicate] :
    Decidable (occurrencePasses ctx predicate) := by
  cases h : ctx.occurrence with
  | none => exact isTrue (by simp [occurrencePasses, h])
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
  | .duplicateAsset => hasAsset pre command.asset = false
  | .duplicateOrigin => hasOrigin pre command.originRoot = false

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
      (Decidable (hasAsset pre command.asset = false))
  | .duplicateOrigin => inferInstanceAs
      (Decidable (hasOrigin pre command.originRoot = false))

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
    (selected : RejectCode) (hselected : selected ∈ allRejectCodes)
    (hfail : ¬ guardPasses ctx pre command selected)
    (hearlier : ∀ earlier ∈ allRejectCodes,
      earlier.rank < selected.rank → guardPasses ctx pre command earlier) :
    rejectCode ctx pre command = some selected := by
  cases selected <;> simp_all [rejectCode, firstFailing, allRejectCodes, RejectCode.rank]

structure Accepted where
  post : State
  registered : Record
  consumedOccurrences : List Root
  laneWriteCount : Nat
  valueEffectCount : Nat
  externalOutboxCount : Nat
  privatePortRootIsZero : Bool
  terminalObligationsRootIsZero : Bool
  oraclePlanRootIsZero : Bool
  deriving DecidableEq, Repr

structure Rejected where
  code : RejectCode
  pre : State
  post : State
  consumedOccurrences : List Root
  laneWriteCount : Nat
  valueEffectCount : Nat
  externalOutboxCount : Nat
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
      consumedOccurrences := []
      laneWriteCount := 0
      valueEffectCount := 0
      externalOutboxCount := 0
    }
  | none =>
      match ctx.occurrence with
      | none => .rejected {
          code := .missingOccurrence
          pre := pre
          post := pre
          consumedOccurrences := []
          laneWriteCount := 0
          valueEffectCount := 0
          externalOutboxCount := 0
        }
      | some occurrence => .accepted {
          post := postState pre command
          registered := commandRecord command
          consumedOccurrences := [occurrence.occurrenceId]
          laneWriteCount := 1
          valueEffectCount := 0
          externalOutboxCount := 0
          privatePortRootIsZero := true
          terminalObligationsRootIsZero := true
          oraclePlanRootIsZero := true
        }

/-! ## Concrete non-vacuity witnesses -/

def witnessPolicy : RegistrationPolicy where
  authoritySubject := "governance"
  authorityGrantRoot := "grant-root"
  allowNative := true
  allowTauOriginated := true

def witnessState : State where
  moduleReleaseId := "module-release"
  policy := witnessPolicy
  assets := []

def witnessCommand : Command where
  commandKind := registrationCommandKind
  commandBodyHash := "command-hash"
  asset := "USD"
  originKind := .tauOriginated
  originRoot := "origin-root"
  transferPolicyRoot := "transfer-policy-root"
  issuePolicyRoot := "zero-root"
  decimals := assetAtomDecimals
  assetClass := .registeredOrdinaryToken

def witnessOccurrence : Occurrence where
  preStateRoot := "global-pre-root"
  consumedObjectIds := []
  commandKind := registrationCommandKind
  commandBodyHash := "command-hash"
  subjectId := "governance"
  grantRoot := "grant-root"
  occurrenceId := "occurrence-root"

def witnessContext : Context where
  moduleReleaseId := "module-release"
  globalPreStateRoot := "global-pre-root"
  occurrence := some witnessOccurrence

def witnessAccepted : Accepted where
  post := postState witnessState witnessCommand
  registered := commandRecord witnessCommand
  consumedOccurrences := [witnessOccurrence.occurrenceId]
  laneWriteCount := 1
  valueEffectCount := 0
  externalOutboxCount := 0
  privatePortRootIsZero := true
  terminalObligationsRootIsZero := true
  oraclePlanRootIsZero := true

theorem acceptance_witness :
    transition witnessContext witnessState witnessCommand = .accepted witnessAccepted := by
  decide

def nativeWitnessCommand : Command := {
  witnessCommand with
  asset := "TAU"
  originKind := .native
  originRoot := "native-origin-root"
  assetClass := .tauNativeCoin
}

theorem native_registration_rejection_witness :
    rejectCode witnessContext witnessState nativeWitnessCommand =
      some .nativeAssetAccountingUnimplemented := by
  decide

theorem transition_total (ctx : Context) (pre : State) (command : Command) :
    ∃ result, transition ctx pre command = result := ⟨_, rfl⟩

theorem rejected_is_exact_noop {ctx : Context} {pre : State} {command : Command}
    {rejected : Rejected} (h : transition ctx pre command = .rejected rejected) :
    rejected.pre = pre ∧ rejected.post = pre ∧
      rejected.consumedOccurrences = [] ∧ rejected.laneWriteCount = 0 ∧
      rejected.valueEffectCount = 0 ∧ rejected.externalOutboxCount = 0 := by
  simp only [transition] at h
  split at h
  · cases h
    simp
  · split at h
    · cases h
      simp
    · contradiction

theorem accepted_has_exact_effect_shape {ctx : Context} {pre : State} {command : Command}
    {accepted : Accepted} (h : transition ctx pre command = .accepted accepted) :
    accepted.post = postState pre command ∧
      accepted.registered = commandRecord command ∧
      accepted.laneWriteCount = 1 ∧ accepted.valueEffectCount = 0 ∧
      accepted.externalOutboxCount = 0 ∧ accepted.privatePortRootIsZero = true ∧
      accepted.terminalObligationsRootIsZero = true ∧
      accepted.oraclePlanRootIsZero = true := by
  simp only [transition] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · cases h
      simp

theorem accepted_consumes_exact_occurrence {ctx : Context} {pre : State}
    {command : Command} {accepted : Accepted}
    (h : transition ctx pre command = .accepted accepted) :
    ∃ occurrence, ctx.occurrence = some occurrence ∧
      accepted.consumedOccurrences = [occurrence.occurrenceId] := by
  simp only [transition] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i occurrence hoccur
      cases h
      exact ⟨occurrence, hoccur, rfl⟩

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
  have noReject : rejectCode ctx pre command = none := by
    simp only [transition] at h
    split at h
    · contradiction
    · assumption
  have allPass := (firstFailing_eq_none_iff (guardPasses ctx pre command) allRejectCodes).mp noReject
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

theorem disabled_native_precedes_native_unimplemented
    (ctx : Context) (pre : State) (command : Command)
    (hkind : command.originKind = .native)
    (hdisabled : pre.policy.allowNative = false)
    (hearlier : ∀ earlier ∈ allRejectCodes,
      earlier.rank < RejectCode.disabledOriginKind.rank →
        guardPasses ctx pre command earlier) :
    rejectCode ctx pre command = some .disabledOriginKind := by
  apply exact_reject_precedence ctx pre command .disabledOriginKind (by decide)
  · simp [guardPasses, originEnabled, hkind, hdisabled]
  · exact hearlier

theorem duplicate_asset_precedes_duplicate_origin
    (ctx : Context) (pre : State) (command : Command)
    (hasset : hasAsset pre command.asset = true)
    (horigin : hasOrigin pre command.originRoot = true)
    (hearlier : ∀ earlier ∈ allRejectCodes,
      earlier.rank < RejectCode.duplicateAsset.rank →
        guardPasses ctx pre command earlier) :
    rejectCode ctx pre command = some .duplicateAsset ∧
      hasOrigin pre command.originRoot = true := by
  constructor
  · apply exact_reject_precedence ctx pre command .duplicateAsset (by decide)
    · simp [guardPasses, hasset]
    · exact hearlier
  · exact horigin

end AssetOriginRegistryRefinementV2
end Proofs
