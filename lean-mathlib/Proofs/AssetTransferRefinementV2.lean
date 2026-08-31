/-!
# ASSET_TRANSFER V2 bounded functional-core model

This file models the deciding arithmetic and rejection order of
`src/core/asset_transfer_module_v2.py`, with its public values from
`src/core/asset_transfer_types_v2.py`.  It is a one-asset projection: policy
and supply lookup become one policy and one supply value, while balances remain
a total principal-to-atom function.  Missing rows therefore read as zero, as in
the Python core.

The first fifteen failures are checked in a fixed order.  The last balance
phase follows the Python V2 implementation more closely than the V1 model: it
scans the deduplicated touched principals in canonical principal order and
returns the first underflow or overflow it encounters.  The theorem
`sorted_balance_scan_can_report_overflow_before_sender_underflow` records the
resulting adversarial witness.

Amounts and supplies use explicit `u128` predicates.  Effect deltas use an
explicit `i128` predicate.  Runtime constructors establish these input
predicates; they are premises here.  An occurrence is consumed exactly once on
acceptance, consumed-object inputs must be empty, the external outbox is empty,
and the private-port, terminal-obligation, and Oracle-plan roots are the zero
root.  Roots and command-body digests are opaque strings whose equality is
observed.  No cryptographic property is claimed.

`AssetLaneAggregate` and `rebindLane` model the coordinator's bounded
projection and envelope rewrite.  Registry membership, canonical encoding,
hash or codec equivalence, runtime mounting, release/profile authentication,
settlement, publication, migration, and production authority remain outside
this model.  In particular, this file proves no refinement theorem connecting
Lean evaluation to Python or Rust execution.  The source-pin test reopens
review when the modeled Python files change.

The local leaf aggregates a fee-owner alias with the sender and can conserve
that transfer locally.  The current global refinement checker imposes a
stronger annotation rule: each fee allocation needs a same-key positive
state-bearing credit at least as large as the allocation.  A net-debited
sender/fee-owner alias therefore does not obtain global acceptance from any
theorem here.
-/

namespace Proofs
namespace AssetTransferRefinementV2

/-! ## Widths and opaque identifiers -/

def u128Max : Int := 340282366920938463463374607431768211455
def i128Max : Int := 170141183460469231731687303715884105727
def i128Min : Int := -170141183460469231731687303715884105728

theorem u128Max_eq_pow : u128Max = 2 ^ 128 - 1 := by decide
theorem i128Max_eq_pow : i128Max = 2 ^ 127 - 1 := by decide
theorem i128Min_eq_pow : i128Min = -(2 ^ 127) := by decide

def IsU128 (x : Int) : Prop := 0 ≤ x ∧ x ≤ u128Max
def IsI128 (x : Int) : Prop := i128Min ≤ x ∧ x ≤ i128Max

instance (x : Int) : Decidable (IsU128 x) :=
  inferInstanceAs (Decidable (0 ≤ x ∧ x ≤ u128Max))

instance (x : Int) : Decidable (IsI128 x) :=
  inferInstanceAs (Decidable (i128Min ≤ x ∧ x ≤ i128Max))

abbrev Principal := String
abbrev Asset := String
abbrev Root := String
abbrev CommandKind := String

def zeroRoot : Root :=
  "0x0000000000000000000000000000000000000000000000000000000000000000"

def assetTransferCommandKind : CommandKind := "asset_transfer"
def productionAuthority : String := "NONE"

theorem production_authority_is_none : productionAuthority = "NONE" := rfl

/-! ## Closed asset classes and rejection codes -/

inductive AssetClass where
  | tauNativeCoin
  | canonicalZusd
  | lpShare
  | zdexProtocolToken
  | sealedBidPaymentOrInventory
  | registeredOrdinaryToken
  deriving DecidableEq, Repr

def AssetClass.code : AssetClass → String
  | .tauNativeCoin => "tau_native_coin"
  | .canonicalZusd => "canonical_zusd"
  | .lpShare => "lp_share"
  | .zdexProtocolToken => "zdex_protocol_token"
  | .sealedBidPaymentOrInventory => "sealed_bid_payment_or_inventory"
  | .registeredOrdinaryToken => "registered_ordinary_token"

def allAssetClasses : List AssetClass :=
  [ .tauNativeCoin, .canonicalZusd, .lpShare, .zdexProtocolToken,
    .sealedBidPaymentOrInventory, .registeredOrdinaryToken ]

theorem all_asset_classes_complete (c : AssetClass) : c ∈ allAssetClasses := by
  cases c <;> decide

inductive RejectCode where
  | missingOccurrence
  | occurrenceBindingMismatch
  | releaseMismatch
  | unknownCommand
  | occurrenceCommandMismatch
  | unknownAsset
  | disabledAsset
  | unregisteredAsset
  | assetOriginMismatch
  | nativeAssetAccountingUnimplemented
  | unauthorizedSubject
  | selfTransfer
  | zeroAmount
  | feeLimitExceeded
  | effectDeltaOverflow
  | insufficientBalance
  | balanceOverflow
  deriving DecidableEq, Repr

def RejectCode.code : RejectCode → String
  | .missingOccurrence => "MISSING_OCCURRENCE"
  | .occurrenceBindingMismatch => "OCCURRENCE_BINDING_MISMATCH"
  | .releaseMismatch => "RELEASE_MISMATCH"
  | .unknownCommand => "UNKNOWN_COMMAND"
  | .occurrenceCommandMismatch => "OCCURRENCE_COMMAND_MISMATCH"
  | .unknownAsset => "UNKNOWN_ASSET"
  | .disabledAsset => "DISABLED_ASSET"
  | .unregisteredAsset => "UNREGISTERED_ASSET"
  | .assetOriginMismatch => "ASSET_ORIGIN_MISMATCH"
  | .nativeAssetAccountingUnimplemented => "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED"
  | .unauthorizedSubject => "UNAUTHORIZED_SUBJECT"
  | .selfTransfer => "SELF_TRANSFER"
  | .zeroAmount => "ZERO_AMOUNT"
  | .feeLimitExceeded => "FEE_LIMIT_EXCEEDED"
  | .effectDeltaOverflow => "EFFECT_DELTA_OVERFLOW"
  | .insufficientBalance => "INSUFFICIENT_BALANCE"
  | .balanceOverflow => "BALANCE_OVERFLOW"

def RejectCode.rank : RejectCode → Nat
  | .missingOccurrence => 0
  | .occurrenceBindingMismatch => 1
  | .releaseMismatch => 2
  | .unknownCommand => 3
  | .occurrenceCommandMismatch => 4
  | .unknownAsset => 5
  | .disabledAsset => 6
  | .unregisteredAsset => 7
  | .assetOriginMismatch => 8
  | .nativeAssetAccountingUnimplemented => 9
  | .unauthorizedSubject => 10
  | .selfTransfer => 11
  | .zeroAmount => 12
  | .feeLimitExceeded => 13
  | .effectDeltaOverflow => 14
  | .insufficientBalance => 15
  | .balanceOverflow => 16

def allRejectCodes : List RejectCode :=
  [ .missingOccurrence, .occurrenceBindingMismatch, .releaseMismatch,
    .unknownCommand, .occurrenceCommandMismatch, .unknownAsset, .disabledAsset,
    .unregisteredAsset, .assetOriginMismatch, .nativeAssetAccountingUnimplemented,
    .unauthorizedSubject, .selfTransfer, .zeroAmount, .feeLimitExceeded,
    .effectDeltaOverflow, .insufficientBalance, .balanceOverflow ]

/-- Codes decided before the ordered account-row scan. -/
def preBalanceRejectCodes : List RejectCode := allRejectCodes.take 15

def hasDuplicateCode : List RejectCode → Bool
  | [] => false
  | c :: rest => rest.contains c || hasDuplicateCode rest

theorem all_reject_codes_length : allRejectCodes.length = 17 := rfl

theorem all_reject_codes_wire_order :
    allRejectCodes.map RejectCode.code =
      [ "MISSING_OCCURRENCE", "OCCURRENCE_BINDING_MISMATCH", "RELEASE_MISMATCH",
        "UNKNOWN_COMMAND", "OCCURRENCE_COMMAND_MISMATCH", "UNKNOWN_ASSET",
        "DISABLED_ASSET", "UNREGISTERED_ASSET", "ASSET_ORIGIN_MISMATCH",
        "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED", "UNAUTHORIZED_SUBJECT",
        "SELF_TRANSFER", "ZERO_AMOUNT", "FEE_LIMIT_EXCEEDED",
        "EFFECT_DELTA_OVERFLOW", "INSUFFICIENT_BALANCE", "BALANCE_OVERFLOW" ] := rfl

theorem all_reject_codes_complete (c : RejectCode) : c ∈ allRejectCodes := by
  cases c <;> decide

theorem all_reject_codes_no_duplicates : hasDuplicateCode allRejectCodes = false := by
  decide

theorem RejectCode.rank_injective {a b : RejectCode} (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact absurd h (by decide)

/-! ## Source-shaped state, context, occurrence, and command -/

structure Policy where
  asset : Asset
  feeOwner : Principal
  transferFeeAtoms : Int
  enabled : Bool
  assetClass : AssetClass
  assetOriginRoot : Option Root
  atomDecimals : Nat
  deriving DecidableEq, Repr

structure TransferState where
  moduleReleaseId : Root
  policy : Policy
  balance : Principal → Int
  supplyAtoms : Int
  /-- Projection of the finite Python balance-row sum. -/
  accountTotalAtoms : Int

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
  sender : Principal
  recipient : Principal
  amountAtoms : Int
  maxFeeAtoms : Int
  assetOriginRoot : Option Root
  deriving DecidableEq, Repr

structure StateWellFormed (s : TransferState) : Prop where
  balances : ∀ p : Principal, IsU128 (s.balance p)
  supply : IsU128 s.supplyAtoms
  accountTotal : IsU128 s.accountTotalAtoms
  accountCover : s.accountTotalAtoms ≤ s.supplyAtoms
  fee : IsU128 s.policy.transferFeeAtoms
  decimals : s.policy.atomDecimals = 8

structure CommandWellFormed (c : Command) : Prop where
  amount : IsU128 c.amountAtoms
  maxFee : IsU128 c.maxFeeAtoms

/-! ## Aggregated deltas and canonical balance scan -/

def indicator (q : Principal) (value : Int) (p : Principal) : Int :=
  if p = q then value else 0

def delta (pre : TransferState) (cmd : Command) (p : Principal) : Int :=
  indicator cmd.sender (-(cmd.amountAtoms + pre.policy.transferFeeAtoms)) p
    + indicator cmd.recipient cmd.amountAtoms p
    + indicator pre.policy.feeOwner pre.policy.transferFeeAtoms p

def postBalance (pre : TransferState) (cmd : Command) (p : Principal) : Int :=
  pre.balance p + delta pre cmd p

/-- The three dictionary keys before Python's final `sorted` call.  The
sender/recipient duplicate is excluded by the earlier self-transfer guard. -/
def roleOrder (pre : TransferState) (cmd : Command) : List Principal :=
  if pre.policy.feeOwner = cmd.sender ∨ pre.policy.feeOwner = cmd.recipient then
    [cmd.sender, cmd.recipient]
  else
    [cmd.sender, cmd.recipient, pre.policy.feeOwner]

/-- Transparent insertion sort for the bounded role list.  String order is the
canonical-order abstraction; no Python/Lean Unicode collation equivalence is
claimed. -/
def insertPrincipal (principal : Principal) : List Principal → List Principal
  | [] => [principal]
  | head :: rest =>
      if principal ≤ head then principal :: head :: rest
      else head :: insertPrincipal principal rest

def sortPrincipals : List Principal → List Principal
  | [] => []
  | head :: rest => insertPrincipal head (sortPrincipals rest)

def orderedRoles (pre : TransferState) (cmd : Command) : List Principal :=
  sortPrincipals (roleOrder pre cmd)

theorem mem_insert_principal (p q : Principal) :
    ∀ ps : List Principal, p ∈ insertPrincipal q ps ↔ p = q ∨ p ∈ ps
  | [] => by simp [insertPrincipal]
  | head :: rest => by
      by_cases h : q ≤ head
      · simp [insertPrincipal, h]
      · simp [insertPrincipal, h, mem_insert_principal p q rest, or_left_comm]

theorem mem_sort_principals (p : Principal) :
    ∀ ps : List Principal, p ∈ sortPrincipals ps ↔ p ∈ ps
  | [] => by simp [sortPrincipals]
  | head :: rest => by
      simp [sortPrincipals, mem_insert_principal, mem_sort_principals p rest]

def widthAdmitted (pre : TransferState) (cmd : Command) : Prop :=
  IsI128 pre.policy.transferFeeAtoms
    ∧ IsI128 (delta pre cmd cmd.sender)
    ∧ IsI128 (delta pre cmd cmd.recipient)
    ∧ IsI128 (delta pre cmd pre.policy.feeOwner)

instance (pre : TransferState) (cmd : Command) : Decidable (widthAdmitted pre cmd) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def occurrencePasses (ctx : Context) (predicate : Occurrence → Prop) : Prop :=
  match ctx.occurrence with
  | none => True
  | some occurrence => predicate occurrence

instance occurrencePassesDecidable (ctx : Context) (predicate : Occurrence → Prop)
    [DecidablePred predicate] : Decidable (occurrencePasses ctx predicate) := by
  cases h : ctx.occurrence with
  | none => exact isTrue (by simp [occurrencePasses, h])
  | some occurrence =>
      simpa [occurrencePasses, h] using (inferInstance : Decidable (predicate occurrence))

def originRegistered (pre : TransferState) (cmd : Command) : Prop :=
  pre.policy.assetOriginRoot.isSome = true ∧ cmd.assetOriginRoot.isSome = true

instance originRegisteredDecidable (pre : TransferState) (cmd : Command) :
    Decidable (originRegistered pre cmd) :=
  inferInstanceAs (Decidable
    (pre.policy.assetOriginRoot.isSome = true ∧ cmd.assetOriginRoot.isSome = true))

/-! ## Fixed pre-balance guards -/

def guardPasses (ctx : Context) (pre : TransferState) (cmd : Command) : RejectCode → Prop
  | .missingOccurrence => ctx.occurrence ≠ none
  | .occurrenceBindingMismatch => occurrencePasses ctx fun occurrence =>
      occurrence.preStateRoot = ctx.globalPreStateRoot ∧ occurrence.consumedObjectIds = []
  | .releaseMismatch => ctx.moduleReleaseId = pre.moduleReleaseId
  | .unknownCommand => cmd.commandKind = assetTransferCommandKind
  | .occurrenceCommandMismatch => occurrencePasses ctx fun occurrence =>
      occurrence.commandKind = cmd.commandKind ∧
      occurrence.commandBodyHash = cmd.commandBodyHash
  | .unknownAsset => cmd.asset = pre.policy.asset
  | .disabledAsset => pre.policy.enabled = true
  | .unregisteredAsset => originRegistered pre cmd
  | .assetOriginMismatch => pre.policy.assetOriginRoot = cmd.assetOriginRoot
  | .nativeAssetAccountingUnimplemented => pre.policy.assetClass ≠ .tauNativeCoin
  | .unauthorizedSubject => occurrencePasses ctx fun occurrence =>
      cmd.sender = occurrence.subjectId
  | .selfTransfer => cmd.sender ≠ cmd.recipient
  | .zeroAmount => cmd.amountAtoms ≠ 0
  | .feeLimitExceeded => pre.policy.transferFeeAtoms ≤ cmd.maxFeeAtoms
  | .effectDeltaOverflow => widthAdmitted pre cmd
  | .insufficientBalance => True
  | .balanceOverflow => True

instance guardPassesDecidable (ctx : Context) (pre : TransferState) (cmd : Command) :
    DecidablePred (guardPasses ctx pre cmd)
  | .missingOccurrence => inferInstanceAs (Decidable (ctx.occurrence ≠ none))
  | .occurrenceBindingMismatch => inferInstanceAs (Decidable (occurrencePasses ctx fun o =>
      o.preStateRoot = ctx.globalPreStateRoot ∧ o.consumedObjectIds = []))
  | .releaseMismatch => inferInstanceAs (Decidable (ctx.moduleReleaseId = pre.moduleReleaseId))
  | .unknownCommand => inferInstanceAs (Decidable (cmd.commandKind = assetTransferCommandKind))
  | .occurrenceCommandMismatch => inferInstanceAs (Decidable (occurrencePasses ctx fun o =>
      o.commandKind = cmd.commandKind ∧ o.commandBodyHash = cmd.commandBodyHash))
  | .unknownAsset => inferInstanceAs (Decidable (cmd.asset = pre.policy.asset))
  | .disabledAsset => inferInstanceAs (Decidable (pre.policy.enabled = true))
  | .unregisteredAsset => inferInstanceAs (Decidable (originRegistered pre cmd))
  | .assetOriginMismatch => inferInstanceAs
      (Decidable (pre.policy.assetOriginRoot = cmd.assetOriginRoot))
  | .nativeAssetAccountingUnimplemented => inferInstanceAs
      (Decidable (pre.policy.assetClass ≠ AssetClass.tauNativeCoin))
  | .unauthorizedSubject => inferInstanceAs (Decidable (occurrencePasses ctx fun o =>
      cmd.sender = o.subjectId))
  | .selfTransfer => inferInstanceAs (Decidable (cmd.sender ≠ cmd.recipient))
  | .zeroAmount => inferInstanceAs (Decidable (cmd.amountAtoms ≠ 0))
  | .feeLimitExceeded => inferInstanceAs
      (Decidable (pre.policy.transferFeeAtoms ≤ cmd.maxFeeAtoms))
  | .effectDeltaOverflow => inferInstanceAs (Decidable (widthAdmitted pre cmd))
  | .insufficientBalance => inferInstanceAs (Decidable True)
  | .balanceOverflow => inferInstanceAs (Decidable True)

def firstFailing (g : RejectCode → Prop) [DecidablePred g] : List RejectCode → Option RejectCode
  | [] => none
  | code :: rest => if g code then firstFailing g rest else some code

/-- Exact left-to-right loop over the canonically ordered touched rows. -/
def balanceCodeOn (pre : TransferState) (cmd : Command) : List Principal → Option RejectCode
  | [] => none
  | principal :: rest =>
      if postBalance pre cmd principal < 0 then some .insufficientBalance
      else if u128Max < postBalance pre cmd principal then some .balanceOverflow
      else balanceCodeOn pre cmd rest

def rejectCode (ctx : Context) (pre : TransferState) (cmd : Command) : Option RejectCode :=
  match firstFailing (guardPasses ctx pre cmd) preBalanceRejectCodes with
  | some code => some code
  | none => balanceCodeOn pre cmd (orderedRoles pre cmd)

/-! ## Exact fixed-prefix precedence -/

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
  | c :: rest => (∀ c' ∈ rest, c.rank < c'.rank) ∧ RankSorted rest

instance RankSorted.decidable : ∀ codes : List RejectCode, Decidable (RankSorted codes)
  | [] => inferInstanceAs (Decidable True)
  | _ :: rest =>
      have : Decidable (RankSorted rest) := RankSorted.decidable rest
      inferInstanceAs (Decidable ((_ ∧ RankSorted rest)))

theorem pre_balance_codes_rank_sorted : RankSorted preBalanceRejectCodes := by decide

theorem pre_balance_codes_complete {c : RejectCode} (h : c.rank < 15) :
    c ∈ preBalanceRejectCodes := by
  cases c <;> simp_all [RejectCode.rank, preBalanceRejectCodes, allRejectCodes]

theorem firstFailing_some_spec (g : RejectCode → Prop) [DecidablePred g] :
    ∀ (codes : List RejectCode) (c : RejectCode), RankSorted codes →
      firstFailing g codes = some c →
        c ∈ codes ∧ ¬ g c ∧ ∀ c' ∈ codes, c'.rank < c.rank → g c'
  | [], _, _, h => by simp [firstFailing] at h
  | c₀ :: rest, c, hs, h => by
      by_cases hg : g c₀
      · simp only [firstFailing, if_pos hg] at h
        obtain ⟨hmem, hnot, hbefore⟩ := firstFailing_some_spec g rest c hs.2 h
        refine ⟨List.mem_cons_of_mem c₀ hmem, hnot, ?_⟩
        intro c' hc' hlt
        rcases List.mem_cons.mp hc' with rfl | hc'
        · exact hg
        · exact hbefore c' hc' hlt
      · simp only [firstFailing, if_neg hg, Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_self, hg, ?_⟩
        intro c' hc' hlt
        rcases List.mem_cons.mp hc' with rfl | hc'
        · omega
        · have := hs.1 c' hc'
          omega

theorem firstFailing_some_of (g : RejectCode → Prop) [DecidablePred g]
    (codes : List RejectCode) (hs : RankSorted codes) (c : RejectCode) (hc : c ∈ codes)
    (hnot : ¬ g c) (hbefore : ∀ c' ∈ codes, c'.rank < c.rank → g c') :
    firstFailing g codes = some c := by
  cases hf : firstFailing g codes with
  | none => exact absurd ((firstFailing_eq_none_iff g codes).mp hf c hc) hnot
  | some c'' =>
      obtain ⟨hmem, hnot'', hbefore''⟩ := firstFailing_some_spec g codes c'' hs hf
      by_cases h1 : c''.rank < c.rank
      · exact absurd (hbefore c'' hmem h1) hnot''
      · by_cases h2 : c.rank < c''.rank
        · exact absurd (hbefore'' c hc h2) hnot
        · have heq : c''.rank = c.rank := by omega
          rw [RejectCode.rank_injective heq]

theorem pre_balance_reject_exact_precedence
    (ctx : Context) (pre : TransferState) (cmd : Command) (c : RejectCode)
    (hc : c.rank < 15) :
    firstFailing (guardPasses ctx pre cmd) preBalanceRejectCodes = some c ↔
      ¬ guardPasses ctx pre cmd c ∧
      ∀ c', c'.rank < c.rank → guardPasses ctx pre cmd c' := by
  constructor
  · intro h
    obtain ⟨_, hnot, hbefore⟩ :=
      firstFailing_some_spec _ preBalanceRejectCodes c pre_balance_codes_rank_sorted h
    exact ⟨hnot, fun c' hlt => hbefore c' (pre_balance_codes_complete (by omega)) hlt⟩
  · intro h
    exact firstFailing_some_of _ preBalanceRejectCodes pre_balance_codes_rank_sorted c
      (pre_balance_codes_complete hc) h.1 (fun c' _ hlt => h.2 c' hlt)

theorem reject_code_none_parts (ctx : Context) (pre : TransferState) (cmd : Command) :
    rejectCode ctx pre cmd = none ↔
      (∀ c ∈ preBalanceRejectCodes, guardPasses ctx pre cmd c) ∧
      balanceCodeOn pre cmd (orderedRoles pre cmd) = none := by
  unfold rejectCode
  cases h : firstFailing (guardPasses ctx pre cmd) preBalanceRejectCodes with
  | none =>
      simp only
      exact ⟨
        fun hscan => ⟨(firstFailing_eq_none_iff _ _).mp h, hscan⟩,
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

theorem balance_code_none_iff (pre : TransferState) (cmd : Command) :
    ∀ principals : List Principal,
      balanceCodeOn pre cmd principals = none ↔
        ∀ p ∈ principals, IsU128 (postBalance pre cmd p)
  | [] => by simp [balanceCodeOn]
  | p :: ps => by
      by_cases hneg : postBalance pre cmd p < 0
      · constructor
        · intro h
          simp [balanceCodeOn, hneg] at h
        · intro hall
          have hp := hall p List.mem_cons_self
          exact absurd hp.1 (by omega)
      · by_cases hover : u128Max < postBalance pre cmd p
        · constructor
          · intro h
            simp [balanceCodeOn, hneg, hover] at h
          · intro hall
            have hp := hall p List.mem_cons_self
            exact absurd hp.2 (by omega)
        · constructor
          · intro h q hq
            have htail : balanceCodeOn pre cmd ps = none := by
              simpa [balanceCodeOn, hneg, hover] using h
            rcases List.mem_cons.mp hq with rfl | hq
            · exact ⟨by omega, by omega⟩
            · exact (balance_code_none_iff pre cmd ps).mp htail q hq
          · intro hall
            have htail : balanceCodeOn pre cmd ps = none :=
              (balance_code_none_iff pre cmd ps).mpr
                (fun q hq => hall q (List.mem_cons_of_mem p hq))
            simpa [balanceCodeOn, hneg, hover] using htail

/-! ## Effects, transition, and the no-op boundary -/

structure LaneWrite where
  preRoot : Root
  postRoot : Root
  deriving DecidableEq, Repr

structure ExternalRoots where
  privatePortRoot : Root
  terminalObligationsRoot : Root
  oracleOccurrencePlanRoot : Root
  deriving DecidableEq, Repr

def ExternalRoots.zero : ExternalRoots := ⟨zeroRoot, zeroRoot, zeroRoot⟩

structure MovementRow where
  principal : Principal
  deltaAtoms : Int
  deriving DecidableEq, Repr

structure ConservationRow where
  ownedPreAtoms : Int
  ownedPostAtoms : Int
  supplyPreAtoms : Int
  supplyPostAtoms : Int
  authorizedIssueAtoms : Int
  authorizedBurnAtoms : Int
  deriving DecidableEq, Repr

structure TransferPayload where
  movements : List MovementRow
  feeAllocations : List MovementRow
  conservation : ConservationRow
  deriving DecidableEq, Repr

structure EffectEnvelope (Payload : Type) where
  payload : Option Payload
  laneWrites : List LaneWrite
  occurrenceConsumptions : List Root
  externalOutbox : List Root
  externalRoots : ExternalRoots
  deriving DecidableEq, Repr

def EffectEnvelope.empty {Payload : Type} : EffectEnvelope Payload :=
  ⟨none, [], [], [], ExternalRoots.zero⟩

def movementRows (pre : TransferState) (cmd : Command) : List Principal → List MovementRow
  | [] => []
  | p :: rest =>
      if delta pre cmd p = 0 then movementRows pre cmd rest
      else ⟨p, delta pre cmd p⟩ :: movementRows pre cmd rest

def acceptedState (pre : TransferState) (cmd : Command) : TransferState :=
  { pre with
    balance := postBalance pre cmd
    accountTotalAtoms := pre.accountTotalAtoms }

structure RootModel where
  stateRoot : TransferState → Root

def acceptedPayload (pre : TransferState) (cmd : Command) : TransferPayload where
  movements := movementRows pre cmd (orderedRoles pre cmd)
  feeAllocations :=
    if pre.policy.transferFeeAtoms = 0 then []
    else [⟨pre.policy.feeOwner, pre.policy.transferFeeAtoms⟩]
  conservation :=
    ⟨pre.accountTotalAtoms, pre.accountTotalAtoms, pre.supplyAtoms,
      pre.supplyAtoms, 0, 0⟩

def occurrenceIds (ctx : Context) : List Root :=
  match ctx.occurrence with
  | none => []
  | some occurrence => [occurrence.occurrenceId]

def acceptedEffects (roots : RootModel) (ctx : Context)
    (pre : TransferState) (cmd : Command) : EffectEnvelope TransferPayload :=
  { payload := some (acceptedPayload pre cmd)
    laneWrites := [⟨roots.stateRoot pre, roots.stateRoot (acceptedState pre cmd)⟩]
    occurrenceConsumptions := occurrenceIds ctx
    externalOutbox := []
    externalRoots := ExternalRoots.zero }

inductive Verdict where
  | accepted
  | rejected (code : RejectCode)
  deriving DecidableEq, Repr

structure TransitionResult where
  verdict : Verdict
  post : TransferState
  effects : EffectEnvelope TransferPayload

def reject (code : RejectCode) (pre : TransferState) : TransitionResult :=
  ⟨.rejected code, pre, EffectEnvelope.empty⟩

def transition (roots : RootModel) (ctx : Context)
    (pre : TransferState) (cmd : Command) : TransitionResult :=
  match rejectCode ctx pre cmd with
  | some code => reject code pre
  | none => ⟨.accepted, acceptedState pre cmd, acceptedEffects roots ctx pre cmd⟩

theorem transition_total (roots : RootModel) (ctx : Context)
    (pre : TransferState) (cmd : Command) :
    (∃ code, rejectCode ctx pre cmd = some code ∧
      transition roots ctx pre cmd = reject code pre) ∨
    (rejectCode ctx pre cmd = none ∧
      transition roots ctx pre cmd =
        ⟨.accepted, acceptedState pre cmd, acceptedEffects roots ctx pre cmd⟩) := by
  unfold transition
  cases h : rejectCode ctx pre cmd with
  | none => exact Or.inr ⟨rfl, rfl⟩
  | some code => exact Or.inl ⟨code, rfl, rfl⟩

theorem accepted_iff_no_reject (roots : RootModel) (ctx : Context)
    (pre : TransferState) (cmd : Command) :
    (transition roots ctx pre cmd).verdict = .accepted ↔ rejectCode ctx pre cmd = none := by
  rcases transition_total roots ctx pre cmd with ⟨code, hc, heq⟩ | ⟨hn, heq⟩
  · rw [heq, hc]
    simp [reject]
  · rw [heq, hn]
    simp

theorem rejected_post_eq_pre {roots : RootModel} {ctx : Context}
    {pre : TransferState} {cmd : Command} {code : RejectCode}
    (h : (transition roots ctx pre cmd).verdict = .rejected code) :
    (transition roots ctx pre cmd).post = pre := by
  rcases transition_total roots ctx pre cmd with ⟨code', -, heq⟩ | ⟨-, heq⟩
  · rw [heq]
    rfl
  · rw [heq] at h
    simp at h

theorem rejected_effects_empty {roots : RootModel} {ctx : Context}
    {pre : TransferState} {cmd : Command} {code : RejectCode}
    (h : (transition roots ctx pre cmd).verdict = .rejected code) :
    (transition roots ctx pre cmd).effects = EffectEnvelope.empty := by
  rcases transition_total roots ctx pre cmd with ⟨code', -, heq⟩ | ⟨-, heq⟩
  · rw [heq]
    rfl
  · rw [heq] at h
    simp at h

theorem accepted_post_and_effects {roots : RootModel} {ctx : Context}
    {pre : TransferState} {cmd : Command}
    (h : (transition roots ctx pre cmd).verdict = .accepted) :
    (transition roots ctx pre cmd).post = acceptedState pre cmd ∧
    (transition roots ctx pre cmd).effects = acceptedEffects roots ctx pre cmd := by
  rcases transition_total roots ctx pre cmd with ⟨code, -, heq⟩ | ⟨-, heq⟩
  · rw [heq] at h
    simp [reject] at h
  · rw [heq]
    exact ⟨rfl, rfl⟩

theorem accepted_pre_balance_guard {roots : RootModel} {ctx : Context}
    {pre : TransferState} {cmd : Command}
    (h : (transition roots ctx pre cmd).verdict = .accepted)
    {code : RejectCode} (hmem : code ∈ preBalanceRejectCodes) :
    guardPasses ctx pre cmd code := by
  have hn := (accepted_iff_no_reject roots ctx pre cmd).mp h
  exact (reject_code_none_parts ctx pre cmd).mp hn |>.1 code hmem

theorem accepted_consumes_exact_occurrence {roots : RootModel} {ctx : Context}
    {pre : TransferState} {cmd : Command}
    (h : (transition roots ctx pre cmd).verdict = .accepted) :
    ∃ occurrence, ctx.occurrence = some occurrence ∧
      (transition roots ctx pre cmd).effects.occurrenceConsumptions =
        [occurrence.occurrenceId] := by
  have hp := accepted_post_and_effects h
  have hm := accepted_pre_balance_guard h (code := RejectCode.missingOccurrence) (by decide)
  cases ho : ctx.occurrence with
  | none =>
      simp [guardPasses, ho] at hm
  | some occurrence =>
      refine ⟨occurrence, rfl, ?_⟩
      rw [hp.2]
      simp [acceptedEffects, occurrenceIds, ho]

theorem accepted_zero_external_roots {roots : RootModel} {ctx : Context}
    {pre : TransferState} {cmd : Command}
    (h : (transition roots ctx pre cmd).verdict = .accepted) :
    (transition roots ctx pre cmd).effects.externalRoots = ExternalRoots.zero ∧
    (transition roots ctx pre cmd).effects.externalOutbox = [] := by
  rw [(accepted_post_and_effects h).2]
  exact ⟨rfl, rfl⟩

theorem accepted_conservation_row_exact {roots : RootModel} {ctx : Context}
    {pre : TransferState} {cmd : Command}
    (h : (transition roots ctx pre cmd).verdict = .accepted) :
    (transition roots ctx pre cmd).effects.payload.map
      (fun payload => payload.conservation) =
      some ⟨pre.accountTotalAtoms, pre.accountTotalAtoms, pre.supplyAtoms,
        pre.supplyAtoms, 0, 0⟩ := by
  rw [(accepted_post_and_effects h).2]
  rfl

theorem accepted_supply_unchanged {roots : RootModel} {ctx : Context}
    {pre : TransferState} {cmd : Command}
    (h : (transition roots ctx pre cmd).verdict = .accepted) :
    (transition roots ctx pre cmd).post.supplyAtoms = pre.supplyAtoms := by
  rw [(accepted_post_and_effects h).1]
  rfl

theorem accepted_balance_eq {roots : RootModel} {ctx : Context}
    {pre : TransferState} {cmd : Command}
    (h : (transition roots ctx pre cmd).verdict = .accepted) (p : Principal) :
    (transition roots ctx pre cmd).post.balance p = postBalance pre cmd p := by
  rw [(accepted_post_and_effects h).1]
  rfl

theorem delta_untouched {pre : TransferState} {cmd : Command} {p : Principal}
    (hs : p ≠ cmd.sender) (hr : p ≠ cmd.recipient) (hf : p ≠ pre.policy.feeOwner) :
    delta pre cmd p = 0 := by
  simp [delta, indicator, hs, hr, hf]

/-- The sender/fee-owner alias is locally net-debited only by the transfer
amount.  This arithmetic statement carries no global-refinement acceptance. -/
theorem fee_owner_sender_alias_is_locally_conserving
    {pre : TransferState} {cmd : Command}
    (hfee : pre.policy.feeOwner = cmd.sender)
    (hdifferent : cmd.sender ≠ cmd.recipient) :
    delta pre cmd cmd.sender = -cmd.amountAtoms ∧
    delta pre cmd cmd.recipient = cmd.amountAtoms ∧
    delta pre cmd cmd.sender + delta pre cmd cmd.recipient = 0 := by
  constructor
  · unfold delta
    rw [hfee]
    simp [indicator, hdifferent, Int.neg_add]
    exact Int.neg_add_cancel_right _ _
  · constructor
    · unfold delta
      rw [hfee]
      simp [indicator, Ne.symm hdifferent]
    · unfold delta
      rw [hfee]
      simp [indicator, hdifferent, Ne.symm hdifferent, Int.neg_add]
      rw [Int.neg_add_cancel_right]
      simpa using Int.neg_add_cancel_left cmd.amountAtoms 0

theorem sender_mem_ordered_roles (pre : TransferState) (cmd : Command) :
    cmd.sender ∈ orderedRoles pre cmd := by
  rw [orderedRoles, mem_sort_principals]
  unfold roleOrder
  split <;> simp

theorem recipient_mem_ordered_roles (pre : TransferState) (cmd : Command) :
    cmd.recipient ∈ orderedRoles pre cmd := by
  rw [orderedRoles, mem_sort_principals]
  unfold roleOrder
  split <;> simp

theorem fee_owner_mem_ordered_roles (pre : TransferState) (cmd : Command) :
    pre.policy.feeOwner ∈ orderedRoles pre cmd := by
  rw [orderedRoles, mem_sort_principals]
  unfold roleOrder
  split
  · next h => rcases h with h | h <;> simp [h]
  · simp

theorem accepted_deltas_i128 {roots : RootModel} {ctx : Context}
    {pre : TransferState} {cmd : Command}
    (h : (transition roots ctx pre cmd).verdict = .accepted) (p : Principal) :
    IsI128 (delta pre cmd p) := by
  have hw : widthAdmitted pre cmd :=
    accepted_pre_balance_guard h (code := RejectCode.effectDeltaOverflow) (by decide)
  by_cases hs : p = cmd.sender
  · rw [hs]
    exact hw.2.1
  by_cases hr : p = cmd.recipient
  · rw [hr]
    exact hw.2.2.1
  by_cases hf : p = pre.policy.feeOwner
  · rw [hf]
    exact hw.2.2.2
  rw [delta_untouched hs hr hf]
  exact ⟨by decide, by decide⟩

theorem accepted_balances_u128 {roots : RootModel} {ctx : Context}
    {pre : TransferState} {cmd : Command}
    (hpre : StateWellFormed pre)
    (h : (transition roots ctx pre cmd).verdict = .accepted) (p : Principal) :
    IsU128 ((transition roots ctx pre cmd).post.balance p) := by
  rw [accepted_balance_eq h p]
  have hn := (accepted_iff_no_reject roots ctx pre cmd).mp h
  have hscan := (reject_code_none_parts ctx pre cmd).mp hn |>.2
  have hb := (balance_code_none_iff pre cmd (orderedRoles pre cmd)).mp hscan
  by_cases hs : p = cmd.sender
  · apply hb p
    rw [hs]
    exact sender_mem_ordered_roles pre cmd
  by_cases hr : p = cmd.recipient
  · apply hb p
    rw [hr]
    exact recipient_mem_ordered_roles pre cmd
  by_cases hf : p = pre.policy.feeOwner
  · apply hb p
    rw [hf]
    exact fee_owner_mem_ordered_roles pre cmd
  rw [postBalance, delta_untouched hs hr hf]
  simpa using hpre.balances p

/-! ## Enumerated conservation -/

def sumOver (f : Principal → Int) : List Principal → Int
  | [] => 0
  | p :: rest => f p + sumOver f rest

def occ (q : Principal) : List Principal → Int
  | [] => 0
  | p :: rest => (if p = q then 1 else 0) + occ q rest

theorem sumOver_add (f g : Principal → Int) :
    ∀ ps : List Principal,
      sumOver (fun p => f p + g p) ps = sumOver f ps + sumOver g ps
  | [] => rfl
  | p :: ps => by
      simp only [sumOver, sumOver_add f g ps]
      omega

theorem sumOver_indicator (q : Principal) (value : Int) :
    ∀ ps : List Principal,
      sumOver (fun p => indicator q value p) ps = value * occ q ps
  | [] => by simp [sumOver, occ]
  | p :: ps => by
      have ih := sumOver_indicator q value ps
      simp only [sumOver, occ]
      rw [ih, Int.mul_add]
      by_cases h : p = q
      · simp [indicator, h]
      · simp [indicator, h]

theorem sumOver_delta (pre : TransferState) (cmd : Command) (ps : List Principal) :
    sumOver (delta pre cmd) ps =
      -(cmd.amountAtoms + pre.policy.transferFeeAtoms) * occ cmd.sender ps
        + cmd.amountAtoms * occ cmd.recipient ps
        + pre.policy.transferFeeAtoms * occ pre.policy.feeOwner ps := by
  show sumOver (fun p =>
      (fun p => indicator cmd.sender (-(cmd.amountAtoms + pre.policy.transferFeeAtoms)) p
        + indicator cmd.recipient cmd.amountAtoms p) p
        + indicator pre.policy.feeOwner pre.policy.transferFeeAtoms p) ps = _
  rw [sumOver_add, sumOver_add, sumOver_indicator, sumOver_indicator, sumOver_indicator]

theorem accepted_conserves_enumerated_total {roots : RootModel} {ctx : Context}
    {pre : TransferState} {cmd : Command}
    (h : (transition roots ctx pre cmd).verdict = .accepted) (ps : List Principal)
    (hs : occ cmd.sender ps = 1) (hr : occ cmd.recipient ps = 1)
    (hf : occ pre.policy.feeOwner ps = 1) :
    sumOver (transition roots ctx pre cmd).post.balance ps = sumOver pre.balance ps := by
  rw [(accepted_post_and_effects h).1]
  have hsum : sumOver (acceptedState pre cmd).balance ps =
      sumOver pre.balance ps + sumOver (delta pre cmd) ps := by
    rw [← sumOver_add]
    rfl
  rw [hsum, sumOver_delta, hs, hr, hf]
  omega

/-! ## Coordinator projection and exact envelope rebind -/

structure AssetLaneAggregate (OtherProjection : Type) where
  transferProjection : TransferState
  otherProjection : OtherProjection
  aggregateRoot : Root

def replaceTransfer {OtherProjection : Type}
    (pre : AssetLaneAggregate OtherProjection) (post : TransferState)
    (postAggregateRoot : Root) : AssetLaneAggregate OtherProjection :=
  { transferProjection := post
    otherProjection := pre.otherProjection
    aggregateRoot := postAggregateRoot }

def rebindLane {Payload : Type} (preRoot postRoot : Root)
    (leaf : EffectEnvelope Payload) : EffectEnvelope Payload :=
  { leaf with
    laneWrites := [⟨preRoot, postRoot⟩]
    externalOutbox := [] }

theorem replace_transfer_projects_leaf {OtherProjection : Type}
    (pre : AssetLaneAggregate OtherProjection) (leafPost : TransferState)
    (postRoot : Root) :
    (replaceTransfer pre leafPost postRoot).transferProjection = leafPost ∧
    (replaceTransfer pre leafPost postRoot).otherProjection = pre.otherProjection := by
  exact ⟨rfl, rfl⟩

theorem coordinator_rebind_preserves_payload_and_occurrence {Payload : Type}
    (preRoot postRoot : Root) (leaf : EffectEnvelope Payload) :
    (rebindLane preRoot postRoot leaf).payload = leaf.payload ∧
    (rebindLane preRoot postRoot leaf).occurrenceConsumptions =
      leaf.occurrenceConsumptions ∧
    (rebindLane preRoot postRoot leaf).externalRoots = leaf.externalRoots := by
  exact ⟨rfl, rfl, rfl⟩

theorem coordinator_rebind_exact_lane_write {Payload : Type}
    (preRoot postRoot : Root) (leaf : EffectEnvelope Payload) :
    (rebindLane preRoot postRoot leaf).laneWrites = [⟨preRoot, postRoot⟩] ∧
    (rebindLane preRoot postRoot leaf).externalOutbox = [] := by
  exact ⟨rfl, rfl⟩

theorem coordinator_transfer_projection_and_rebind {OtherProjection : Type}
    (pre : AssetLaneAggregate OtherProjection) (leafPost : TransferState)
    (postRoot : Root) (leaf : EffectEnvelope TransferPayload) :
    (replaceTransfer pre leafPost postRoot).transferProjection = leafPost ∧
    (replaceTransfer pre leafPost postRoot).otherProjection = pre.otherProjection ∧
    (rebindLane pre.aggregateRoot postRoot leaf).laneWrites =
      [⟨pre.aggregateRoot, postRoot⟩] ∧
    (rebindLane pre.aggregateRoot postRoot leaf).occurrenceConsumptions =
      leaf.occurrenceConsumptions ∧
    (rebindLane pre.aggregateRoot postRoot leaf).externalOutbox = [] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Concrete negative and boundary witnesses -/

def ledger : List (Principal × Int) → Principal → Int
  | [], _ => 0
  | (owner, amount) :: rest, principal =>
      if principal = owner then amount else ledger rest principal

def ordinaryPolicy : Policy :=
  { asset := "USD"
    feeOwner := "m_treasury"
    transferFeeAtoms := 0
    enabled := true
    assetClass := .registeredOrdinaryToken
    assetOriginRoot := some "origin-usd"
    atomDecimals := 8 }

def validOccurrence (subject : Principal) : Occurrence :=
  { preStateRoot := "global-pre"
    consumedObjectIds := []
    commandKind := assetTransferCommandKind
    commandBodyHash := "body"
    subjectId := subject
    grantRoot := "unused-transfer-grant"
    occurrenceId := "occurrence-1" }

def baseContext (subject : Principal) : Context :=
  { moduleReleaseId := "release-v2"
    globalPreStateRoot := "global-pre"
    occurrence := some (validOccurrence subject) }

def baseCommand (sender recipient : Principal) (amount : Int) : Command :=
  { commandKind := assetTransferCommandKind
    commandBodyHash := "body"
    asset := "USD"
    sender := sender
    recipient := recipient
    amountAtoms := amount
    maxFeeAtoms := 0
    assetOriginRoot := some "origin-usd" }

def sortedFailureState : TransferState :=
  { moduleReleaseId := "release-v2"
    policy := ordinaryPolicy
    balance := ledger [("a_recipient", u128Max), ("z_sender", 0)]
    supplyAtoms := u128Max
    accountTotalAtoms := u128Max }

def sortedFailureCommand : Command := baseCommand "z_sender" "a_recipient" 1

theorem sorted_failure_role_order :
    orderedRoles sortedFailureState sortedFailureCommand =
      ["a_recipient", "m_treasury", "z_sender"] := by decide

/-- The sender is insufficient and the recipient overflows.  Canonical key
order visits `a_recipient` first, so the V2 Python-shaped scan reports overflow. -/
theorem sorted_balance_scan_can_report_overflow_before_sender_underflow :
    postBalance sortedFailureState sortedFailureCommand "z_sender" < 0 ∧
    u128Max < postBalance sortedFailureState sortedFailureCommand "a_recipient" ∧
    rejectCode (baseContext "z_sender") sortedFailureState sortedFailureCommand =
      some .balanceOverflow := by
  constructor
  · decide
  · constructor
    · decide
    · unfold rejectCode
      rw [sorted_failure_role_order]
      simp [preBalanceRejectCodes, allRejectCodes, firstFailing, guardPasses,
        occurrencePasses, originRegistered, widthAdmitted, IsI128,
        balanceCodeOn, postBalance,
        delta, indicator, baseContext, validOccurrence, sortedFailureState,
        sortedFailureCommand, baseCommand, ordinaryPolicy, ledger, u128Max,
        i128Min, i128Max]

def missingOccurrenceContext : Context :=
  { moduleReleaseId := "stale-release"
    globalPreStateRoot := "wrong-global-root"
    occurrence := none }

def malformedEarlyCommand : Command :=
  { commandKind := "unknown"
    commandBodyHash := "wrong-body"
    asset := "MISSING"
    sender := "same"
    recipient := "same"
    amountAtoms := 0
    maxFeeAtoms := 0
    assetOriginRoot := none }

theorem missing_occurrence_precedes_other_failures :
    rejectCode missingOccurrenceContext sortedFailureState malformedEarlyCommand =
      some .missingOccurrence := by decide

def unregisteredState : TransferState :=
  { sortedFailureState with
    policy := { ordinaryPolicy with assetOriginRoot := none }
    balance := ledger [("alice", 2)]
    supplyAtoms := 2
    accountTotalAtoms := 2 }

def unregisteredCommand : Command :=
  { baseCommand "alice" "bob" 1 with assetOriginRoot := none }

theorem omitted_origin_rejects_before_origin_equality_can_authorize :
    rejectCode (baseContext "alice") unregisteredState unregisteredCommand =
      some .unregisteredAsset := by rfl

def nativeState : TransferState :=
  { unregisteredState with
    policy := { ordinaryPolicy with
      assetClass := .tauNativeCoin
      assetOriginRoot := some "origin-tau" }
    balance := ledger [("alice", 2)] }

def nativeCommand : Command :=
  { baseCommand "alice" "bob" 1 with assetOriginRoot := some "origin-tau" }

theorem native_asset_accounting_is_explicitly_unimplemented :
    rejectCode (baseContext "alice") nativeState nativeCommand =
      some .nativeAssetAccountingUnimplemented := by rfl

def feePolicy : Policy := { ordinaryPolicy with transferFeeAtoms := 2 }
def feeState : TransferState :=
  { sortedFailureState with
    policy := feePolicy
    balance := ledger [("alice", 32), ("bob", 0), ("m_treasury", 0)]
    supplyAtoms := 32
    accountTotalAtoms := 32 }
def feeCommand : Command := { baseCommand "alice" "bob" 30 with maxFeeAtoms := 2 }

def leakyDelta (pre : TransferState) (cmd : Command) (p : Principal) : Int :=
  indicator cmd.sender (-(cmd.amountAtoms + pre.policy.transferFeeAtoms)) p
    + indicator cmd.recipient cmd.amountAtoms p

theorem omitted_fee_credit_breaks_conservation_counterexample :
    leakyDelta feeState feeCommand "alice" +
      leakyDelta feeState feeCommand "bob" +
      leakyDelta feeState feeCommand "m_treasury" = -2 ∧
    leakyDelta feeState feeCommand "alice" +
      leakyDelta feeState feeCommand "bob" +
      leakyDelta feeState feeCommand "m_treasury" ≠ 0 := by decide

end AssetTransferRefinementV2
end Proofs
