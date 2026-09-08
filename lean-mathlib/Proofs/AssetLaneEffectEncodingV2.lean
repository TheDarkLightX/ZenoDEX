import Proofs.AssetTransferFiniteEffectPlanV2
import Init.Data.String.Basic

/-!
Explicit canonical effect-plan bytes on the existing finite six-field carrier,
including the fixed ABI schema. String correspondence is restricted to admitted
printable ASCII tokens and canonical roots. Signed decimal output is explicit;
no universal equality to Lean's opaque negative Int printer is assumed.
Byte bounds confer no root, occurrence, receipt, journal or runtime authority.
-/
set_option warningAsError true

namespace Proofs.AssetLaneEffectEncodingV2

open GlobalSettlementCoreV2
namespace B
export AssetLaneFiniteByteAccountingV2 (Bytes raw quoted number tokenCost numberCost array weight emptyBit
  ValidToken quoted_length array_length)
end B

namespace Numeric
-- Parent-supplied decimal-width proof, recompiled here; see retained provenance.
private theorem digitChar_utf8Size (n : Nat) : (Nat.digitChar n).utf8Size = 1 := by
  unfold Nat.digitChar
  simp only [apply_ite Char.utf8Size]
  simp +decide only [Char.utf8Size, if_true, ite_self]

private theorem ofList_cons_byteSize (c : Char) (cs : List Char) :
    (String.ofList (c :: cs)).utf8ByteSize = c.utf8Size + (String.ofList cs).utf8ByteSize := by
  rw [show c :: cs = [c] ++ cs from rfl, String.ofList_append, String.utf8ByteSize_append]
  rw [← String.singleton_eq_ofList, String.utf8ByteSize_singleton]

private theorem digitsCore_byteSize (digits fuel n : Nat) (cs : List Char)
    (bound : n < 10 ^ (digits + 1)) :
    (String.ofList (Nat.toDigitsCore 10 fuel n cs)).utf8ByteSize ≤
      digits + 1 + (String.ofList cs).utf8ByteSize := by
  induction digits generalizing fuel n cs with
  | zero =>
    have small : n < 10 := by simpa using bound
    have quotient : n / 10 = 0 := Nat.div_eq_of_lt small
    cases fuel with
    | zero => simp [Nat.toDigitsCore]
    | succ fuel =>
      simp only [Nat.toDigitsCore, quotient, if_true, ofList_cons_byteSize, digitChar_utf8Size]
      omega
  | succ digits ih =>
    cases fuel with
    | zero => simp [Nat.toDigitsCore]
    | succ fuel =>
      simp only [Nat.toDigitsCore]
      by_cases quotient : n / 10 = 0
      · simp only [quotient, if_true, ofList_cons_byteSize, digitChar_utf8Size]
        omega
      · rw [if_neg quotient]
        have smaller : n / 10 < 10 ^ (digits + 1) := by
          apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).mpr
          simpa [Nat.pow_succ] using bound
        have step := ih fuel (n / 10) (Nat.digitChar (n % 10) :: cs) smaller
        rw [ofList_cons_byteSize, digitChar_utf8Size] at step
        omega

theorem nat_decimal_bytes_le (n digits : Nat) (bound : n < 10 ^ (digits + 1)) :
    (B.raw (toString n)).length ≤ digits + 1 := by
  have size := digitsCore_byteSize digits (n + 1) n [] bound
  change (B.raw (Nat.repr n)).length ≤ digits + 1
  simp only [B.raw, String.toUTF8_eq_toByteArray, Array.length_toList]
  change (Nat.repr n).utf8ByteSize ≤ digits + 1
  simpa [Nat.repr, Nat.toDigits, String.ofList_nil, String.utf8ByteSize_empty] using size

def decimalBytes : Int → B.Bytes
  | .ofNat n => B.raw (toString n)
  | .negSucc n => [45] ++ B.raw (toString (n + 1))

theorem decimalBytes_nonnegative (n : Int) (nonnegative : 0 ≤ n) :
    decimalBytes n = B.number n := by
  cases n with
  | ofNat n => rfl
  | negSucc n => omega

theorem decimalBytes_u128 (n : Int) (width : FitsU128 n) : (decimalBytes n).length ≤ 39 := by
  cases n with
  | ofNat n =>
    have bounded : n < 10 ^ (38 + 1) := by
      simp only [FitsU128, maxU128, Int.ofNat_eq_natCast] at width
      omega
    exact nat_decimal_bytes_le n 38 bounded
  | negSucc n =>
    unfold FitsU128 at width
    omega

theorem decimalBytes_i128 (n : Int) (width : FitsI128 n) : (decimalBytes n).length ≤ 40 := by
  cases n with
  | ofNat n =>
    have bounded : n < 10 ^ (38 + 1) := by
      simp only [FitsI128, minI128, maxI128, Int.ofNat_eq_natCast] at width
      omega
    have size := nat_decimal_bytes_le n 38 bounded
    change (B.raw (toString n)).length ≤ 40
    omega
  | negSucc n =>
    have bounded : n + 1 < 10 ^ (38 + 1) := by
      unfold FitsI128 minI128 maxI128 at width
      omega
    have size := nat_decimal_bytes_le (n + 1) 38 bounded
    simp only [decimalBytes, List.length_append, List.length_cons, List.length_nil]
    omega
end Numeric

def effectRowBytes (row : EconomicEffectRow) : B.Bytes :=
  B.raw "{\"asset\":" ++ B.quoted row.asset ++ B.raw ",\"custody_domain\":" ++ B.quoted row.custodyDomain ++
    B.raw ",\"delta_atoms\":" ++ Numeric.decimalBytes row.deltaAtoms ++ B.raw ",\"kind\":" ++ B.quoted row.kind.code ++
    B.raw ",\"principal\":" ++ B.quoted row.principal ++ B.raw "}"

def assetConservationBytes (row : AssetConservationRow) : B.Bytes :=
  B.raw "{\"asset\":" ++ B.quoted row.asset ++
    B.raw ",\"authorized_burn_atoms\":" ++ Numeric.decimalBytes row.authorizedBurnAtoms ++
    B.raw ",\"authorized_issue_atoms\":" ++ Numeric.decimalBytes row.authorizedIssueAtoms ++
    B.raw ",\"owned_and_custodied_post_atoms\":" ++ Numeric.decimalBytes row.ownedAndCustodiedPostAtoms ++
    B.raw ",\"owned_and_custodied_pre_atoms\":" ++ Numeric.decimalBytes row.ownedAndCustodiedPreAtoms ++
    B.raw ",\"supply_post_atoms\":" ++ Numeric.decimalBytes row.supplyPostAtoms ++
    B.raw ",\"supply_pre_atoms\":" ++ Numeric.decimalBytes row.supplyPreAtoms ++ B.raw "}"

def feeConservationBytes (row : FeeConservationRow) : B.Bytes :=
  B.raw "{\"asset\":" ++ B.quoted row.asset ++
    B.raw ",\"carried_residue_atoms\":" ++ Numeric.decimalBytes row.carriedResidueAtoms ++
    B.raw ",\"current_allocations_atoms\":" ++ Numeric.decimalBytes row.currentAllocationsAtoms ++
    B.raw ",\"fee_charged_atoms\":" ++ Numeric.decimalBytes row.feeChargedAtoms ++ B.raw "}"

def laneWriteBytes (row : LaneWrite) : B.Bytes :=
  B.raw "{\"lane_id\":" ++ B.quoted row.laneId.code ++
    B.raw ",\"post_root\":" ++ B.quoted row.postRoot ++ B.raw ",\"pre_root\":" ++ B.quoted row.preRoot ++ B.raw "}"

def outboxBytes (row : ExternalOutboxEnqueue) : B.Bytes :=
  B.raw "{\"adapter_profile_root\":" ++ B.quoted row.adapterProfileRoot ++
    B.raw ",\"destination_id\":" ++ B.quoted row.destinationId ++
    B.raw ",\"effect_id\":" ++ B.quoted row.effectId ++ B.raw ",\"payload_hash\":" ++ B.quoted row.payloadHash ++ B.raw "}"

/-- Seven serialized keys: the six existing plan fields plus the fixed ABI schema. -/
def planBytes (plan : EffectPlan) : B.Bytes :=
  B.raw "{\"asset_conservation\":" ++ B.array assetConservationBytes plan.assetConservation ++
    B.raw ",\"external_outbox_enqueue\":" ++ B.array outboxBytes plan.externalOutboxEnqueue ++
    B.raw ",\"fee_conservation\":" ++ B.array feeConservationBytes plan.feeConservation ++
    B.raw ",\"lane_writes\":" ++ B.array laneWriteBytes plan.laneWrites ++
    B.raw ",\"occurrence_consumptions\":" ++ B.array B.quoted plan.occurrenceConsumptions ++
    B.raw ",\"rows\":" ++ B.array effectRowBytes plan.rows ++
    B.raw ",\"schema\":\"zenodex/global-settlement-abi/v2\"}"

def effectRowCost (row : EconomicEffectRow) : Nat :=
  64 + B.tokenCost row.asset + B.tokenCost row.custodyDomain + (Numeric.decimalBytes row.deltaAtoms).length +
    B.tokenCost row.kind.code + B.tokenCost row.principal

def assetConservationCost (row : AssetConservationRow) : Nat :=
  169 + B.tokenCost row.asset + (Numeric.decimalBytes row.authorizedBurnAtoms).length +
    (Numeric.decimalBytes row.authorizedIssueAtoms).length + (Numeric.decimalBytes row.ownedAndCustodiedPostAtoms).length +
    (Numeric.decimalBytes row.ownedAndCustodiedPreAtoms).length + (Numeric.decimalBytes row.supplyPostAtoms).length +
    (Numeric.decimalBytes row.supplyPreAtoms).length

def feeConservationCost (row : FeeConservationRow) : Nat :=
  85 + B.tokenCost row.asset + (Numeric.decimalBytes row.carriedResidueAtoms).length +
    (Numeric.decimalBytes row.currentAllocationsAtoms).length + (Numeric.decimalBytes row.feeChargedAtoms).length

def laneWriteCost (row : LaneWrite) : Nat :=
  37 + B.tokenCost row.laneId.code + B.tokenCost row.postRoot + B.tokenCost row.preRoot

def outboxCost (row : ExternalOutboxEnqueue) : Nat :=
  72 + B.tokenCost row.adapterProfileRoot + B.tokenCost row.destinationId + B.tokenCost row.effectId + B.tokenCost row.payloadHash

def arrayCost {α : Type} (cost : α → Nat) (rows : List α) : Nat :=
  B.weight (fun row => cost row + 1) rows + 1 + B.emptyBit rows

def planCost (plan : EffectPlan) : Nat :=
  164 + arrayCost assetConservationCost plan.assetConservation + arrayCost outboxCost plan.externalOutboxEnqueue +
    arrayCost feeConservationCost plan.feeConservation + arrayCost laneWriteCost plan.laneWrites +
    arrayCost B.tokenCost plan.occurrenceConsumptions + arrayCost effectRowCost plan.rows

theorem effectRowBytes_length (row : EconomicEffectRow) : (effectRowBytes row).length = effectRowCost row := by
  simp only [effectRowBytes, List.length_append, B.quoted_length]
  change 9 + B.tokenCost row.asset + 18 + B.tokenCost row.custodyDomain + 15 +
    (Numeric.decimalBytes row.deltaAtoms).length + 8 + B.tokenCost row.kind.code + 13 + B.tokenCost row.principal + 1 = _
  unfold effectRowCost
  omega

theorem assetConservationBytes_length (row : AssetConservationRow) :
    (assetConservationBytes row).length = assetConservationCost row := by
  simp only [assetConservationBytes, List.length_append, B.quoted_length]
  change 9 + B.tokenCost row.asset + 25 + (Numeric.decimalBytes row.authorizedBurnAtoms).length +
    26 + (Numeric.decimalBytes row.authorizedIssueAtoms).length + 34 + (Numeric.decimalBytes row.ownedAndCustodiedPostAtoms).length +
    33 + (Numeric.decimalBytes row.ownedAndCustodiedPreAtoms).length + 21 + (Numeric.decimalBytes row.supplyPostAtoms).length +
    20 + (Numeric.decimalBytes row.supplyPreAtoms).length + 1 = _
  unfold assetConservationCost
  omega

theorem feeConservationBytes_length (row : FeeConservationRow) :
    (feeConservationBytes row).length = feeConservationCost row := by
  simp only [feeConservationBytes, List.length_append, B.quoted_length]
  change 9 + B.tokenCost row.asset + 25 + (Numeric.decimalBytes row.carriedResidueAtoms).length +
    29 + (Numeric.decimalBytes row.currentAllocationsAtoms).length + 21 + (Numeric.decimalBytes row.feeChargedAtoms).length + 1 = _
  unfold feeConservationCost
  omega

theorem laneWriteBytes_length (row : LaneWrite) : (laneWriteBytes row).length = laneWriteCost row := by
  simp only [laneWriteBytes, List.length_append, B.quoted_length]
  change 11 + B.tokenCost row.laneId.code + 13 + B.tokenCost row.postRoot + 12 + B.tokenCost row.preRoot + 1 = _
  unfold laneWriteCost
  omega

theorem outboxBytes_length (row : ExternalOutboxEnqueue) : (outboxBytes row).length = outboxCost row := by
  simp only [outboxBytes, List.length_append, B.quoted_length]
  change 24 + B.tokenCost row.adapterProfileRoot + 18 + B.tokenCost row.destinationId +
    13 + B.tokenCost row.effectId + 16 + B.tokenCost row.payloadHash + 1 = _
  unfold outboxCost
  omega

theorem planBytes_length (plan : EffectPlan) : (planBytes plan).length = planCost plan := by
  simp only [planBytes, List.length_append, B.array_length, effectRowBytes_length, assetConservationBytes_length,
    feeConservationBytes_length, laneWriteBytes_length, outboxBytes_length, B.quoted_length]
  change 22 + arrayCost assetConservationCost plan.assetConservation +
    27 + arrayCost outboxCost plan.externalOutboxEnqueue + 20 + arrayCost feeConservationCost plan.feeConservation +
    15 + arrayCost laneWriteCost plan.laneWrites + 27 + arrayCost B.tokenCost plan.occurrenceConsumptions +
    8 + arrayCost effectRowCost plan.rows + 45 = _
  unfold planCost
  omega

def LowerHexByte (byte : UInt8) : Prop :=
  (48 ≤ byte.toNat ∧ byte.toNat ≤ 57) ∨ (97 ≤ byte.toNat ∧ byte.toNat ≤ 102)

/-- Exact lowercase 0x-prefixed 32-byte hex syntax; zero is permitted for lane roots. -/
def CanonicalRoot (value : String) : Prop :=
  (B.raw value).length = 66 ∧ (B.raw value).take 2 = [48, 120] ∧
    ∀ byte ∈ (B.raw value).drop 2, LowerHexByte byte

def NonzeroCanonicalRoot (value : String) : Prop :=
  CanonicalRoot value ∧ value ≠ "0x0000000000000000000000000000000000000000000000000000000000000000"

def RootObserverSyntax (digest : B.Bytes → String) : Prop := ∀ bytes, CanonicalRoot (digest bytes)

/-- Syntax of serialized commitments only; this predicate authenticates nothing. -/
def PlanRootSyntax (plan : EffectPlan) : Prop :=
  (∀ row ∈ plan.laneWrites, CanonicalRoot row.preRoot ∧ CanonicalRoot row.postRoot) ∧
    ∀ root ∈ plan.occurrenceConsumptions, NonzeroCanonicalRoot root

theorem tokenCost_raw_bound (value : String) : B.tokenCost value ≤ 2 + 2 * (B.raw value).length := by
  have filtered := List.length_filter_le (fun byte : UInt8 => byte == 34 || byte == 92) (B.raw value)
  unfold B.tokenCost
  omega

theorem tokenCost_token_bound (value : String) (token : B.ValidToken value) : B.tokenCost value ≤ 322 := by
  have size := tokenCost_raw_bound value
  have bound := token.2.1
  omega

/-- Conservative escape bound; exact root syntax is retained even though this
size estimate needs only its 66-byte length. -/
theorem tokenCost_root_bound (value : String) (root : CanonicalRoot value) : B.tokenCost value ≤ 134 := by
  have size := tokenCost_raw_bound value
  have count := root.1
  omega

theorem effect_kind_cost_bound (kind : EffectKind) : B.tokenCost kind.code ≤ 18 := by
  cases kind <;> decide

theorem lane_id_cost_bound (lane : LaneId) : B.tokenCost lane.code ≤ 22 := by
  cases lane <;> decide

theorem effectRowBytes_bound (row : EconomicEffectRow) (admitted : EffectRowAdmitted row)
    (tokens : B.ValidToken row.principal ∧ B.ValidToken row.asset ∧ B.ValidToken row.custodyDomain) :
    (effectRowBytes row).length ≤ 1088 := by
  have principal := tokenCost_token_bound row.principal tokens.1
  have asset := tokenCost_token_bound row.asset tokens.2.1
  have domain := tokenCost_token_bound row.custodyDomain tokens.2.2
  have number := Numeric.decimalBytes_i128 row.deltaAtoms admitted.1
  have kind := effect_kind_cost_bound row.kind
  rw [effectRowBytes_length]
  unfold effectRowCost
  omega

theorem assetConservationBytes_bound (row : AssetConservationRow) (admitted : AssetConservationAdmitted row)
    (token : B.ValidToken row.asset) : (assetConservationBytes row).length ≤ 725 := by
  have asset := tokenCost_token_bound row.asset token
  have pre := Numeric.decimalBytes_u128 _ admitted.1
  have post := Numeric.decimalBytes_u128 _ admitted.2.1
  have supplyPre := Numeric.decimalBytes_u128 _ admitted.2.2.1
  have supplyPost := Numeric.decimalBytes_u128 _ admitted.2.2.2.1
  have issue := Numeric.decimalBytes_u128 _ admitted.2.2.2.2.1
  have burn := Numeric.decimalBytes_u128 _ admitted.2.2.2.2.2.1
  rw [assetConservationBytes_length]
  unfold assetConservationCost
  omega

theorem feeConservationBytes_bound (row : FeeConservationRow) (admitted : FeeConservationAdmitted row)
    (token : B.ValidToken row.asset) : (feeConservationBytes row).length ≤ 524 := by
  have asset := tokenCost_token_bound row.asset token
  have charged := Numeric.decimalBytes_u128 _ admitted.1
  have allocated := Numeric.decimalBytes_u128 _ admitted.2.1
  have residue := Numeric.decimalBytes_u128 _ admitted.2.2.1
  rw [feeConservationBytes_length]
  unfold feeConservationCost
  omega

theorem laneWriteBytes_bound (row : LaneWrite) (roots : CanonicalRoot row.preRoot ∧ CanonicalRoot row.postRoot) :
    (laneWriteBytes row).length ≤ 327 := by
  have pre := tokenCost_root_bound row.preRoot roots.1
  have post := tokenCost_root_bound row.postRoot roots.2
  have lane := lane_id_cost_bound row.laneId
  rw [laneWriteBytes_length]
  unfold laneWriteCost
  omega

theorem weight_bound {α : Type} (cost : α → Nat) (rows : List α) (limit : Nat)
    (bounded : ∀ row ∈ rows, cost row ≤ limit) : B.weight cost rows ≤ rows.length * limit := by
  induction rows with
  | nil => simp [B.weight]
  | cons head tail ih =>
    have first := bounded head List.mem_cons_self
    have rest := ih (fun row member => bounded row (List.mem_cons_of_mem head member))
    simp only [B.weight, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul] at rest ⊢
    omega

theorem arrayBytes_bound {α : Type} (encode : α → B.Bytes) (rows : List α) (limit : Nat)
    (bounded : ∀ row ∈ rows, (encode row).length ≤ limit) :
    (B.array encode rows).length ≤ rows.length * (limit + 1) + 2 := by
  have weight := weight_bound (fun row => (encode row).length + 1) rows (limit + 1)
    (fun row member => Nat.add_le_add_right (bounded row member) 1)
  have empty : B.emptyBit rows ≤ 1 := by unfold B.emptyBit; split <;> decide
  rw [B.array_length]
  omega

theorem small_plan_bytes_bounded (plan : EffectPlan) (admitted : EffectPlanAdmitted plan)
    (tokens : AssetLaneFiniteEffectPlanV2.PlanTokens plan) (roots : PlanRootSyntax plan)
    (counts : plan.rows.length ≤ 4 ∧ plan.assetConservation.length ≤ 1 ∧ plan.feeConservation.length ≤ 1 ∧
      plan.laneWrites.length ≤ 1 ∧ plan.occurrenceConsumptions.length ≤ 1)
    (outbox : plan.externalOutboxEnqueue = []) : (planBytes plan).length ≤ 8192 := by
  have rows := arrayBytes_bound effectRowBytes plan.rows 1088
    (fun row member => effectRowBytes_bound row (admitted.1 row member) (tokens.1 row member))
  have assets := arrayBytes_bound assetConservationBytes plan.assetConservation 725
    (fun row member => assetConservationBytes_bound row (admitted.2.1 row member) (tokens.2.1 row member))
  have fees := arrayBytes_bound feeConservationBytes plan.feeConservation 524
    (fun row member => feeConservationBytes_bound row (admitted.2.2.1 row member) (tokens.2.2 row member))
  have writes := arrayBytes_bound laneWriteBytes plan.laneWrites 327
    (fun row member => laneWriteBytes_bound row (roots.1 row member))
  have occurrences := arrayBytes_bound B.quoted plan.occurrenceConsumptions 134 (fun root member => by
    rw [B.quoted_length]
    exact tokenCost_root_bound root (roots.2 root member).1)
  have empty : (B.array outboxBytes plan.externalOutboxEnqueue).length = 2 := by rw [outbox]; rfl
  simp only [planBytes, List.length_append]
  change 22 + (B.array assetConservationBytes plan.assetConservation).length +
    27 + (B.array outboxBytes plan.externalOutboxEnqueue).length + 20 + (B.array feeConservationBytes plan.feeConservation).length +
    15 + (B.array laneWriteBytes plan.laneWrites).length + 27 + (B.array B.quoted plan.occurrenceConsumptions).length +
    8 + (B.array effectRowBytes plan.rows).length + 45 ≤ 8192
  omega

namespace FM
export ManagedAssetFiniteOutcomeV2 (State Structural transition)
end FM
namespace M
export ManagedAssetLifecycleRefinementV2 (Context Command CommandWellFormed)
end M
namespace FT
export AssetTransferFiniteOutcomeV2 (State Structural CommandAdmission transition)
end FT
namespace T
export AssetTransferRefinementV2 (Context Command)
end T

open AssetLaneFiniteEffectPlanV2 (managedPlan managed_plan_admitted managed_plan_tokens
  managed_accepted_fields managed_items managed_rejected_empty)
open AssetTransferFiniteEffectPlanV2 (transferPlan transfer_plan_admitted transfer_plan_tokens
  transfer_accepted_fields transfer_items transfer_rejected_empty)

theorem managed_plan_bytes_bounded {digest : B.Bytes → String} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} (structural : FM.Structural pre) (commandAdmitted : M.CommandWellFormed command)
    (ownerToken : B.ValidToken command.accountOwner) (roots : RootObserverSyntax digest)
    (occurrenceSyntax : ∀ occurrence, ctx.occurrence = some occurrence → NonzeroCanonicalRoot occurrence.occurrenceId)
    (accepted : (FM.transition digest ctx pre command).verdict = .accepted) :
    (planBytes (managedPlan digest ctx pre command)).length ≤ 8192 := by
  obtain ⟨occurrence, present, fields⟩ := managed_accepted_fields structural accepted
  apply small_plan_bytes_bounded _ (managed_plan_admitted structural commandAdmitted ownerToken accepted)
    (managed_plan_tokens structural ownerToken accepted)
  · rw [fields]
    constructor
    · intro row member
      simp only [List.mem_singleton] at member
      subst row
      exact ⟨roots _, roots _⟩
    · intro root member
      simp only [List.mem_singleton] at member
      subst root
      exact occurrenceSyntax occurrence present
  · have count := (managed_items accepted).1
    refine ⟨by omega, ?_⟩
    rw [fields]
    simp
  · rw [fields]

theorem transfer_plan_bytes_bounded {digest : B.Bytes → String} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} (structural : FT.Structural pre) (commandAdmitted : FT.CommandAdmission command)
    (roots : RootObserverSyntax digest)
    (occurrenceSyntax : ∀ occurrence, ctx.occurrence = some occurrence → NonzeroCanonicalRoot occurrence.occurrenceId)
    (accepted : (FT.transition digest ctx pre command).verdict = .accepted) :
    (planBytes (transferPlan digest ctx pre command)).length ≤ 8192 := by
  obtain ⟨policy, occurrence, _, present, fields⟩ := transfer_accepted_fields accepted
  apply small_plan_bytes_bounded _ (transfer_plan_admitted structural accepted)
    (transfer_plan_tokens structural commandAdmitted accepted)
  · rw [fields]
    constructor
    · intro row member
      simp only [List.mem_singleton] at member
      subst row
      exact ⟨roots _, roots _⟩
    · intro root member
      simp only [List.mem_singleton] at member
      subst root
      exact occurrenceSyntax occurrence present
  · have count := (transfer_items accepted).1
    refine ⟨count, ?_⟩
    rw [fields]
    by_cases zero : policy.transferFeeAtoms = 0 <;> simp [AssetTransferFiniteEffectPlanV2.transferFees, zero]
  · rw [fields]

set_option maxRecDepth 4096 in
theorem planBytes_empty : planBytes EffectPlan.empty =
    B.raw "{\"asset_conservation\":[],\"external_outbox_enqueue\":[],\"fee_conservation\":[],\"lane_writes\":[],\"occurrence_consumptions\":[],\"rows\":[],\"schema\":\"zenodex/global-settlement-abi/v2\"}" := by
  decide

theorem planBytes_empty_length : (planBytes EffectPlan.empty).length = 176 := by
  rw [planBytes_length]
  rfl

theorem managed_rejected_bytes {digest : B.Bytes → String} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} {code : ManagedAssetFiniteOutcomeV2.RejectCode}
    (rejected : (FM.transition digest ctx pre command).verdict = .rejected code) :
    planBytes (managedPlan digest ctx pre command) = planBytes EffectPlan.empty := by
  rw [managed_rejected_empty rejected]

theorem transfer_rejected_bytes {digest : B.Bytes → String} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} {code : AssetTransferFiniteOutcomeV2.RejectCode}
    (rejected : (FT.transition digest ctx pre command).verdict = .rejected code) :
    planBytes (transferPlan digest ctx pre command) = planBytes EffectPlan.empty := by
  rw [transfer_rejected_empty rejected]

end Proofs.AssetLaneEffectEncodingV2
