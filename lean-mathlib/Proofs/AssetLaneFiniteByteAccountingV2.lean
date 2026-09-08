import Proofs.AssetLaneFiniteRowGrowthV2

/-!
Exact byte accounting for finite managed balance and complete supply rows.
Token correspondence is restricted to printable ASCII, including escaped quote
and backslash. Fixed serialized metadata parameters frame the row update; their
correspondence to external metadata serializers is a separate obligation.
-/
set_option warningAsError true

namespace Proofs.AssetLaneFiniteByteAccountingV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open RegisteredSupplySupportV1 RegisteredSupplyUpdateV1

namespace S
export AssetTransferSparseTablesV1 (Unique accounts accountKey balanceWire makeAmount
  makeAmount_key eraseKey mem_eraseKey putAmount)
end S
namespace C
export CanonicalEpochEconomicRowsV1 (AmountKey amountKey lookupLast sortOn sortOn_perm)
end C
namespace A
export ManagedAssetFiniteAccountingV2 (updateRows)
end A
namespace R
export AssetLaneFiniteRecompositionV2 (AccountsDomain recomposeBalances recomposeSupplies
  managed_balance_recompose managed_complete_supply_recompose)
end R
namespace G
export AssetLaneFiniteRowGrowthV2 (lookupLast_member updateRows_length recomposeBalances_length)
end G

attribute [local instance] lexOrd

abbrev Bytes := List UInt8

def raw (value : String) : Bytes := value.toUTF8.data.toList

def ValidToken (value : String) : Prop :=
  (raw value).length > 0 ∧ (raw value).length ≤ 160 ∧
    ∀ byte ∈ raw value, 0x21 ≤ byte.toNat ∧ byte.toNat ≤ 0x7e

def BalanceTokens (rows : List AmountRow) : Prop :=
  ∀ row ∈ rows, ValidToken row.owner ∧ ValidToken row.asset ∧ ValidToken row.custodyDomain

def SupplyTokens (rows : List V1SupplyRow) : Prop :=
  ∀ row ∈ rows, ValidToken row.asset

def escapeByte (byte : UInt8) : Bytes :=
  if byte = 34 ∨ byte = 92 then [92, byte] else [byte]

def quoted (value : String) : Bytes := [34] ++ (raw value).flatMap escapeByte ++ [34]

def tokenCost (value : String) : Nat :=
  2 + (raw value).length + ((raw value).filter (fun byte => byte == 34 || byte == 92)).length

def number (atoms : Int) : Bytes := raw (toString atoms)
def numberCost (atoms : Int) : Nat := (number atoms).length

def amountRow (row : AmountRow) : Bytes :=
  raw "{\"amount_atoms\":" ++ number row.amountAtoms ++ raw ",\"asset\":" ++ quoted row.asset ++
    raw ",\"custody_domain\":" ++ quoted row.custodyDomain ++ raw ",\"owner\":" ++ quoted row.owner ++ raw "}"

def supplyRow (row : V1SupplyRow) : Bytes :=
  raw "{\"amount_atoms\":" ++ number row.amountAtoms ++ raw ",\"asset\":" ++ quoted row.asset ++ raw "}"

def amountCost (row : AmountRow) : Nat :=
  53 + numberCost row.amountAtoms + tokenCost row.asset + tokenCost row.custodyDomain + tokenCost row.owner

def supplyCost (row : V1SupplyRow) : Nat := 26 + numberCost row.amountAtoms + tokenCost row.asset

def weight {α : Type} (cost : α → Nat) (rows : List α) : Nat := (rows.map cost).sum

def array {α : Type} (encodeRow : α → Bytes) : List α → Bytes
  | [] => [91, 93]
  | row :: rows => [91] ++ encodeRow row ++ rows.flatMap (fun next => [44] ++ encodeRow next) ++ [93]

def emptyBit {α : Type} (rows : List α) : Nat := if rows.isEmpty then 1 else 0

theorem escaped_length (bytes : Bytes) :
    (bytes.flatMap escapeByte).length =
      bytes.length + (bytes.filter (fun byte => byte == 34 || byte == 92)).length := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      by_cases escaped : byte = 34 ∨ byte = 92
      · simp [escapeByte, escaped, ih]
        omega
      · simp [escapeByte, escaped, ih]
        omega

theorem quoted_length (value : String) : (quoted value).length = tokenCost value := by
  simp only [quoted, List.length_append, List.length_cons, List.length_nil, escaped_length, tokenCost]
  omega

theorem amountRow_length (row : AmountRow) : (amountRow row).length = amountCost row := by
  simp only [amountRow, List.length_append, quoted_length]
  change 16 + numberCost row.amountAtoms + 9 + tokenCost row.asset + 18 + tokenCost row.custodyDomain +
    9 + tokenCost row.owner + 1 = amountCost row
  unfold amountCost
  omega

theorem supplyRow_length (row : V1SupplyRow) : (supplyRow row).length = supplyCost row := by
  simp only [supplyRow, List.length_append, quoted_length]
  change 16 + numberCost row.amountAtoms + 9 + tokenCost row.asset + 1 = supplyCost row
  unfold supplyCost
  omega

theorem array_length {α : Type} (encodeRow : α → Bytes) (rows : List α) :
    (array encodeRow rows).length = weight (fun row => (encodeRow row).length + 1) rows +
      1 + emptyBit rows := by
  cases rows with
  | nil => rfl
  | cons row rows =>
      simp only [array, List.length_append, List.length_cons, List.length_nil,
        List.length_flatMap, weight, List.map_cons, List.sum_cons, emptyBit, List.isEmpty_cons,
        Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      have same : (rows.map (fun a => 1 + (encodeRow a).length)).sum =
          (rows.map (fun a => (encodeRow a).length + 1)).sum := by
        simp only [Nat.add_comm]
      omega

theorem array_length_perm {α : Type} (encodeRow : α → Bytes) {left right : List α}
    (perm : left.Perm right) : (array encodeRow left).length = (array encodeRow right).length := by
  rw [array_length, array_length]
  have weights := (perm.map (fun row => (encodeRow row).length + 1)).sum_nat
  have counts := perm.length_eq
  have empties : emptyBit left = emptyBit right := by
    simp only [emptyBit, List.isEmpty_iff_length_eq_zero, counts]
  unfold weight
  rw [weights, empties]

def balanceBytes (rows : List AmountRow) : Bytes := array amountRow rows
def supplyBytes (rows : List V1SupplyRow) : Bytes := array supplyRow rows

theorem balanceBytes_length (rows : List AmountRow) :
    (balanceBytes rows).length = weight (fun row => amountCost row + 1) rows + 1 + emptyBit rows := by
  simp only [balanceBytes, array_length, amountRow_length]

theorem supplyBytes_length (rows : List V1SupplyRow) :
    (supplyBytes rows).length = weight (fun row => supplyCost row + 1) rows + 1 + emptyBit rows := by
  simp only [supplyBytes, array_length, supplyRow_length]

theorem eraseKey_of_absent (key : C.AmountKey) (rows : List AmountRow)
    (absent : key ∉ rows.map C.amountKey) : S.eraseKey key rows = rows := by
  unfold S.eraseKey
  apply List.filter_eq_self.mpr
  intro row member
  simp only [bne_iff_ne]
  intro same
  exact absent (List.mem_map.mpr ⟨row, member, same⟩)

theorem eraseKey_weight_member (cost : AmountRow → Nat) (rows : List AmountRow)
    (row : AmountRow) (unique : S.Unique rows) (member : row ∈ rows) :
    weight cost (S.eraseKey (C.amountKey row) rows) + cost row = weight cost rows := by
  induction rows with
  | nil => contradiction
  | cons head tail ih =>
      have keys := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | member
      · have unchanged := eraseKey_of_absent (C.amountKey row) tail keys.1
        simp only [S.eraseKey, List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        change weight cost (S.eraseKey (C.amountKey row) tail) + cost row = weight cost (row :: tail)
        rw [unchanged]
        simp [weight, Nat.add_comm]
      · have different : C.amountKey head ≠ C.amountKey row := by
          intro same
          exact keys.1 (same ▸ List.mem_map.mpr ⟨row, member, rfl⟩)
        have step := ih keys.2 member
        simp only [S.eraseKey, List.filter_cons, bne_iff_ne, if_pos different]
        change weight cost (head :: S.eraseKey (C.amountKey row) tail) + cost row = weight cost (head :: tail)
        simp only [weight, List.map_cons, List.sum_cons] at step ⊢
        omega

theorem eraseKey_weight (cost : AmountRow → Nat) (key : C.AmountKey) (rows : List AmountRow)
    (unique : S.Unique rows) :
    weight cost (S.eraseKey key rows) +
        (if key ∈ rows.map C.amountKey then cost (S.makeAmount key (C.lookupLast key rows)) else 0) =
      weight cost rows := by
  by_cases present : key ∈ rows.map C.amountKey
  · obtain ⟨row, member, same⟩ := List.mem_map.mp present
    have amount := G.lookupLast_member rows row unique member
    have exactRow : S.makeAmount key (C.lookupLast key rows) = row := by
      rw [← same, amount]
      cases row
      rfl
    rw [if_pos present, exactRow, ← same]
    exact eraseKey_weight_member cost rows row unique member
  · rw [if_neg present, eraseKey_of_absent key rows present, Nat.add_zero]

def oldBalanceWeight (rows : List AmountRow) (asset owner : String) : Nat :=
  if S.accountKey asset owner ∈ rows.map C.amountKey then
    amountCost (S.makeAmount (S.accountKey asset owner) (C.lookupLast (S.accountKey asset owner) rows)) + 1
  else 0

def newBalanceWeight (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int) : Nat :=
  let atoms := C.lookupLast (S.accountKey asset owner) rows + deltaAtoms
  if atoms = 0 then 0 else amountCost (S.makeAmount (S.accountKey asset owner) atoms) + 1

theorem updateRows_weight (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int)
    (unique : S.Unique rows) :
    weight (fun row => amountCost row + 1) (A.updateRows rows asset owner deltaAtoms) +
      oldBalanceWeight rows asset owner =
    weight (fun row => amountCost row + 1) rows + newBalanceWeight rows asset owner deltaAtoms := by
  have removed := eraseKey_weight (fun row => amountCost row + 1) (S.accountKey asset owner) rows unique
  change weight (fun row => amountCost row + 1) (S.eraseKey (S.accountKey asset owner) rows) +
    oldBalanceWeight rows asset owner = weight (fun row => amountCost row + 1) rows at removed
  unfold weight at removed
  unfold A.updateRows weight
  rw [((C.sortOn_perm S.balanceWire _).map (fun row => amountCost row + 1)).sum_nat]
  unfold S.putAmount newBalanceWeight
  by_cases zero : C.lookupLast (S.accountKey asset owner) rows + deltaAtoms = 0
  · simpa only [if_pos zero, Nat.add_zero] using removed
  · simp only [if_neg zero, List.map_cons, List.sum_cons]
    omega

/-- Empty-array correction computed only from the old table and selected update. -/
def postEmptyBit (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int) : Nat :=
  if rows.length + (if C.lookupLast (S.accountKey asset owner) rows + deltaAtoms ≠ 0 then 1 else 0) =
      (if S.accountKey asset owner ∈ rows.map C.amountKey then 1 else 0) then 1 else 0

theorem updateRows_emptyBit (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int)
    (unique : S.Unique rows) :
    emptyBit (A.updateRows rows asset owner deltaAtoms) = postEmptyBit rows asset owner deltaAtoms := by
  have count := G.updateRows_length rows asset owner deltaAtoms unique
  have zero : (A.updateRows rows asset owner deltaAtoms).length = 0 ↔
      rows.length + (if C.lookupLast (S.accountKey asset owner) rows + deltaAtoms ≠ 0 then 1 else 0) =
        (if S.accountKey asset owner ∈ rows.map C.amountKey then 1 else 0) := by omega
  simp only [emptyBit, List.isEmpty_iff_length_eq_zero, zero, postEmptyBit]

theorem updateRows_bytes (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int)
    (unique : S.Unique rows) :
    (balanceBytes (A.updateRows rows asset owner deltaAtoms)).length + oldBalanceWeight rows asset owner +
        emptyBit rows =
      (balanceBytes rows).length + newBalanceWeight rows asset owner deltaAtoms +
        postEmptyBit rows asset owner deltaAtoms := by
  have changed := updateRows_weight rows asset owner deltaAtoms unique
  rw [balanceBytes_length, balanceBytes_length, updateRows_emptyBit rows asset owner deltaAtoms unique]
  omega

theorem adjustComplete_weight_member (cost : V1SupplyRow → Nat) (rows : List V1SupplyRow)
    (row : V1SupplyRow) (deltaAtoms : Int) (unique : SourceAssetKeysUnique rows) (member : row ∈ rows) :
    weight cost (adjustComplete row.asset deltaAtoms rows) + cost row =
      weight cost rows + cost ⟨row.asset, row.amountAtoms + deltaAtoms⟩ := by
  induction rows with
  | nil => contradiction
  | cons head tail ih =>
      have keys := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | member
      · have absent : ∀ next ∈ tail, next.asset ≠ row.asset := by
          intro next member same
          exact keys.1 (List.mem_map.mpr ⟨next, member, same⟩)
        have unchanged := adjustComplete_of_absent absent deltaAtoms
        change weight cost ((if row.asset = row.asset then
          ⟨row.asset, row.amountAtoms + deltaAtoms⟩ else row) ::
          adjustComplete row.asset deltaAtoms tail) + cost row = _
        rw [if_pos rfl, unchanged]
        simp only [weight, List.map_cons, List.sum_cons]
        omega
      · have different : head.asset ≠ row.asset := by
          intro same
          exact keys.1 (same ▸ List.mem_map.mpr ⟨row, member, rfl⟩)
        have step := ih keys.2 member
        change weight cost ((if head.asset = row.asset then
          ⟨head.asset, head.amountAtoms + deltaAtoms⟩ else head) ::
          adjustComplete row.asset deltaAtoms tail) + cost row = _
        rw [if_neg different]
        simp only [weight, List.map_cons, List.sum_cons] at step ⊢
        omega

def oldSupplyCost (rows : List V1SupplyRow) (asset : Asset) : Nat :=
  supplyCost ⟨asset, supplyFor (numericRows rows) asset⟩

def newSupplyCost (rows : List V1SupplyRow) (asset : Asset) (deltaAtoms : Int) : Nat :=
  supplyCost ⟨asset, supplyFor (numericRows rows) asset + deltaAtoms⟩

theorem adjustComplete_bytes (rows : List V1SupplyRow) (asset : Asset) (deltaAtoms : Int)
    (unique : SourceAssetKeysUnique rows) (registered : asset ∈ rows.map V1SupplyRow.asset) :
    (supplyBytes (adjustComplete asset deltaAtoms rows)).length + oldSupplyCost rows asset =
      (supplyBytes rows).length + newSupplyCost rows asset deltaAtoms := by
  obtain ⟨row, member, same⟩ := List.mem_map.mp registered
  have lookup : supplyFor (numericRows rows) asset = row.amountAtoms := by
    rw [supplyFor_numericRows_preserved, ← same]
    exact source_supplyFor_eq_member_of_unique unique member
  have changed := adjustComplete_weight_member (fun r => supplyCost r + 1) rows row deltaAtoms unique member
  have lengths : (adjustComplete asset deltaAtoms rows).length = rows.length := by
    simp only [adjustComplete, List.length_map]
  have empties : emptyBit (adjustComplete asset deltaAtoms rows) = emptyBit rows := by
    simp only [emptyBit, List.isEmpty_iff_length_eq_zero, lengths]
  rw [supplyBytes_length, supplyBytes_length, empties]
  unfold oldSupplyCost newSupplyCost
  rw [lookup, ← same]
  have eta : (⟨row.asset, row.amountAtoms⟩ : V1SupplyRow) = row := by cases row; rfl
  rw [eta]
  simp only [] at changed
  omega

def framedBytes (opening middle closing : Bytes) (balances : List AmountRow)
    (supplies : List V1SupplyRow) : Bytes :=
  opening ++ balanceBytes balances ++ middle ++ supplyBytes supplies ++ closing

/-- Exact sorted-field leaf schema. `policies` is the unchanged serialized value,
whose relationship to the actual policy serializer is an external obligation. -/
def leafBytes (schema release : String) (policies : Bytes) (balances : List AmountRow)
    (supplies : List V1SupplyRow) : Bytes :=
  framedBytes (raw "{\"balances\":")
    (raw ",\"module_release_id\":" ++ quoted release ++ raw ",\"policies\":" ++ policies ++
      raw ",\"schema\":" ++ quoted schema ++ raw ",\"supplies\":")
    (raw "}") balances supplies

/-- Exact sorted-field aggregate schema. The three metadata byte values must
represent the same owned immutable metadata before and after recomposition. -/
def laneBytes (release : String) (managedPolicies originRegistry transferPolicies : Bytes)
    (balances : List AmountRow) (supplies : List V1SupplyRow) : Bytes :=
  framedBytes (raw "{\"balances\":")
    (raw ",\"managed_policies\":" ++ managedPolicies ++ raw ",\"module_release_id\":" ++ quoted release ++
      raw ",\"origin_registry\":" ++ originRegistry ++
      raw ",\"schema\":\"zenodex/asset-lane-state/v2\",\"supplies\":")
    (raw ",\"transfer_policies\":" ++ transferPolicies ++ raw "}") balances supplies

theorem framedBytes_length (opening middle closing : Bytes) (balances : List AmountRow)
    (supplies : List V1SupplyRow) :
    (framedBytes opening middle closing balances supplies).length =
      opening.length + middle.length + closing.length + (balanceBytes balances).length +
        (supplyBytes supplies).length := by
  simp only [framedBytes, List.length_append]
  omega

theorem framed_update_bytes (opening middle closing : Bytes) (balances : List AmountRow)
    (supplies : List V1SupplyRow) (asset owner : String) (deltaAtoms : Int)
    (balanceUnique : S.Unique balances) (supplyUnique : SourceAssetKeysUnique supplies)
    (registered : asset ∈ supplies.map V1SupplyRow.asset) :
    (framedBytes opening middle closing (A.updateRows balances asset owner deltaAtoms)
        (adjustComplete asset deltaAtoms supplies)).length + oldBalanceWeight balances asset owner +
        oldSupplyCost supplies asset + emptyBit balances =
      (framedBytes opening middle closing balances supplies).length +
        newBalanceWeight balances asset owner deltaAtoms + newSupplyCost supplies asset deltaAtoms +
        postEmptyBit balances asset owner deltaAtoms := by
  have balance := updateRows_bytes balances asset owner deltaAtoms balanceUnique
  have supply := adjustComplete_bytes supplies asset deltaAtoms supplyUnique registered
  rw [framedBytes_length, framedBytes_length]
  omega

theorem framed_recomposition_bytes (opening middle closing : Bytes) (managed : List Asset)
    (balances : List AmountRow) (supplies : List V1SupplyRow) (asset owner : String) (deltaAtoms : Int)
    (balanceUnique : S.Unique balances) (accounts : R.AccountsDomain balances)
    (supplyUnique : SourceAssetKeysUnique supplies) (supplyOrdered : SourceAssetKeysOrdered supplies)
    (selected : asset ∈ managed) (registered : asset ∈ supplies.map V1SupplyRow.asset) :
    (framedBytes opening middle closing (R.recomposeBalances managed balances asset owner deltaAtoms)
        (R.recomposeSupplies managed supplies asset deltaAtoms)).length +
        oldBalanceWeight balances asset owner + oldSupplyCost supplies asset + emptyBit balances =
      (framedBytes opening middle closing balances supplies).length +
        newBalanceWeight balances asset owner deltaAtoms + newSupplyCost supplies asset deltaAtoms +
        postEmptyBit balances asset owner deltaAtoms := by
  rw [R.managed_balance_recompose managed balances asset owner deltaAtoms balanceUnique accounts selected,
    R.managed_complete_supply_recompose managed supplies asset deltaAtoms supplyUnique supplyOrdered selected]
  exact framed_update_bytes opening middle closing balances supplies asset owner deltaAtoms
    balanceUnique supplyUnique registered

theorem updateRows_tokens (balances : List AmountRow) (asset owner : String) (deltaAtoms : Int)
    (tokens : BalanceTokens balances) (assetToken : ValidToken asset) (ownerToken : ValidToken owner) :
    BalanceTokens (A.updateRows balances asset owner deltaAtoms) := by
  intro row member
  have rawMember := (C.sortOn_perm S.balanceWire _).mem_iff.mp member
  change row ∈ S.putAmount (S.accountKey asset owner)
    (C.lookupLast (S.accountKey asset owner) balances + deltaAtoms) balances at rawMember
  unfold S.putAmount at rawMember
  split at rawMember
  · exact tokens row ((S.mem_eraseKey _ balances row).mp rawMember).1
  · rcases List.mem_cons.mp rawMember with rfl | existing
    · exact ⟨ownerToken, assetToken, by change ValidToken "accounts"; unfold ValidToken; decide⟩
    · exact tokens row ((S.mem_eraseKey _ balances row).mp existing).1

theorem adjustComplete_tokens (supplies : List V1SupplyRow) (asset : Asset) (deltaAtoms : Int)
    (tokens : SupplyTokens supplies) : SupplyTokens (adjustComplete asset deltaAtoms supplies) := by
  intro row member
  unfold adjustComplete at member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  by_cases same : source.asset = asset
  · simpa only [if_pos same] using tokens source sourceMember
  · simpa only [if_neg same] using tokens source sourceMember

/-- Scoped printable-token closure accompanies the exact aggregate byte change.
Metadata parameters are fixed serialized values, not an admission witness. -/
theorem lane_recomposition_bytes (release : String) (managedPolicies originRegistry transferPolicies : Bytes)
    (managed : List Asset) (balances : List AmountRow) (supplies : List V1SupplyRow)
    (asset owner : String) (deltaAtoms : Int) (balanceUnique : S.Unique balances)
    (accounts : R.AccountsDomain balances) (supplyUnique : SourceAssetKeysUnique supplies)
    (supplyOrdered : SourceAssetKeysOrdered supplies) (selected : asset ∈ managed)
    (registered : asset ∈ supplies.map V1SupplyRow.asset) (balanceTokens : BalanceTokens balances)
    (supplyTokens : SupplyTokens supplies) (ownerToken : ValidToken owner) :
    BalanceTokens (R.recomposeBalances managed balances asset owner deltaAtoms) ∧
      SupplyTokens (R.recomposeSupplies managed supplies asset deltaAtoms) ∧
      (laneBytes release managedPolicies originRegistry transferPolicies
          (R.recomposeBalances managed balances asset owner deltaAtoms)
          (R.recomposeSupplies managed supplies asset deltaAtoms)).length +
          oldBalanceWeight balances asset owner + oldSupplyCost supplies asset + emptyBit balances =
        (laneBytes release managedPolicies originRegistry transferPolicies balances supplies).length +
          newBalanceWeight balances asset owner deltaAtoms + newSupplyCost supplies asset deltaAtoms +
          postEmptyBit balances asset owner deltaAtoms := by
  obtain ⟨source, member, same⟩ := List.mem_map.mp registered
  have assetToken : ValidToken asset := same ▸ supplyTokens source member
  have balance : BalanceTokens (R.recomposeBalances managed balances asset owner deltaAtoms) := by
    rw [R.managed_balance_recompose managed balances asset owner deltaAtoms balanceUnique accounts selected]
    exact updateRows_tokens balances asset owner deltaAtoms balanceTokens assetToken ownerToken
  have supply : SupplyTokens (R.recomposeSupplies managed supplies asset deltaAtoms) := by
    rw [R.managed_complete_supply_recompose managed supplies asset deltaAtoms supplyUnique supplyOrdered selected]
    exact adjustComplete_tokens supplies asset deltaAtoms supplyTokens
  exact ⟨balance, supply, framed_recomposition_bytes _ _ _ managed balances supplies asset owner deltaAtoms
    balanceUnique accounts supplyUnique supplyOrdered selected registered⟩

/-- Exact row-and-byte capacity criterion derived from the source. It does not
include the separate metadata, asset-count, quantity or runtime outcome checks. -/
theorem recomposition_capacity_iff (opening middle closing : Bytes) (managed : List Asset)
    (balances : List AmountRow) (supplies : List V1SupplyRow) (asset owner : String) (deltaAtoms : Int)
    (rowLimit byteLimit : Nat) (balanceUnique : S.Unique balances) (accounts : R.AccountsDomain balances)
    (supplyUnique : SourceAssetKeysUnique supplies) (supplyOrdered : SourceAssetKeysOrdered supplies)
    (selected : asset ∈ managed) (registered : asset ∈ supplies.map V1SupplyRow.asset) :
    ((R.recomposeBalances managed balances asset owner deltaAtoms).length ≤ rowLimit ∧
      (framedBytes opening middle closing (R.recomposeBalances managed balances asset owner deltaAtoms)
        (R.recomposeSupplies managed supplies asset deltaAtoms)).length ≤ byteLimit) ↔
    (balances.length +
        (if C.lookupLast (S.accountKey asset owner) balances + deltaAtoms ≠ 0 then 1 else 0) ≤
        rowLimit + (if S.accountKey asset owner ∈ balances.map C.amountKey then 1 else 0) ∧
      (framedBytes opening middle closing balances supplies).length +
          newBalanceWeight balances asset owner deltaAtoms + newSupplyCost supplies asset deltaAtoms +
          postEmptyBit balances asset owner deltaAtoms ≤
        byteLimit + oldBalanceWeight balances asset owner + oldSupplyCost supplies asset + emptyBit balances) := by
  have rows := G.recomposeBalances_length managed balances asset owner deltaAtoms balanceUnique accounts selected
  have bytes := framed_recomposition_bytes opening middle closing managed balances supplies asset owner deltaAtoms
    balanceUnique accounts supplyUnique supplyOrdered selected registered
  omega

theorem lane_capacity_4096_1048576 (release : String) (managedPolicies originRegistry transferPolicies : Bytes)
    (managed : List Asset) (balances : List AmountRow) (supplies : List V1SupplyRow)
    (asset owner : String) (deltaAtoms : Int) (balanceUnique : S.Unique balances)
    (accounts : R.AccountsDomain balances) (supplyUnique : SourceAssetKeysUnique supplies)
    (supplyOrdered : SourceAssetKeysOrdered supplies) (selected : asset ∈ managed)
    (registered : asset ∈ supplies.map V1SupplyRow.asset) :
    ((R.recomposeBalances managed balances asset owner deltaAtoms).length ≤ 4096 ∧
      (laneBytes release managedPolicies originRegistry transferPolicies
        (R.recomposeBalances managed balances asset owner deltaAtoms)
        (R.recomposeSupplies managed supplies asset deltaAtoms)).length ≤ 1048576) ↔
    (balances.length +
        (if C.lookupLast (S.accountKey asset owner) balances + deltaAtoms ≠ 0 then 1 else 0) ≤
        4096 + (if S.accountKey asset owner ∈ balances.map C.amountKey then 1 else 0) ∧
      (laneBytes release managedPolicies originRegistry transferPolicies balances supplies).length +
          newBalanceWeight balances asset owner deltaAtoms + newSupplyCost supplies asset deltaAtoms +
          postEmptyBit balances asset owner deltaAtoms ≤
        1048576 + oldBalanceWeight balances asset owner + oldSupplyCost supplies asset + emptyBit balances) :=
  recomposition_capacity_iff _ _ _ managed balances supplies asset owner deltaAtoms 4096 1048576
    balanceUnique accounts supplyUnique supplyOrdered selected registered

end Proofs.AssetLaneFiniteByteAccountingV2
