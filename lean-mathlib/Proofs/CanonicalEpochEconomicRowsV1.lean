import Proofs.CheckedEpochEconomicTablesV1
import Init.Data.List.Sort
import Init.Data.Ord

/-!
Canonical value-level emission for checked epoch totals. Effect keys use the
runtime token order (kind code, asset, principal, domain); amount delta records
use (table code, owner, asset, domain, delta). Neither enum declaration order
nor a permutation alone specifies the runtime tuple.

The endpoint builder models dictionary last-write lookup and requires unique
endpoint amount keys for agreement with the existing sum-based table relation.
This is a universal Lean value model and a finite Python correspondence target,
not universal Python execution, ABI bytes, cryptography or publication authority.
-/
namespace Proofs.CanonicalEpochEconomicRowsV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open CheckedEconomicAggregationV1 CheckedEpochEconomicTablesV1

attribute [local instance] lexOrd

def uniqueFirst {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (uniqueFirst xs).filter (fun y => decide (y ≠ x))

theorem mem_uniqueFirst {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    x ∈ uniqueFirst xs ↔ x ∈ xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      simp only [uniqueFirst, List.mem_cons, List.mem_filter, decide_eq_true_eq, ih]
      by_cases same : x = y <;> simp [same]

theorem uniqueFirst_nodup {α : Type} [DecidableEq α] (xs : List α) :
    (uniqueFirst xs).Nodup := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
      refine List.nodup_cons.mpr ⟨?_, ih.filter _⟩
      simp only [List.mem_filter, decide_eq_true_eq, not_and]
      intro _ same
      exact same rfl

def sortOn {α β : Type} [Ord β] (key : α → β) (xs : List α) : List α :=
  xs.mergeSort (fun a b => (compare (key a) (key b)).isLE)

theorem sortOn_perm {α β : Type} [Ord β] (key : α → β) (xs : List α) :
    (sortOn key xs).Perm xs := List.mergeSort_perm _ _

theorem mem_sortOn {α β : Type} [Ord β] (key : α → β) (x : α) (xs : List α) :
    x ∈ sortOn key xs ↔ x ∈ xs := (sortOn_perm key xs).mem_iff

theorem sortOn_ordered {α β : Type} [Ord β] [Std.TransOrd β]
    (key : α → β) (xs : List α) :
    (sortOn key xs).Pairwise (fun a b => (compare (key a) (key b)).isLE = true) := by
  apply List.pairwise_mergeSort
  · intro a b c hab hbc
    exact Std.TransOrd.isLE_trans hab hbc
  · intro a b
    rw [Std.OrientedOrd.eq_swap (a := key b) (b := key a)]
    cases compare (key a) (key b) <;> decide

def decodeKind : Kind → EffectKind
  | .accountMovement => .accountMovement
  | .issue => .issue
  | .burn => .burn
  | .custody => .custody
  | .liability => .liability
  | .reserve => .reserve
  | .feeAllocation => .feeAllocation
  | .reward => .reward
  | .slash => .slash

def rowOf (key : Key) (delta : Int) : EconomicEffectRow :=
  ⟨decodeKind key.kind, key.principal, key.asset, key.domain, delta⟩

def wireKey (key : Key) : String × String × String × String :=
  ((decodeKind key.kind).code, key.asset, key.principal, key.domain)

def sourceKeys (plans : List EffectPlan) : List Key :=
  (orderedRows plans).map (fun row => row.key)

def emissionKeys (plans : List EffectPlan) (totals : Totals) : List Key :=
  (sortOn wireKey (uniqueFirst (sourceKeys plans))).filter (fun key => decide (totals key ≠ 0))

def emitRows (plans : List EffectPlan) (totals : Totals) : List EconomicEffectRow :=
  (emissionKeys plans totals).map (fun key => rowOf key (totals key))

theorem encode_decode_kind (kind : Kind) : encodeKind (decodeKind kind) = kind := by
  cases kind <;> rfl

theorem decode_encode_kind (kind : EffectKind) : decodeKind (encodeKind kind) = kind := by
  cases kind <;> rfl

theorem rowOf_key (key : Key) (delta : Int) : (encodeRow (rowOf key delta)).key = key := by
  cases key
  simp only [rowOf, encodeRow, encodeKey, encode_decode_kind]

theorem rowOf_exemplar (row : EconomicEffectRow) (delta : Int) :
    rowOf (encodeRow row).key delta = {row with deltaAtoms := delta} := by
  cases row
  simp only [rowOf, encodeRow, encodeKey, decode_encode_kind]

theorem effect_code_injective {a b : EffectKind} (same : a.code = b.code) : a = b := by
  cases a <;> cases b <;> simp_all [EffectKind.code]

theorem wireKey_injective {a b : Key} (same : wireKey a = wireKey b) : a = b := by
  rcases a with ⟨ak, ap, aa, ad⟩
  rcases b with ⟨bk, bp, ba, bd⟩
  simp only [wireKey, Prod.mk.injEq] at same
  have kinds := effect_code_injective same.1
  have encoded := congrArg encodeKind kinds
  simp only [encode_decode_kind] at encoded
  simp only [Key.mk.injEq]
  exact ⟨encoded, same.2.2.1, same.2.1, same.2.2.2⟩

theorem mem_emissionKeys (plans : List EffectPlan) (totals : Totals) (key : Key) :
    key ∈ emissionKeys plans totals ↔ key ∈ sourceKeys plans ∧ totals key ≠ 0 := by
  simp only [emissionKeys, List.mem_filter, mem_sortOn, mem_uniqueFirst, decide_eq_true_eq]

theorem emissionKeys_nodup (plans : List EffectPlan) (totals : Totals) :
    (emissionKeys plans totals).Nodup :=
  ((uniqueFirst_nodup (sourceKeys plans)).perm (sortOn_perm wireKey _).symm).filter _

theorem emissionKeys_ordered (plans : List EffectPlan) (totals : Totals) :
    (emissionKeys plans totals).Pairwise
      (fun a b => (compare (wireKey a) (wireKey b)).isLE = true) :=
  (sortOn_ordered wireKey (uniqueFirst (sourceKeys plans))).filter _

theorem keyedSum_absent (key : Key) (rows : List Row)
    (absent : key ∉ rows.map (fun row => row.key)) : keyedSum key rows = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simp only [keyedSum, if_neg (Ne.symm absent.1), ih absent.2, Int.zero_add]

theorem successful_total_supported (plans : List EffectPlan) (totals : Totals)
    (accepted : checkedEpoch i128 plans = .ok totals) (key : Key)
    (nonzero : totals key ≠ 0) : key ∈ sourceKeys plans := by
  by_cases present : key ∈ sourceKeys plans
  · exact present
  · exact False.elim (nonzero ((successful_epoch_complete_keys i128 plans totals accepted key).trans
      (keyedSum_absent key (orderedRows plans) present)))

theorem checkedFold_bounded (bounds : Bounds) (initial output : Totals) (rows : List Row)
    (initialFits : ∀ key, Fits bounds (initial key))
    (accepted : checkedFold bounds initial rows = .ok output) :
    ∀ key, Fits bounds (output key) := by
  induction rows generalizing initial with
  | nil => cases accepted; exact initialFits
  | cons row rows ih =>
      simp only [checkedFold] at accepted
      split at accepted
      next fits =>
        apply ih (advance initial row) ?_ accepted
        intro key
        by_cases same : row.key = key
        · subst key
          simpa only [advance, if_pos rfl] using fits
        · simpa only [advance, if_neg same, Int.add_zero] using initialFits key
      next => contradiction

theorem successful_total_bounded (plans : List EffectPlan) (totals : Totals)
    (accepted : checkedEpoch i128 plans = .ok totals) (key : Key) : Fits i128 (totals key) :=
  checkedFold_bounded i128 empty totals (orderedRows plans)
    (fun _ => by change Fits i128 0; decide) accepted key

theorem encode_rowOf (key : Key) (delta : Int) : encodeRow (rowOf key delta) = ⟨key, delta⟩ := by
  cases key
  simp only [encodeRow, rowOf, encodeKey, encode_decode_kind]

theorem emitRows_keys (plans : List EffectPlan) (totals : Totals) :
    (emitRows plans totals).map (fun row => (encodeRow row).key) = emissionKeys plans totals := by
  simp only [emitRows, List.map_map, Function.comp_def, rowOf_key]
  exact List.map_id _

theorem mem_emitRows (plans : List EffectPlan) (totals : Totals) (row : EconomicEffectRow) :
    row ∈ emitRows plans totals ↔
      ∃ key, key ∈ sourceKeys plans ∧ totals key ≠ 0 ∧ rowOf key (totals key) = row := by
  simp only [emitRows, List.mem_map, mem_emissionKeys, and_assoc]

theorem emitted_row_value (plans : List EffectPlan) (totals : Totals) (row : EconomicEffectRow)
    (member : row ∈ emitRows plans totals) :
    row.deltaAtoms = totals (encodeRow row).key ∧ row.deltaAtoms ≠ 0 := by
  obtain ⟨key, _, nonzero, rfl⟩ := (mem_emitRows plans totals row).mp member
  rw [rowOf_key]
  exact ⟨rfl, nonzero⟩

theorem keyedSum_unique_map (keys : List Key) (totals : Totals) (key : Key)
    (unique : keys.Nodup) :
    keyedSum key (keys.map (fun k => (⟨k, totals k⟩ : Row))) =
      if key ∈ keys then totals key else 0 := by
  induction keys with
  | nil => simp only [List.map_nil, keyedSum, List.not_mem_nil, if_false]
  | cons head tail ih =>
      have parts := List.nodup_cons.mp unique
      simp only [List.map_cons, keyedSum, ih parts.2, List.mem_cons]
      by_cases same : head = key
      · subst key
        simp only [parts.1, if_false, Int.add_zero, true_or, if_true]
      · have other : key ≠ head := Ne.symm same
        simp only [if_neg same, other, false_or, Int.zero_add]

theorem emitted_complete_sums (plans : List EffectPlan) (totals : Totals)
    (accepted : checkedEpoch i128 plans = .ok totals) (key : Key) :
    keyedSum key (encodeRows (emitRows plans totals)) = totals key := by
  simp only [emitRows, encodeRows, List.map_map, Function.comp_def, encode_rowOf]
  rw [keyedSum_unique_map _ totals key (emissionKeys_nodup plans totals)]
  by_cases zero : totals key = 0
  · simp only [zero, ite_self]
  · rw [if_pos ((mem_emissionKeys plans totals key).mpr
      ⟨successful_total_supported plans totals accepted key zero, zero⟩)]

theorem emissionKeys_strict (plans : List EffectPlan) (totals : Totals) :
    (emissionKeys plans totals).Pairwise (fun a b => compare (wireKey a) (wireKey b) = .lt) := by
  apply ((emissionKeys_ordered plans totals).and (emissionKeys_nodup plans totals)).imp
  intro a b ⟨ordered, different⟩
  rcases Ordering.isLE_iff_eq_lt_or_eq_eq.mp ordered with less | same
  · exact less
  · exact False.elim (different (wireKey_injective (Std.LawfulEqOrd.eq_of_compare same)))

def CanonicalEffectRows (rows : List EconomicEffectRow) : Prop :=
  (rows.map (fun row => (encodeRow row).key)).Nodup ∧
  rows.Pairwise (fun a b => compare (wireKey (encodeRow a).key) (wireKey (encodeRow b).key) = .lt) ∧
  ∀ row ∈ rows, row.deltaAtoms ≠ 0

theorem emitted_rows_canonical (plans : List EffectPlan) (totals : Totals) :
    CanonicalEffectRows (emitRows plans totals) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [emitRows_keys]
    exact emissionKeys_nodup plans totals
  · simpa only [emitRows, List.pairwise_map, rowOf_key] using emissionKeys_strict plans totals
  · intro row member
    exact (emitted_row_value plans totals row member).2

theorem emitted_rows_bounded (plans : List EffectPlan) (totals : Totals)
    (accepted : checkedEpoch i128 plans = .ok totals) :
    ∀ row ∈ emitRows plans totals, Fits i128 row.deltaAtoms := by
  intro row member
  rw [(emitted_row_value plans totals row member).1]
  exact successful_total_bounded plans totals accepted _

abbrev AmountKey := String × String × String

def amountKey (row : AmountRow) : AmountKey := (row.owner, row.asset, row.custodyDomain)

/-- A repeated key takes the last row, as in the Python dictionary builder. -/
def lookupLast (key : AmountKey) : List AmountRow → Int
  | [] => 0
  | row :: rows =>
      if key ∈ rows.map amountKey then lookupLast key rows
      else if amountKey row = key then row.amountAtoms else 0

def amountSum (key : AmountKey) : List AmountRow → Int
  | [] => 0
  | row :: rows => (if amountKey row = key then row.amountAtoms else 0) + amountSum key rows

theorem amountSum_eq_amountAt (key : AmountKey) (rows : List AmountRow) :
    amountSum key rows = amountAt rows key.1 key.2.1 key.2.2 := by
  rcases key with ⟨owner, asset, domain⟩
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [amountSum, amountAt, List.map_cons, List.sum_cons, amountKey,
        Prod.mk.injEq] at *
      rw [ih]

theorem amountSum_absent (key : AmountKey) (rows : List AmountRow)
    (absent : key ∉ rows.map amountKey) : amountSum key rows = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simp only [amountSum, if_neg (Ne.symm absent.1), ih absent.2, Int.zero_add]

theorem lookupLast_absent (key : AmountKey) (rows : List AmountRow)
    (absent : key ∉ rows.map amountKey) : lookupLast key rows = 0 := by
  cases rows with
  | nil => rfl
  | cons row rows =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simp only [lookupLast, if_neg absent.2, if_neg (Ne.symm absent.1)]

theorem lookupLast_eq_amountAt (key : AmountKey) (rows : List AmountRow)
    (unique : (rows.map amountKey).Nodup) :
    lookupLast key rows = amountAt rows key.1 key.2.1 key.2.2 := by
  rw [← amountSum_eq_amountAt]
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have parts := List.nodup_cons.mp unique
      by_cases tailHas : key ∈ rows.map amountKey
      · have different : amountKey row ≠ key := by
          intro same
          exact parts.1 (same ▸ tailHas)
        simp only [lookupLast, if_pos tailHas, amountSum, if_neg different,
          ih parts.2, Int.zero_add]
      · simp only [lookupLast, if_neg tailHas, amountSum, amountSum_absent key rows tailHas,
          Int.add_zero]

def tableCode : Table → String
  | .balances => "balances"
  | .custody => "custody"
  | .liabilities => "liabilities"
  | .reserves => "reserves"

structure DeltaRow where
  table : Table
  owner : String
  asset : String
  domain : String
  delta : Int
  deriving DecidableEq, BEq, Repr

def deltaKey (row : DeltaRow) : AmountKey := (row.owner, row.asset, row.domain)

def deltaWire (row : DeltaRow) : String × String × String × String × Int :=
  (tableCode row.table, row.owner, row.asset, row.domain, row.delta)

def makeDelta (table : Table) (key : AmountKey) (delta : Int) : DeltaRow :=
  ⟨table, key.1, key.2.1, key.2.2, delta⟩

def projectRaw (table : Table) (rows : List EconomicEffectRow) : List DeltaRow :=
  (rows.filter (fun row => decide (row.kind = tableKind table))).map
    (fun row => ⟨table, row.principal, row.asset, row.custodyDomain, row.deltaAtoms⟩)

def projectDeltaRows (table : Table) (rows : List EconomicEffectRow) : List DeltaRow :=
  sortOn deltaWire (projectRaw table rows)

def endpointKeys (pre post : List AmountRow) : List AmountKey :=
  sortOn (fun key : AmountKey => (key.2.1, key.1, key.2.2))
    (uniqueFirst (pre.map amountKey ++ post.map amountKey))

def endpointRaw (table : Table) (pre post : List AmountRow) : List DeltaRow :=
  (endpointKeys pre post).map (fun key =>
    makeDelta table key (lookupLast key post - lookupLast key pre))

def checkDeltaRows : List DeltaRow → Except Reject (List DeltaRow)
  | [] => .ok []
  | row :: rows =>
      if Fits i128 row.delta then
        (checkDeltaRows rows).map (fun rest => if row.delta = 0 then rest else row :: rest)
      else .error .signedAggregationBounds

def checkedStateDeltaRows (table : Table) (pre post : List AmountRow) : Except Reject (List DeltaRow) :=
  (checkDeltaRows (endpointRaw table pre post)).map (sortOn deltaWire)

def EndpointKeysUnique (pre post : GlobalState) : Prop :=
  ∀ table, ((tableRows table pre).map amountKey).Nodup ∧
    ((tableRows table post).map amountKey).Nodup

theorem checkDeltaRows_of_bounded (rows : List DeltaRow)
    (bounded : ∀ row ∈ rows, Fits i128 row.delta) :
    checkDeltaRows rows = .ok (rows.filter (fun row => decide (row.delta ≠ 0))) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rw [checkDeltaRows, if_pos (bounded row (by simp)),
        ih (fun r member => bounded r (by simp [member]))]
      by_cases zero : row.delta = 0 <;> simp [Except.map, zero]

theorem mem_endpointKeys (pre post : List AmountRow) (key : AmountKey) :
    key ∈ endpointKeys pre post ↔ key ∈ pre.map amountKey ∨ key ∈ post.map amountKey := by
  simp only [endpointKeys, mem_sortOn, mem_uniqueFirst, List.mem_append]

theorem endpointKeys_nodup (pre post : List AmountRow) : (endpointKeys pre post).Nodup :=
  (uniqueFirst_nodup _).perm (sortOn_perm _ _).symm

theorem endpoint_delta_equation {pre post : GlobalState} {plans : List EffectPlan}
    (totals : Totals) (chain : TableChain pre plans post) (unique : EndpointKeysUnique pre post)
    (accepted : checkedEpoch i128 plans = .ok totals) (table : Table) (key : AmountKey) :
    lookupLast key (tableRows table post) - lookupLast key (tableRows table pre) =
      totals (encodeKey (tableKind table) key.1 key.2.1 key.2.2) := by
  rw [lookupLast_eq_amountAt key _ (unique table).2,
    lookupLast_eq_amountAt key _ (unique table).1]
  exact successful_epoch_exact_tables i128 totals chain accepted table key.1 key.2.1 key.2.2

theorem endpoint_rows_bounded {pre post : GlobalState} {plans : List EffectPlan}
    (totals : Totals) (chain : TableChain pre plans post) (unique : EndpointKeysUnique pre post)
    (accepted : checkedEpoch i128 plans = .ok totals) (table : Table) :
    ∀ row ∈ endpointRaw table (tableRows table pre) (tableRows table post), Fits i128 row.delta := by
  intro row member
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
  change Fits i128 (lookupLast key _ - lookupLast key _)
  rw [endpoint_delta_equation totals chain unique accepted table key]
  exact successful_total_bounded plans totals accepted _

theorem makeDelta_key (table : Table) (key : AmountKey) (delta : Int) :
    deltaKey (makeDelta table key delta) = key := by
  rcases key with ⟨owner, asset, domain⟩
  rfl

theorem endpoint_delta_supported (pre post : List AmountRow) (key : AmountKey)
    (nonzero : lookupLast key post - lookupLast key pre ≠ 0) : key ∈ endpointKeys pre post := by
  by_cases present : key ∈ pre.map amountKey ∨ key ∈ post.map amountKey
  · exact (mem_endpointKeys pre post key).mpr present
  · have parts := not_or.mp present
    rw [lookupLast_absent key pre parts.1, lookupLast_absent key post parts.2] at nonzero
    exact False.elim (nonzero rfl)

theorem endpoint_nonzero_membership (table : Table) (pre post : List AmountRow) (row : DeltaRow) :
    row ∈ (endpointRaw table pre post).filter (fun r => decide (r.delta ≠ 0)) ↔
      ∃ key, lookupLast key post - lookupLast key pre ≠ 0 ∧
        makeDelta table key (lookupLast key post - lookupLast key pre) = row := by
  constructor
  · intro member
    obtain ⟨inRows, nonzero⟩ := List.mem_filter.mp member
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp inRows
    exact ⟨key, of_decide_eq_true nonzero, rfl⟩
  · rintro ⟨key, nonzero, rfl⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨key, endpoint_delta_supported pre post key nonzero, rfl⟩,
      decide_eq_true nonzero⟩

theorem projected_emission_membership (plans : List EffectPlan) (totals : Totals)
    (accepted : checkedEpoch i128 plans = .ok totals) (table : Table) (row : DeltaRow) :
    row ∈ projectRaw table (emitRows plans totals) ↔
      ∃ key : AmountKey, totals (encodeKey (tableKind table) key.1 key.2.1 key.2.2) ≠ 0 ∧
        makeDelta table key (totals (encodeKey (tableKind table) key.1 key.2.1 key.2.2)) = row := by
  constructor
  · intro member
    obtain ⟨effect, filtered, rfl⟩ := List.mem_map.mp member
    obtain ⟨emitted, kindTrue⟩ := List.mem_filter.mp filtered
    obtain ⟨key, _, nonzero, rfl⟩ := (mem_emitRows plans totals effect).mp emitted
    have kind : decodeKind key.kind = tableKind table := of_decide_eq_true kindTrue
    have same : encodeKey (tableKind table) key.principal key.asset key.domain = key := by
      rw [← kind]
      exact rowOf_key key (totals key)
    refine ⟨(key.principal, key.asset, key.domain), ?_, ?_⟩
    · simpa only [same] using nonzero
    · simp only [same, makeDelta, rowOf]
  · rintro ⟨key, nonzero, rfl⟩
    let encoded := encodeKey (tableKind table) key.1 key.2.1 key.2.2
    have emitted : rowOf encoded (totals encoded) ∈ emitRows plans totals :=
      (mem_emitRows plans totals _).mpr
        ⟨encoded, successful_total_supported plans totals accepted encoded nonzero, nonzero, rfl⟩
    apply List.mem_map.mpr
    refine ⟨rowOf encoded (totals encoded), List.mem_filter.mpr ⟨emitted, ?_⟩, ?_⟩
    · simp only [rowOf, encoded, encodeKey, decode_encode_kind, decide_true]
    · rfl

theorem endpoint_projected_membership {pre post : GlobalState} {plans : List EffectPlan}
    (totals : Totals) (chain : TableChain pre plans post) (unique : EndpointKeysUnique pre post)
    (accepted : checkedEpoch i128 plans = .ok totals) (table : Table) (row : DeltaRow) :
    row ∈ (endpointRaw table (tableRows table pre) (tableRows table post)).filter
        (fun r => decide (r.delta ≠ 0)) ↔ row ∈ projectRaw table (emitRows plans totals) := by
  rw [endpoint_nonzero_membership, projected_emission_membership plans totals accepted]
  simp only [endpoint_delta_equation totals chain unique accepted table]

theorem endpointRaw_nodup (table : Table) (pre post : List AmountRow) :
    (endpointRaw table pre post).Nodup := by
  apply List.pairwise_map.mpr
  apply (endpointKeys_nodup pre post).imp
  intro a b different same
  exact different (by simpa only [makeDelta_key] using congrArg deltaKey same)

theorem projectRaw_nodup (table : Table) (plans : List EffectPlan) (totals : Totals) :
    (projectRaw table (emitRows plans totals)).Nodup := by
  have base := List.pairwise_map.mp (emitted_rows_canonical plans totals).1
  have filtered := base.filter (fun row => decide (row.kind = tableKind table))
  apply List.pairwise_map.mpr
  apply (List.Pairwise.and_mem.mp filtered).imp
  intro a b ⟨am, bm, different⟩ same
  have ak : a.kind = tableKind table := of_decide_eq_true (List.mem_filter.mp am).2
  have bk : b.kind = tableKind table := of_decide_eq_true (List.mem_filter.mp bm).2
  have coordinates := congrArg deltaKey same
  simp only [deltaKey, Prod.mk.injEq] at coordinates
  apply different
  simp only [encodeRow, encodeKey, Key.mk.injEq]
  exact ⟨congrArg encodeKind (ak.trans bk.symm), coordinates.1, coordinates.2.1, coordinates.2.2⟩

theorem tableCode_injective {a b : Table} (same : tableCode a = tableCode b) : a = b := by
  cases a <;> cases b <;> simp_all [tableCode]

theorem deltaWire_injective {a b : DeltaRow} (same : deltaWire a = deltaWire b) : a = b := by
  rcases a with ⟨aTable, ao, aa, ad, av⟩
  rcases b with ⟨bt, bo, ba, bd, bv⟩
  simp only [deltaWire, Prod.mk.injEq] at same
  simp only [DeltaRow.mk.injEq]
  exact ⟨tableCode_injective same.1, same.2⟩

theorem sortOn_eq_of_membership {α β : Type} [DecidableEq α] [Ord β]
    [Std.TransOrd β] [Std.LawfulEqOrd β] (key : α → β)
    (injective : ∀ {a b}, key a = key b → a = b) (left right : List α)
    (leftUnique : left.Nodup) (rightUnique : right.Nodup)
    (sameMembers : ∀ row, row ∈ left ↔ row ∈ right) : sortOn key left = sortOn key right := by
  letI : BEq α := ⟨fun a b => decide (a = b)⟩
  letI : LawfulBEq α := {
    eq_of_beq := by intro a b same; exact of_decide_eq_true same
    rfl := by intro a; exact decide_eq_true rfl }
  have permutation : left.Perm right := by
    apply List.perm_iff_count.mpr
    intro row
    simp only [leftUnique.count, rightUnique.count, sameMembers row]
  apply List.Perm.eq_of_pairwise ?_ (sortOn_ordered key left) (sortOn_ordered key right)
    ((sortOn_perm key left).trans (permutation.trans (sortOn_perm key right).symm))
  intro a b _ _ ab ba
  exact injective (Std.LawfulEqOrd.eq_of_compare (Std.OrientedCmp.isLE_antisymm ab ba))

/-- The constructed checked endpoint tuple equals the constructed projected effect tuple. -/
theorem checked_epoch_canonical_amount_delta_rows {pre post : GlobalState} {plans : List EffectPlan}
    (totals : Totals) (chain : TableChain pre plans post) (unique : EndpointKeysUnique pre post)
    (accepted : checkedEpoch i128 plans = .ok totals) :
    CanonicalEffectRows (emitRows plans totals) ∧
    (∀ row ∈ emitRows plans totals, Fits i128 row.deltaAtoms) ∧
    (∀ key, keyedSum key (encodeRows (emitRows plans totals)) = totals key) ∧
    ∀ table, checkedStateDeltaRows table (tableRows table pre) (tableRows table post) =
      .ok (projectDeltaRows table (emitRows plans totals)) := by
  refine ⟨emitted_rows_canonical plans totals, emitted_rows_bounded plans totals accepted,
    emitted_complete_sums plans totals accepted, ?_⟩
  intro table
  rw [checkedStateDeltaRows, checkDeltaRows_of_bounded _
    (endpoint_rows_bounded totals chain unique accepted table)]
  change Except.ok (sortOn deltaWire _) = Except.ok (sortOn deltaWire _)
  congr 1
  exact sortOn_eq_of_membership deltaWire (fun same => deltaWire_injective same) _ _
    ((endpointRaw_nodup table _ _).filter _) (projectRaw_nodup table plans totals)
    (endpoint_projected_membership totals chain unique accepted table)

end Proofs.CanonicalEpochEconomicRowsV1
