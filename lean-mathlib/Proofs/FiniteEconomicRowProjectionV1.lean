import Proofs.CheckedSignedDeltaRefinementV1

/-!
Finite economic rows retain the complete (asset, owner, custody-domain) key.
Accepted rows have unique keys and positive u128 amounts. Projection acceptance
also checks domain separation, named supply coverage and per-asset totals.
The finite-key accounting theorem derives totals from rows and lookup; its
enumeration must contain every row key exactly once (extra absent keys are safe).

This is an executable mathematical row model. String/token decoding, row-count
limits, canonical sorting/bytes, source/compiler refinement, roots, receipts,
actual custody control and publication authority are separate obligations.
-/
namespace Proofs.FiniteEconomicRowProjectionV1

namespace D
export Proofs.CheckedSignedDeltaRefinementV1 (Holding checkedSignedDelta
  exactDifference representable success_iff_exact_representable
  rejection_iff_out_of_range unchanged_holdings_accept_zero)
end D

structure Key where
  asset : String
  owner : String
  custodyDomain : String
  deriving DecidableEq, Repr

structure Row where
  key : Key
  atoms : Nat
  deriving DecidableEq, Repr

def ValidRows (rows : List Row) : Prop :=
  (rows.map Row.key).Nodup ∧ ∀ row ∈ rows, 0 < row.atoms ∧ row.atoms < 2 ^ 128

instance (rows : List Row) : Decidable (ValidRows rows) :=
  inferInstanceAs (Decidable (_ ∧ _))

def checkRows (rows : List Row) : Bool := decide (ValidRows rows)

def sumOver {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + sumOver f xs

def lookupAtoms (key : Key) : List Row → Nat
  | [] => 0
  | row :: rows => if row.key = key then row.atoms else lookupAtoms key rows

def aggregateAtoms (key : Key) (rows : List Row) : Nat :=
  sumOver (fun row => if row.key = key then row.atoms else 0) rows

def assetTotal (asset : String) (rows : List Row) : Nat :=
  sumOver (fun row => if row.key.asset = asset then row.atoms else 0) rows

def elideZeroRows : List Row → List Row
  | [] => []
  | row :: rows =>
      if row.atoms = 0 then elideZeroRows rows else row :: elideZeroRows rows

def ProjectionValid (balances custody : List Row) (supplies : List (String × Nat)) : Prop :=
  ValidRows (balances ++ custody) ∧
  (∀ row ∈ balances, row.key.custodyDomain = "accounts") ∧
  (∀ row ∈ custody, row.key.custodyDomain ≠ "accounts") ∧
  (supplies.map Prod.fst).Nodup ∧
  (∀ supply ∈ supplies, supply.2 < 2 ^ 128) ∧
  (∀ row ∈ balances ++ custody, row.key.asset ∈ supplies.map Prod.fst) ∧
  (∀ supply ∈ supplies, assetTotal supply.1 (balances ++ custody) = supply.2)

instance (balances custody : List Row) (supplies : List (String × Nat)) :
    Decidable (ProjectionValid balances custody supplies) :=
  inferInstanceAs (Decidable (_ ∧ _))

def checkProjection (balances custody : List Row) (supplies : List (String × Nat)) : Bool :=
  decide (ProjectionValid balances custody supplies)

theorem checkRows_accepts_iff (rows : List Row) : checkRows rows = true ↔ ValidRows rows := by
  simp [checkRows]

theorem checkProjection_accepts_iff (balances custody : List Row)
    (supplies : List (String × Nat)) :
    checkProjection balances custody supplies = true ↔ ProjectionValid balances custody supplies := by
  simp [checkProjection]

theorem lookup_absent (key : Key) (rows : List Row)
    (absent : key ∉ rows.map Row.key) : lookupAtoms key rows = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simp [lookupAtoms, Ne.symm absent.1, ih absent.2]

theorem aggregate_absent (key : Key) (rows : List Row)
    (absent : key ∉ rows.map Row.key) : aggregateAtoms key rows = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simpa only [aggregateAtoms, sumOver, if_neg (Ne.symm absent.1), Nat.zero_add]
        using ih absent.2

theorem aggregate_eq_lookup (key : Key) (rows : List Row)
    (unique : (rows.map Row.key).Nodup) : aggregateAtoms key rows = lookupAtoms key rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have hu := List.nodup_cons.mp unique
      by_cases same : row.key = key
      · subst key
        simp [aggregateAtoms, sumOver, lookupAtoms,
          show sumOver (fun r => if r.key = row.key then r.atoms else 0) rows = 0 from
            aggregate_absent row.key rows hu.1]
      · simpa [aggregateAtoms, sumOver, lookupAtoms, same] using ih hu.2

theorem lookup_recovers_row {rows : List Row} (valid : ValidRows rows)
    {row : Row} (member : row ∈ rows) : lookupAtoms row.key rows = row.atoms := by
  induction rows with
  | nil => simp at member
  | cons head tail ih =>
      have hu := List.nodup_cons.mp valid.1
      rcases List.mem_cons.mp member with same | member
      · subst row
        simp [lookupAtoms]
      · have different : head.key ≠ row.key := by
          intro same
          exact hu.1 (same ▸ List.mem_map_of_mem member)
        rw [lookupAtoms, if_neg different]
        exact ih ⟨hu.2, fun r hr => valid.2 r (List.mem_cons_of_mem head hr)⟩ member

theorem lookup_bounded (key : Key) (rows : List Row) (valid : ValidRows rows) :
    lookupAtoms key rows < 2 ^ 128 := by
  by_cases present : key ∈ rows.map Row.key
  · obtain ⟨row, member, same⟩ := List.mem_map.mp present
    subst key
    rw [lookup_recovers_row valid member]
    exact (valid.2 row member).2
  · rw [lookup_absent key rows present]
    decide

theorem sumOver_add {α : Type} (f g : α → Nat) (xs : List α) :
    sumOver (fun x => f x + g x) xs = sumOver f xs + sumOver g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumOver, ih]; omega

theorem sumOver_point (key : Key) (atoms : Nat) (keys : List Key)
    (unique : keys.Nodup) :
    sumOver (fun k => if key = k then atoms else 0) keys =
      if key ∈ keys then atoms else 0 := by
  induction keys with
  | nil => simp [sumOver]
  | cons head tail ih =>
      have hu := List.nodup_cons.mp unique
      by_cases same : key = head
      · subst key
        simp [sumOver, ih hu.2, hu.1]
      · simp [sumOver, same, ih hu.2]

theorem aggregate_covered_weighted_sum (weight : Key → Nat) (rows : List Row) (keys : List Key)
    (unique : keys.Nodup) (covered : ∀ row ∈ rows, row.key ∈ keys) :
    sumOver (fun key => weight key * aggregateAtoms key rows) keys =
      sumOver (fun row => weight row.key * row.atoms) rows := by
  induction rows with
  | nil =>
      induction keys with
      | nil => rfl
      | cons key keys ih => simp_all [sumOver, aggregateAtoms]
  | cons row rows ih =>
      change sumOver (fun key =>
        weight key * ((if row.key = key then row.atoms else 0) + aggregateAtoms key rows)) keys = _
      simp only [Nat.mul_add]
      rw [sumOver_add]
      have point : (fun key => weight key * (if row.key = key then row.atoms else 0)) =
          (fun key => if row.key = key then weight row.key * row.atoms else 0) := by
        funext key
        by_cases same : row.key = key <;> simp [same]
      rw [point, sumOver_point row.key (weight row.key * row.atoms) keys unique,
        if_pos (covered row (by simp)), ih (fun r hr => covered r (by simp [hr]))]
      rfl

theorem aggregate_covered_sum (rows : List Row) (keys : List Key)
    (unique : keys.Nodup) (covered : ∀ row ∈ rows, row.key ∈ keys) :
    sumOver (fun key => aggregateAtoms key rows) keys = sumOver Row.atoms rows := by
  simpa using aggregate_covered_weighted_sum (fun _ => 1) rows keys unique covered

/-! Uniqueness is needed because the observable is first-match lookup.
Coverage and a duplicate-free enumeration prevent omission and double counting. -/
theorem finite_lookup_total (rows : List Row) (valid : ValidRows rows) (keys : List Key)
    (unique : keys.Nodup) (covered : ∀ row ∈ rows, row.key ∈ keys) :
    sumOver (fun key => lookupAtoms key rows) keys = sumOver Row.atoms rows := by
  have functions : (fun key => lookupAtoms key rows) =
      (fun key => aggregateAtoms key rows) := by
    funext key
    exact (aggregate_eq_lookup key rows valid.1).symm
  rw [functions]
  exact aggregate_covered_sum rows keys unique covered

theorem finite_lookup_assetTotal (asset : String) (rows : List Row) (valid : ValidRows rows)
    (keys : List Key) (unique : keys.Nodup) (covered : ∀ row ∈ rows, row.key ∈ keys) :
    sumOver (fun key => if key.asset = asset then lookupAtoms key rows else 0) keys =
      assetTotal asset rows := by
  have rowPoint : (fun row : Row => (if row.key.asset = asset then 1 else 0) * row.atoms) =
      (fun row => if row.key.asset = asset then row.atoms else 0) := by
    funext row
    split <;> simp_all
  have keyPoint : (fun key : Key => (if key.asset = asset then 1 else 0) * aggregateAtoms key rows) =
      (fun key => if key.asset = asset then lookupAtoms key rows else 0) := by
    funext key
    split <;> simp_all [aggregate_eq_lookup key rows valid.1]
  have h := aggregate_covered_weighted_sum
    (fun key => if key.asset = asset then 1 else 0) rows keys unique covered
  rw [keyPoint, rowPoint] at h
  exact h

theorem sumOver_perm {α : Type} (f : α → Nat) {xs ys : List α} (perm : xs.Perm ys) :
    sumOver f xs = sumOver f ys := by
  induction perm with
  | nil => rfl
  | cons x _ ih => simp [sumOver, ih]
  | swap x y xs => simp only [sumOver]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem lookup_perm (key : Key) {rows other : List Row} (valid : ValidRows rows)
    (perm : rows.Perm other) : lookupAtoms key rows = lookupAtoms key other := by
  rw [← aggregate_eq_lookup key rows valid.1,
    ← aggregate_eq_lookup key other ((perm.map Row.key).nodup valid.1)]
  exact sumOver_perm _ perm

theorem assetTotal_perm (asset : String) {rows other : List Row} (perm : rows.Perm other) :
    assetTotal asset rows = assetTotal asset other := sumOver_perm _ perm

theorem elide_preserves_sum (weight : Key → Nat) (rows : List Row) :
    sumOver (fun row => weight row.key * row.atoms) (elideZeroRows rows) =
      sumOver (fun row => weight row.key * row.atoms) rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases zero : row.atoms = 0 <;> simp [elideZeroRows, sumOver, zero, ih]

theorem elide_preserves_assetTotal (asset : String) (rows : List Row) :
    assetTotal asset (elideZeroRows rows) = assetTotal asset rows := by
  have point : (fun row : Row => (if row.key.asset = asset then 1 else 0) * row.atoms) =
      (fun row => if row.key.asset = asset then row.atoms else 0) := by
    funext row
    split <;> simp_all
  have h := elide_preserves_sum (fun key => if key.asset = asset then 1 else 0) rows
  rw [point] at h
  exact h

theorem elide_preserves_aggregate (key : Key) (rows : List Row) :
    aggregateAtoms key (elideZeroRows rows) = aggregateAtoms key rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases zero : row.atoms = 0
      · simpa [elideZeroRows, aggregateAtoms, sumOver, zero] using ih
      · simp only [elideZeroRows, if_neg zero, aggregateAtoms, sumOver] at *
        rw [ih]

theorem assetTotal_append (asset : String) (balances custody : List Row) :
    assetTotal asset (balances ++ custody) = assetTotal asset balances + assetTotal asset custody := by
  induction balances with
  | nil => simp [assetTotal, sumOver]
  | cons row rows ih => simp only [List.cons_append, assetTotal, sumOver] at *; omega

theorem accepted_projection_accounts_for_asset {balances custody : List Row}
    {supplies : List (String × Nat)} (accepted : checkProjection balances custody supplies = true)
    {supply : String × Nat} (member : supply ∈ supplies) :
    assetTotal supply.1 balances + assetTotal supply.1 custody = supply.2 := by
  have valid := (checkProjection_accepts_iff balances custody supplies).mp accepted
  rw [← assetTotal_append]
  exact valid.2.2.2.2.2.2 supply member

theorem accepted_projection_finite_lookup_supply {balances custody : List Row}
    {supplies : List (String × Nat)} (accepted : checkProjection balances custody supplies = true)
    {supply : String × Nat} (member : supply ∈ supplies) (keys : List Key)
    (unique : keys.Nodup) (covered : ∀ row ∈ balances ++ custody, row.key ∈ keys) :
    sumOver (fun key => if key.asset = supply.1 then lookupAtoms key (balances ++ custody) else 0)
      keys = supply.2 ∧ supply.2 < 2 ^ 128 := by
  have valid := (checkProjection_accepts_iff balances custody supplies).mp accepted
  rw [finite_lookup_assetTotal supply.1 (balances ++ custody) valid.1 keys unique covered]
  exact ⟨valid.2.2.2.2.2.2 supply member, valid.2.2.2.2.1 supply member⟩

def projectionKeys (balances custody : List Row) : List Key :=
  (balances ++ custody).map Row.key

/-! Construct the enumeration from admitted rows, removing caller-chosen
coverage and uniqueness premises from the per-asset supply result. -/
theorem accepted_projection_derived_lookup_supply {balances custody : List Row}
    {supplies : List (String × Nat)} (accepted : checkProjection balances custody supplies = true)
    {supply : String × Nat} (member : supply ∈ supplies) :
    sumOver (fun key => if key.asset = supply.1 then lookupAtoms key (balances ++ custody) else 0)
      (projectionKeys balances custody) = supply.2 ∧ supply.2 < 2 ^ 128 := by
  have valid := (checkProjection_accepts_iff balances custody supplies).mp accepted
  exact accepted_projection_finite_lookup_supply accepted member
    (projectionKeys balances custody) valid.1.1
    (fun _ h => List.mem_map_of_mem h)

def holdingAt (key : Key) (rows : List Row) (valid : ValidRows rows) : D.Holding :=
  ⟨lookupAtoms key rows, lookup_bounded key rows valid⟩

theorem checked_keyed_delta (key : Key) (post pre : List Row)
    (postValid : ValidRows post) (preValid : ValidRows pre) (delta : Int) :
    D.checkedSignedDelta (holdingAt key post postValid) (holdingAt key pre preValid) = .ok delta ↔
      delta = (lookupAtoms key post : Int) - (lookupAtoms key pre : Int) ∧ D.representable delta := by
  exact D.success_iff_exact_representable _ _ _

theorem checked_keyed_delta_rejects_iff (key : Key) (post pre : List Row)
    (postValid : ValidRows post) (preValid : ValidRows pre) :
    D.checkedSignedDelta (holdingAt key post postValid) (holdingAt key pre preValid) =
      .error .signedStateDeltaBounds ↔
      ¬D.representable ((lookupAtoms key post : Int) - (lookupAtoms key pre : Int)) := by
  exact D.rejection_iff_out_of_range _ _

theorem unchanged_custody_keyed_delta (key : Key) (custody : List Row) (valid : ValidRows custody) :
    D.checkedSignedDelta (holdingAt key custody valid) (holdingAt key custody valid) = .ok 0 :=
  D.unchanged_holdings_accept_zero _

/-! Enumerate every post key, then pre keys absent from post. The uniqueness
proof requires valid input rows; this construction does not repair duplicates. -/
def unionKeys (post pre : List Row) : List Key :=
  post.map Row.key ++ (pre.map Row.key).filter (fun key => decide (key ∉ post.map Row.key))

theorem unionKeys_unique_and_covers (post pre : List Row)
    (postValid : ValidRows post) (preValid : ValidRows pre) :
    (unionKeys post pre).Nodup ∧
      (∀ row ∈ post, row.key ∈ unionKeys post pre) ∧
      (∀ row ∈ pre, row.key ∈ unionKeys post pre) := by
  constructor
  · apply List.nodup_append.mpr
    exact ⟨postValid.1, List.filter_sublist.nodup preValid.1, by
      intro a ha b hb same
      have absent : b ∉ post.map Row.key := by simpa using (List.mem_filter.mp hb).2
      exact absent (same ▸ ha)⟩
  constructor
  · intro row member
    exact List.mem_append_left _ (List.mem_map_of_mem member)
  · intro row member
    by_cases present : row.key ∈ post.map Row.key
    · exact List.mem_append_left _ present
    · exact List.mem_append_right _
        (List.mem_filter.mpr ⟨List.mem_map_of_mem member, by simpa using present⟩)

def sumSigned {α : Type} (f : α → Int) : List α → Int
  | [] => 0
  | key :: keys => f key + sumSigned f keys

def assetDeltaSum (asset : String) (post pre : List Row) : Int :=
  sumSigned (fun key => if key.asset = asset then
    (lookupAtoms key post : Int) - (lookupAtoms key pre : Int) else 0) (unionKeys post pre)

theorem sumSigned_nat_difference {α : Type} (post pre : α → Nat) (keys : List α) :
    sumSigned (fun key => (post key : Int) - (pre key : Int)) keys =
      (sumOver post keys : Int) - (sumOver pre keys : Int) := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simp only [sumSigned, sumOver, Int.natCast_add, ih]; omega

/-! New and removed holdings are included through absent-key zero. No caller
enumeration, coverage premise, or total-delta premise is needed. -/
theorem assetDeltaSum_eq_total_difference (asset : String) (post pre : List Row)
    (postValid : ValidRows post) (preValid : ValidRows pre) :
    assetDeltaSum asset post pre = (assetTotal asset post : Int) - (assetTotal asset pre : Int) := by
  have support := unionKeys_unique_and_covers post pre postValid preValid
  have point : (fun key => if key.asset = asset then
      (lookupAtoms key post : Int) - (lookupAtoms key pre : Int) else 0) =
      (fun key => Int.ofNat (if key.asset = asset then lookupAtoms key post else 0) -
        Int.ofNat (if key.asset = asset then lookupAtoms key pre else 0)) := by
    funext key
    split <;> simp_all
  unfold assetDeltaSum
  rw [point]
  have folded := sumSigned_nat_difference
    (fun key : Key => if key.asset = asset then lookupAtoms key post else 0)
    (fun key : Key => if key.asset = asset then lookupAtoms key pre else 0) (unionKeys post pre)
  rw [
    finite_lookup_assetTotal asset post postValid (unionKeys post pre) support.1 support.2.1,
    finite_lookup_assetTotal asset pre preValid (unionKeys post pre) support.1 support.2.2] at folded
  exact folded

theorem conserved_assetDeltaSum_zero (asset : String) (post pre : List Row)
    (postValid : ValidRows post) (preValid : ValidRows pre)
    (conserved : assetTotal asset post = assetTotal asset pre) :
    assetDeltaSum asset post pre = 0 := by
  rw [assetDeltaSum_eq_total_difference asset post pre postValid preValid, conserved, Int.sub_self]

theorem accepted_equal_supply_delta_zero
    {postBalances postCustody preBalances preCustody : List Row}
    {postSupplies preSupplies : List (String × Nat)}
    (postAccepted : checkProjection postBalances postCustody postSupplies = true)
    (preAccepted : checkProjection preBalances preCustody preSupplies = true)
    {supply : String × Nat} (postMember : supply ∈ postSupplies) (preMember : supply ∈ preSupplies) :
    assetDeltaSum supply.1 (postBalances ++ postCustody) (preBalances ++ preCustody) = 0 := by
  have postValid := (checkProjection_accepts_iff _ _ _).mp postAccepted
  have preValid := (checkProjection_accepts_iff _ _ _).mp preAccepted
  apply conserved_assetDeltaSum_zero _ _ _ postValid.1 preValid.1
  exact (postValid.2.2.2.2.2.2 supply postMember).trans
    (preValid.2.2.2.2.2.2 supply preMember).symm

def witnessBalances : List Row :=
  [⟨⟨"A", "alice", "accounts"⟩, 10⟩, ⟨⟨"B", "alice", "accounts"⟩, 20⟩]

def witnessCustody : List Row :=
  [⟨⟨"A", "alice", "vault"⟩, 3⟩, ⟨⟨"A", "alice", "escrow"⟩, 4⟩,
   ⟨⟨"B", "bob", "vault"⟩, 5⟩]

theorem multiasset_projection_accepts :
    checkProjection witnessBalances witnessCustody [("A", 17), ("B", 25)] = true := by decide

theorem same_owner_distinct_domains_recover :
    lookupAtoms ⟨"A", "alice", "accounts"⟩ (witnessBalances ++ witnessCustody) = 10 ∧
    lookupAtoms ⟨"A", "alice", "vault"⟩ (witnessBalances ++ witnessCustody) = 3 ∧
    lookupAtoms ⟨"A", "alice", "escrow"⟩ (witnessBalances ++ witnessCustody) = 4 ∧
    lookupAtoms ⟨"B", "alice", "vault"⟩ (witnessBalances ++ witnessCustody) = 0 := by decide

theorem duplicate_key_rejects :
    checkRows (witnessBalances ++ witnessBalances) = false := by decide

theorem wrong_domain_rejects :
    checkProjection witnessBalances [⟨⟨"A", "carol", "accounts"⟩, 7⟩]
      [("A", 17), ("B", 20)] = false := by decide

theorem unnamed_asset_rejects :
    checkProjection witnessBalances witnessCustody [("A", 17)] = false := by decide

theorem shifted_asset_supply_rejects :
    checkProjection witnessBalances witnessCustody [("A", 18), ("B", 24)] = false := by decide

theorem zero_and_overflow_rows_reject :
    checkRows [⟨⟨"A", "alice", "accounts"⟩, 0⟩] = false ∧
    checkRows [⟨⟨"A", "alice", "accounts"⟩, 2 ^ 128⟩] = false := by decide

end Proofs.FiniteEconomicRowProjectionV1
