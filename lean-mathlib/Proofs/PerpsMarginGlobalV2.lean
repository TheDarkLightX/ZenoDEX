import Proofs.PerpsMarginClaimsV2

/-!
# Connected perps margin global successor (V2)

This file is an independent finite reference for `perps_margin_global_v2.py`
and `zk/perps_margin_global_v2/src/global.rs`. It composes the existing
account kernel (`PerpsMarginTransitionV1.stepMarket`) with the existing claim
episode (`PerpsMarginClaimsV2.advance`) and the shared global relation
(`GlobalEconomicStateRefinementV2.Verified`), deriving the joint
custody/account/liability/terminal outcome from those constructors.

Roots, body hashes and claim identifiers are opaque digests supplied as
parameters. No theorem assumes digest injectivity except where a hypothesis
names it explicitly. Canonical bytes, byte ceilings, token syntax, the origin
registry binding, authentication, receipts, publication and Python/Rust
source refinement are outside this model; a companion Python gate checks
finite executable correspondence only.
-/

set_option warningAsError true

namespace ZenoDEX.PerpsMarginGlobalV2

open Proofs.GlobalSettlementCoreV2
open Proofs.GlobalEconomicStateRefinementV2

/-! ## Keyed finite tables

Runtime tables are canonically sorted tuples with unique keys. The update used
here erases the key and inserts before the first larger key, which reproduces
the runtime order on sorted input. Proofs rely only on key uniqueness. -/

section Sorted

variable {α κ : Type} (key : α → κ) (lt : κ → κ → Bool)

def insertSorted (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt (key x) (key y) then x :: y :: ys else y :: insertSorted x ys

theorem mem_insertSorted (x z : α) (rows : List α) :
    z ∈ insertSorted key lt x rows ↔ z = x ∨ z ∈ rows := by
  induction rows with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    simp only [insertSorted]
    split
    · simp only [List.mem_cons]
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (h | h | h) <;> simp_all
      · rintro (h | h | h) <;> simp_all

theorem find?_insertSorted_of_none (p : α → Bool) (x : α) (rows : List α)
    (hnone : rows.find? p = none) (hx : p x = true) :
    (insertSorted key lt x rows).find? p = some x := by
  induction rows with
  | nil => simp [insertSorted, hx]
  | cons y ys ih =>
    simp only [insertSorted]
    have hy : p y = false := by
      have := List.find?_eq_none.mp hnone y (List.mem_cons_self)
      simpa using this
    have hys : ys.find? p = none := by
      apply List.find?_eq_none.mpr
      intro z hz
      exact List.find?_eq_none.mp hnone z (List.mem_cons_of_mem _ hz)
    split
    · simp [hx]
    · simp [hy, ih hys]

theorem find?_insertSorted_of_false (p : α → Bool) (x : α) (rows : List α)
    (hx : p x = false) :
    (insertSorted key lt x rows).find? p = rows.find? p := by
  induction rows with
  | nil => simp [insertSorted, hx]
  | cons y ys ih =>
    simp only [insertSorted]
    split
    · simp [hx]
    · cases hy : p y <;> simp [hy, ih]

theorem nodup_map_insertSorted {β : Type} (f : α → β) (x : α) (rows : List α)
    (hnodup : (rows.map f).Nodup) (hx : f x ∉ rows.map f) :
    ((insertSorted key lt x rows).map f).Nodup := by
  induction rows with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    rw [List.map_cons] at hnodup hx
    obtain ⟨hy, hys⟩ := List.nodup_cons.mp hnodup
    have hx1 : f x ≠ f y := fun h => hx (List.mem_cons.mpr (Or.inl h))
    have hx2 : f x ∉ ys.map f := fun h => hx (List.mem_cons.mpr (Or.inr h))
    simp only [insertSorted]
    split
    · rw [List.map_cons, List.map_cons]
      exact List.nodup_cons.mpr ⟨hx, List.nodup_cons.mpr ⟨hy, hys⟩⟩
    · rw [List.map_cons]
      refine List.nodup_cons.mpr ⟨?_, ih hys hx2⟩
      intro h
      obtain ⟨z, hz, hzk⟩ := List.mem_map.mp h
      rcases (mem_insertSorted key lt x z ys).mp hz with rfl | hz'
      · exact hx1 hzk
      · exact hy (List.mem_map.mpr ⟨z, hz', hzk⟩)

theorem nodup_insertSorted (x : α) (rows : List α) (hnodup : (rows.map key).Nodup)
    (hx : key x ∉ rows.map key) : ((insertSorted key lt x rows).map key).Nodup :=
  nodup_map_insertSorted key lt key x rows hnodup hx

theorem length_insertSorted (x : α) (rows : List α) :
    (insertSorted key lt x rows).length = rows.length + 1 := by
  induction rows with
  | nil => rfl
  | cons y ys ih =>
    simp only [insertSorted]
    split
    · rfl
    · simp [ih]

theorem sum_insertSorted (w : α → Int) (x : α) (rows : List α) :
    ((insertSorted key lt x rows).map w).sum = w x + (rows.map w).sum := by
  induction rows with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    simp only [insertSorted]
    split
    · simp
    · simp only [List.map_cons, List.sum_cons, ih]
      omega

end Sorted

section Keyed

variable {α κ : Type} [DecidableEq κ] (key : α → κ) (lt : κ → κ → Bool)

def lookupKey (k : κ) (rows : List α) : Option α :=
  rows.find? (fun r => decide (key r = k))

def eraseKey (k : κ) (rows : List α) : List α :=
  rows.filter (fun r => decide (key r ≠ k))

def putKey (x : α) (rows : List α) : List α :=
  insertSorted key lt x (eraseKey key (key x) rows)

theorem mem_eraseKey (k : κ) (z : α) (rows : List α) :
    z ∈ eraseKey key k rows ↔ z ∈ rows ∧ key z ≠ k := by
  simp [eraseKey, List.mem_filter]

theorem mem_putKey (x z : α) (rows : List α) :
    z ∈ putKey key lt x rows ↔ z = x ∨ (z ∈ rows ∧ key z ≠ key x) := by
  simp [putKey, mem_insertSorted, mem_eraseKey]

theorem lookupKey_eraseKey_self (k : κ) (rows : List α) :
    lookupKey key k (eraseKey key k rows) = none := by
  apply List.find?_eq_none.mpr
  intro z hz
  have := (mem_eraseKey key k z rows).mp hz
  simpa using this.2

theorem lookupKey_eraseKey_other (k k' : κ) (rows : List α) (h : k' ≠ k) :
    lookupKey key k' (eraseKey key k rows) = lookupKey key k' rows := by
  unfold lookupKey eraseKey
  rw [List.find?_filter]
  congr 1
  funext r
  by_cases hr : key r = k'
  · simp [hr, h]
  · simp [hr]

theorem lookupKey_putKey_self (x : α) (rows : List α) :
    lookupKey key (key x) (putKey key lt x rows) = some x := by
  unfold putKey
  apply find?_insertSorted_of_none
  · exact lookupKey_eraseKey_self key (key x) rows
  · simp

theorem lookupKey_putKey_other (x : α) (k : κ) (rows : List α) (h : k ≠ key x) :
    lookupKey key k (putKey key lt x rows) = lookupKey key k rows := by
  unfold putKey
  rw [show lookupKey key k (insertSorted key lt x (eraseKey key (key x) rows)) =
      lookupKey key k (eraseKey key (key x) rows) from
    find?_insertSorted_of_false key lt _ x _ (by simpa using Ne.symm h)]
  exact lookupKey_eraseKey_other key (key x) k rows h

theorem lookupKey_mem (k : κ) (rows : List α) (z : α) (h : lookupKey key k rows = some z) :
    z ∈ rows ∧ key z = k :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem lookupKey_eq_none (k : κ) (rows : List α) :
    lookupKey key k rows = none ↔ ∀ z ∈ rows, key z ≠ k := by
  simp [lookupKey, List.find?_eq_none]

/-- With unique keys, a member is exactly the row found at its own key. -/
theorem lookupKey_of_mem (rows : List α) (hnodup : (rows.map key).Nodup) (z : α)
    (hz : z ∈ rows) : lookupKey key (key z) rows = some z := by
  induction rows with
  | nil => cases hz
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnodup
    rcases List.mem_cons.mp hz with rfl | hz'
    · simp [lookupKey]
    · have hne : key z ≠ key y := by
        intro h
        exact hnodup.1 ⟨z, hz', h⟩
      simp only [lookupKey, List.find?_cons]
      simp [Ne.symm hne]
      exact ih hnodup.2 hz'

theorem nodup_eraseKey (k : κ) (rows : List α) (hnodup : (rows.map key).Nodup) :
    ((eraseKey key k rows).map key).Nodup :=
  List.Nodup.sublist (List.Sublist.map key List.filter_sublist) hnodup

theorem nodup_putKey (x : α) (rows : List α) (hnodup : (rows.map key).Nodup) :
    ((putKey key lt x rows).map key).Nodup := by
  apply nodup_insertSorted
  · exact nodup_eraseKey key (key x) rows hnodup
  · intro h
    obtain ⟨z, hz, hzk⟩ := List.mem_map.mp h
    exact ((mem_eraseKey key (key x) z rows).mp hz).2 hzk

theorem lookupKey_cons_self (k : κ) (y : α) (ys : List α) (hy : key y = k) :
    lookupKey key k (y :: ys) = some y := by
  simp [lookupKey, hy]

theorem lookupKey_cons_other (k : κ) (y : α) (ys : List α) (hy : key y ≠ k) :
    lookupKey key k (y :: ys) = lookupKey key k ys := by
  simp [lookupKey, hy]

theorem eraseKey_cons_self (k : κ) (y : α) (ys : List α) (hy : key y = k) :
    eraseKey key k (y :: ys) = eraseKey key k ys := by
  simp [eraseKey, hy]

theorem eraseKey_cons_other (k : κ) (y : α) (ys : List α) (hy : key y ≠ k) :
    eraseKey key k (y :: ys) = y :: eraseKey key k ys := by
  simp [eraseKey, hy]

theorem eraseKey_of_not_mem (k : κ) (rows : List α) (h : k ∉ rows.map key) :
    eraseKey key k rows = rows := by
  apply List.filter_eq_self.mpr
  intro z hz
  have : key z ≠ k := fun hzk => h (List.mem_map.mpr ⟨z, hz, hzk⟩)
  simpa using this

theorem length_eraseKey (k : κ) (rows : List α) (hnodup : (rows.map key).Nodup) :
    (eraseKey key k rows).length + (if lookupKey key k rows = none then 0 else 1) =
      rows.length := by
  induction rows with
  | nil => simp [eraseKey, lookupKey]
  | cons y ys ih =>
    rw [List.map_cons] at hnodup
    obtain ⟨hy', hys⟩ := List.nodup_cons.mp hnodup
    by_cases hy : key y = k
    · rw [eraseKey_cons_self key k y ys hy, lookupKey_cons_self key k y ys hy,
        eraseKey_of_not_mem key k ys (hy ▸ hy')]
      simp
    · rw [eraseKey_cons_other key k y ys hy, lookupKey_cons_other key k y ys hy, List.length_cons,
        List.length_cons]
      have := ih hys
      omega

theorem length_putKey (x : α) (rows : List α) (hnodup : (rows.map key).Nodup) :
    (putKey key lt x rows).length =
      rows.length + (if lookupKey key (key x) rows = none then 1 else 0) := by
  unfold putKey
  rw [length_insertSorted]
  have := length_eraseKey key (key x) rows hnodup
  split <;> simp_all <;> omega

/-- Weighted sums: erasure removes the found weight. -/
theorem sum_eraseKey (w : α → Int) (k : κ) (rows : List α)
    (hnodup : (rows.map key).Nodup) :
    ((eraseKey key k rows).map w).sum =
      (rows.map w).sum - ((lookupKey key k rows).map w).getD 0 := by
  induction rows with
  | nil => simp [eraseKey, lookupKey]
  | cons y ys ih =>
    rw [List.map_cons] at hnodup
    obtain ⟨hy', hys⟩ := List.nodup_cons.mp hnodup
    by_cases hy : key y = k
    · rw [eraseKey_cons_self key k y ys hy, lookupKey_cons_self key k y ys hy,
        eraseKey_of_not_mem key k ys (hy ▸ hy')]
      simp only [List.map_cons, List.sum_cons, Option.map_some, Option.getD_some]
      omega
    · rw [eraseKey_cons_other key k y ys hy, lookupKey_cons_other key k y ys hy, List.map_cons,
        List.sum_cons, ih hys, List.map_cons, List.sum_cons]
      omega

theorem sum_putKey (w : α → Int) (x : α) (rows : List α)
    (hnodup : (rows.map key).Nodup) :
    ((putKey key lt x rows).map w).sum =
      (rows.map w).sum + w x - ((lookupKey key (key x) rows).map w).getD 0 := by
  unfold putKey
  rw [sum_insertSorted, sum_eraseKey key w (key x) rows hnodup]
  omega

end Keyed

/-! ## Amount tables -/

abbrev AmountKey := Asset × Principal × AccountingLocation

def amountKey (row : AmountRow) : AmountKey := (row.asset, row.owner, row.custodyDomain)

def keyLt (x y : AmountKey) : Bool :=
  x.1 < y.1 || (x.1 = y.1 && (x.2.1 < y.2.1 || (x.2.1 = y.2.1 && x.2.2 < y.2.2)))

def amountLookup (rows : List AmountRow) (asset : Asset) (owner : Principal)
    (domain : AccountingLocation) : Int :=
  ((lookupKey amountKey (asset, owner, domain) rows).map (·.amountAtoms)).getD 0

/-- Selected weighted total over key coordinates; every shared projection
(`amountAt`, `amountForAsset`, `amountForAssetDomain`) has this shape. -/
def sumQ (Q : Principal → Asset → AccountingLocation → Prop)
    [∀ o a d, Decidable (Q o a d)] (rows : List AmountRow) : Int :=
  (rows.map fun r => if Q r.owner r.asset r.custodyDomain then r.amountAtoms else 0).sum

def AmountRowsUnique (rows : List AmountRow) : Prop := (rows.map amountKey).Nodup

/-- The runtime applies one signed delta to one coordinate, keeps tables
sparse and rejects any value outside u128. -/
def applyDelta (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (delta : Int) : Option (List AmountRow) :=
  if 0 ≤ amountLookup rows asset owner domain + delta ∧
      amountLookup rows asset owner domain + delta ≤ maxU128 then
    some (if amountLookup rows asset owner domain + delta = 0 then
        eraseKey amountKey (asset, owner, domain) rows
      else putKey amountKey keyLt
        ⟨owner, asset, domain, amountLookup rows asset owner domain + delta⟩ rows)
  else none

theorem amountAt_eq_sumQ (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) :
    amountAt rows owner asset domain =
      sumQ (fun o a d => o = owner ∧ a = asset ∧ d = domain) rows := rfl

theorem amountForAsset_eq_sumQ (rows : List AmountRow) (asset : Asset) :
    amountForAsset rows asset = sumQ (fun _ a _ => a = asset) rows := rfl

theorem amountForAssetDomain_eq_sumQ (rows : List AmountRow) (asset : Asset)
    (domain : AccountingLocation) :
    amountForAssetDomain rows asset domain = sumQ (fun _ a d => a = asset ∧ d = domain) rows := rfl

theorem lookup_weight (Q : Principal → Asset → AccountingLocation → Prop)
    [∀ o a d, Decidable (Q o a d)]
    (rows : List AmountRow) (asset : Asset) (owner : Principal) (domain : AccountingLocation) :
    ((lookupKey amountKey (asset, owner, domain) rows).map
        fun r => if Q r.owner r.asset r.custodyDomain then r.amountAtoms else 0).getD 0 =
      if Q owner asset domain then amountLookup rows asset owner domain else 0 := by
  unfold amountLookup
  cases h : lookupKey amountKey (asset, owner, domain) rows with
  | none => simp
  | some r =>
    have hk := (lookupKey_mem amountKey _ rows r h).2
    simp only [amountKey, Prod.mk.injEq] at hk
    obtain ⟨ha, ho, hd⟩ := hk
    subst ha ho hd
    simp

theorem applyDelta_some (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (delta : Int) (post : List AmountRow)
    (h : applyDelta rows owner asset domain delta = some post) :
    0 ≤ amountLookup rows asset owner domain + delta ∧
      amountLookup rows asset owner domain + delta ≤ maxU128 ∧
      post = (if amountLookup rows asset owner domain + delta = 0 then
        eraseKey amountKey (asset, owner, domain) rows
      else putKey amountKey keyLt ⟨owner, asset, domain,
        amountLookup rows asset owner domain + delta⟩ rows) := by
  unfold applyDelta at h
  split at h
  · rename_i hrange
    cases h
    exact ⟨hrange.1, hrange.2, rfl⟩
  · cases h

theorem applyDelta_none (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (delta : Int)
    (h : applyDelta rows owner asset domain delta = none) :
    ¬ (0 ≤ amountLookup rows asset owner domain + delta ∧
      amountLookup rows asset owner domain + delta ≤ maxU128) := by
  unfold applyDelta at h
  split at h
  · cases h
  · assumption

theorem applyDelta_available (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (delta : Int)
    (hrange : 0 ≤ amountLookup rows asset owner domain + delta ∧
      amountLookup rows asset owner domain + delta ≤ maxU128) :
    ∃ post, applyDelta rows owner asset domain delta = some post := by
  unfold applyDelta
  simp only [hrange, and_self, if_true]
  exact ⟨_, rfl⟩

theorem applyDelta_sumQ (Q : Principal → Asset → AccountingLocation → Prop)
    [∀ o a d, Decidable (Q o a d)]
    (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (delta : Int) (post : List AmountRow)
    (hunique : AmountRowsUnique rows)
    (h : applyDelta rows owner asset domain delta = some post) :
    sumQ Q post = sumQ Q rows + if Q owner asset domain then delta else 0 := by
  obtain ⟨_, _, hpost⟩ := applyDelta_some rows owner asset domain delta post h
  subst hpost
  unfold sumQ
  have hw := lookup_weight Q rows asset owner domain
  split
  · rename_i hzero
    rw [sum_eraseKey amountKey _ _ rows hunique, hw]
    by_cases hq : Q owner asset domain <;> simp only [hq, if_true, if_false] <;> omega
  · rw [sum_putKey amountKey keyLt _ _ rows hunique]
    simp only [amountKey]
    rw [hw]
    by_cases hq : Q owner asset domain <;> simp only [hq, if_true, if_false] <;> omega

theorem applyDelta_lookup_self (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (delta : Int) (post : List AmountRow)
    (h : applyDelta rows owner asset domain delta = some post) :
    amountLookup post asset owner domain = amountLookup rows asset owner domain + delta := by
  obtain ⟨_, _, hpost⟩ := applyDelta_some rows owner asset domain delta post h
  subst hpost
  split
  · rename_i hzero
    show ((lookupKey amountKey (asset, owner, domain) _).map (·.amountAtoms)).getD 0 = _
    rw [lookupKey_eraseKey_self]
    simp only [Option.map_none, Option.getD_none]
    omega
  · have hput := lookupKey_putKey_self amountKey keyLt
      (⟨owner, asset, domain, amountLookup rows asset owner domain + delta⟩ : AmountRow) rows
    simp only [amountKey] at hput
    show ((lookupKey amountKey (asset, owner, domain) _).map (·.amountAtoms)).getD 0 = _
    rw [hput]
    rfl

theorem applyDelta_lookup_other (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (delta : Int) (post : List AmountRow)
    (h : applyDelta rows owner asset domain delta = some post)
    (asset' : Asset) (owner' : Principal) (domain' : AccountingLocation)
    (hne : (asset', owner', domain') ≠ (asset, owner, domain)) :
    lookupKey amountKey (asset', owner', domain') post =
      lookupKey amountKey (asset', owner', domain') rows := by
  obtain ⟨_, _, hpost⟩ := applyDelta_some rows owner asset domain delta post h
  subst hpost
  split
  · exact lookupKey_eraseKey_other amountKey _ _ rows hne
  · exact lookupKey_putKey_other amountKey keyLt _ _ rows hne

theorem applyDelta_unique (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (delta : Int) (post : List AmountRow)
    (hunique : AmountRowsUnique rows)
    (h : applyDelta rows owner asset domain delta = some post) : AmountRowsUnique post := by
  obtain ⟨_, _, hpost⟩ := applyDelta_some rows owner asset domain delta post h
  subst hpost
  split
  · exact nodup_eraseKey amountKey _ rows hunique
  · exact nodup_putKey amountKey keyLt _ rows hunique

theorem applyDelta_mem (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (delta : Int) (post : List AmountRow)
    (h : applyDelta rows owner asset domain delta = some post) (r : AmountRow) (hr : r ∈ post) :
    (r ∈ rows ∧ amountKey r ≠ (asset, owner, domain)) ∨
      (amountKey r = (asset, owner, domain) ∧
        r.amountAtoms = amountLookup rows asset owner domain + delta) := by
  obtain ⟨_, _, hpost⟩ := applyDelta_some rows owner asset domain delta post h
  subst hpost
  split at hr
  · exact Or.inl ((mem_eraseKey amountKey _ r rows).mp hr)
  · rcases (mem_putKey amountKey keyLt _ r rows).mp hr with rfl | hmem
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl hmem

theorem applyDelta_sparse (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (delta : Int) (post : List AmountRow)
    (hsparse : SparseAmountRowsAdmitted rows)
    (h : applyDelta rows owner asset domain delta = some post) :
    SparseAmountRowsAdmitted post := by
  obtain ⟨hlo, hhi, hpost⟩ := applyDelta_some rows owner asset domain delta post h
  intro r hr
  rcases applyDelta_mem rows owner asset domain delta post h r hr with ⟨hmem, _⟩ | ⟨hkey, hval⟩
  · exact hsparse r hmem
  · subst hpost
    split at hr
    · exact absurd hkey ((mem_eraseKey amountKey _ r rows).mp hr).2
    · rename_i hzero
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hval]; exact hlo
      · rw [hval]; exact hhi
      · rw [hval]; exact hzero

theorem applyDelta_length (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (delta : Int) (post : List AmountRow)
    (h : applyDelta rows owner asset domain delta = some post) :
    post.length ≤ rows.length + 1 := by
  obtain ⟨_, _, hpost⟩ := applyDelta_some rows owner asset domain delta post h
  subst hpost
  split
  · exact Nat.le_succ_of_le (List.length_filter_le _ _)
  · unfold putKey
    rw [length_insertSorted]
    exact Nat.succ_le_succ (List.length_filter_le _ _)


/-! ## Joint state

The asset lane keeps its complete supply rows; the global frame keeps only
positive supply rows. Lane rows follow the runtime's canonical twelve-lane
tuple; the margin lane keeps the existing complete market plus one active
claim binding per funded account. -/

open PerpsMarginTransitionV1 (Account Command Context Kind MarketState MarketStatus
  lookupAccount putAccount stepMarket MarketAdmitted maxAtoms maxDelta maxNonce)

namespace K
export PerpsMarginClaimsV2 (State Entry openClaim activeId install setAt EntryValid WellFormed
  OwnerPreserved advance correspondence_preserved changed_terminal_admitted
  terminal_registry_retains advance_frame drain_retains_last_amount
  refill_requires_fresh_record inactive_history_preserved advance_available)
end K

def accountsDomain : AccountingLocation := "accounts"
def marginDomain : AccountingLocation := "perps_margin"
def assetRowCeiling : Nat := 4096
def globalRowCeiling : Nat := 65536
def strLt (x y : String) : Bool := decide (x < y)

structure Policy where
  asset : Asset
  enabled : Bool
  native : Bool
  decimals : Nat
  deriving DecidableEq, Repr

structure Assets where
  releaseId : RootId
  policies : List Policy
  balances : List AmountRow
  supplies : List SupplyRow
  custody : List AmountRow
  deriving DecidableEq, Repr

structure Binding where
  accountId : Identifier
  obligationId : Identifier
  deriving DecidableEq, Repr

structure Margin where
  market : MarketState
  bindings : List Binding
  deriving DecidableEq, Repr

structure LaneRow where
  laneId : LaneId
  releaseId : RootId
  enabled : Bool
  root : RootId
  deriving DecidableEq, Repr

structure Frame where
  chainId : Identifier
  deploymentRoot : RootId
  writerEpoch : Nat
  height : Nat
  profileRoot : RootId
  lanes : List LaneRow
  balances : List AmountRow
  supplies : List SupplyRow
  custody : List AmountRow
  liabilities : List AmountRow
  reserves : List AmountRow
  oracles : List OracleOccurrence
  replay : List ReplayRecord
  terminals : TerminalRegistry
  historyRoot : RootId
  outbox : List RootId
  deriving DecidableEq, Repr

structure Joint where
  assets : Assets
  margin : Margin
  frame : Frame
  deriving DecidableEq, Repr

structure Occurrence where
  occurrenceId : RootId
  replayId : Identifier
  chainId : Identifier
  deploymentRoot : RootId
  profileRoot : RootId
  preStateRoot : RootId
  height : Nat
  subject : Principal
  commandKind : Kind
  commandBodyHash : RootId
  consumedObjectIds : List Identifier
  deriving DecidableEq, Repr

def Occurrence.shared (o : Occurrence) : CommandOccurrence :=
  ⟨o.occurrenceId, o.replayId, o.chainId, o.deploymentRoot, o.profileRoot, o.preStateRoot, o.height⟩

structure Oracle where
  price : Nat
  deriving DecidableEq, Repr

structure Request where
  command : Command
  occurrence : Occurrence
  oracle : Option Oracle
  deriving DecidableEq, Repr

/-- Opaque digests. The model never computes a hash; the companion gate feeds
the actual runtime values as finite tables. -/
structure Digests where
  assetRoot : Assets → RootId
  marginRoot : Margin → RootId
  globalRoot : Frame → RootId
  bodyHash : Command → RootId
  claimId : MarketState → Identifier → RootId → Identifier

/-! ## Views into the shared relation -/

def laneRow (frame : Frame) (lane : LaneId) : Option LaneRow :=
  frame.lanes.find? (fun row => decide (row.laneId = lane))

def replayLookup (rows : List ReplayRecord) (id : Identifier) : Option RootId :=
  (lookupKey ReplayRecord.replayId id rows).map ReplayRecord.occurrenceId

def view (d : Digests) (frame : Frame) : GlobalState where
  stateRoot := d.globalRoot frame
  chainId := frame.chainId
  deploymentRoot := frame.deploymentRoot
  writerEpoch := frame.writerEpoch
  height := frame.height
  profileRoot := frame.profileRoot
  laneRoots := fun lane => ((laneRow frame lane).map LaneRow.root).getD ""
  laneReleaseIds := fun lane => ((laneRow frame lane).map LaneRow.releaseId).getD ""
  laneEnabled := fun lane => ((laneRow frame lane).map LaneRow.enabled).getD false
  balances := frame.balances
  supplies := frame.supplies
  custody := frame.custody
  liabilities := frame.liabilities
  reserves := frame.reserves
  oracleOccurrences := fun id => lookupKey OracleOccurrence.oracleId id frame.oracles
  replayState := replayLookup frame.replay
  terminalObligations := frame.terminals
  historyRoot := frame.historyRoot
  outbox := frame.outbox

def bindingOf (bindings : List Binding) (accountId : Identifier) : Option Identifier :=
  (lookupKey Binding.accountId accountId bindings).map Binding.obligationId

/-- The claim episode's functional tables, read from the finite margin state
and the global terminal registry. -/
def claimsView (margin : Margin) (terminals : TerminalRegistry) : K.State :=
  ⟨margin.market.asset,
    fun key => (lookupAccount key margin.market.accounts).map
      fun a => ⟨a, bindingOf margin.bindings key⟩,
    fun id => terminalLookup terminals id⟩

/-! ## Projections checked by the producer -/

def positiveSupplies (rows : List SupplyRow) : List SupplyRow :=
  rows.filter (fun row => decide (row.amountAtoms ≠ 0))

def AssetProjection (d : Digests) (assets : Assets) (frame : Frame) : Prop :=
  frame.balances = assets.balances ∧ frame.custody = assets.custody ∧
    frame.supplies = positiveSupplies assets.supplies ∧ frame.reserves = [] ∧
    laneRow frame .assetTransfer = some ⟨.assetTransfer, assets.releaseId, true, d.assetRoot assets⟩

instance (d : Digests) (assets : Assets) (frame : Frame) :
    Decidable (AssetProjection d assets frame) := by
  unfold AssetProjection
  infer_instance

def ownerCollateral (accounts : List Account) (owner : Principal) : Int :=
  (accounts.map fun a => if a.owner = owner then (a.collateral : Int) else 0).sum

/-- Custody rows in the margin domain are exactly the funded accounts, owner
liabilities are the per-owner sums, and open perps claims are exactly the
bindings with matching claimant, asset, domain and amount. -/
def MarginProjection (d : Digests) (margin : Margin) (frame : Frame) : Prop :=
  laneRow frame .perpsMarket =
      some ⟨.perpsMarket, margin.market.release, true, d.marginRoot margin⟩ ∧
    (∀ a ∈ margin.market.accounts,
      amountLookup frame.custody margin.market.asset a.id marginDomain = a.collateral) ∧
    (∀ row ∈ frame.custody, row.custodyDomain = marginDomain →
      row.asset = margin.market.asset ∧ ∃ a ∈ margin.market.accounts, a.id = row.owner) ∧
    (∀ a ∈ margin.market.accounts,
      amountLookup frame.liabilities margin.market.asset a.owner marginDomain =
        ownerCollateral margin.market.accounts a.owner) ∧
    (∀ row ∈ frame.liabilities, row.custodyDomain = marginDomain →
      row.asset = margin.market.asset ∧ ∃ a ∈ margin.market.accounts, a.owner = row.owner) ∧
    (∀ row ∈ frame.terminals, row.laneId = .perpsMarket → row.status = .open →
      ∃ b ∈ margin.bindings, b.obligationId = row.obligationId) ∧
    (∀ b ∈ margin.bindings, ∃ a ∈ margin.market.accounts, a.id = b.accountId ∧
      terminalLookup frame.terminals b.obligationId =
        some (K.openClaim margin.market.asset b.obligationId a))

instance (d : Digests) (margin : Margin) (frame : Frame) :
    Decidable (MarginProjection d margin frame) := by
  unfold MarginProjection
  infer_instance

/-! ## Constructor-level admission (validated inputs, not reject codes) -/

structure MarginAdmitted (margin : Margin) : Prop where
  market : MarketAdmitted margin.market
  accountsUnique : (margin.bindings.map Binding.accountId).Nodup
  claimsUnique : (margin.bindings.map Binding.obligationId).Nodup
  coverFunded : ∀ a ∈ margin.market.accounts,
    (bindingOf margin.bindings a.id).isSome = true ↔ 0 < a.collateral
  bindingAccounts : ∀ b ∈ margin.bindings, ∃ a ∈ margin.market.accounts, a.id = b.accountId

structure FrameAdmitted (d : Digests) (frame : Frame) : Prop where
  lanes : frame.lanes.map LaneRow.laneId = allLaneIds
  replayUnique : (frame.replay.map ReplayRecord.replayId).Nodup
  quantities : StateQuantitiesAdmitted (view d frame)
  ownedSupply : OwnedMatchesSupply (view d frame)
  liabilities : ClaimantLiabilitiesBacked (view d frame)

structure Invariant (d : Digests) (state : Joint) : Prop where
  margin : MarginAdmitted state.margin
  frame : FrameAdmitted d state.frame
  assetProjection : AssetProjection d state.assets state.frame
  marginProjection : MarginProjection d state.margin state.frame

/-! ## The modeled joint step -/

inductive Reject where
  | occurrenceContextMismatch
  | replayAlreadyConsumed
  | occurrenceCommandMismatch
  | projectionMismatch
  | unknownCollateral
  | disabledCollateral
  | unsupportedCollateral
  | insufficientBalance
  | successorRejected
  | margin (code : PerpsMarginTransitionV1.Reject)
  deriving DecidableEq, Repr

structure Accepted where
  post : Joint
  effects : EffectPlan
  terminalPlan : TerminalPlan
  deriving DecidableEq, Repr

/-- Decidable outcome equality, used by the decided controls and the gate. -/
instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e, .error e' =>
    if h : e = e' then isTrue (by rw [h]) else isFalse (fun heq => h (by cases heq; rfl))
  | .ok a, .ok a' =>
    if h : a = a' then isTrue (by rw [h]) else isFalse (fun heq => h (by cases heq; rfl))
  | .error _, .ok _ => isFalse (fun h => by cases h)
  | .ok _, .error _ => isFalse (fun h => by cases h)

def replayConsumed (rows : List ReplayRecord) (o : Occurrence) : Bool :=
  rows.any fun row => decide (row.replayId = o.replayId ∨ row.occurrenceId = o.occurrenceId)

/-- Global context, replay and command binding, in runtime order. The
occurrence height is a u64 in both runtimes. -/
def contextReject (d : Digests) (frame : Frame) (o : Occurrence) : Option Reject :=
  if o.chainId ≠ frame.chainId ∨ o.deploymentRoot ≠ frame.deploymentRoot ∨
      o.profileRoot ≠ frame.profileRoot ∨ o.preStateRoot ≠ d.globalRoot frame ∨
      o.height ≠ frame.height + 1 ∨ maxU64 < o.height then
    some .occurrenceContextMismatch
  else if replayConsumed frame.replay o then some .replayAlreadyConsumed
  else none

def commandReject (d : Digests) (c : Command) (o : Occurrence) : Option Reject :=
  if o.consumedObjectIds ≠ [] ∨ o.commandKind ≠ c.kind ∨ o.commandBodyHash ≠ d.bodyHash c then
    some .occurrenceCommandMismatch
  else none

def collateralReject (assets : Assets) (asset : Asset) : Option Reject :=
  match assets.policies.find? (fun policy => decide (policy.asset = asset)) with
  | none => some .unknownCollateral
  | some policy =>
    if policy.enabled = false then some .disabledCollateral
    else if policy.native = true ∨ policy.decimals ≠ 8 then some .unsupportedCollateral
    else none

def economicContext (pre : Joint) (r : Request) : Context :=
  ⟨pre.margin.market.release, r.occurrence.subject, r.oracle.isSome,
    (r.oracle.map Oracle.price).getD 0⟩

def commandDelta (c : Command) : Int :=
  match c.kind with
  | .deposit => c.amount
  | .withdraw => -(c.amount : Int)
  | _ => 0

def effectRows (c : Command) : List EconomicEffectRow :=
  match c.kind with
  | .deposit | .withdraw =>
    [⟨.accountMovement, c.owner, c.asset, accountsDomain, -commandDelta c⟩,
      ⟨.custody, c.accountId, c.asset, marginDomain, commandDelta c⟩,
      ⟨.liability, c.owner, c.asset, marginDomain, commandDelta c⟩]
  | _ => []

structure Tables where
  balances : List AmountRow
  custody : List AmountRow
  liabilities : List AmountRow
  deriving DecidableEq, Repr

def preTables (frame : Frame) : Tables := ⟨frame.balances, frame.custody, frame.liabilities⟩

/-- Apply the three effect rows to the physical and claimant tables. -/
def successorTables (frame : Frame) (c : Command) : Option Tables :=
  match c.kind with
  | .deposit | .withdraw =>
    match applyDelta frame.balances c.owner c.asset accountsDomain (-commandDelta c) with
    | none => none
    | some balances =>
      match applyDelta frame.custody c.accountId c.asset marginDomain (commandDelta c) with
      | none => none
      | some custody =>
        match applyDelta frame.liabilities c.owner c.asset marginDomain (commandDelta c) with
        | none => none
        | some liabilities => some ⟨balances, custody, liabilities⟩
  | _ => some (preTables frame)

def putTerminal (row : TerminalObligation) (terminals : TerminalRegistry) : TerminalRegistry :=
  putKey TerminalObligation.obligationId strLt row terminals

def putBinding (binding : Binding) (bindings : List Binding) : List Binding :=
  putKey Binding.accountId strLt binding bindings

/-- Finite mirror of `advance_margin_claims_v2`. -/
def advanceClaims (asset : Asset) (bindings : List Binding) (terminals : TerminalRegistry)
    (b : Account) (fresh : Identifier) : Option (List Binding × TerminalRegistry) :=
  match bindingOf bindings b.id with
  | some id =>
    match terminalLookup terminals id with
    | none => none
    | some old =>
      if b.collateral = 0 then
        some (eraseKey Binding.accountId b.id bindings,
          putTerminal { old with status := .drained } terminals)
      else some (bindings, putTerminal { old with amountAtoms := b.collateral } terminals)
  | none =>
    if b.collateral = 0 then some (bindings, terminals)
    else if terminalLookup terminals fresh = none then
      some (putBinding ⟨b.id, fresh⟩ bindings, putTerminal (K.openClaim asset fresh b) terminals)
    else none

def updateLane (d : Digests) (assets : Assets) (margin : Margin) (row : LaneRow) : LaneRow :=
  match row.laneId with
  | .assetTransfer => { row with root := d.assetRoot assets }
  | .perpsMarket => { row with root := d.marginRoot margin }
  | _ => row

def laneWrites (lanes : List LaneRow) (update : LaneRow → LaneRow) : List LaneWrite :=
  lanes.filterMap fun row =>
    if (update row).root = row.root then none else some ⟨row.laneId, row.root, (update row).root⟩

def terminalDeltas (pre post : TerminalRegistry) : List TerminalDelta :=
  post.filterMap fun row =>
    if terminalLookup pre row.obligationId = some row then none
    else some ⟨row.obligationId, terminalLookup pre row.obligationId, row⟩

def ownedTotal (frame : Frame) (asset : Asset) : Int :=
  amountForAsset frame.balances asset + amountForAsset frame.custody asset +
    amountForAsset frame.reserves asset

def conservationRows (pre post : Frame) (c : Command) : List AssetConservationRow :=
  match c.kind with
  | .deposit | .withdraw =>
    [⟨c.asset, ownedTotal pre c.asset, ownedTotal post c.asset,
      supplyFor pre.supplies c.asset, supplyFor post.supplies c.asset, 0, 0⟩]
  | _ => []

def insertReplay (o : Occurrence) (rows : List ReplayRecord) : List ReplayRecord :=
  putKey ReplayRecord.replayId strLt ⟨o.replayId, o.occurrenceId⟩ rows

/-- Runtime row ceilings that a successor can newly exceed. Canonical byte
ceilings are outside this model. -/
def WithinCeilings (state : Joint) : Prop :=
  state.frame.balances.length ≤ assetRowCeiling ∧ state.frame.custody.length ≤ assetRowCeiling ∧
    state.frame.liabilities.length ≤ globalRowCeiling ∧
    state.frame.replay.length ≤ globalRowCeiling ∧
    state.frame.terminals.length ≤ globalRowCeiling

instance (state : Joint) : Decidable (WithinCeilings state) := by
  unfold WithinCeilings
  infer_instance

def successorAssets (assets : Assets) (tables : Tables) : Assets :=
  { assets with balances := tables.balances, custody := tables.custody }

def successorFrame (d : Digests) (frame : Frame) (o : Occurrence) (assets : Assets)
    (margin : Margin) (tables : Tables) (terminals : TerminalRegistry) : Frame :=
  { frame with
    lanes := frame.lanes.map (updateLane d assets margin)
    balances := tables.balances
    custody := tables.custody
    liabilities := tables.liabilities
    replay := insertReplay o frame.replay
    terminals := terminals
    height := frame.height + 1 }

def successorPlan (d : Digests) (frame next : Frame) (c : Command) (o : Occurrence)
    (assets : Assets) (margin : Margin) : EffectPlan :=
  ⟨effectRows c, conservationRows frame next c, [],
    laneWrites frame.lanes (updateLane d assets margin), [o.occurrenceId], []⟩

def freshClaim (d : Digests) (pre : Joint) (r : Request) : Identifier :=
  d.claimId pre.margin.market r.command.accountId r.occurrence.occurrenceId

/-- The complete candidate assembled from the kernel's market, the applied
tables and the advanced claims. -/
def build (d : Digests) (pre : Joint) (r : Request) (market : MarketState) (tables : Tables)
    (bindings : List Binding) (terminals : TerminalRegistry) : Accepted :=
  let assets := successorAssets pre.assets tables
  let margin : Margin := ⟨market, bindings⟩
  let next := successorFrame d pre.frame r.occurrence assets margin tables terminals
  ⟨⟨assets, margin, next⟩, successorPlan d pre.frame next r.command r.occurrence assets margin,
    ⟨terminalDeltas pre.frame.terminals terminals⟩⟩

def successor (d : Digests) (pre : Joint) (r : Request) (market : MarketState) : Option Accepted :=
  match lookupAccount r.command.accountId market.accounts with
  | none => none
  | some b =>
    match successorTables pre.frame r.command with
    | none => none
    | some tables =>
      match advanceClaims market.asset pre.margin.bindings pre.frame.terminals b
          (freshClaim d pre r) with
      | none => none
      | some (bindings, terminals) =>
        if WithinCeilings (build d pre r market tables bindings terminals).post then
          some (build d pre r market tables bindings terminals)
        else none

/-- One joint margin command in the runtime's reject order. -/
def step (d : Digests) (pre : Joint) (r : Request) : Except Reject Accepted :=
  match contextReject d pre.frame r.occurrence with
  | some code => .error code
  | none =>
    match commandReject d r.command r.occurrence with
    | some code => .error code
    | none =>
      if AssetProjection d pre.assets pre.frame ∧ MarginProjection d pre.margin pre.frame then
        match collateralReject pre.assets pre.margin.market.asset with
        | some code => .error code
        | none =>
          match stepMarket (economicContext pre r) pre.margin.market r.command with
          | .error code => .error (.margin code)
          | .ok market =>
            if r.command.kind = .deposit ∧
                amountLookup pre.frame.balances r.command.asset r.command.owner accountsDomain <
                  r.command.amount then
              .error .insufficientBalance
            else
              match successor d pre r market with
              | none => .error .successorRejected
              | some accepted => .ok accepted
      else .error .projectionMismatch

/-- A rejected attempt returns the complete predecessor. -/
def advanceMargin (d : Digests) (pre : Joint) (r : Request) : Joint :=
  match step d pre r with
  | .error _ => pre
  | .ok accepted => accepted.post

theorem rejected_is_exact_noop (d : Digests) (pre : Joint) (r : Request) (code : Reject)
    (h : step d pre r = .error code) : advanceMargin d pre r = pre := by
  simp [advanceMargin, h]


/-! ## Decomposition of an accepted step -/

namespace T
export PerpsMarginTransitionV1 (accepted_market_materialization accepted_account_facts
  accepted_subject_owns_account accepted_exposes_guards prepared_exact
  prepared_account_owner_and_nonce post_preserves_identity_and_position deposit_exact
  withdraw_exact_and_covered close_is_flat_empty_terminal lookup_put_self lookup_put_other
  lookup_selected lookup_none mem_put put_ordered accepted_market_admitted
  accepted_market_lookup_frame closed_cannot_accept commonReject prepareAccount postAccount
  oracleReject OrderedAccounts lookup_before_head Market)
end T

theorem accepted_exposes (d : Digests) (pre : Joint) (r : Request) (acc : Accepted)
    (h : step d pre r = .ok acc) :
    contextReject d pre.frame r.occurrence = none ∧
    commandReject d r.command r.occurrence = none ∧
    AssetProjection d pre.assets pre.frame ∧ MarginProjection d pre.margin pre.frame ∧
    collateralReject pre.assets pre.margin.market.asset = none ∧
    ∃ market, stepMarket (economicContext pre r) pre.margin.market r.command = .ok market ∧
      ¬ (r.command.kind = .deposit ∧
        amountLookup pre.frame.balances r.command.asset r.command.owner accountsDomain <
          r.command.amount) ∧
      successor d pre r market = some acc := by
  unfold step at h
  cases hctx : contextReject d pre.frame r.occurrence with
  | some code => simp [hctx] at h
  | none =>
  simp only [hctx] at h
  cases hcmd : commandReject d r.command r.occurrence with
  | some code => simp [hcmd] at h
  | none =>
  simp only [hcmd] at h
  by_cases hproj : AssetProjection d pre.assets pre.frame ∧ MarginProjection d pre.margin pre.frame
  · rw [if_pos hproj] at h
    cases hcol : collateralReject pre.assets pre.margin.market.asset with
    | some code => simp [hcol] at h
    | none =>
    simp only [hcol] at h
    cases hmarket : stepMarket (economicContext pre r) pre.margin.market r.command with
    | error code => simp [hmarket] at h
    | ok market =>
    simp only [hmarket] at h
    by_cases hbal : r.command.kind = .deposit ∧
        amountLookup pre.frame.balances r.command.asset r.command.owner accountsDomain <
          r.command.amount
    · rw [if_pos hbal] at h
      cases h
    · rw [if_neg hbal] at h
      cases hsucc : successor d pre r market with
      | none => simp [hsucc] at h
      | some acc' =>
      simp only [hsucc] at h
      cases h
      exact ⟨rfl, rfl, hproj.1, hproj.2, rfl, market, rfl, hbal, hsucc⟩
  · rw [if_neg hproj] at h
    cases h

theorem successor_exposes (d : Digests) (pre : Joint) (r : Request) (market : MarketState)
    (acc : Accepted) (h : successor d pre r market = some acc) :
    ∃ b tables bindings terminals,
      lookupAccount r.command.accountId market.accounts = some b ∧
      successorTables pre.frame r.command = some tables ∧
      advanceClaims market.asset pre.margin.bindings pre.frame.terminals b (freshClaim d pre r) =
        some (bindings, terminals) ∧
      WithinCeilings (build d pre r market tables bindings terminals).post ∧
      acc = build d pre r market tables bindings terminals := by
  unfold successor at h
  cases hb : lookupAccount r.command.accountId market.accounts with
  | none => simp [hb] at h
  | some b =>
  simp only [hb] at h
  cases ht : successorTables pre.frame r.command with
  | none => simp [ht] at h
  | some tables =>
  simp only [ht] at h
  cases hc : advanceClaims market.asset pre.margin.bindings pre.frame.terminals b
      (freshClaim d pre r) with
  | none => simp [hc] at h
  | some pair =>
  obtain ⟨bindings, terminals⟩ := pair
  simp only [hc] at h
  split at h
  · rename_i hceil
    cases h
    exact ⟨b, tables, bindings, terminals, rfl, rfl, hc, hceil, rfl⟩
  · cases h

/-! ## Facts derived from the existing economic kernel -/

theorem common_guards (ctx : Context) (m : T.Market) (c : Command)
    (h : T.commonReject ctx m c = none) :
    ctx.release = m.release ∧ c.kind ≠ .unknown ∧ m.status ≠ .halted ∧
    c.market = m.id ∧ c.asset = m.asset ∧ c.owner = ctx.subject := by
  unfold T.commonReject at h
  repeat' (split at h <;> try simp_all)

theorem close_keeps_collateral (m : T.Market) (c : Command) (a b : Account) (hc : c.kind = .close)
    (h : T.postAccount m c a = .ok b) : b.collateral = a.collateral := by
  simp only [T.postAccount, hc] at h
  repeat' (split at h <;> try simp_all)
  all_goals cases h; simp_all

/-- Everything the joint proof needs from one accepted kernel step, derived
rather than assumed: ownership, subject, nonce, asset, the collateral
replacement and the amount bounds. -/
structure EconomicFacts (pre : Joint) (r : Request) (market : MarketState) (b : Account) : Prop where
  materialized : market =
    { pre.margin.market with accounts := putAccount b pre.margin.market.accounts }
  selected : lookupAccount r.command.accountId market.accounts = some b
  id : b.id = r.command.accountId
  owner : b.owner = r.command.owner
  subject : r.command.owner = r.occurrence.subject
  asset : r.command.asset = pre.margin.market.asset
  nonce : b.nonce = r.command.nonce
  nonceStep : r.command.nonce =
    ((lookupAccount r.command.accountId pre.margin.market.accounts).map Account.nonce).getD 0 + 1
  preAccount : ∀ a, lookupAccount r.command.accountId pre.margin.market.accounts = some a →
    a.owner = r.command.owner ∧ a.closed = false
  collateral : (b.collateral : Int) =
    ((lookupAccount r.command.accountId pre.margin.market.accounts).map
      fun a => (a.collateral : Int)).getD 0 + commandDelta r.command
  kind : r.command.kind = .deposit ∨ r.command.kind = .withdraw ∨ r.command.kind = .close
  movement : r.command.kind ≠ .close → 0 < r.command.amount ∧ r.command.amount ≤ maxDelta
  close : r.command.kind = .close → r.command.amount = 0 ∧ b.collateral = 0

theorem economic_facts (pre : Joint) (r : Request) (market : MarketState)
    (h : stepMarket (economicContext pre r) pre.margin.market r.command = .ok market) :
    ∃ b, EconomicFacts pre r market b := by
  obtain ⟨b, hstep, hmat⟩ := T.accepted_market_materialization _ _ _ _ h
  obtain ⟨hid, _, _⟩ := T.accepted_account_facts _ _ _ _ hstep
  obtain ⟨hown, hsubj⟩ := T.accepted_subject_owns_account _ _ _ _ _ hstep
  obtain ⟨hcommon, a0, hprep, _, hpost⟩ := T.accepted_exposes_guards _ _ _ _ _ hstep
  obtain ⟨_, hkind, _, _, hasset, _⟩ := common_guards _ _ _ hcommon
  have hexact := T.prepared_exact _ _ _ _ hprep
  obtain ⟨ha0own, ha0closed, _, hnonce⟩ := T.prepared_account_owner_and_nonce _ _ _ _ hprep
  obtain ⟨_, hbown, _, _, hbnonce⟩ := T.post_preserves_identity_and_position _ _ _ _ hpost
  have hselected : lookupAccount r.command.accountId market.accounts = some b := by
    rw [hmat]
    simpa [← hid] using T.lookup_put_self b pre.margin.market.accounts
  have ha0coll : (a0.collateral : Int) =
      ((lookupAccount r.command.accountId pre.margin.market.accounts).map
        fun a => (a.collateral : Int)).getD 0 := by
    rw [hexact]
    cases lookupAccount r.command.accountId pre.margin.market.accounts <;> simp
  have ha0nonce : a0.nonce =
      ((lookupAccount r.command.accountId pre.margin.market.accounts).map Account.nonce).getD 0 := by
    rw [hexact]
    cases lookupAccount r.command.accountId pre.margin.market.accounts <;> simp
  refine ⟨b, ⟨hmat, hselected, hid, hown, hsubj, hasset, hbnonce, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · omega
  · intro a hl
    rw [hl] at hexact
    simp only [Option.getD_some] at hexact
    subst hexact
    exact ⟨ha0own, ha0closed⟩
  · rw [← ha0coll]
    cases hk : r.command.kind with
    | deposit =>
      have := (T.deposit_exact _ _ _ _ hk hpost).1
      simp [commandDelta, hk, this]
    | withdraw =>
      have := (T.withdraw_exact_and_covered _ _ _ _ hk hpost).1
      simp only [commandDelta, hk]
      omega
    | close =>
      have := close_keeps_collateral _ _ _ _ hk hpost
      simp [commandDelta, hk, this]
    | unknown => exact absurd hk hkind
  · cases hk : r.command.kind with
    | deposit => exact Or.inl rfl
    | withdraw => exact Or.inr (Or.inl rfl)
    | close => exact Or.inr (Or.inr rfl)
    | unknown => exact absurd hk hkind
  · intro hne
    cases hk : r.command.kind with
    | deposit =>
      have := T.deposit_exact _ _ _ _ hk hpost
      exact ⟨this.2.2.1, this.2.2.2⟩
    | withdraw =>
      have := T.withdraw_exact_and_covered _ _ _ _ hk hpost
      exact ⟨this.2.1, this.2.2.1⟩
    | close => exact absurd hk hne
    | unknown => exact absurd hk hkind
  · intro hk
    have := T.close_is_flat_empty_terminal _ _ _ _ hk hpost
    exact ⟨this.2.2.2, this.2.2.1⟩

/-! ## Correspondence with the claim episode -/

theorem terminalLookup_eq (terminals : TerminalRegistry) (id : Identifier) :
    terminalLookup terminals id = lookupKey TerminalObligation.obligationId id terminals := by
  unfold terminalLookup lookupKey
  congr 1

theorem terminalLookup_putTerminal (row : TerminalObligation) (terminals : TerminalRegistry)
    (id : Identifier) :
    terminalLookup (putTerminal row terminals) id =
      if id = row.obligationId then some row else terminalLookup terminals id := by
  rw [terminalLookup_eq, terminalLookup_eq]
  unfold putTerminal
  split
  · rename_i heq
    subst heq
    exact lookupKey_putKey_self TerminalObligation.obligationId strLt row terminals
  · rename_i hne
    exact lookupKey_putKey_other TerminalObligation.obligationId strLt row id terminals hne

theorem terminalLookup_mem (terminals : TerminalRegistry) (id : Identifier)
    (row : TerminalObligation) (h : terminalLookup terminals id = some row) :
    row ∈ terminals ∧ row.obligationId = id := by
  rw [terminalLookup_eq] at h
  exact lookupKey_mem TerminalObligation.obligationId id terminals row h

theorem bindingOf_erase_self (bindings : List Binding) (id : Identifier) :
    bindingOf (eraseKey Binding.accountId id bindings) id = none := by
  simp [bindingOf, lookupKey_eraseKey_self]

theorem bindingOf_erase_other (bindings : List Binding) (id key : Identifier) (h : key ≠ id) :
    bindingOf (eraseKey Binding.accountId id bindings) key = bindingOf bindings key := by
  simp [bindingOf, lookupKey_eraseKey_other Binding.accountId id key bindings h]

theorem bindingOf_put_self (bindings : List Binding) (binding : Binding) :
    bindingOf (putBinding binding bindings) binding.accountId = some binding.obligationId := by
  simp [bindingOf, putBinding, lookupKey_putKey_self]

theorem bindingOf_put_other (bindings : List Binding) (binding : Binding) (key : Identifier)
    (h : key ≠ binding.accountId) :
    bindingOf (putBinding binding bindings) key = bindingOf bindings key := by
  simp [bindingOf, putBinding, lookupKey_putKey_other Binding.accountId strLt binding key bindings h]

/-- Under constructor admission every binding names an existing account, so the
episode's active identifier is exactly the finite binding lookup. -/
theorem activeId_claimsView (margin : Margin) (terminals : TerminalRegistry)
    (hadm : MarginAdmitted margin) (key : Identifier) :
    K.activeId (claimsView margin terminals) key = bindingOf margin.bindings key := by
  unfold K.activeId claimsView
  simp only
  cases hl : lookupAccount key margin.market.accounts with
  | some a => simp
  | none =>
    simp only [Option.map_none, Option.bind_none]
    cases hb : bindingOf margin.bindings key with
    | none => rfl
    | some id =>
      exfalso
      unfold bindingOf at hb
      cases hk : lookupKey Binding.accountId key margin.bindings with
      | none => simp [hk] at hb
      | some binding =>
        obtain ⟨hmem, hkey⟩ := lookupKey_mem Binding.accountId key margin.bindings binding hk
        obtain ⟨a, ha, haid⟩ := hadm.bindingAccounts binding hmem
        exact (T.lookup_none key margin.market.accounts).mp hl a ha (haid.trans hkey)

theorem claimsView_install (pre : Joint) (b : Account) (bindings' : List Binding)
    (terminals' : TerminalRegistry) (claim : Option Identifier)
    (target : Identifier → Option TerminalObligation)
    (hself : bindingOf bindings' b.id = claim)
    (hother : ∀ key, key ≠ b.id → bindingOf bindings' key = bindingOf pre.margin.bindings key)
    (hterm : ∀ id, terminalLookup terminals' id = target id) :
    claimsView ⟨{ pre.margin.market with accounts := putAccount b pre.margin.market.accounts },
        bindings'⟩ terminals' =
      K.install (claimsView pre.margin pre.frame.terminals) b claim target := by
  unfold claimsView K.install
  simp only
  congr 1
  · funext key
    simp only [K.setAt]
    by_cases hkey : key = b.id
    · subst hkey
      rw [T.lookup_put_self, if_pos rfl, hself]
      rfl
    · rw [T.lookup_put_other b pre.margin.market.accounts key hkey, if_neg hkey, hother key hkey]
  · funext id
    exact hterm id

/-- The finite binding/terminal update projects exactly to the proved episode. -/
theorem advanceClaims_correspond (pre : Joint) (hadm : MarginAdmitted pre.margin) (b : Account)
    (fresh : Identifier) :
    (advanceClaims pre.margin.market.asset pre.margin.bindings pre.frame.terminals b fresh).map
        (fun pair => claimsView
          ⟨{ pre.margin.market with accounts := putAccount b pre.margin.market.accounts },
            pair.1⟩ pair.2) =
      K.advance (claimsView pre.margin pre.frame.terminals) b fresh := by
  have hactive := activeId_claimsView pre.margin pre.frame.terminals hadm b.id
  unfold advanceClaims K.advance
  rw [hactive]
  cases hb : bindingOf pre.margin.bindings b.id with
  | some id =>
    simp only
    cases ht : terminalLookup pre.frame.terminals id with
    | none => simp [claimsView, ht]
    | some old =>
      have hterm : ∀ row, terminalLookup (putTerminal row pre.frame.terminals) id =
          some row → True := fun _ _ => trivial
      have hold := (terminalLookup_mem _ _ _ ht).2
      simp only [claimsView, ht]
      by_cases hz : b.collateral = 0
      · simp only [hz, if_true, Option.map_some]
        congr 1
        apply claimsView_install pre b _ _ none _
        · exact bindingOf_erase_self pre.margin.bindings b.id
        · intro key hkey
          exact bindingOf_erase_other pre.margin.bindings b.id key hkey
        · intro i
          rw [terminalLookup_putTerminal]
          simp only [K.setAt]
          simp [hold]
      · simp only [hz, if_false, Option.map_some]
        congr 1
        apply claimsView_install pre b _ _ (some id) _
        · exact hb
        · intro _ _
          rfl
        · intro i
          rw [terminalLookup_putTerminal]
          simp only [K.setAt]
          simp [hold]
  | none =>
    simp only
    by_cases hz : b.collateral = 0
    · simp only [hz, if_true, Option.map_some]
      congr 1
      apply claimsView_install pre b _ _ none _
      · exact hb
      · intro _ _
        rfl
      · intro i
        rfl
    · simp only [hz, if_false]
      by_cases hfresh : terminalLookup pre.frame.terminals fresh = none
      · simp only [claimsView, hfresh, if_true, Option.map_some]
        congr 1
        apply claimsView_install pre b _ _ (some fresh) _
        · exact bindingOf_put_self pre.margin.bindings ⟨b.id, fresh⟩
        · intro key hkey
          exact bindingOf_put_other pre.margin.bindings ⟨b.id, fresh⟩ key hkey
        · intro i
          rw [terminalLookup_putTerminal]
          simp only [K.setAt, K.openClaim]
      · simp only [claimsView, hfresh, if_false, Option.map_none]


/-! ## Physical and claimant tables -/

def IsMovement (c : Command) : Prop := c.kind = .deposit ∨ c.kind = .withdraw

theorem successorTables_movement (frame : Frame) (c : Command) (tables : Tables)
    (hk : IsMovement c) (h : successorTables frame c = some tables) :
    applyDelta frame.balances c.owner c.asset accountsDomain (-commandDelta c) =
        some tables.balances ∧
      applyDelta frame.custody c.accountId c.asset marginDomain (commandDelta c) =
        some tables.custody ∧
      applyDelta frame.liabilities c.owner c.asset marginDomain (commandDelta c) =
        some tables.liabilities := by
  unfold successorTables at h
  have reduce : ∀ (balances custody liabilities : Option (List AmountRow)),
      (match balances with
        | none => none
        | some balances =>
          match custody with
          | none => none
          | some custody =>
            match liabilities with
            | none => none
            | some liabilities => some (⟨balances, custody, liabilities⟩ : Tables)) = some tables →
      balances = some tables.balances ∧ custody = some tables.custody ∧
        liabilities = some tables.liabilities := by
    intro balances custody liabilities hm
    cases balances with
    | none => cases hm
    | some balances =>
      cases custody with
      | none => cases hm
      | some custody =>
        cases liabilities with
        | none => cases hm
        | some liabilities =>
          cases hm
          exact ⟨rfl, rfl, rfl⟩
  rcases hk with hk | hk <;> simp only [hk] at h <;> exact reduce _ _ _ h

theorem successorTables_close (frame : Frame) (c : Command) (tables : Tables)
    (hk : c.kind = .close) (h : successorTables frame c = some tables) : tables = preTables frame := by
  unfold successorTables at h
  simp only [hk, Option.some.injEq] at h
  exact h.symm

theorem commandDelta_close (c : Command) (hk : c.kind = .close) : commandDelta c = 0 := by
  simp [commandDelta, hk]

def KnownKind (c : Command) : Prop :=
  c.kind = .deposit ∨ c.kind = .withdraw ∨ c.kind = .close

theorem known_movement_or_close (c : Command) (hk : KnownKind c) : IsMovement c ∨ c.kind = .close := by
  rcases hk with hk | hk | hk
  · exact Or.inl (Or.inl hk)
  · exact Or.inl (Or.inr hk)
  · exact Or.inr hk

structure TablesUnique (tables : Tables) : Prop where
  balances : AmountRowsUnique tables.balances
  custody : AmountRowsUnique tables.custody
  liabilities : AmountRowsUnique tables.liabilities

/-- Every selected total moves by exactly the command delta at the three
addressed coordinates, for all three command families. -/
theorem tables_sumQ (Q : Principal → Asset → AccountingLocation → Prop)
    [∀ o a d, Decidable (Q o a d)] (frame : Frame) (c : Command) (tables : Tables)
    (hunique : TablesUnique (preTables frame)) (hk : KnownKind c)
    (h : successorTables frame c = some tables) :
    sumQ Q tables.balances = sumQ Q frame.balances +
        (if Q c.owner c.asset accountsDomain then -commandDelta c else 0) ∧
      sumQ Q tables.custody = sumQ Q frame.custody +
        (if Q c.accountId c.asset marginDomain then commandDelta c else 0) ∧
      sumQ Q tables.liabilities = sumQ Q frame.liabilities +
        (if Q c.owner c.asset marginDomain then commandDelta c else 0) := by
  rcases known_movement_or_close c hk with hm | hc
  · obtain ⟨hb, hcu, hl⟩ := successorTables_movement frame c tables hm h
    exact ⟨applyDelta_sumQ Q _ _ _ _ _ _ hunique.balances hb,
      applyDelta_sumQ Q _ _ _ _ _ _ hunique.custody hcu,
      applyDelta_sumQ Q _ _ _ _ _ _ hunique.liabilities hl⟩
  · have htc := successorTables_close frame c tables hc h
    subst htc
    simp [preTables, commandDelta_close c hc]

theorem tables_unique (frame : Frame) (c : Command) (tables : Tables)
    (hunique : TablesUnique (preTables frame)) (hk : KnownKind c)
    (h : successorTables frame c = some tables) : TablesUnique tables := by
  rcases known_movement_or_close c hk with hm | hc
  · obtain ⟨hb, hcu, hl⟩ := successorTables_movement frame c tables hm h
    exact ⟨applyDelta_unique _ _ _ _ _ _ hunique.balances hb,
      applyDelta_unique _ _ _ _ _ _ hunique.custody hcu,
      applyDelta_unique _ _ _ _ _ _ hunique.liabilities hl⟩
  · have htc := successorTables_close frame c tables hc h
    subst htc
    exact hunique

structure TablesSparse (tables : Tables) : Prop where
  balances : SparseAmountRowsAdmitted tables.balances
  custody : SparseAmountRowsAdmitted tables.custody
  liabilities : SparseAmountRowsAdmitted tables.liabilities

theorem tables_sparse (frame : Frame) (c : Command) (tables : Tables)
    (hsparse : TablesSparse (preTables frame)) (hk : KnownKind c)
    (h : successorTables frame c = some tables) : TablesSparse tables := by
  rcases known_movement_or_close c hk with hm | hc
  · obtain ⟨hb, hcu, hl⟩ := successorTables_movement frame c tables hm h
    exact ⟨applyDelta_sparse _ _ _ _ _ _ hsparse.balances hb,
      applyDelta_sparse _ _ _ _ _ _ hsparse.custody hcu,
      applyDelta_sparse _ _ _ _ _ _ hsparse.liabilities hl⟩
  · have htc := successorTables_close frame c tables hc h
    subst htc
    exact hsparse

theorem tables_length (frame : Frame) (c : Command) (tables : Tables) (hk : KnownKind c)
    (h : successorTables frame c = some tables) :
    tables.balances.length ≤ frame.balances.length + 1 ∧
      tables.custody.length ≤ frame.custody.length + 1 ∧
      tables.liabilities.length ≤ frame.liabilities.length + 1 := by
  rcases known_movement_or_close c hk with hm | hc
  · obtain ⟨hb, hcu, hl⟩ := successorTables_movement frame c tables hm h
    exact ⟨applyDelta_length _ _ _ _ _ _ hb, applyDelta_length _ _ _ _ _ _ hcu,
      applyDelta_length _ _ _ _ _ _ hl⟩
  · have htc := successorTables_close frame c tables hc h
    subst htc
    simp [preTables]

/-- The effect rows project to exactly the same three coordinate deltas. -/
theorem effectFor_rows (c : Command) (rest : List AssetConservationRow)
    (fees : List FeeConservationRow) (writes : List LaneWrite) (occ : List RootId)
    (outbox : List ExternalOutboxEnqueue) (hk : KnownKind c)
    (o : Principal) (a : Asset) (dm : AccountingLocation) :
    effectFor .accountMovement ⟨effectRows c, rest, fees, writes, occ, outbox⟩ o a dm =
        (if c.owner = o ∧ c.asset = a ∧ accountsDomain = dm then -commandDelta c else 0) ∧
      effectFor .custody ⟨effectRows c, rest, fees, writes, occ, outbox⟩ o a dm =
        (if c.accountId = o ∧ c.asset = a ∧ marginDomain = dm then commandDelta c else 0) ∧
      effectFor .liability ⟨effectRows c, rest, fees, writes, occ, outbox⟩ o a dm =
        (if c.owner = o ∧ c.asset = a ∧ marginDomain = dm then commandDelta c else 0) ∧
      effectFor .reserve ⟨effectRows c, rest, fees, writes, occ, outbox⟩ o a dm = 0 := by
  rcases hk with hk | hk | hk <;> simp [effectFor, effectRows, hk, commandDelta] <;>
    (refine ⟨?_, ?_, ?_⟩ <;> split <;> simp_all)

theorem issued_burned_rows (c : Command) (a : Asset) (hk : KnownKind c) :
    issuedFor a (effectRows c) = 0 ∧ burnedFor a (effectRows c) = 0 := by
  rcases hk with hk | hk | hk <;>
    simp [issuedFor, burnedFor, issueContribution, burnContribution, effectRows, hk]

theorem allocatedFee_rows (c : Command) (a : Asset) (hk : KnownKind c) :
    allocatedFeeFor a (effectRows c) = 0 := by
  rcases hk with hk | hk | hk <;> simp [allocatedFeeFor, feeAllocationContribution, effectRows, hk]

/-! ### Owned totals, domain totals and the partition bound -/

theorem sumQ_nonneg (Q : Principal → Asset → AccountingLocation → Prop)
    [∀ o a d, Decidable (Q o a d)] (rows : List AmountRow)
    (h : ∀ r ∈ rows, 0 ≤ r.amountAtoms) : 0 ≤ sumQ Q rows := by
  induction rows with
  | nil => simp [sumQ]
  | cons r rs ih =>
    have hr := h r List.mem_cons_self
    have hrs := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [sumQ, List.map_cons, List.sum_cons] at hrs ⊢
    split <;> omega

theorem sparse_nonneg (rows : List AmountRow) (h : SparseAmountRowsAdmitted rows) :
    ∀ r ∈ rows, 0 ≤ r.amountAtoms := fun r hr => (h r hr).1.1

theorem amountForAsset_cons (r : AmountRow) (rs : List AmountRow) (a : Asset) :
    amountForAsset (r :: rs) a =
      (if r.asset = a then r.amountAtoms else 0) + amountForAsset rs a := by
  simp [amountForAsset]

theorem amountForAssetDomain_cons (r : AmountRow) (rs : List AmountRow) (a : Asset)
    (dm : AccountingLocation) :
    amountForAssetDomain (r :: rs) a dm =
      (if r.asset = a ∧ r.custodyDomain = dm then r.amountAtoms else 0) +
        amountForAssetDomain rs a dm := by
  simp [amountForAssetDomain]

def outsideDomain (dm : AccountingLocation) (rows : List AmountRow) : List AmountRow :=
  rows.filter fun r => decide (r.custodyDomain ≠ dm)

theorem outsideDomain_cons (dm : AccountingLocation) (r : AmountRow) (rs : List AmountRow) :
    outsideDomain dm (r :: rs) =
      if r.custodyDomain = dm then outsideDomain dm rs else r :: outsideDomain dm rs := by
  unfold outsideDomain
  rw [List.filter_cons]
  by_cases hd : r.custodyDomain = dm <;> simp [hd]

theorem outsideDomain_length (dm : AccountingLocation) (rows : List AmountRow) :
    (outsideDomain dm rows).length ≤ rows.length :=
  List.length_filter_le _ rows

theorem mem_outsideDomain (dm : AccountingLocation) (rows : List AmountRow) (r : AmountRow)
    (h : r ∈ outsideDomain dm rows) : r ∈ rows :=
  (List.mem_filter.mp h).1

theorem amountForAsset_split (rows : List AmountRow) (a : Asset) (dm : AccountingLocation) :
    amountForAsset rows a =
      amountForAssetDomain rows a dm + amountForAsset (outsideDomain dm rows) a := by
  induction rows with
  | nil => simp [amountForAsset, amountForAssetDomain, outsideDomain]
  | cons r rs ih =>
    rw [amountForAsset_cons, amountForAssetDomain_cons, outsideDomain_cons, ih]
    by_cases hd : r.custodyDomain = dm
    · rw [if_pos hd]
      by_cases ha : r.asset = a
      · simp only [ha, hd, and_self, if_true]
        omega
      · simp only [ha, false_and, if_false]
        omega
    · rw [if_neg hd, amountForAsset_cons]
      simp only [hd, and_false, if_false]
      omega

theorem amountForAssetDomain_outside (rows : List AmountRow) (a : Asset)
    (dm dm' : AccountingLocation) :
    amountForAssetDomain (outsideDomain dm rows) a dm' =
      if dm' = dm then 0 else amountForAssetDomain rows a dm' := by
  induction rows with
  | nil => simp [amountForAssetDomain, outsideDomain]
  | cons r rs ih =>
    rw [outsideDomain_cons]
    by_cases hd : r.custodyDomain = dm
    · rw [if_pos hd, ih]
      by_cases hdd : dm' = dm
      · simp [hdd]
      · rw [if_neg hdd, if_neg hdd, amountForAssetDomain_cons]
        have : ¬ (r.asset = a ∧ r.custodyDomain = dm') := by
          intro hc
          exact hdd (hc.2.symm.trans hd)
        simp only [this, if_false]
        omega
    · rw [if_neg hd, amountForAssetDomain_cons, ih, amountForAssetDomain_cons]
      by_cases hdd : dm' = dm
      · subst hdd
        simp only [hd, and_false, if_false, if_true]
        omega
      · simp only [hdd, if_false]

theorem amountForAsset_nonneg (rows : List AmountRow) (a : Asset)
    (h : ∀ r ∈ rows, 0 ≤ r.amountAtoms) : 0 ≤ amountForAsset rows a := by
  rw [amountForAsset_eq_sumQ]
  exact sumQ_nonneg _ rows h

theorem amountForAssetDomain_nonneg (rows : List AmountRow) (a : Asset) (dm : AccountingLocation)
    (h : ∀ r ∈ rows, 0 ≤ r.amountAtoms) : 0 ≤ amountForAssetDomain rows a dm := by
  rw [amountForAssetDomain_eq_sumQ]
  exact sumQ_nonneg _ rows h

/-- Per-domain backing bounds the whole-asset total: this is how claimant
liabilities stay inside physical holdings without any per-asset guard. -/
theorem amountForAsset_le_of_domains (n : Nat) : ∀ (L C : List AmountRow) (a : Asset),
    L.length ≤ n → (∀ r ∈ C, 0 ≤ r.amountAtoms) →
    (∀ dm, amountForAssetDomain L a dm ≤ amountForAssetDomain C a dm) →
    amountForAsset L a ≤ amountForAsset C a := by
  induction n with
  | zero =>
    intro L C a hlen hC _
    cases L with
    | nil => simpa [amountForAsset] using amountForAsset_nonneg C a hC
    | cons => simp at hlen
  | succ n ih =>
    intro L C a hlen hC hdom
    cases L with
    | nil => simpa [amountForAsset] using amountForAsset_nonneg C a hC
    | cons r rs =>
      by_cases ha : r.asset = a
      · rw [amountForAsset_split (r :: rs) a r.custodyDomain,
          amountForAsset_split C a r.custodyDomain, outsideDomain_cons, if_pos rfl]
        have h1 := hdom r.custodyDomain
        have hlen' : (outsideDomain r.custodyDomain rs).length ≤ n := by
          have := outsideDomain_length r.custodyDomain rs
          simp at hlen
          omega
        have h2 := ih (outsideDomain r.custodyDomain rs) (outsideDomain r.custodyDomain C) a hlen'
          (fun x hx => hC x (mem_outsideDomain _ _ x hx)) (by
            intro dm'
            rw [amountForAssetDomain_outside, amountForAssetDomain_outside]
            by_cases hdd : dm' = r.custodyDomain
            · simp [hdd]
            · rw [if_neg hdd, if_neg hdd]
              have := hdom dm'
              rw [amountForAssetDomain_cons] at this
              have hzero : ¬ (r.asset = a ∧ r.custodyDomain = dm') := by
                intro hc
                exact hdd hc.2.symm
              rw [if_neg hzero] at this
              omega)
        omega
      · have hL : amountForAsset (r :: rs) a = amountForAsset rs a := by
          rw [amountForAsset_cons, if_neg ha]
          omega
        have hLd : ∀ dm, amountForAssetDomain (r :: rs) a dm = amountForAssetDomain rs a dm := by
          intro dm
          rw [amountForAssetDomain_cons]
          have : ¬ (r.asset = a ∧ r.custodyDomain = dm) := fun hc => ha hc.1
          rw [if_neg this]
          omega
        rw [hL]
        exact ih rs C a (by simp at hlen; omega) hC (fun dm => hLd dm ▸ hdom dm)

theorem liabilities_le_custody_total (L C : List AmountRow) (a : Asset)
    (hC : ∀ r ∈ C, 0 ≤ r.amountAtoms)
    (hdom : ∀ dm, amountForAssetDomain L a dm ≤ amountForAssetDomain C a dm) :
    amountForAsset L a ≤ amountForAsset C a :=
  amountForAsset_le_of_domains L.length L C a (Nat.le_refl _) hC hdom

/-- Balance debit equals custody credit: every owned total is conserved. -/
theorem ownedTotal_conserved (frame : Frame) (c : Command) (tables : Tables)
    (hunique : TablesUnique (preTables frame)) (hk : KnownKind c)
    (h : successorTables frame c = some tables) (a : Asset) :
    amountForAsset tables.balances a + amountForAsset tables.custody a =
      amountForAsset frame.balances a + amountForAsset frame.custody a := by
  obtain ⟨hb, hcu, _⟩ := tables_sumQ (fun _ a' _ => a' = a) frame c tables hunique hk h
  rw [amountForAsset_eq_sumQ, amountForAsset_eq_sumQ, amountForAsset_eq_sumQ,
    amountForAsset_eq_sumQ, hb, hcu]
  split <;> omega

theorem domain_totals_shift (frame : Frame) (c : Command) (tables : Tables)
    (hunique : TablesUnique (preTables frame)) (hk : KnownKind c)
    (h : successorTables frame c = some tables) (a : Asset) (dm : AccountingLocation) :
    amountForAssetDomain tables.custody a dm = amountForAssetDomain frame.custody a dm +
        (if c.asset = a ∧ marginDomain = dm then commandDelta c else 0) ∧
      amountForAssetDomain tables.liabilities a dm = amountForAssetDomain frame.liabilities a dm +
        (if c.asset = a ∧ marginDomain = dm then commandDelta c else 0) := by
  obtain ⟨_, hcu, hl⟩ := tables_sumQ (fun _ a' d' => a' = a ∧ d' = dm) frame c tables hunique hk h
  rw [amountForAssetDomain_eq_sumQ, amountForAssetDomain_eq_sumQ, amountForAssetDomain_eq_sumQ,
    amountForAssetDomain_eq_sumQ]
  exact ⟨hcu, hl⟩

theorem amountAt_shift (frame : Frame) (c : Command) (tables : Tables)
    (hunique : TablesUnique (preTables frame)) (hk : KnownKind c)
    (h : successorTables frame c = some tables) (o : Principal) (a : Asset)
    (dm : AccountingLocation) :
    amountAt tables.balances o a dm = amountAt frame.balances o a dm +
        (if c.owner = o ∧ c.asset = a ∧ accountsDomain = dm then -commandDelta c else 0) ∧
      amountAt tables.custody o a dm = amountAt frame.custody o a dm +
        (if c.accountId = o ∧ c.asset = a ∧ marginDomain = dm then commandDelta c else 0) ∧
      amountAt tables.liabilities o a dm = amountAt frame.liabilities o a dm +
        (if c.owner = o ∧ c.asset = a ∧ marginDomain = dm then commandDelta c else 0) := by
  obtain ⟨hb, hcu, hl⟩ :=
    tables_sumQ (fun o' a' d' => o' = o ∧ a' = a ∧ d' = dm) frame c tables hunique hk h
  simp only [amountAt_eq_sumQ]
  exact ⟨hb, hcu, hl⟩


/-! ## Guard extraction -/

theorem context_guards (d : Digests) (frame : Frame) (o : Occurrence)
    (h : contextReject d frame o = none) :
    o.chainId = frame.chainId ∧ o.deploymentRoot = frame.deploymentRoot ∧
      o.profileRoot = frame.profileRoot ∧ o.preStateRoot = d.globalRoot frame ∧
      o.height = frame.height + 1 ∧ o.height ≤ maxU64 ∧ replayConsumed frame.replay o = false := by
  unfold contextReject at h
  split at h
  · cases h
  · rename_i hfields
    split at h
    · cases h
    · rename_i hreplay
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by simpa using hreplay⟩
      · exact Decidable.not_not.mp fun hne => hfields (Or.inl hne)
      · exact Decidable.not_not.mp fun hne => hfields (Or.inr (Or.inl hne))
      · exact Decidable.not_not.mp fun hne => hfields (Or.inr (Or.inr (Or.inl hne)))
      · exact Decidable.not_not.mp fun hne => hfields (Or.inr (Or.inr (Or.inr (Or.inl hne))))
      · exact Decidable.not_not.mp fun hne =>
          hfields (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hne)))))
      · exact Nat.not_lt.mp fun hlt => hfields (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlt)))))

theorem command_guards (d : Digests) (c : Command) (o : Occurrence)
    (h : commandReject d c o = none) :
    o.consumedObjectIds = [] ∧ o.commandKind = c.kind ∧ o.commandBodyHash = d.bodyHash c := by
  unfold commandReject at h
  split at h
  · cases h
  · rename_i hfields
    exact ⟨Decidable.not_not.mp fun hne => hfields (Or.inl hne),
      Decidable.not_not.mp fun hne => hfields (Or.inr (Or.inl hne)),
      Decidable.not_not.mp fun hne => hfields (Or.inr (Or.inr hne))⟩

theorem replayConsumed_false (rows : List ReplayRecord) (o : Occurrence)
    (h : replayConsumed rows o = false) :
    ∀ row ∈ rows, row.replayId ≠ o.replayId ∧ row.occurrenceId ≠ o.occurrenceId := by
  intro row hrow
  constructor
  · intro heq
    have : replayConsumed rows o = true :=
      List.any_eq_true.mpr ⟨row, hrow, by simp [heq]⟩
    rw [h] at this
    cases this
  · intro heq
    have : replayConsumed rows o = true :=
      List.any_eq_true.mpr ⟨row, hrow, by simp [heq]⟩
    rw [h] at this
    cases this

/-! ## Lane rows and writes -/

theorem laneRow_eq (frame : Frame) (lane : LaneId) :
    laneRow frame lane = lookupKey LaneRow.laneId lane frame.lanes := rfl

theorem updateLane_laneId (d : Digests) (assets : Assets) (margin : Margin) (row : LaneRow) :
    (updateLane d assets margin row).laneId = row.laneId := by
  unfold updateLane
  split <;> rfl

theorem updateLane_releaseId (d : Digests) (assets : Assets) (margin : Margin) (row : LaneRow) :
    (updateLane d assets margin row).releaseId = row.releaseId := by
  unfold updateLane
  split <;> rfl

theorem updateLane_enabled (d : Digests) (assets : Assets) (margin : Margin) (row : LaneRow) :
    (updateLane d assets margin row).enabled = row.enabled := by
  unfold updateLane
  split <;> rfl

theorem updateLane_other (d : Digests) (assets : Assets) (margin : Margin) (row : LaneRow)
    (h1 : row.laneId ≠ .assetTransfer) (h2 : row.laneId ≠ .perpsMarket) :
    updateLane d assets margin row = row := by
  unfold updateLane
  split
  · rename_i heq
    exact absurd heq h1
  · rename_i heq
    exact absurd heq h2
  · rfl

theorem updateLane_asset (d : Digests) (assets : Assets) (margin : Margin) (row : LaneRow)
    (h : row.laneId = .assetTransfer) :
    updateLane d assets margin row = { row with root := d.assetRoot assets } := by
  unfold updateLane
  rw [h]

theorem updateLane_margin (d : Digests) (assets : Assets) (margin : Margin) (row : LaneRow)
    (h : row.laneId = .perpsMarket) :
    updateLane d assets margin row = { row with root := d.marginRoot margin } := by
  unfold updateLane
  rw [h]

theorem find?_map_laneId (lanes : List LaneRow) (u : LaneRow → LaneRow)
    (hu : ∀ row, (u row).laneId = row.laneId) (lane : LaneId) :
    (lanes.map u).find? (fun row => decide (row.laneId = lane)) =
      (lanes.find? (fun row => decide (row.laneId = lane))).map u := by
  induction lanes with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.find?_cons, hu]
    by_cases h : r.laneId = lane
    · simp [h]
    · simp [h, ih]

theorem laneRow_successor (d : Digests) (frame : Frame) (o : Occurrence) (assets : Assets)
    (margin : Margin) (tables : Tables) (terminals : TerminalRegistry) (lane : LaneId) :
    laneRow (successorFrame d frame o assets margin tables terminals) lane =
      (laneRow frame lane).map (updateLane d assets margin) := by
  unfold laneRow successorFrame
  exact find?_map_laneId frame.lanes _ (updateLane_laneId d assets margin) lane

theorem laneRow_complete (frame : Frame) (hl : frame.lanes.map LaneRow.laneId = allLaneIds)
    (lane : LaneId) : ∃ row, laneRow frame lane = some row ∧ row.laneId = lane := by
  have hmem : lane ∈ frame.lanes.map LaneRow.laneId := hl ▸ allLaneIds_complete lane
  obtain ⟨row, hrow, hid⟩ := List.mem_map.mp hmem
  have hnodup : (frame.lanes.map LaneRow.laneId).Nodup := hl ▸ allLaneIds_noDuplicates
  refine ⟨row, ?_, hid⟩
  rw [laneRow_eq, ← hid]
  exact lookupKey_of_mem LaneRow.laneId frame.lanes hnodup row hrow

theorem laneRow_of_mem (frame : Frame) (hl : frame.lanes.map LaneRow.laneId = allLaneIds)
    (row : LaneRow) (hrow : row ∈ frame.lanes) : laneRow frame row.laneId = some row := by
  have hnodup : (frame.lanes.map LaneRow.laneId).Nodup := hl ▸ allLaneIds_noDuplicates
  rw [laneRow_eq]
  exact lookupKey_of_mem LaneRow.laneId frame.lanes hnodup row hrow

theorem mem_laneWrites (lanes : List LaneRow) (u : LaneRow → LaneRow) (write : LaneWrite) :
    write ∈ laneWrites lanes u ↔
      ∃ row ∈ lanes, (u row).root ≠ row.root ∧ write = ⟨row.laneId, row.root, (u row).root⟩ := by
  unfold laneWrites
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨row, hrow, h⟩
    split at h
    · cases h
    · rename_i hne
      cases h
      exact ⟨row, hrow, hne, rfl⟩
  · rintro ⟨row, hrow, hne, rfl⟩
    exact ⟨row, hrow, by simp [hne]⟩

theorem laneWrites_ids_sublist (lanes : List LaneRow) (u : LaneRow → LaneRow) :
    ((laneWrites lanes u).map LaneWrite.laneId).Sublist (lanes.map LaneRow.laneId) := by
  induction lanes with
  | nil => simp [laneWrites]
  | cons r rs ih =>
    unfold laneWrites at ih ⊢
    rw [List.filterMap_cons]
    split
    · exact List.Sublist.cons _ ih
    · rename_i write hwrite
      split at hwrite
      · cases hwrite
      · cases hwrite
        exact List.Sublist.cons₂ _ ih

theorem laneWrites_length (lanes : List LaneRow) (u : LaneRow → LaneRow) :
    (laneWrites lanes u).length ≤ lanes.length :=
  List.length_filterMap_le _ lanes

/-! ## Replay rows -/

theorem replayLookup_insert (o : Occurrence) (rows : List ReplayRecord) (id : Identifier) :
    replayLookup (insertReplay o rows) id =
      if id = o.replayId then some o.occurrenceId else replayLookup rows id := by
  unfold replayLookup insertReplay
  split
  · rename_i heq
    subst heq
    rw [show lookupKey ReplayRecord.replayId o.replayId
        (putKey ReplayRecord.replayId strLt (⟨o.replayId, o.occurrenceId⟩ : ReplayRecord) rows) =
        some ⟨o.replayId, o.occurrenceId⟩ from
      lookupKey_putKey_self ReplayRecord.replayId strLt
        (⟨o.replayId, o.occurrenceId⟩ : ReplayRecord) rows]
    rfl
  · rename_i hne
    rw [lookupKey_putKey_other ReplayRecord.replayId strLt _ id rows hne]

theorem replayLookup_mem (rows : List ReplayRecord) (id : Identifier) (occ : RootId)
    (h : replayLookup rows id = some occ) : ∃ row ∈ rows, row.replayId = id ∧ row.occurrenceId = occ := by
  unfold replayLookup at h
  cases hk : lookupKey ReplayRecord.replayId id rows with
  | none => simp [hk] at h
  | some row =>
    simp only [hk, Option.map_some, Option.some.injEq] at h
    obtain ⟨hmem, hkey⟩ := lookupKey_mem ReplayRecord.replayId id rows row hk
    exact ⟨row, hmem, hkey, h⟩

theorem replayLookup_none_of_fresh (rows : List ReplayRecord) (id : Identifier)
    (h : ∀ row ∈ rows, row.replayId ≠ id) : replayLookup rows id = none := by
  unfold replayLookup
  rw [(lookupKey_eq_none ReplayRecord.replayId id rows).mpr h]
  rfl

theorem insertReplay_nodup (o : Occurrence) (rows : List ReplayRecord)
    (hnodup : (rows.map ReplayRecord.replayId).Nodup) :
    ((insertReplay o rows).map ReplayRecord.replayId).Nodup :=
  nodup_putKey ReplayRecord.replayId strLt _ rows hnodup

theorem insertReplay_length (o : Occurrence) (rows : List ReplayRecord)
    (hnodup : (rows.map ReplayRecord.replayId).Nodup) (hfresh : ∀ row ∈ rows, row.replayId ≠ o.replayId) :
    (insertReplay o rows).length = rows.length + 1 := by
  unfold insertReplay
  rw [length_putKey ReplayRecord.replayId strLt _ rows hnodup]
  rw [if_pos ((lookupKey_eq_none ReplayRecord.replayId o.replayId rows).mpr hfresh)]

/-! ## Terminal deltas -/

theorem filterMap_of_all_none {α β : Type} (f : α → Option β) (l : List α)
    (h : ∀ y ∈ l, f y = none) : l.filterMap f = [] := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    rw [List.filterMap_cons, h y List.mem_cons_self]
    exact ih fun z hz => h z (List.mem_cons_of_mem _ hz)

theorem filterMap_insertSorted_of_none {α β κ : Type} (key : α → κ) (lt : κ → κ → Bool)
    (f : α → Option β) (x : α) (l : List α) (h : ∀ y ∈ l, f y = none) :
    (insertSorted key lt x l).filterMap f = (f x).toList := by
  induction l with
  | nil =>
    simp only [insertSorted, List.filterMap_cons, List.filterMap_nil]
    cases f x <;> rfl
  | cons y ys ih =>
    have hy := h y List.mem_cons_self
    have hys : ∀ z ∈ ys, f z = none := fun z hz => h z (List.mem_cons_of_mem _ hz)
    simp only [insertSorted]
    split
    · rw [List.filterMap_cons, List.filterMap_cons, hy, filterMap_of_all_none f ys hys]
      cases f x <;> rfl
    · rw [List.filterMap_cons, hy]
      exact ih hys

theorem terminals_nodup_lookup (terminals : TerminalRegistry)
    (hnodup : (terminals.map TerminalObligation.obligationId).Nodup) (row : TerminalObligation)
    (hrow : row ∈ terminals) : terminalLookup terminals row.obligationId = some row := by
  rw [terminalLookup_eq]
  exact lookupKey_of_mem TerminalObligation.obligationId terminals hnodup row hrow

theorem terminalDeltas_self (terminals : TerminalRegistry)
    (hnodup : (terminals.map TerminalObligation.obligationId).Nodup) :
    terminalDeltas terminals terminals = [] := by
  unfold terminalDeltas
  apply filterMap_of_all_none
  intro row hrow
  simp [terminals_nodup_lookup terminals hnodup row hrow]

theorem terminalDeltas_put (pre : TerminalRegistry) (row : TerminalObligation)
    (hnodup : (pre.map TerminalObligation.obligationId).Nodup) :
    terminalDeltas pre (putTerminal row pre) =
      if terminalLookup pre row.obligationId = some row then []
      else [⟨row.obligationId, terminalLookup pre row.obligationId, row⟩] := by
  unfold terminalDeltas putTerminal putKey
  rw [filterMap_insertSorted_of_none]
  · split <;> rfl
  · intro y hy
    obtain ⟨hmem, _⟩ := (mem_eraseKey TerminalObligation.obligationId _ y pre).mp hy
    simp [terminals_nodup_lookup pre hnodup y hmem]

theorem putTerminal_nodup (row : TerminalObligation) (terminals : TerminalRegistry)
    (hnodup : (terminals.map TerminalObligation.obligationId).Nodup) :
    ((putTerminal row terminals).map TerminalObligation.obligationId).Nodup :=
  nodup_putKey TerminalObligation.obligationId strLt row terminals hnodup

theorem putTerminal_length (row : TerminalObligation) (terminals : TerminalRegistry)
    (hnodup : (terminals.map TerminalObligation.obligationId).Nodup) :
    (putTerminal row terminals).length =
      terminals.length + (if terminalLookup terminals row.obligationId = none then 1 else 0) := by
  unfold putTerminal
  rw [length_putKey TerminalObligation.obligationId strLt row terminals hnodup, terminalLookup_eq]

theorem mem_putTerminal (row z : TerminalObligation) (terminals : TerminalRegistry) :
    z ∈ putTerminal row terminals ↔ z = row ∨ (z ∈ terminals ∧ z.obligationId ≠ row.obligationId) :=
  mem_putKey TerminalObligation.obligationId strLt row z terminals

/-- The four runtime outcomes of one claim update. -/
theorem advanceClaims_cases (asset : Asset) (bindings : List Binding) (terminals : TerminalRegistry)
    (b : Account) (fresh : Identifier) (bindings' : List Binding) (terminals' : TerminalRegistry)
    (h : advanceClaims asset bindings terminals b fresh = some (bindings', terminals')) :
    (∃ id old, bindingOf bindings b.id = some id ∧ terminalLookup terminals id = some old ∧
        b.collateral = 0 ∧ bindings' = eraseKey Binding.accountId b.id bindings ∧
        terminals' = putTerminal { old with status := .drained } terminals) ∨
      (∃ id old, bindingOf bindings b.id = some id ∧ terminalLookup terminals id = some old ∧
        b.collateral ≠ 0 ∧ bindings' = bindings ∧
        terminals' = putTerminal { old with amountAtoms := b.collateral } terminals) ∨
      (bindingOf bindings b.id = none ∧ b.collateral = 0 ∧ bindings' = bindings ∧
        terminals' = terminals) ∨
      (bindingOf bindings b.id = none ∧ b.collateral ≠ 0 ∧ terminalLookup terminals fresh = none ∧
        bindings' = putBinding ⟨b.id, fresh⟩ bindings ∧
        terminals' = putTerminal (K.openClaim asset fresh b) terminals) := by
  unfold advanceClaims at h
  cases hb : bindingOf bindings b.id with
  | some id =>
    simp only [hb] at h
    cases ht : terminalLookup terminals id with
    | none => simp [ht] at h
    | some old =>
      simp only [ht] at h
      by_cases hz : b.collateral = 0
      · simp only [hz, if_true, Option.some.injEq, Prod.mk.injEq] at h
        exact Or.inl ⟨id, old, rfl, ht, hz, h.1.symm, h.2.symm⟩
      · simp only [hz, if_false, Option.some.injEq, Prod.mk.injEq] at h
        exact Or.inr (Or.inl ⟨id, old, rfl, ht, hz, h.1.symm, h.2.symm⟩)
  | none =>
    simp only [hb] at h
    by_cases hz : b.collateral = 0
    · simp only [hz, if_true, Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inr (Or.inr (Or.inl ⟨rfl, hz, h.1.symm, h.2.symm⟩))
    · simp only [hz, if_false] at h
      split at h
      · rename_i hfresh
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact Or.inr (Or.inr (Or.inr ⟨rfl, hz, hfresh, h.1.symm, h.2.symm⟩))
      · cases h

/-! ## The episode premises, derived from the finite invariant -/

theorem lookupAccount_eq (id : Identifier) (accounts : List Account) :
    lookupAccount id accounts = lookupKey Account.id id accounts := by
  unfold lookupAccount lookupKey
  congr 1

theorem accounts_nodup (accounts : List Account) (h : T.OrderedAccounts accounts) :
    (accounts.map Account.id).Nodup := by
  unfold T.OrderedAccounts at h
  unfold List.Nodup
  rw [List.pairwise_map]
  exact h.imp fun {a b} (hlt : a.id < b.id) (heq : a.id = b.id) =>
    String.lt_irrefl b.id (show b.id < b.id from heq ▸ hlt)

theorem lookupAccount_of_mem (accounts : List Account) (hord : T.OrderedAccounts accounts)
    (a : Account) (ha : a ∈ accounts) : lookupAccount a.id accounts = some a := by
  rw [lookupAccount_eq]
  exact lookupKey_of_mem Account.id accounts (accounts_nodup accounts hord) a ha

theorem account_eq_of_id (accounts : List Account) (hord : T.OrderedAccounts accounts)
    (a a' : Account) (ha : a ∈ accounts) (ha' : a' ∈ accounts) (h : a.id = a'.id) : a = a' := by
  have h1 := lookupAccount_of_mem accounts hord a ha
  have h2 := lookupAccount_of_mem accounts hord a' ha'
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

theorem binding_eq_of_obligation (bindings : List Binding)
    (hnodup : (bindings.map Binding.obligationId).Nodup) (b b' : Binding) (hb : b ∈ bindings)
    (hb' : b' ∈ bindings) (h : b.obligationId = b'.obligationId) : b = b' := by
  have h1 := lookupKey_of_mem Binding.obligationId bindings hnodup b hb
  have h2 := lookupKey_of_mem Binding.obligationId bindings hnodup b' hb'
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

theorem bindingOf_some (bindings : List Binding) (key id : Identifier)
    (h : bindingOf bindings key = some id) :
    ∃ binding ∈ bindings, binding.accountId = key ∧ binding.obligationId = id := by
  unfold bindingOf at h
  cases hk : lookupKey Binding.accountId key bindings with
  | none => simp [hk] at h
  | some binding =>
    simp only [hk, Option.map_some, Option.some.injEq] at h
    obtain ⟨hmem, hkey⟩ := lookupKey_mem Binding.accountId key bindings binding hk
    exact ⟨binding, hmem, hkey, h⟩

theorem bindingOf_of_mem (bindings : List Binding) (hnodup : (bindings.map Binding.accountId).Nodup)
    (binding : Binding) (hb : binding ∈ bindings) :
    bindingOf bindings binding.accountId = some binding.obligationId := by
  unfold bindingOf
  rw [lookupKey_of_mem Binding.accountId bindings hnodup binding hb]
  rfl

theorem quantities_terminals (state : GlobalState) (h : StateQuantitiesAdmitted state) :
    ∀ obligation ∈ state.terminalObligations, TerminalObligationAdmitted obligation := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hterm, _, _⟩ := h
  exact hterm

theorem quantities_terminal_ids (state : GlobalState) (h : StateQuantitiesAdmitted state) :
    (state.terminalObligations.map fun obligation => obligation.obligationId).Nodup := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hids, _, _, _⟩ := h
  exact hids

theorem invariant_wellFormed (d : Digests) (state : Joint) (inv : Invariant d state) :
    K.WellFormed (claimsView state.margin state.frame.terminals) := by
  have hord := inv.margin.market.ordered
  obtain ⟨_, _, _, _, _, hopen, hbind⟩ := inv.marginProjection
  constructor
  · intro key entry hentry
    simp only [claimsView] at hentry
    cases hl : lookupAccount key state.margin.market.accounts with
    | none => simp [hl] at hentry
    | some a =>
      simp only [hl, Option.map_some, Option.some.injEq] at hentry
      subst hentry
      obtain ⟨hmem, hid⟩ := T.lookup_selected key _ a hl
      refine ⟨hid, ?_, ?_⟩
      · have := (inv.margin.market.accountsValid a hmem).collateralBound
        simp only [FitsU128, maxU128, maxAtoms] at *
        omega
      · cases hb : bindingOf state.margin.bindings key with
        | none =>
          have hcover := inv.margin.coverFunded a hmem
          rw [hid, hb] at hcover
          simp at hcover
          show a.collateral = 0
          omega
        | some id =>
          have hcover := inv.margin.coverFunded a hmem
          rw [hid, hb] at hcover
          simp at hcover
          show 0 < a.collateral ∧ _
          refine ⟨hcover, ?_⟩
          obtain ⟨binding, hbmem, hbkey, hbid⟩ := bindingOf_some _ _ _ hb
          obtain ⟨a', ha', haid, hterm⟩ := hbind binding hbmem
          have : a' = a := account_eq_of_id _ hord a' a ha' hmem (haid.trans (hbkey.trans hid.symm))
          subst this
          simp only [claimsView]
          rw [← hbid]
          exact hterm
  · intro left right id hleft hright
    rw [activeId_claimsView _ _ inv.margin] at hleft hright
    obtain ⟨bl, hbl, hblk, hbli⟩ := bindingOf_some _ _ _ hleft
    obtain ⟨br, hbr, hbrk, hbri⟩ := bindingOf_some _ _ _ hright
    have := binding_eq_of_obligation _ inv.margin.claimsUnique bl br hbl hbr (hbli.trans hbri.symm)
    subst this
    exact hblk.symm.trans hbrk
  · intro id row h
    exact (terminalLookup_mem _ _ _ h).2
  · intro id row h
    exact quantities_terminals _ inv.frame.quantities row (terminalLookup_mem _ _ _ h).1
  · intro id row hrow hlane hstatus
    obtain ⟨hmem, hid⟩ := terminalLookup_mem _ _ _ hrow
    obtain ⟨b, hb, hbid⟩ := hopen row hmem hlane hstatus
    obtain ⟨a, _, haid, _⟩ := hbind b hb
    refine ⟨a.id, ?_⟩
    rw [activeId_claimsView _ _ inv.margin, haid, bindingOf_of_mem _ inv.margin.accountsUnique b hb,
      hbid, hid]

theorem owner_preserved (pre : Joint) (r : Request) (market : MarketState) (b : Account)
    (f : EconomicFacts pre r market b) :
    K.OwnerPreserved (claimsView pre.margin pre.frame.terminals) b := by
  intro entry hentry
  simp only [claimsView] at hentry
  cases hl : lookupAccount b.id pre.margin.market.accounts with
  | none => simp [hl] at hentry
  | some a =>
    simp only [hl, Option.map_some, Option.some.injEq] at hentry
    subst hentry
    rw [f.id] at hl
    exact ((f.preAccount a hl).1).trans f.owner.symm

theorem replacement_fits (market : MarketState) (hadm : MarketAdmitted market) (b : Account)
    (hb : b ∈ market.accounts) : FitsU128 (b.collateral : Int) := by
  have := (hadm.accountsValid b hb).collateralBound
  simp only [FitsU128, maxU128, maxAtoms] at *
  omega


/-! ## Everything one accepted step exposes -/

structure Witness (d : Digests) (pre : Joint) (r : Request) where
  market : MarketState
  b : Account
  tables : Tables
  bindings : List Binding
  terminals : TerminalRegistry
  context : contextReject d pre.frame r.occurrence = none
  command : commandReject d r.command r.occurrence = none
  assetProjection : AssetProjection d pre.assets pre.frame
  marginProjection : MarginProjection d pre.margin pre.frame
  collateral : collateralReject pre.assets pre.margin.market.asset = none
  hmarket : stepMarket (economicContext pre r) pre.margin.market r.command = .ok market
  facts : EconomicFacts pre r market b
  hbalance : ¬ (r.command.kind = .deposit ∧
    amountLookup pre.frame.balances r.command.asset r.command.owner accountsDomain <
      r.command.amount)
  htables : successorTables pre.frame r.command = some tables
  hclaims : advanceClaims market.asset pre.margin.bindings pre.frame.terminals b
    (freshClaim d pre r) = some (bindings, terminals)
  hceil : WithinCeilings (build d pre r market tables bindings terminals).post

variable {d : Digests} {pre : Joint} {r : Request}

def Witness.assets (w : Witness d pre r) : Assets := successorAssets pre.assets w.tables
def Witness.margin (w : Witness d pre r) : Margin := ⟨w.market, w.bindings⟩
def Witness.frame (w : Witness d pre r) : Frame :=
  successorFrame d pre.frame r.occurrence w.assets w.margin w.tables w.terminals
def Witness.plan (w : Witness d pre r) : EffectPlan :=
  successorPlan d pre.frame w.frame r.command r.occurrence w.assets w.margin
def Witness.tplan (w : Witness d pre r) : TerminalPlan :=
  ⟨terminalDeltas pre.frame.terminals w.terminals⟩
def Witness.post (w : Witness d pre r) : Joint := ⟨w.assets, w.margin, w.frame⟩

theorem Witness.build_eq (w : Witness d pre r) :
    build d pre r w.market w.tables w.bindings w.terminals = ⟨w.post, w.plan, w.tplan⟩ := rfl

theorem accepted_witness (d : Digests) (pre : Joint) (r : Request) (acc : Accepted)
    (h : step d pre r = .ok acc) :
    ∃ w : Witness d pre r, acc = ⟨w.post, w.plan, w.tplan⟩ := by
  obtain ⟨hctx, hcmd, hassets, hmargin, hcol, market, hmarket, hbal, hsucc⟩ :=
    accepted_exposes d pre r acc h
  obtain ⟨b', tables, bindings, terminals, hb', htables, hclaims, hceil, hacc⟩ :=
    successor_exposes d pre r market acc hsucc
  obtain ⟨b, facts⟩ := economic_facts pre r market hmarket
  have hbb : b' = b := Option.some.inj (hb'.symm.trans facts.selected)
  subst hbb
  exact ⟨⟨market, b', tables, bindings, terminals, hctx, hcmd, hassets, hmargin, hcol, hmarket,
    facts, hbal, htables, hclaims, hceil⟩, hacc⟩

theorem Witness.kind (w : Witness d pre r) : KnownKind r.command := w.facts.kind

theorem Invariant.tablesUnique (inv : Invariant d pre) : TablesUnique (preTables pre.frame) := by
  obtain ⟨_, _, _, _, _, _, _, hnb, hnc, hnl, _, _, _, _, _, _, _⟩ := inv.frame.quantities
  exact ⟨hnb, hnc, hnl⟩

theorem Invariant.tablesSparse (inv : Invariant d pre) : TablesSparse (preTables pre.frame) := by
  obtain ⟨_, _, hsb, _, hsc, hsl, _, _, _, _, _, _, _, _, _, _, _⟩ := inv.frame.quantities
  exact ⟨hsb, hsc, hsl⟩

theorem Invariant.lanesLength (inv : Invariant d pre) : pre.frame.lanes.length = 12 := by
  have := congrArg List.length inv.frame.lanes
  simpa [allLaneIds_length] using this

theorem Witness.amount_bounds (w : Witness d pre r) :
    FitsI128 (commandDelta r.command) ∧ FitsI128 (-commandDelta r.command) := by
  rcases w.facts.kind with hk | hk | hk
  · obtain ⟨_, hle⟩ := w.facts.movement (by simp [hk])
    simp only [commandDelta, hk, FitsI128, minI128, maxI128, maxDelta] at *
    omega
  · obtain ⟨_, hle⟩ := w.facts.movement (by simp [hk])
    simp only [commandDelta, hk, FitsI128, minI128, maxI128, maxDelta] at *
    omega
  · simp [commandDelta, hk, FitsI128, minI128, maxI128]

theorem Witness.movement_delta (w : Witness d pre r) (hm : IsMovement r.command) :
    commandDelta r.command ≠ 0 := by
  rcases hm with hk | hk
  · have := (w.facts.movement (by simp [hk])).1
    simp [commandDelta, hk]
    omega
  · have := (w.facts.movement (by simp [hk])).1
    simp [commandDelta, hk]
    omega

/-! ### Fixed context and lane writes -/

theorem Witness.lanes_map (w : Witness d pre r) :
    w.frame.lanes = pre.frame.lanes.map (updateLane d w.assets w.margin) := rfl

theorem Witness.laneRow_post (w : Witness d pre r) (lane : LaneId) :
    laneRow w.frame lane = (laneRow pre.frame lane).map (updateLane d w.assets w.margin) :=
  laneRow_successor d pre.frame r.occurrence w.assets w.margin w.tables w.terminals lane

theorem Witness.fixedContext (w : Witness d pre r) :
    FixedContext (view d pre.frame) (view d w.frame) := by
  unfold FixedContext
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · funext lane
    simp only [view, w.laneRow_post]
    cases laneRow pre.frame lane <;> simp [updateLane_releaseId]
  · funext lane
    simp only [view, w.laneRow_post]
    cases laneRow pre.frame lane <;> simp [updateLane_enabled]

theorem Witness.lane_enabled (w : Witness d pre r) (inv : Invariant d pre) (row : LaneRow)
    (hrow : row ∈ pre.frame.lanes) (hlane : row.laneId = .assetTransfer ∨ row.laneId = .perpsMarket) :
    row.enabled = true := by
  have hfound := laneRow_of_mem pre.frame inv.frame.lanes row hrow
  rcases hlane with hl | hl
  · rw [hl, w.assetProjection.2.2.2.2] at hfound
    cases hfound
    rfl
  · rw [hl, w.marginProjection.1] at hfound
    cases hfound
    rfl

theorem Witness.laneWrites_eq (w : Witness d pre r) :
    w.plan.laneWrites = laneWrites pre.frame.lanes (updateLane d w.assets w.margin) := rfl

theorem Witness.exactLaneWrites (w : Witness d pre r) (inv : Invariant d pre) :
    ExactLaneWrites (view d pre.frame) (view d w.frame) w.plan := by
  have hl := inv.frame.lanes
  refine ⟨?_, ?_, ?_⟩
  · intro lane
    obtain ⟨row, hrow, hid⟩ := laneRow_complete pre.frame hl lane
    have hpost := w.laneRow_post lane
    rw [hrow] at hpost
    simp only [LaneWrittenBy, view, hrow, hpost, Option.map_some, Option.getD_some,
      w.laneWrites_eq]
    constructor
    · rintro ⟨write, hwrite, hwl⟩
      obtain ⟨row', hrow', hne, rfl⟩ := (mem_laneWrites _ _ write).mp hwrite
      have hfound := laneRow_of_mem pre.frame hl row' hrow'
      simp only at hwl
      rw [hwl, hrow] at hfound
      cases hfound
      exact fun heq => hne heq.symm
    · intro hne
      obtain ⟨hmem, _⟩ := lookupKey_mem LaneRow.laneId lane pre.frame.lanes row hrow
      exact ⟨⟨row.laneId, row.root, (updateLane d w.assets w.margin row).root⟩,
        (mem_laneWrites _ _ _).mpr ⟨row, hmem, fun heq => hne heq.symm, rfl⟩, hid⟩
  · intro lane hne
    obtain ⟨row, hrow, hid⟩ := laneRow_complete pre.frame hl lane
    have hpost := w.laneRow_post lane
    rw [hrow] at hpost
    simp only [view, hrow, hpost, Option.map_some, Option.getD_some] at hne ⊢
    obtain ⟨hmem, _⟩ := lookupKey_mem LaneRow.laneId lane pre.frame.lanes row hrow
    by_cases hkind : row.laneId = .assetTransfer ∨ row.laneId = .perpsMarket
    · exact w.lane_enabled inv row hmem hkind
    · exfalso
      rw [updateLane_other d w.assets w.margin row (fun h => hkind (Or.inl h))
        (fun h => hkind (Or.inr h))] at hne
      exact hne rfl
  · intro write hwrite
    rw [w.laneWrites_eq] at hwrite
    obtain ⟨row, hrow, hne, rfl⟩ := (mem_laneWrites _ _ write).mp hwrite
    have hfound := laneRow_of_mem pre.frame hl row hrow
    have hpost := w.laneRow_post row.laneId
    rw [hfound] at hpost
    have henabled : row.enabled = true := by
      by_cases hkind : row.laneId = .assetTransfer ∨ row.laneId = .perpsMarket
      · exact w.lane_enabled inv row hrow hkind
      · exfalso
        rw [updateLane_other d w.assets w.margin row (fun h => hkind (Or.inl h))
          (fun h => hkind (Or.inr h))] at hne
        exact hne rfl
    refine ⟨?_, ?_, ?_⟩
    · show ((laneRow pre.frame row.laneId).map LaneRow.enabled).getD false = true
      rw [hfound]
      exact henabled
    · show row.root = ((laneRow pre.frame row.laneId).map LaneRow.root).getD ""
      rw [hfound]
      rfl
    · show (updateLane d w.assets w.margin row).root =
        ((laneRow w.frame row.laneId).map LaneRow.root).getD ""
      rw [hpost]
      rfl

/-! ### Physical tables -/

theorem Witness.tables_eq (w : Witness d pre r) :
    w.frame.balances = w.tables.balances ∧ w.frame.custody = w.tables.custody ∧
      w.frame.liabilities = w.tables.liabilities ∧ w.frame.reserves = pre.frame.reserves ∧
      w.frame.supplies = pre.frame.supplies := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Witness.plan_rows (w : Witness d pre r) : w.plan.rows = effectRows r.command := rfl

theorem Witness.plan_eq (w : Witness d pre r) :
    w.plan = ⟨effectRows r.command, conservationRows pre.frame w.frame r.command, [],
      laneWrites pre.frame.lanes (updateLane d w.assets w.margin), [r.occurrence.occurrenceId], []⟩ :=
  rfl

theorem Witness.effectFor (w : Witness d pre r) (o : Principal) (a : Asset)
    (dm : AccountingLocation) :
    effectFor .accountMovement w.plan o a dm =
        (if r.command.owner = o ∧ r.command.asset = a ∧ accountsDomain = dm then
          -commandDelta r.command else 0) ∧
      effectFor .custody w.plan o a dm =
        (if r.command.accountId = o ∧ r.command.asset = a ∧ marginDomain = dm then
          commandDelta r.command else 0) ∧
      effectFor .liability w.plan o a dm =
        (if r.command.owner = o ∧ r.command.asset = a ∧ marginDomain = dm then
          commandDelta r.command else 0) ∧
      effectFor .reserve w.plan o a dm = 0 :=
  effectFor_rows r.command _ _ _ _ _ w.kind o a dm

theorem Witness.exactEconomicTables (w : Witness d pre r) (inv : Invariant d pre) :
    ExactEconomicTables (view d pre.frame) (view d w.frame) w.plan := by
  have hshift := amountAt_shift pre.frame r.command w.tables inv.tablesUnique w.kind w.htables
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro o a dm
  · rw [(w.effectFor o a dm).1]
    show amountAt w.tables.balances o a dm - amountAt pre.frame.balances o a dm = _
    rw [(hshift o a dm).1]
    omega
  · rw [(w.effectFor o a dm).2.1]
    show amountAt w.tables.custody o a dm - amountAt pre.frame.custody o a dm = _
    rw [(hshift o a dm).2.1]
    omega
  · rw [(w.effectFor o a dm).2.2.1]
    show amountAt w.tables.liabilities o a dm - amountAt pre.frame.liabilities o a dm = _
    rw [(hshift o a dm).2.2]
    omega
  · rw [(w.effectFor o a dm).2.2.2]
    show amountAt pre.frame.reserves o a dm - amountAt pre.frame.reserves o a dm = 0
    omega

theorem Witness.ownedConserved (w : Witness d pre r) (inv : Invariant d pre) (a : Asset) :
    ownedTotal w.frame a = ownedTotal pre.frame a := by
  have := ZenoDEX.PerpsMarginGlobalV2.ownedTotal_conserved pre.frame r.command w.tables
    inv.tablesUnique w.kind w.htables a
  unfold ownedTotal
  show amountForAsset w.tables.balances a + amountForAsset w.tables.custody a +
    amountForAsset pre.frame.reserves a = _
  omega

theorem ownedFor_view (d : Digests) (frame : Frame) (a : Asset) :
    ownedFor (view d frame) a = ownedTotal frame a := rfl

theorem Witness.exactSupplyEffects (w : Witness d pre r) :
    ExactSupplyEffects (view d pre.frame) (view d w.frame) w.plan := by
  intro a
  have := issued_burned_rows r.command a w.kind
  show supplyFor pre.frame.supplies a - supplyFor pre.frame.supplies a =
    issuedFor a (effectRows r.command) - burnedFor a (effectRows r.command)
  rw [this.1, this.2]
  omega

theorem Witness.ownedSupplyPost (w : Witness d pre r) (inv : Invariant d pre) :
    OwnedMatchesSupply (view d w.frame) := by
  intro a
  rw [ownedFor_view, w.ownedConserved inv a, ← ownedFor_view]
  exact inv.frame.ownedSupply a

theorem Witness.conservationRows_eq (w : Witness d pre r) :
    w.plan.assetConservation = conservationRows pre.frame w.frame r.command := rfl

theorem Witness.conservationRowsMatch (w : Witness d pre r) :
    ConservationRowsMatchState (view d pre.frame) (view d w.frame) w.plan := by
  intro row hrow
  rw [w.conservationRows_eq] at hrow
  rcases w.kind with hk | hk | hk <;> simp [conservationRows, hk] at hrow
  · subst hrow
    exact ⟨rfl, rfl, rfl, rfl⟩
  · subst hrow
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem Witness.effectRows_asset (w : Witness d pre r) (row : EconomicEffectRow)
    (hrow : row ∈ effectRows r.command) : row.asset = r.command.asset := by
  rcases w.kind with hk | hk | hk <;> simp [effectRows, hk] at hrow <;>
    rcases hrow with rfl | rfl | rfl <;> rfl

theorem Witness.conservationCoverage (w : Witness d pre r) (inv : Invariant d pre) :
    ExactConservationCoverage (view d pre.frame) (view d w.frame) w.plan := by
  intro a
  have hshift := amountAt_shift pre.frame r.command w.tables inv.tablesUnique w.kind w.htables
  rw [w.conservationRows_eq]
  rcases known_movement_or_close r.command w.kind with hm | hc
  · have hrows : conservationRows pre.frame w.frame r.command =
        [⟨r.command.asset, ownedTotal pre.frame r.command.asset, ownedTotal w.frame r.command.asset,
          supplyFor pre.frame.supplies r.command.asset, supplyFor w.frame.supplies r.command.asset,
          0, 0⟩] := by
      rcases hm with hk | hk <;> simp [conservationRows, hk]
    rw [hrows]
    constructor
    · intro ⟨row, hrow, ha⟩
      simp only [List.mem_singleton] at hrow
      subst hrow
      simp only at ha
      subst ha
      refine Or.inl ⟨⟨.accountMovement, r.command.owner, r.command.asset, accountsDomain,
        -commandDelta r.command⟩, ?_, rfl⟩
      rcases hm with hk | hk <;> simp [Witness.plan, successorPlan, effectRows, hk]
    · intro touched
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rcases touched with ⟨row, hrow, ha⟩ | ⟨row, hrow, _⟩ | ⟨o, dm, hne⟩ | ⟨o, dm, hne⟩ |
        ⟨o, dm, hne⟩ | ⟨o, dm, hne⟩ | hne
      · exact (w.effectRows_asset row hrow).symm.trans ha
      · simp [Witness.plan, successorPlan] at hrow
      · show r.command.asset = a
        have := (hshift o a dm).1
        change amountAt pre.frame.balances o a dm ≠ amountAt w.tables.balances o a dm at hne
        by_cases ha : r.command.asset = a
        · exact ha
        · exfalso
          apply hne
          rw [this, if_neg (fun hc => ha hc.2.1)]
          omega
      · show r.command.asset = a
        have := (hshift o a dm).2.1
        change amountAt pre.frame.custody o a dm ≠ amountAt w.tables.custody o a dm at hne
        by_cases ha : r.command.asset = a
        · exact ha
        · exfalso
          apply hne
          rw [this, if_neg (fun hc => ha hc.2.1)]
          omega
      · show r.command.asset = a
        have := (hshift o a dm).2.2
        change amountAt pre.frame.liabilities o a dm ≠ amountAt w.tables.liabilities o a dm at hne
        by_cases ha : r.command.asset = a
        · exact ha
        · exfalso
          apply hne
          rw [this, if_neg (fun hc => ha hc.2.1)]
          omega
      · exact absurd rfl hne
      · exact absurd rfl hne
  · have htc := successorTables_close pre.frame r.command w.tables hc w.htables
    have hrows : conservationRows pre.frame w.frame r.command = [] := by simp [conservationRows, hc]
    rw [hrows]
    simp only [List.not_mem_nil, false_and, exists_false, false_iff]
    intro touched
    rcases touched with ⟨row, hrow, _⟩ | ⟨row, hrow, _⟩ | ⟨o, dm, hne⟩ | ⟨o, dm, hne⟩ |
      ⟨o, dm, hne⟩ | ⟨o, dm, hne⟩ | hne
    · simp [Witness.plan, successorPlan, effectRows, hc] at hrow
    · simp [Witness.plan, successorPlan] at hrow
    · exact hne (by
        show amountAt pre.frame.balances o a dm = amountAt w.tables.balances o a dm
        rw [htc]
        rfl)
    · exact hne (by
        show amountAt pre.frame.custody o a dm = amountAt w.tables.custody o a dm
        rw [htc]
        rfl)
    · exact hne (by
        show amountAt pre.frame.liabilities o a dm = amountAt w.tables.liabilities o a dm
        rw [htc]
        rfl)
    · exact absurd rfl hne
    · exact absurd rfl hne

/-! ### Effect plan admission and annotation mirrors -/

theorem accounts_ne_margin : accountsDomain ≠ marginDomain := by decide

theorem stateBearing_of_kind (o : Principal) (a : Asset) (dm : AccountingLocation)
    (p : Principal) (asset : Asset) (dom : AccountingLocation) (delta : Int) (k : EffectKind)
    (hk : k = .accountMovement ∨ k = .custody ∨ k = .reserve) :
    stateBearingContribution o a dm ⟨k, p, asset, dom, delta⟩ =
      if p = o ∧ asset = a ∧ dom = dm then delta else 0 := by
  unfold stateBearingContribution
  dsimp only
  by_cases h : p = o ∧ asset = a ∧ dom = dm
  · rw [if_pos ⟨h.1, h.2.1, h.2.2, hk⟩, if_pos h]
  · rw [if_neg (fun hc => h ⟨hc.1, hc.2.1, hc.2.2.1⟩), if_neg h]

theorem stateBearing_liability (o : Principal) (a : Asset) (dm : AccountingLocation)
    (p : Principal) (asset : Asset) (dom : AccountingLocation) (delta : Int) :
    stateBearingContribution o a dm ⟨.liability, p, asset, dom, delta⟩ = 0 := by
  simp [stateBearingContribution]


theorem Witness.effectPlanAdmitted (w : Witness d pre r) (inv : Invariant d pre) :
    EffectPlanAdmitted w.plan := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, htot, _, _, _, _⟩ := inv.frame.quantities
  have hbounds := w.amount_bounds
  have hconserved := w.ownedConserved inv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row hrow
    rw [w.plan_rows] at hrow
    rcases known_movement_or_close r.command w.kind with hm | hc
    · have hne := w.movement_delta hm
      rcases hm with hk | hk <;> simp [effectRows, hk] at hrow <;>
        rcases hrow with rfl | rfl | rfl <;>
        simp [EffectRowAdmitted, hbounds.1, hbounds.2] <;> simp [commandDelta, hk] at hne ⊢ <;> omega
    · simp [effectRows, hc] at hrow
  · intro row hrow
    rw [w.conservationRows_eq] at hrow
    rcases w.kind with hk | hk | hk <;> simp [conservationRows, hk] at hrow
    all_goals
      subst hrow
      have h1 := (htot r.command.asset).1
      have h3 := (htot r.command.asset).2.2
      rw [ownedFor_view] at h1
      refine ⟨h1, ?_, h3, ?_, zero_fits_u128, zero_fits_u128, ?_, ?_⟩
      · show FitsU128 (ownedTotal w.frame r.command.asset)
        rw [hconserved]
        exact h1
      · show FitsU128 (supplyFor pre.frame.supplies r.command.asset)
        exact h3
      · show ownedTotal w.frame r.command.asset = ownedTotal pre.frame r.command.asset + 0 - 0
        rw [hconserved]
        omega
      · show supplyFor pre.frame.supplies r.command.asset =
          supplyFor pre.frame.supplies r.command.asset + 0 - 0
        omega
  · intro row hrow
    simp [Witness.plan, successorPlan] at hrow
  · intro a
    have := issued_burned_rows r.command a w.kind
    rw [w.plan_rows] at *
    show declaredIssueFor a (conservationRows pre.frame w.frame r.command) = _ ∧
      declaredBurnFor a (conservationRows pre.frame w.frame r.command) = _
    rw [this.1, this.2]
    rcases w.kind with hk | hk | hk <;> simp [conservationRows, declaredIssueFor, declaredBurnFor, hk]
  · intro a
    show declaredCurrentAllocationsFor a [] = allocatedFeeFor a (effectRows r.command)
    rw [allocatedFee_rows r.command a w.kind]
    rfl
  · have hwrites := laneWrites_length pre.frame.lanes (updateLane d w.assets w.margin)
    rw [inv.lanesLength] at hwrites
    have hrows : (effectRows r.command).length ≤ 3 := by
      rcases w.kind with hk | hk | hk <;> simp [effectRows, hk]
    have hcons : (conservationRows pre.frame w.frame r.command).length ≤ 1 := by
      rcases w.kind with hk | hk | hk <;> simp [conservationRows, hk]
    show (effectRows r.command).length ≤ 4096 ∧
      (conservationRows pre.frame w.frame r.command).length ≤ 256 ∧ ([] : List FeeConservationRow).length ≤ 256 ∧
      (laneWrites pre.frame.lanes (updateLane d w.assets w.margin)).length ≤ 12 ∧
      [r.occurrence.occurrenceId].length ≤ 64 ∧ ([] : List ExternalOutboxEnqueue).length ≤ 4096 ∧
      (effectRows r.command).length + (conservationRows pre.frame w.frame r.command).length +
        ([] : List FeeConservationRow).length +
        (laneWrites pre.frame.lanes (updateLane d w.assets w.margin)).length +
        [r.occurrence.occurrenceId].length + ([] : List ExternalOutboxEnqueue).length ≤ 8192
    simp only [List.length_nil, List.length_singleton]
    omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [w.plan_rows]
      rcases w.kind with hk | hk | hk <;> simp [effectRows, hk, EconomicEffectRow.key]
    · rw [w.conservationRows_eq]
      rcases w.kind with hk | hk | hk <;> simp [conservationRows, hk]
    · simp [Witness.plan, successorPlan]
    · rw [w.laneWrites_eq]
      exact List.Nodup.sublist (laneWrites_ids_sublist _ _) (inv.frame.lanes ▸ allLaneIds_noDuplicates)
    · simp [Witness.plan, successorPlan]
    · simp [Witness.plan, successorPlan]

theorem Witness.annotations (w : Witness d pre r) : AnnotationMirrors w.plan := by
  have hbounds := w.amount_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro o a dm
    rw [w.plan_rows]
    rcases known_movement_or_close r.command w.kind with hm | hc
    · have hrows : effectRows r.command =
          [⟨.accountMovement, r.command.owner, r.command.asset, accountsDomain, -commandDelta r.command⟩,
            ⟨.custody, r.command.accountId, r.command.asset, marginDomain, commandDelta r.command⟩,
            ⟨.liability, r.command.owner, r.command.asset, marginDomain, commandDelta r.command⟩] := by
        rcases hm with hk | hk <;> simp [effectRows, hk]
      rw [hrows]
      simp only [RunningTotalsFitI128, stateBearing_liability,
        stateBearing_of_kind o a dm _ _ _ _ .accountMovement (Or.inl rfl),
        stateBearing_of_kind o a dm _ _ _ _ .custody (Or.inr (Or.inl rfl))]
      simp only [FitsI128, minI128, maxI128] at hbounds ⊢
      by_cases h1 : r.command.owner = o ∧ r.command.asset = a ∧ accountsDomain = dm
      · have h2 : ¬ (r.command.accountId = o ∧ r.command.asset = a ∧ marginDomain = dm) := by
          intro h2
          exact accounts_ne_margin (h1.2.2.trans h2.2.2.symm)
        rw [if_pos h1, if_neg h2]
        refine ⟨?_, ?_, ?_, trivial⟩ <;> omega
      · rw [if_neg h1]
        by_cases h2 : r.command.accountId = o ∧ r.command.asset = a ∧ marginDomain = dm
        · rw [if_pos h2]
          refine ⟨?_, ?_, ?_, trivial⟩ <;> omega
        · rw [if_neg h2]
          refine ⟨?_, ?_, ?_, trivial⟩ <;> omega
    · simp [effectRows, hc, RunningTotalsFitI128]
  · intro row hrow hkind
    rw [w.plan_rows] at hrow
    rcases w.kind with hk | hk | hk <;> simp [effectRows, hk] at hrow <;>
      rcases hrow with rfl | rfl | rfl <;> cases hkind
  · intro row hrow hkind
    rw [w.plan_rows] at hrow
    rcases w.kind with hk | hk | hk <;> simp [effectRows, hk] at hrow <;>
      rcases hrow with rfl | rfl | rfl <;> rcases hkind with h | h <;> cases h
  · intro row hrow
    simp [Witness.plan, successorPlan] at hrow
  · intro a
    rw [w.plan_eq]
    rcases w.kind with hk | hk | hk <;>
      simp [positiveDesignatedResidueFor, positiveCarriedResidueFor, effectRows, hk]

/-! ### Replay and Oracle refinement -/

theorem Witness.replay_eq (w : Witness d pre r) :
    w.frame.replay = insertReplay r.occurrence pre.frame.replay := rfl

theorem Witness.height_eq (w : Witness d pre r) : w.frame.height = pre.frame.height + 1 := rfl

theorem Witness.fresh_replay (w : Witness d pre r) :
    ∀ row ∈ pre.frame.replay,
      row.replayId ≠ r.occurrence.replayId ∧ row.occurrenceId ≠ r.occurrence.occurrenceId :=
  replayConsumed_false _ _ (context_guards d pre.frame r.occurrence w.context).2.2.2.2.2.2

theorem Witness.exactReplay (w : Witness d pre r) :
    ExactReplayRefinement (view d pre.frame) (view d w.frame) w.plan [r.occurrence.shared] := by
  obtain ⟨hchain, hdeploy, hprofile, hroot, hheight, hu64, _⟩ :=
    context_guards d pre.frame r.occurrence w.context
  have hfresh := w.fresh_replay
  refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [OrderedOccurrenceIds]
  · intro occ hocc
    simp only [List.mem_singleton] at hocc
    subst hocc
    exact ⟨hchain, hdeploy, hprofile, hroot⟩
  · simp
  · intro occ hocc
    simp only [List.mem_singleton] at hocc
    subst hocc
    refine ⟨?_, ?_, ?_⟩
    · exact replayLookup_none_of_fresh _ _ fun row hrow => (hfresh row hrow).1
    · show replayLookup (insertReplay r.occurrence pre.frame.replay) r.occurrence.replayId = _
      rw [replayLookup_insert, if_pos rfl]
      rfl
    · intro replayId prior hprior
      obtain ⟨row, hrow, _, hocc⟩ := replayLookup_mem _ _ _ hprior
      exact hocc ▸ (hfresh row hrow).2
  · intro replayId hother
    have hne : replayId ≠ r.occurrence.replayId := fun heq =>
      hother r.occurrence.shared (List.mem_singleton_self _) heq.symm
    show replayLookup (insertReplay r.occurrence pre.frame.replay) replayId = _
    rw [replayLookup_insert, if_neg hne]
    rfl
  · simp [view, w.height_eq]
  · show FitsU64 (pre.frame.height + 1)
    unfold FitsU64
    omega
  · intro occ hocc
    simp only [List.mem_singleton] at hocc
    subst hocc
    exact hheight

theorem Witness.exactOracle (w : Witness d pre r) :
    ExactOracleRefinement (view d pre.frame) (view d w.frame) w.plan ⟨[]⟩ := by
  refine ⟨⟨?_, ?_, ?_⟩, Or.inl rfl⟩
  · simp
  · intro delta hdelta
    simp at hdelta
  · intro _ _
    rfl

theorem replayLookup_injective_insert (rows : List ReplayRecord) (o : Occurrence)
    (hinj : ∀ left right occ, replayLookup rows left = some occ → replayLookup rows right = some occ →
      left = right)
    (hfresh : ∀ row ∈ rows, row.replayId ≠ o.replayId ∧ row.occurrenceId ≠ o.occurrenceId) :
    ∀ left right occ, replayLookup (insertReplay o rows) left = some occ →
      replayLookup (insertReplay o rows) right = some occ → left = right := by
  intro left right occ hleft hright
  rw [replayLookup_insert] at hleft hright
  by_cases hl : left = o.replayId
  · rw [if_pos hl] at hleft
    by_cases hr : right = o.replayId
    · exact hl.trans hr.symm
    · rw [if_neg hr] at hright
      obtain ⟨row, hrow, _, hocc⟩ := replayLookup_mem _ _ _ hright
      exact absurd (hocc.trans (Option.some.inj hleft).symm) (hfresh row hrow).2
  · rw [if_neg hl] at hleft
    by_cases hr : right = o.replayId
    · rw [if_pos hr] at hright
      obtain ⟨row, hrow, _, hocc⟩ := replayLookup_mem _ _ _ hleft
      exact absurd (hocc.trans (Option.some.inj hright).symm) (hfresh row hrow).2
    · rw [if_neg hr] at hright
      exact hinj left right occ hleft hright

theorem Witness.replayInjective (w : Witness d pre r) (inv : Invariant d pre) :
    ReplayOccurrenceIdsInjective (view d w.frame) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hinj, _⟩ := inv.frame.quantities
  exact replayLookup_injective_insert pre.frame.replay r.occurrence hinj w.fresh_replay

theorem oracle_admitted_succ (d : Digests) (pre post : Frame) (hor : post.oracles = pre.oracles)
    (hheight : post.height = pre.height + 1) (h : OracleRegistryAdmitted (view d pre)) :
    OracleRegistryAdmitted (view d post) := by
  refine ⟨?_, ?_⟩
  · intro id occ hocc
    change lookupKey OracleOccurrence.oracleId id post.oracles = some occ at hocc
    rw [hor] at hocc
    have := h.1 id occ hocc
    refine ⟨this.1, ?_⟩
    show occ.observedHeight ≤ post.height
    have h2 : occ.observedHeight ≤ pre.height := this.2
    rw [hheight]
    omega
  · intro id occ hocc
    change lookupKey OracleOccurrence.oracleId id post.oracles = some occ at hocc
    rw [hor] at hocc
    exact h.2 id occ hocc

theorem Witness.oracleAdmitted (w : Witness d pre r) (inv : Invariant d pre) :
    OracleRegistryAdmitted (view d w.frame) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, horacle⟩ := inv.frame.quantities
  exact oracle_admitted_succ d pre.frame w.frame rfl rfl horacle


/-! ### Terminal refinement through the proved episode -/

theorem Witness.market_eq (w : Witness d pre r) :
    w.market = { pre.margin.market with accounts := putAccount w.b pre.margin.market.accounts } :=
  w.facts.materialized

theorem Witness.market_asset (w : Witness d pre r) : w.market.asset = pre.margin.market.asset := by
  rw [w.market_eq]

theorem Witness.marketAdmitted (w : Witness d pre r) (inv : Invariant d pre) :
    MarketAdmitted w.market :=
  T.accepted_market_admitted _ _ _ _ inv.margin.market w.hmarket

theorem Witness.b_mem (w : Witness d pre r) : w.b ∈ w.market.accounts :=
  (T.lookup_selected _ _ _ w.facts.selected).1

/-- The accepted joint step is exactly one accepted episode of the proved claim model. -/
theorem Witness.advance_eq (w : Witness d pre r) (inv : Invariant d pre) :
    K.advance (claimsView pre.margin pre.frame.terminals) w.b (freshClaim d pre r) =
      some (claimsView w.margin w.terminals) := by
  have hcorr := advanceClaims_correspond pre inv.margin w.b (freshClaim d pre r)
  have hclaims := w.hclaims
  rw [w.market_asset] at hclaims
  rw [hclaims] at hcorr
  rw [← hcorr]
  simp only [Option.map_some]
  show some (claimsView
      ⟨{ pre.margin.market with accounts := putAccount w.b pre.margin.market.accounts }, w.bindings⟩
      w.terminals) = some (claimsView ⟨w.market, w.bindings⟩ w.terminals)
  rw [w.market_eq]

theorem Witness.wellFormedPost (w : Witness d pre r) (inv : Invariant d pre) :
    K.WellFormed (claimsView w.margin w.terminals) :=
  K.correspondence_preserved _ _ _ _ (invariant_wellFormed d pre inv)
    (owner_preserved pre r w.market w.b w.facts)
    (replacement_fits w.market (w.marketAdmitted inv) w.b w.b_mem) (w.advance_eq inv)

theorem Witness.pre_account_zero (w : Witness d pre r) (inv : Invariant d pre)
    (hnone : bindingOf pre.margin.bindings w.b.id = none) :
    ((lookupAccount r.command.accountId pre.margin.market.accounts).map
      fun a => (a.collateral : Int)).getD 0 = 0 := by
  cases hl : lookupAccount r.command.accountId pre.margin.market.accounts with
  | none => rfl
  | some a =>
    obtain ⟨hmem, hid⟩ := T.lookup_selected _ _ _ hl
    have hcover := inv.margin.coverFunded a hmem
    rw [hid, ← w.facts.id, hnone] at hcover
    simp at hcover
    simp [hcover]

theorem Witness.pre_account_bound (w : Witness d pre r) (inv : Invariant d pre) (id : Identifier)
    (hsome : bindingOf pre.margin.bindings w.b.id = some id) :
    ∃ a0, lookupAccount r.command.accountId pre.margin.market.accounts = some a0 ∧
      a0.owner = r.command.owner ∧
      terminalLookup pre.frame.terminals id = some (K.openClaim pre.margin.market.asset id a0) := by
  obtain ⟨binding, hmem, hkey, hoid⟩ := bindingOf_some _ _ _ hsome
  obtain ⟨a0, ha0, haid, hterm⟩ := inv.marginProjection.2.2.2.2.2.2 binding hmem
  have hl : lookupAccount r.command.accountId pre.margin.market.accounts = some a0 := by
    rw [← w.facts.id, ← hkey, ← haid]
    exact lookupAccount_of_mem _ inv.margin.market.ordered a0 ha0
  refine ⟨a0, hl, (w.facts.preAccount a0 hl).1, ?_⟩
  rw [← hoid]
  exact hterm

theorem contribution_drain (o : Principal) (a : Asset) (dm : AccountingLocation)
    (asset id : String) (a0 : Account) :
    terminalLiabilityContribution o a dm
        ⟨id, some (K.openClaim asset id a0), { K.openClaim asset id a0 with status := .drained }⟩ =
      if a0.owner = o ∧ asset = a ∧ marginDomain = dm then -(a0.collateral : Int) else 0 := by
  simp only [terminalLiabilityContribution, optionalTerminalOpenContribution,
    terminalOpenContribution, K.openClaim, marginDomain, and_true, and_false, if_false,
    reduceCtorEq]
  by_cases h : a0.owner = o ∧ asset = a ∧ "perps_margin" = dm <;> simp [h] <;> omega

theorem contribution_update (o : Principal) (a : Asset) (dm : AccountingLocation)
    (asset id : String) (a0 : Account) (v : Nat) :
    terminalLiabilityContribution o a dm
        ⟨id, some (K.openClaim asset id a0), { K.openClaim asset id a0 with amountAtoms := v }⟩ =
      if a0.owner = o ∧ asset = a ∧ marginDomain = dm then (v : Int) - a0.collateral else 0 := by
  simp only [terminalLiabilityContribution, optionalTerminalOpenContribution,
    terminalOpenContribution, K.openClaim, marginDomain, and_true]
  by_cases h : a0.owner = o ∧ asset = a ∧ "perps_margin" = dm <;> simp [h] <;> omega

theorem contribution_refill (o : Principal) (a : Asset) (dm : AccountingLocation)
    (asset id : String) (b : Account) :
    terminalLiabilityContribution o a dm ⟨id, none, K.openClaim asset id b⟩ =
      if b.owner = o ∧ asset = a ∧ marginDomain = dm then (b.collateral : Int) else 0 := by
  simp only [terminalLiabilityContribution, optionalTerminalOpenContribution,
    terminalOpenContribution, K.openClaim, marginDomain, and_true]
  by_cases h : b.owner = o ∧ asset = a ∧ "perps_margin" = dm <;> simp [h] <;> omega

/-- Either the terminal table is untouched (and the command moved nothing), or
exactly one perps row is written whose open-liability change equals the
command delta at the owner's coordinate: drain, update or fresh refill. -/
theorem Witness.terminals_shape (w : Witness d pre r) (inv : Invariant d pre) :
    (w.terminals = pre.frame.terminals ∧ commandDelta r.command = 0) ∨
    ∃ row, w.terminals = putTerminal row pre.frame.terminals ∧ row.laneId = .perpsMarket ∧
      ∀ o a dm, terminalLiabilityContribution o a dm
          ⟨row.obligationId, terminalLookup pre.frame.terminals row.obligationId, row⟩ =
        if r.command.owner = o ∧ r.command.asset = a ∧ marginDomain = dm then
          commandDelta r.command else 0 := by
  have hcoll := w.facts.collateral
  have hown := w.facts.owner
  have hasset := w.facts.asset
  have hclaims := w.hclaims
  rw [w.market_asset] at hclaims
  rcases advanceClaims_cases _ _ _ _ _ _ _ hclaims with
    ⟨id, old, hb, ht, hz, _, hterm⟩ | ⟨id, old, hb, ht, hz, _, hterm⟩ | ⟨hb, hz, _, hterm⟩ |
    ⟨hb, hz, hfresh, _, hterm⟩
  · obtain ⟨a0, hl, ha0own, hopen⟩ := w.pre_account_bound inv id hb
    rw [hopen] at ht
    have hold : old = K.openClaim pre.margin.market.asset id a0 := (Option.some.inj ht).symm
    subst hold
    right
    refine ⟨_, hterm, rfl, ?_⟩
    intro o a dm
    rw [hl] at hcoll
    simp only [Option.map_some, Option.getD_some] at hcoll
    simp [hz] at hcoll
    show terminalLiabilityContribution o a dm ⟨id, terminalLookup pre.frame.terminals id, _⟩ = _
    rw [hopen, contribution_drain, ha0own, ← hasset]
    by_cases hm : r.command.owner = o ∧ r.command.asset = a ∧ marginDomain = dm
    · rw [if_pos hm, if_pos hm]
      omega
    · rw [if_neg hm, if_neg hm]
  · obtain ⟨a0, hl, ha0own, hopen⟩ := w.pre_account_bound inv id hb
    rw [hopen] at ht
    have hold : old = K.openClaim pre.margin.market.asset id a0 := (Option.some.inj ht).symm
    subst hold
    right
    refine ⟨_, hterm, rfl, ?_⟩
    intro o a dm
    rw [hl] at hcoll
    simp only [Option.map_some, Option.getD_some] at hcoll
    show terminalLiabilityContribution o a dm ⟨id, terminalLookup pre.frame.terminals id, _⟩ = _
    rw [hopen, contribution_update, ha0own, ← hasset]
    by_cases hm : r.command.owner = o ∧ r.command.asset = a ∧ marginDomain = dm
    · rw [if_pos hm, if_pos hm]
      omega
    · rw [if_neg hm, if_neg hm]
  · left
    refine ⟨hterm, ?_⟩
    rw [w.pre_account_zero inv hb, hz] at hcoll
    simp at hcoll
    omega
  · right
    refine ⟨_, hterm, rfl, ?_⟩
    intro o a dm
    rw [w.pre_account_zero inv hb] at hcoll
    show terminalLiabilityContribution o a dm ⟨freshClaim d pre r,
      terminalLookup pre.frame.terminals (freshClaim d pre r), _⟩ = _
    rw [hfresh, contribution_refill, hown, ← hasset]
    by_cases hm : r.command.owner = o ∧ r.command.asset = a ∧ marginDomain = dm
    · rw [if_pos hm, if_pos hm]
      omega
    · rw [if_neg hm, if_neg hm]

theorem Witness.terminalIdsNodup (w : Witness d pre r) (inv : Invariant d pre) :
    (w.terminals.map TerminalObligation.obligationId).Nodup := by
  have hpre : (pre.frame.terminals.map TerminalObligation.obligationId).Nodup :=
    quantities_terminal_ids _ inv.frame.quantities
  rcases w.terminals_shape inv with ⟨heq, _⟩ | ⟨row, heq, _, _⟩
  · rw [heq]
    exact hpre
  · rw [heq]
    exact putTerminal_nodup row _ hpre

theorem Witness.terminalsAdmitted (w : Witness d pre r) (inv : Invariant d pre) :
    ∀ row ∈ w.terminals, TerminalObligationAdmitted row := by
  intro row hrow
  exact (w.wellFormedPost inv).terminalValid row.obligationId row
    (terminals_nodup_lookup w.terminals (w.terminalIdsNodup inv) row hrow)

theorem Witness.tplan_deltas (w : Witness d pre r) :
    w.tplan.deltas = terminalDeltas pre.frame.terminals w.terminals := rfl

theorem Witness.terminalRegistryRefines (w : Witness d pre r) (inv : Invariant d pre) :
    TerminalRegistryRefines pre.frame.terminals w.terminals w.tplan := by
  have hpre : (pre.frame.terminals.map TerminalObligation.obligationId).Nodup :=
    quantities_terminal_ids _ inv.frame.quantities
  have hwf := invariant_wellFormed d pre inv
  rcases w.terminals_shape inv with ⟨heq, _⟩ | ⟨row, heq, _, _⟩
  · have hdeltas : w.tplan.deltas = [] := by
      rw [w.tplan_deltas, heq]
      exact terminalDeltas_self _ hpre
    refine ⟨?_, ?_, ?_⟩
    · rw [hdeltas]
      exact List.nodup_nil
    · intro delta hdelta
      rw [hdeltas] at hdelta
      exact absurd hdelta List.not_mem_nil
    · intro id _
      rw [heq]
  · have hlook : ∀ id, terminalLookup w.terminals id =
        if id = row.obligationId then some row else terminalLookup pre.frame.terminals id := by
      intro id
      rw [heq]
      exact terminalLookup_putTerminal row _ id
    have hdeltas : w.tplan.deltas =
        if terminalLookup pre.frame.terminals row.obligationId = some row then []
        else [⟨row.obligationId, terminalLookup pre.frame.terminals row.obligationId, row⟩] := by
      rw [w.tplan_deltas, heq]
      exact terminalDeltas_put _ row hpre
    by_cases hsame : terminalLookup pre.frame.terminals row.obligationId = some row
    · rw [if_pos hsame] at hdeltas
      refine ⟨?_, ?_, ?_⟩
      · rw [hdeltas]
        exact List.nodup_nil
      · intro delta hdelta
        rw [hdeltas] at hdelta
        exact absurd hdelta List.not_mem_nil
      · intro id _
        rw [hlook]
        split
        · rename_i hid
          rw [hid]
          exact hsame.symm
        · rfl
    · rw [if_neg hsame] at hdeltas
      refine ⟨?_, ?_, ?_⟩
      · rw [hdeltas]
        simp
      · intro delta hdelta
        rw [hdeltas] at hdelta
        simp only [List.mem_singleton] at hdelta
        subst hdelta
        refine ⟨rfl, ?_, ?_⟩
        · rw [hlook, if_pos rfl]
        · exact K.changed_terminal_admitted _ hwf w.b (freshClaim d pre r) _
            (owner_preserved pre r w.market w.b w.facts)
            (replacement_fits w.market (w.marketAdmitted inv) w.b w.b_mem) (w.advance_eq inv)
            row.obligationId row (by
              show terminalLookup w.terminals row.obligationId = some row
              rw [hlook, if_pos rfl]) hsame
      · intro id hid
        have hne : id ≠ row.obligationId := fun heq' =>
          hid _ (hdeltas ▸ List.mem_singleton_self _) heq'.symm
        rw [hlook, if_neg hne]

theorem Witness.perps_write (w : Witness d pre r)
    (hroot : d.marginRoot w.margin ≠ d.marginRoot pre.margin) :
    ∃ write ∈ w.plan.laneWrites, write.laneId = .perpsMarket := by
  have hrow := w.marginProjection.1
  obtain ⟨hmem, _⟩ := lookupKey_mem LaneRow.laneId .perpsMarket pre.frame.lanes _ hrow
  rw [w.laneWrites_eq]
  refine ⟨_, (mem_laneWrites _ _ _).mpr ⟨_, hmem, ?_, rfl⟩, rfl⟩
  rw [updateLane_margin d w.assets w.margin _ rfl]
  exact hroot

theorem Witness.owningLaneWrites (w : Witness d pre r) (inv : Invariant d pre)
    (hroot : d.marginRoot w.margin ≠ d.marginRoot pre.margin) :
    TerminalOwningLaneWrites w.plan w.tplan := by
  have hpre : (pre.frame.terminals.map TerminalObligation.obligationId).Nodup :=
    quantities_terminal_ids _ inv.frame.quantities
  intro delta hdelta
  rcases w.terminals_shape inv with ⟨heq, _⟩ | ⟨row, heq, hlane, _⟩
  · exfalso
    rw [w.tplan_deltas, heq, terminalDeltas_self _ hpre] at hdelta
    exact List.not_mem_nil hdelta
  · rw [w.tplan_deltas, heq, terminalDeltas_put _ row hpre] at hdelta
    split at hdelta
    · exact absurd hdelta List.not_mem_nil
    · simp only [List.mem_singleton] at hdelta
      subst hdelta
      obtain ⟨write, hw, hwl⟩ := w.perps_write hroot
      exact ⟨write, hw, hwl.trans hlane.symm⟩

theorem Witness.terminalLiabilityEffects (w : Witness d pre r) (inv : Invariant d pre) :
    TerminalLiabilityEffects w.plan w.tplan := by
  have hpre : (pre.frame.terminals.map TerminalObligation.obligationId).Nodup :=
    quantities_terminal_ids _ inv.frame.quantities
  have hbounds := w.amount_bounds
  rcases w.terminals_shape inv with ⟨heq, hzero⟩ | ⟨row, heq, _, hcontrib⟩
  · have hdeltas : w.tplan.deltas = [] := by
      rw [w.tplan_deltas, heq]
      exact terminalDeltas_self _ hpre
    refine ⟨?_, ?_⟩
    · intro o a dm
      rw [hdeltas]
      trivial
    · intro o a dm
      rw [(w.effectFor o a dm).2.2.1, hzero]
      simp [terminalLiabilityDeltaFor, hdeltas]
  · have hdeltas : w.tplan.deltas =
        if terminalLookup pre.frame.terminals row.obligationId = some row then []
        else [⟨row.obligationId, terminalLookup pre.frame.terminals row.obligationId, row⟩] := by
      rw [w.tplan_deltas, heq]
      exact terminalDeltas_put _ row hpre
    refine ⟨?_, ?_⟩
    · intro o a dm
      rw [hdeltas]
      split
      · trivial
      · simp only [RunningTotalsFitI128, Int.zero_add]
        refine ⟨?_, trivial⟩
        rw [hcontrib o a dm]
        split
        · exact hbounds.1
        · exact zero_fits_i128
    · intro o a dm
      rw [(w.effectFor o a dm).2.2.1]
      unfold terminalLiabilityDeltaFor
      rw [hdeltas]
      split
      · rename_i hsame
        have hc := hcontrib r.command.owner r.command.asset marginDomain
        rw [if_pos ⟨rfl, rfl, rfl⟩, hsame] at hc
        simp only [terminalLiabilityContribution, optionalTerminalOpenContribution,
          Int.sub_self] at hc
        simp [← hc]
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero]
        exact hcontrib o a dm

/-! ### Claimant backing and post-state quantities -/

theorem openTerminalAmountFor_eq (registry : TerminalRegistry) (o : Principal) (a : Asset)
    (dm : AccountingLocation) :
    openTerminalAmountFor registry o a dm = (registry.map (terminalOpenContribution o a dm)).sum := rfl

theorem openTerminalAmountFor_nonneg (registry : TerminalRegistry)
    (hadm : ∀ row ∈ registry, TerminalObligationAdmitted row) (o : Principal) (a : Asset)
    (dm : AccountingLocation) : 0 ≤ openTerminalAmountFor registry o a dm := by
  induction registry with
  | nil => simp [openTerminalAmountFor]
  | cons row rows ih =>
    have h1 := (hadm row List.mem_cons_self).1.1
    have h2 := ih fun x hx => hadm x (List.mem_cons_of_mem _ hx)
    simp only [openTerminalAmountFor, List.map_cons, List.sum_cons] at h2 ⊢
    split <;> omega

theorem openTerminalAmountFor_put (row : TerminalObligation) (registry : TerminalRegistry)
    (hnodup : (registry.map TerminalObligation.obligationId).Nodup) (o : Principal) (a : Asset)
    (dm : AccountingLocation) :
    openTerminalAmountFor (putTerminal row registry) o a dm =
      openTerminalAmountFor registry o a dm + terminalLiabilityContribution o a dm
        ⟨row.obligationId, terminalLookup registry row.obligationId, row⟩ := by
  rw [openTerminalAmountFor_eq, openTerminalAmountFor_eq]
  unfold putTerminal
  rw [sum_putKey TerminalObligation.obligationId strLt _ row registry hnodup]
  unfold terminalLiabilityContribution optionalTerminalOpenContribution
  rw [terminalLookup_eq]
  cases lookupKey TerminalObligation.obligationId row.obligationId registry <;> simp <;> omega

theorem Witness.openTerminals_shift (w : Witness d pre r) (inv : Invariant d pre) (o : Principal)
    (a : Asset) (dm : AccountingLocation) :
    openTerminalAmountFor w.terminals o a dm = openTerminalAmountFor pre.frame.terminals o a dm +
      (if r.command.owner = o ∧ r.command.asset = a ∧ marginDomain = dm then
        commandDelta r.command else 0) := by
  have hpre : (pre.frame.terminals.map TerminalObligation.obligationId).Nodup :=
    quantities_terminal_ids _ inv.frame.quantities
  rcases w.terminals_shape inv with ⟨heq, hzero⟩ | ⟨row, heq, _, hcontrib⟩
  · rw [heq, hzero]
    simp
  · rw [heq, openTerminalAmountFor_put row _ hpre, hcontrib o a dm]

theorem Witness.liabilitiesPost (w : Witness d pre r) (inv : Invariant d pre) :
    ClaimantLiabilitiesBacked (view d w.frame) := by
  have hsparse := tables_sparse pre.frame r.command w.tables inv.tablesSparse w.kind w.htables
  have hshift := domain_totals_shift pre.frame r.command w.tables inv.tablesUnique w.kind w.htables
  have hat := amountAt_shift pre.frame r.command w.tables inv.tablesUnique w.kind w.htables
  refine ⟨?_, ?_⟩
  · intro a dm
    have hpre := inv.frame.liabilities.1 a dm
    change 0 ≤ amountForAssetDomain pre.frame.liabilities a dm ∧
      amountForAssetDomain pre.frame.liabilities a dm ≤
        amountForAssetDomain pre.frame.custody a dm at hpre
    change 0 ≤ amountForAssetDomain w.tables.liabilities a dm ∧
      amountForAssetDomain w.tables.liabilities a dm ≤ amountForAssetDomain w.tables.custody a dm
    refine ⟨amountForAssetDomain_nonneg _ _ _ (sparse_nonneg _ hsparse.liabilities), ?_⟩
    rw [(hshift a dm).1, (hshift a dm).2]
    omega
  · intro o a dm
    have hpre := inv.frame.liabilities.2 o a dm
    change 0 ≤ openTerminalAmountFor pre.frame.terminals o a dm ∧
      openTerminalAmountFor pre.frame.terminals o a dm ≤ amountAt pre.frame.liabilities o a dm at hpre
    change 0 ≤ openTerminalAmountFor w.terminals o a dm ∧
      openTerminalAmountFor w.terminals o a dm ≤ amountAt w.tables.liabilities o a dm
    refine ⟨openTerminalAmountFor_nonneg _ (w.terminalsAdmitted inv) o a dm, ?_⟩
    rw [w.openTerminals_shift inv o a dm, (hat o a dm).2.2]
    omega

theorem Witness.postQuantities (w : Witness d pre r) (inv : Invariant d pre) :
    StateQuantitiesAdmitted (view d w.frame) := by
  obtain ⟨hepoch, _, _, hss, _, _, hsr, _, _, _, hnr, hns, htot, _, _, _, _⟩ := inv.frame.quantities
  have hsparse := tables_sparse pre.frame r.command w.tables inv.tablesSparse w.kind w.htables
  have hunique := tables_unique pre.frame r.command w.tables inv.tablesUnique w.kind w.htables
  obtain ⟨_, _, _, _, hheight, hu64, _⟩ := context_guards d pre.frame r.occurrence w.context
  have hback := (w.liabilitiesPost inv).1
  refine ⟨hepoch, ?_, hsparse.balances, hss, hsparse.custody, hsparse.liabilities, hsr,
    hunique.balances, hunique.custody, hunique.liabilities, hnr, hns, ?_, w.terminalIdsNodup inv,
    w.terminalsAdmitted inv, w.replayInjective inv, w.oracleAdmitted inv⟩
  · show FitsU64 (pre.frame.height + 1)
    unfold FitsU64
    omega
  · intro a
    have h := htot a
    refine ⟨?_, ?_, h.2.2⟩
    · rw [ownedFor_view, w.ownedConserved inv a, ← ownedFor_view]
      exact h.1
    · change FitsU128 (amountForAsset w.tables.liabilities a)
      have hle := liabilities_le_custody_total w.tables.liabilities w.tables.custody a
        (sparse_nonneg _ hsparse.custody) (fun dm => (hback a dm).2)
      have hcust : amountForAsset w.tables.custody a ≤ ownedTotal w.frame a := by
        have h1 := amountForAsset_nonneg w.tables.balances a (sparse_nonneg _ hsparse.balances)
        have h2 := amountForAsset_nonneg pre.frame.reserves a (sparse_nonneg _ hsr)
        show amountForAsset w.tables.custody a ≤ amountForAsset w.tables.balances a +
          amountForAsset w.tables.custody a + amountForAsset pre.frame.reserves a
        omega
      have howned : FitsU128 (ownedTotal w.frame a) := by
        rw [w.ownedConserved inv a]
        exact h.1
      refine ⟨amountForAsset_nonneg _ _ (sparse_nonneg _ hsparse.liabilities), ?_⟩
      unfold FitsU128 at howned
      omega

/-! ## The connected result -/

/-- One accepted joint step satisfies every field of the shared global
relation. The only premise beyond the finite pre-state invariant is that the
margin digest separates the two margin states, which the runtime relies on to
emit the terminal-owning PERPS_MARKET write. -/
theorem Witness.verified (w : Witness d pre r) (inv : Invariant d pre)
    (hroot : d.marginRoot w.margin ≠ d.marginRoot pre.margin) :
    Verified (view d pre.frame) w.plan w.tplan ⟨[]⟩ [r.occurrence.shared] (view d w.frame) where
  fixedContext := w.fixedContext
  preQuantities := inv.frame.quantities
  postQuantities := w.postQuantities inv
  effectPlan := w.effectPlanAdmitted inv
  laneWrites := w.exactLaneWrites inv
  economicTables := w.exactEconomicTables inv
  supplyEffects := w.exactSupplyEffects
  conservationCoverage := w.conservationCoverage inv
  conservationRows := w.conservationRowsMatch
  annotations := w.annotations
  ownedSupplyPre := inv.frame.ownedSupply
  ownedSupplyPost := w.ownedSupplyPost inv
  liabilitiesPre := inv.frame.liabilities
  liabilitiesPost := w.liabilitiesPost inv
  terminal := ⟨w.terminalRegistryRefines inv, w.owningLaneWrites inv hroot,
    w.terminalLiabilityEffects inv⟩
  oracle := w.exactOracle
  replay := w.exactReplay
  outboxClosed := rfl
  zeroOccurrence := fun h => absurd h (List.cons_ne_nil _ _)

/-- The selected account's nonce advances, so the accepted margin state differs. -/
theorem Witness.margin_changed (w : Witness d pre r) : w.margin ≠ pre.margin := by
  intro heq
  have hmarket : w.market = pre.margin.market := congrArg Margin.market heq
  have hpre : lookupAccount r.command.accountId pre.margin.market.accounts = some w.b := by
    rw [← hmarket]
    exact w.facts.selected
  have hstep := w.facts.nonceStep
  rw [hpre] at hstep
  simp only [Option.map_some, Option.getD_some] at hstep
  have := w.facts.nonce
  omega

theorem accepted_verified (d : Digests) (pre : Joint) (r : Request) (acc : Accepted)
    (inv : Invariant d pre) (h : step d pre r = .ok acc)
    (hdigest : d.marginRoot acc.post.margin = d.marginRoot pre.margin → acc.post.margin = pre.margin) :
    Verified (view d pre.frame) acc.effects acc.terminalPlan ⟨[]⟩ [r.occurrence.shared]
      (view d acc.post.frame) := by
  obtain ⟨w, rfl⟩ := accepted_witness d pre r acc h
  exact w.verified inv fun heq => w.margin_changed (hdigest heq)

theorem accepted_global_witness (d : Digests) (pre : Joint) (r : Request) (acc : Accepted)
    (inv : Invariant d pre) (h : step d pre r = .ok acc)
    (hdigest : d.marginRoot acc.post.margin = d.marginRoot pre.margin → acc.post.margin = pre.margin) :
    ∃ global : Proofs.GlobalEconomicStateRefinementV2.Accepted (view d pre.frame),
      global.post = view d acc.post.frame ∧ global.effects = acc.effects ∧
        global.terminalPlan = acc.terminalPlan ∧ global.oraclePlan = ⟨[]⟩ ∧
        global.occurrences = [r.occurrence.shared] :=
  ⟨⟨acc.effects, acc.terminalPlan, ⟨[]⟩, [r.occurrence.shared], view d acc.post.frame,
    accepted_verified d pre r acc inv h hdigest⟩, rfl, rfl, rfl, rfl, rfl⟩


/-! ## Invariant preservation -/

theorem put_weight_int (w : Account → Int) (a : Account) (accounts : List Account)
    (h : T.OrderedAccounts accounts) :
    ((putAccount a accounts).map w).sum =
      (accounts.map w).sum + w a - ((lookupAccount a.id accounts).map w).getD 0 := by
  induction accounts with
  | nil => simp [PerpsMarginTransitionV1.putAccount, lookupAccount]
  | cons b bs ih =>
    simp only [PerpsMarginTransitionV1.putAccount]
    split
    · rename_i heq
      simp [lookupAccount, heq]
      omega
    · rename_i hne
      split
      · rename_i hlt
        rw [T.lookup_before_head a b bs h hlt]
        simp
        omega
      · have hi := ih (List.pairwise_cons.mp h).2
        simp only [List.map_cons, List.sum_cons, hi]
        simp [lookupAccount, Ne.symm hne]
        omega

theorem amountLookup_zero_of_none (rows : List AmountRow) (a : Asset) (o : Principal)
    (dm : AccountingLocation) (h : ∀ row ∈ rows, amountKey row ≠ (a, o, dm)) :
    amountLookup rows a o dm = 0 := by
  unfold amountLookup
  rw [(lookupKey_eq_none amountKey (a, o, dm) rows).mpr h]
  rfl

theorem ownerCollateral_zero_of_none (accounts : List Account) (o : Principal)
    (h : ∀ y ∈ accounts, y.owner ≠ o) : ownerCollateral accounts o = 0 := by
  induction accounts with
  | nil => rfl
  | cons y ys ih =>
    simp only [ownerCollateral, List.map_cons, List.sum_cons] at ih ⊢
    rw [if_neg (h y List.mem_cons_self), ih fun z hz => h z (List.mem_cons_of_mem _ hz)]
    rfl

theorem mem_putAccount_of_ne (b y : Account) (accounts : List Account) (hy : y ∈ accounts)
    (hne : y.id ≠ b.id) (hord : T.OrderedAccounts accounts) : y ∈ putAccount b accounts := by
  have := lookupAccount_of_mem accounts hord y hy
  rw [← T.lookup_put_other b accounts y.id hne] at this
  exact (T.lookup_selected _ _ _ this).1

theorem Witness.post_ordered (w : Witness d pre r) (inv : Invariant d pre) :
    T.OrderedAccounts w.market.accounts := (w.marketAdmitted inv).ordered

theorem Witness.post_account_cases (w : Witness d pre r) (inv : Invariant d pre) (x : Account)
    (hx : x ∈ w.market.accounts) : x = w.b ∨ (x ∈ pre.margin.market.accounts ∧ x.id ≠ w.b.id) := by
  have hmem : x ∈ putAccount w.b pre.margin.market.accounts := by
    have := w.market_eq
    rw [this] at hx
    exact hx
  rcases T.mem_put w.b x pre.margin.market.accounts hmem with rfl | hpre
  · exact Or.inl rfl
  · by_cases hid : x.id = w.b.id
    · exact Or.inl (account_eq_of_id _ (w.post_ordered inv) x w.b hx w.b_mem hid)
    · exact Or.inr ⟨hpre, hid⟩

theorem Witness.pre_account_mem_post (w : Witness d pre r) (inv : Invariant d pre) (y : Account)
    (hy : y ∈ pre.margin.market.accounts) :
    ∃ x ∈ w.market.accounts, x.id = y.id ∧ x.owner = y.owner := by
  by_cases hid : y.id = w.b.id
  · refine ⟨w.b, w.b_mem, hid.symm, ?_⟩
    have hl : lookupAccount r.command.accountId pre.margin.market.accounts = some y := by
      rw [← w.facts.id, ← hid]
      exact lookupAccount_of_mem _ inv.margin.market.ordered y hy
    rw [w.facts.owner]
    exact (w.facts.preAccount y hl).1.symm
  · refine ⟨y, ?_, rfl, rfl⟩
    rw [w.market_eq]
    exact mem_putAccount_of_ne w.b y _ hy hid inv.margin.market.ordered

theorem Witness.custody_lookup (w : Witness d pre r) (id : Identifier) :
    amountLookup w.tables.custody pre.margin.market.asset id marginDomain =
      amountLookup pre.frame.custody pre.margin.market.asset id marginDomain +
        (if id = r.command.accountId then commandDelta r.command else 0) := by
  have hasset := w.facts.asset
  rcases known_movement_or_close r.command w.kind with hm | hc
  · obtain ⟨_, hcu, _⟩ := successorTables_movement pre.frame r.command w.tables hm w.htables
    rw [hasset] at hcu
    by_cases hid : id = r.command.accountId
    · subst hid
      rw [if_pos rfl]
      exact applyDelta_lookup_self _ _ _ _ _ _ hcu
    · rw [if_neg hid, Int.add_zero]
      unfold amountLookup
      rw [applyDelta_lookup_other _ _ _ _ _ _ hcu _ _ _ (by simp [hid])]
  · have htc := successorTables_close pre.frame r.command w.tables hc w.htables
    rw [htc, commandDelta_close r.command hc]
    simp [preTables]

theorem Witness.liability_lookup (w : Witness d pre r) (o : Principal) :
    amountLookup w.tables.liabilities pre.margin.market.asset o marginDomain =
      amountLookup pre.frame.liabilities pre.margin.market.asset o marginDomain +
        (if o = r.command.owner then commandDelta r.command else 0) := by
  have hasset := w.facts.asset
  rcases known_movement_or_close r.command w.kind with hm | hc
  · obtain ⟨_, _, hl⟩ := successorTables_movement pre.frame r.command w.tables hm w.htables
    rw [hasset] at hl
    by_cases ho : o = r.command.owner
    · subst ho
      rw [if_pos rfl]
      exact applyDelta_lookup_self _ _ _ _ _ _ hl
    · rw [if_neg ho, Int.add_zero]
      unfold amountLookup
      rw [applyDelta_lookup_other _ _ _ _ _ _ hl _ _ _ (by simp [ho])]
  · have htc := successorTables_close pre.frame r.command w.tables hc w.htables
    rw [htc, commandDelta_close r.command hc]
    simp [preTables]

theorem Witness.preCollateral (w : Witness d pre r) :
    ((lookupAccount r.command.accountId pre.margin.market.accounts).map
      fun a => (a.collateral : Int)).getD 0 = (w.b.collateral : Int) - commandDelta r.command := by
  have := w.facts.collateral
  omega

theorem Witness.ownerCollateral_post (w : Witness d pre r) (inv : Invariant d pre) (o : Principal) :
    ownerCollateral w.market.accounts o = ownerCollateral pre.margin.market.accounts o +
      (if r.command.owner = o then commandDelta r.command else 0) := by
  rw [w.market_eq]
  show ((putAccount w.b pre.margin.market.accounts).map
    fun a => if a.owner = o then (a.collateral : Int) else 0).sum = _
  rw [put_weight_int _ w.b _ inv.margin.market.ordered, w.facts.id]
  change ownerCollateral pre.margin.market.accounts o +
    (if w.b.owner = o then (w.b.collateral : Int) else 0) -
    ((lookupAccount r.command.accountId pre.margin.market.accounts).map
      fun a => if a.owner = o then (a.collateral : Int) else 0).getD 0 = _
  have hcoll := w.preCollateral
  cases hl : lookupAccount r.command.accountId pre.margin.market.accounts with
  | none =>
    rw [hl] at hcoll
    simp only [Option.map_none, Option.getD_none] at hcoll
    simp only [Option.map_none, Option.getD_none, w.facts.owner]
    by_cases ho : r.command.owner = o <;> simp only [ho, ite_true, ite_false] <;>
      omega
  | some a0 =>
    rw [hl] at hcoll
    simp only [Option.map_some, Option.getD_some] at hcoll
    have ha0 := (w.facts.preAccount a0 hl).1
    simp only [Option.map_some, Option.getD_some, w.facts.owner, ha0]
    by_cases ho : r.command.owner = o <;> simp only [ho, ite_true, ite_false] <;>
      omega

theorem Witness.custody_row_cases (w : Witness d pre r) (row : AmountRow)
    (hrow : row ∈ w.tables.custody) :
    row ∈ pre.frame.custody ∨ amountKey row = (r.command.asset, r.command.accountId, marginDomain) := by
  rcases known_movement_or_close r.command w.kind with hm | hc
  · obtain ⟨_, hcu, _⟩ := successorTables_movement pre.frame r.command w.tables hm w.htables
    rcases applyDelta_mem _ _ _ _ _ _ hcu row hrow with ⟨hmem, _⟩ | ⟨hkey, _⟩
    · exact Or.inl hmem
    · exact Or.inr hkey
  · have htc := successorTables_close pre.frame r.command w.tables hc w.htables
    rw [htc] at hrow
    exact Or.inl hrow

theorem Witness.liability_row_cases (w : Witness d pre r) (row : AmountRow)
    (hrow : row ∈ w.tables.liabilities) :
    row ∈ pre.frame.liabilities ∨ amountKey row = (r.command.asset, r.command.owner, marginDomain) := by
  rcases known_movement_or_close r.command w.kind with hm | hc
  · obtain ⟨_, _, hl⟩ := successorTables_movement pre.frame r.command w.tables hm w.htables
    rcases applyDelta_mem _ _ _ _ _ _ hl row hrow with ⟨hmem, _⟩ | ⟨hkey, _⟩
    · exact Or.inl hmem
    · exact Or.inr hkey
  · have htc := successorTables_close pre.frame r.command w.tables hc w.htables
    rw [htc] at hrow
    exact Or.inl hrow

theorem Witness.assetProjectionPost (w : Witness d pre r) :
    AssetProjection d w.assets w.frame := by
  obtain ⟨_, _, hsup, hres, hlane⟩ := w.assetProjection
  refine ⟨rfl, rfl, hsup, hres, ?_⟩
  rw [w.laneRow_post, hlane]
  simp only [Option.map_some]
  rw [updateLane_asset d w.assets w.margin _ rfl]
  rfl

/-- The post claim bindings, by the four runtime outcomes. -/
theorem Witness.bindings_cases (w : Witness d pre r) :
    (w.bindings = eraseKey Binding.accountId w.b.id pre.margin.bindings ∧ w.b.collateral = 0 ∧
        (bindingOf pre.margin.bindings w.b.id).isSome = true) ∨
      (w.bindings = pre.margin.bindings ∧ w.b.collateral ≠ 0 ∧
        (bindingOf pre.margin.bindings w.b.id).isSome = true) ∨
      (w.bindings = pre.margin.bindings ∧ w.b.collateral = 0 ∧
        bindingOf pre.margin.bindings w.b.id = none) ∨
      (∃ fresh, w.bindings = putBinding ⟨w.b.id, fresh⟩ pre.margin.bindings ∧ w.b.collateral ≠ 0 ∧
        bindingOf pre.margin.bindings w.b.id = none ∧ terminalLookup pre.frame.terminals fresh = none ∧
        w.terminals = putTerminal (K.openClaim pre.margin.market.asset fresh w.b) pre.frame.terminals) := by
  have hclaims := w.hclaims
  rw [w.market_asset] at hclaims
  rcases advanceClaims_cases _ _ _ _ _ _ _ hclaims with
    ⟨id, _, hb, _, hz, hbind, _⟩ | ⟨id, _, hb, _, hz, hbind, _⟩ | ⟨hb, hz, hbind, _⟩ |
    ⟨hb, hz, hfresh, hbind, hterm⟩
  · exact Or.inl ⟨hbind, hz, by simp [hb]⟩
  · exact Or.inr (Or.inl ⟨hbind, hz, by simp [hb]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hbind, hz, hb⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, hbind, hz, hb, hfresh, hterm⟩))

theorem Witness.bindingOf_post_other (w : Witness d pre r) (key : Identifier)
    (hkey : key ≠ w.b.id) : bindingOf w.bindings key = bindingOf pre.margin.bindings key := by
  rcases w.bindings_cases with ⟨heq, _, _⟩ | ⟨heq, _, _⟩ | ⟨heq, _, _⟩ | ⟨fresh, heq, _, _, _, _⟩
  · rw [heq]
    exact bindingOf_erase_other _ _ _ hkey
  · rw [heq]
  · rw [heq]
  · rw [heq]
    exact bindingOf_put_other _ _ _ hkey

theorem Witness.bindingOf_post_self (w : Witness d pre r) :
    (bindingOf w.bindings w.b.id).isSome = true ↔ 0 < w.b.collateral := by
  rcases w.bindings_cases with ⟨heq, hz, _⟩ | ⟨heq, hz, hsome⟩ | ⟨heq, hz, hnone⟩ |
    ⟨fresh, heq, hz, _, _, _⟩
  · rw [heq, bindingOf_erase_self]
    simp [hz]
  · rw [heq]
    simp only [hsome, true_iff]
    omega
  · rw [heq, hnone]
    simp [hz]
  · rw [heq, bindingOf_put_self]
    simp only [Option.isSome_some, true_iff]
    omega

theorem Witness.marginProjectionPost (w : Witness d pre r) (inv : Invariant d pre) :
    MarginProjection d w.margin w.frame := by
  obtain ⟨hlane, hcust, hcustRows, hliab, hliabRows, hopen, hbind_pre⟩ := w.marginProjection
  have hord := inv.margin.market.ordered
  have hasset := w.facts.asset
  have hcoll := w.preCollateral
  have hown := w.facts.owner
  have hrel : w.market.release = pre.margin.market.release := by rw [w.market_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [w.laneRow_post, hlane]
    simp only [Option.map_some]
    rw [updateLane_margin d w.assets w.margin _ rfl]
    show some (⟨.perpsMarket, pre.margin.market.release, true, d.marginRoot w.margin⟩ : LaneRow) =
      some ⟨.perpsMarket, w.market.release, true, d.marginRoot w.margin⟩
    rw [hrel]
  · intro x hx
    show amountLookup w.tables.custody w.market.asset x.id marginDomain = x.collateral
    rw [w.market_asset, w.custody_lookup x.id]
    rcases w.post_account_cases inv x hx with rfl | ⟨hpre, hne⟩
    · rw [w.facts.id, if_pos rfl]
      cases hl : lookupAccount r.command.accountId pre.margin.market.accounts with
      | none =>
        rw [hl] at hcoll
        simp only [Option.map_none, Option.getD_none] at hcoll
        have hzero : amountLookup pre.frame.custody pre.margin.market.asset r.command.accountId
            marginDomain = 0 := by
          apply amountLookup_zero_of_none
          intro row hrow hkey
          obtain ⟨_, y, hy, hyid⟩ := hcustRows row hrow (by
            simp only [amountKey, Prod.mk.injEq] at hkey
            exact hkey.2.2)
          simp only [amountKey, Prod.mk.injEq] at hkey
          exact (T.lookup_none _ _).mp hl y hy (hyid.trans hkey.2.1)
        rw [hzero]
        omega
      | some a0 =>
        rw [hl] at hcoll
        simp only [Option.map_some, Option.getD_some] at hcoll
        have hid := (T.lookup_selected _ _ _ hl).2
        rw [← hid, hcust a0 (T.lookup_selected _ _ _ hl).1]
        omega
    · rw [if_neg (fun heq => hne (heq.trans w.facts.id.symm)), Int.add_zero]
      exact hcust x hpre
  · intro row hrow hdm
    change row ∈ w.tables.custody at hrow
    rcases w.custody_row_cases row hrow with hpre | hkey
    · obtain ⟨hra, y, hy, hyid⟩ := hcustRows row hpre hdm
      obtain ⟨x, hx, hxid, _⟩ := w.pre_account_mem_post inv y hy
      refine ⟨?_, x, hx, hxid.trans hyid⟩
      show row.asset = w.market.asset
      rw [w.market_asset]
      exact hra
    · simp only [amountKey, Prod.mk.injEq] at hkey
      refine ⟨?_, w.b, w.b_mem, ?_⟩
      · show row.asset = w.market.asset
        rw [w.market_asset, hkey.1]
        exact hasset
      · rw [hkey.2.1]
        exact w.facts.id
  · intro x hx
    show amountLookup w.tables.liabilities w.market.asset x.owner marginDomain =
      ownerCollateral w.market.accounts x.owner
    rw [w.market_asset, w.liability_lookup x.owner, w.ownerCollateral_post inv x.owner]
    have hbase : amountLookup pre.frame.liabilities pre.margin.market.asset x.owner marginDomain =
        ownerCollateral pre.margin.market.accounts x.owner := by
      by_cases hexists : ∃ y ∈ pre.margin.market.accounts, y.owner = x.owner
      · obtain ⟨y, hy, hyo⟩ := hexists
        rw [← hyo]
        exact hliab y hy
      · have hnone : ∀ y ∈ pre.margin.market.accounts, y.owner ≠ x.owner := fun y hy hyo =>
          hexists ⟨y, hy, hyo⟩
        rw [ownerCollateral_zero_of_none _ _ hnone]
        apply amountLookup_zero_of_none
        intro row hrow hkey
        simp only [amountKey, Prod.mk.injEq] at hkey
        obtain ⟨_, y, hy, hyo⟩ := hliabRows row hrow hkey.2.2
        exact hnone y hy (hyo.trans hkey.2.1)
    rw [hbase]
    by_cases ho : x.owner = r.command.owner
    · rw [if_pos ho, if_pos ho.symm]
    · rw [if_neg ho, if_neg (Ne.symm ho)]
  · intro row hrow hdm
    change row ∈ w.tables.liabilities at hrow
    rcases w.liability_row_cases row hrow with hpre | hkey
    · obtain ⟨hra, y, hy, hyo⟩ := hliabRows row hpre hdm
      obtain ⟨x, hx, _, hxo⟩ := w.pre_account_mem_post inv y hy
      refine ⟨?_, x, hx, hxo.trans hyo⟩
      show row.asset = w.market.asset
      rw [w.market_asset]
      exact hra
    · simp only [amountKey, Prod.mk.injEq] at hkey
      refine ⟨?_, w.b, w.b_mem, ?_⟩
      · show row.asset = w.market.asset
        rw [w.market_asset, hkey.1]
        exact hasset
      · rw [hkey.2.1]
        exact hown
  · intro row hrow hl hs
    change row ∈ w.terminals at hrow
    have hclaims := w.hclaims
    rw [w.market_asset] at hclaims
    rcases advanceClaims_cases _ _ _ _ _ _ _ hclaims with
      ⟨id, old, hbo, ht, hz, hbind, hterm⟩ | ⟨id, old, hbo, ht, hz, hbind, hterm⟩ |
      ⟨hbo, hz, hbind, hterm⟩ | ⟨hbo, hz, hfresh, hbind, hterm⟩
    · rw [hterm] at hrow
      rcases (mem_putTerminal _ _ _).mp hrow with rfl | ⟨hmem, hne⟩
      · cases hs
      · obtain ⟨bd, hbd, hbdo⟩ := hopen row hmem hl hs
        refine ⟨bd, ?_, hbdo⟩
        change bd ∈ w.bindings
        rw [hbind]
        apply (mem_eraseKey Binding.accountId _ bd _).mpr
        refine ⟨hbd, ?_⟩
        intro hacc
        have := bindingOf_of_mem _ inv.margin.accountsUnique bd hbd
        rw [hacc, hbo] at this
        have hoid : bd.obligationId = id := (Option.some.inj this).symm
        have hoo := (terminalLookup_mem _ _ _ ht).2
        exact hne (hbdo.symm.trans (hoid.trans hoo.symm))
    · rw [hterm] at hrow
      change ∃ b ∈ w.bindings, b.obligationId = row.obligationId
      rw [hbind]
      rcases (mem_putTerminal _ _ _).mp hrow with rfl | ⟨hmem, _⟩
      · obtain ⟨bd, hbd, hbdk, hbdo⟩ := bindingOf_some _ _ _ hbo
        refine ⟨bd, hbd, ?_⟩
        rw [hbdo]
        exact ((terminalLookup_mem _ _ _ ht).2).symm
      · exact hopen row hmem hl hs
    · rw [hterm] at hrow
      change ∃ b ∈ w.bindings, b.obligationId = row.obligationId
      rw [hbind]
      exact hopen row hrow hl hs
    · rw [hterm] at hrow
      change ∃ b ∈ w.bindings, b.obligationId = row.obligationId
      rw [hbind]
      rcases (mem_putTerminal _ _ _).mp hrow with rfl | ⟨hmem, _⟩
      · exact ⟨⟨w.b.id, _⟩, (mem_putKey Binding.accountId strLt _ _ _).mpr (Or.inl rfl), rfl⟩
      · obtain ⟨bd, hbd, hbdo⟩ := hopen row hmem hl hs
        refine ⟨bd, (mem_putKey Binding.accountId strLt _ _ _).mpr (Or.inr ⟨hbd, ?_⟩), hbdo⟩
        intro hacc
        have := bindingOf_of_mem _ inv.margin.accountsUnique bd hbd
        rw [hacc, hbo] at this
        cases this
  · intro bd hbd
    change bd ∈ w.bindings at hbd
    have hclaims := w.hclaims
    rw [w.market_asset] at hclaims
    have hsibling : ∀ y ∈ pre.margin.market.accounts, y.id ≠ w.b.id → y ∈ w.market.accounts := by
      intro y hy hne
      rw [w.market_eq]
      exact mem_putAccount_of_ne w.b y _ hy hne hord
    have hbound_oid : ∀ id, bindingOf pre.margin.bindings w.b.id = some id →
        ∀ bd' ∈ pre.margin.bindings, bd'.accountId ≠ w.b.id → bd'.obligationId ≠ id := by
      intro id hbo bd' hbd' hne heq
      obtain ⟨bb, hbb, hbbk, hbbo⟩ := bindingOf_some _ _ _ hbo
      have := binding_eq_of_obligation _ inv.margin.claimsUnique bd' bb hbd' hbb (heq.trans hbbo.symm)
      subst this
      exact hne hbbk
    rcases advanceClaims_cases _ _ _ _ _ _ _ hclaims with
      ⟨id, old, hbo, ht, hz, hbind, hterm⟩ | ⟨id, old, hbo, ht, hz, hbind, hterm⟩ |
      ⟨hbo, hz, hbind, hterm⟩ | ⟨hbo, hz, hfresh, hbind, hterm⟩
    · rw [hbind] at hbd
      obtain ⟨hmem, hne⟩ := (mem_eraseKey Binding.accountId _ bd _).mp hbd
      obtain ⟨y, hy, hyid, hyterm⟩ := hbind_pre bd hmem
      refine ⟨y, hsibling y hy (fun h => hne (hyid.symm.trans h)), hyid, ?_⟩
      change terminalLookup w.terminals bd.obligationId =
        some (K.openClaim w.market.asset bd.obligationId y)
      rw [hterm, terminalLookup_putTerminal, w.market_asset]
      have hoid := (terminalLookup_mem _ _ _ ht).2
      rw [if_neg (by
        show bd.obligationId ≠ old.obligationId
        rw [hoid]
        exact hbound_oid id hbo bd hmem hne)]
      exact hyterm
    · rw [hbind] at hbd
      by_cases hid : bd.accountId = w.b.id
      · refine ⟨w.b, w.b_mem, hid.symm, ?_⟩
        have hbid : bd.obligationId = id := by
          have := bindingOf_of_mem _ inv.margin.accountsUnique bd hbd
          rw [hid, hbo] at this
          exact (Option.some.inj this).symm
        obtain ⟨a0, hl, ha0own, hopen⟩ := w.pre_account_bound inv id hbo
        rw [hopen] at ht
        have hold : old = K.openClaim pre.margin.market.asset id a0 := (Option.some.inj ht).symm
        change terminalLookup w.terminals bd.obligationId =
          some (K.openClaim w.market.asset bd.obligationId w.b)
        rw [hterm, hold, hbid, terminalLookup_putTerminal, w.market_asset]
        simp [K.openClaim, ha0own, hown]
      · obtain ⟨y, hy, hyid, hyterm⟩ := hbind_pre bd hbd
        refine ⟨y, hsibling y hy (fun h => hid (hyid.symm.trans h)), hyid, ?_⟩
        change terminalLookup w.terminals bd.obligationId =
          some (K.openClaim w.market.asset bd.obligationId y)
        rw [hterm, terminalLookup_putTerminal, w.market_asset]
        have hoid := (terminalLookup_mem _ _ _ ht).2
        rw [if_neg (by
          show bd.obligationId ≠ old.obligationId
          rw [hoid]
          exact hbound_oid id hbo bd hbd hid)]
        exact hyterm
    · rw [hbind] at hbd
      have hid : bd.accountId ≠ w.b.id := by
        intro heq
        have := bindingOf_of_mem _ inv.margin.accountsUnique bd hbd
        rw [heq, hbo] at this
        cases this
      obtain ⟨y, hy, hyid, hyterm⟩ := hbind_pre bd hbd
      refine ⟨y, hsibling y hy (fun h => hid (hyid.symm.trans h)), hyid, ?_⟩
      change terminalLookup w.terminals bd.obligationId =
        some (K.openClaim w.market.asset bd.obligationId y)
      rw [hterm, w.market_asset]
      exact hyterm
    · rw [hbind] at hbd
      rcases (mem_putKey Binding.accountId strLt _ bd _).mp hbd with rfl | ⟨hmem, hne⟩
      · refine ⟨w.b, w.b_mem, rfl, ?_⟩
        change terminalLookup w.terminals (freshClaim d pre r) =
          some (K.openClaim w.market.asset (freshClaim d pre r) w.b)
        rw [hterm, terminalLookup_putTerminal, w.market_asset]
        simp [K.openClaim]
      · obtain ⟨y, hy, hyid, hyterm⟩ := hbind_pre bd hmem
        refine ⟨y, hsibling y hy (fun h => hne (hyid.symm.trans h)), hyid, ?_⟩
        change terminalLookup w.terminals bd.obligationId =
          some (K.openClaim w.market.asset bd.obligationId y)
        rw [hterm, terminalLookup_putTerminal, w.market_asset]
        rw [if_neg (by
          intro heq
          have heq' : bd.obligationId = freshClaim d pre r := heq
          rw [heq', hfresh] at hyterm
          cases hyterm)]
        exact hyterm

theorem Witness.marginAdmittedPost (w : Witness d pre r) (inv : Invariant d pre) :
    MarginAdmitted w.margin := by
  have hproj := w.marginProjectionPost inv
  have hfreshNe : ∀ fresh, terminalLookup pre.frame.terminals fresh = none →
      fresh ∉ pre.margin.bindings.map Binding.obligationId := by
    intro fresh hfresh hmem
    obtain ⟨bd, hbd, hbdo⟩ := List.mem_map.mp hmem
    obtain ⟨_, _, _, hterm⟩ := inv.marginProjection.2.2.2.2.2.2 bd hbd
    rw [hbdo, hfresh] at hterm
    cases hterm
  refine ⟨w.marketAdmitted inv, ?_, ?_, ?_, ?_⟩
  · show (w.bindings.map Binding.accountId).Nodup
    rcases w.bindings_cases with ⟨heq, _, _⟩ | ⟨heq, _, _⟩ | ⟨heq, _, _⟩ | ⟨fresh, heq, _, _, _, _⟩
    · rw [heq]
      exact nodup_eraseKey Binding.accountId _ _ inv.margin.accountsUnique
    · rw [heq]
      exact inv.margin.accountsUnique
    · rw [heq]
      exact inv.margin.accountsUnique
    · rw [heq]
      exact nodup_putKey Binding.accountId strLt _ _ inv.margin.accountsUnique
  · show (w.bindings.map Binding.obligationId).Nodup
    rcases w.bindings_cases with ⟨heq, _, _⟩ | ⟨heq, _, _⟩ | ⟨heq, _, _⟩ |
      ⟨fresh, heq, _, _, hfresh, _⟩
    · rw [heq]
      exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) inv.margin.claimsUnique
    · rw [heq]
      exact inv.margin.claimsUnique
    · rw [heq]
      exact inv.margin.claimsUnique
    · rw [heq]
      unfold putBinding putKey
      apply nodup_map_insertSorted Binding.accountId strLt Binding.obligationId
      · exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) inv.margin.claimsUnique
      · intro hmem
        apply hfreshNe fresh hfresh
        obtain ⟨bd, hbd, hbdo⟩ := List.mem_map.mp hmem
        exact List.mem_map.mpr ⟨bd, (mem_eraseKey Binding.accountId _ bd _).mp hbd |>.1, hbdo⟩
  · intro x hx
    change (bindingOf w.bindings x.id).isSome = true ↔ 0 < x.collateral
    rcases w.post_account_cases inv x hx with rfl | ⟨hpre, hne⟩
    · exact w.bindingOf_post_self
    · rw [w.bindingOf_post_other x.id hne]
      exact inv.margin.coverFunded x hpre
  · intro bd hbd
    obtain ⟨x, hx, hxid, _⟩ := hproj.2.2.2.2.2.2 bd hbd
    exact ⟨x, hx, hxid⟩

theorem Witness.frameAdmittedPost (w : Witness d pre r) (inv : Invariant d pre) :
    FrameAdmitted d w.frame := by
  refine ⟨?_, ?_, w.postQuantities inv, w.ownedSupplyPost inv, w.liabilitiesPost inv⟩
  · rw [w.lanes_map, List.map_map]
    have : LaneRow.laneId ∘ updateLane d w.assets w.margin = LaneRow.laneId := by
      funext row
      exact updateLane_laneId d w.assets w.margin row
    rw [this]
    exact inv.frame.lanes
  · exact insertReplay_nodup r.occurrence _ inv.frame.replayUnique

theorem Witness.invariantPost (w : Witness d pre r) (inv : Invariant d pre) :
    Invariant d w.post :=
  ⟨w.marginAdmittedPost inv, w.frameAdmittedPost inv, w.assetProjectionPost,
    w.marginProjectionPost inv⟩

theorem invariant_preserved (d : Digests) (pre : Joint) (r : Request) (acc : Accepted)
    (inv : Invariant d pre) (h : step d pre r = .ok acc) : Invariant d acc.post := by
  obtain ⟨w, rfl⟩ := accepted_witness d pre r acc h
  exact w.invariantPost inv

theorem advanceMargin_invariant (d : Digests) (pre : Joint) (r : Request) (inv : Invariant d pre) :
    Invariant d (advanceMargin d pre r) := by
  unfold advanceMargin
  split
  · exact inv
  · rename_i acc h
    exact invariant_preserved d pre r acc inv h


/-! ## The asset-lane frame between episodes

`derive_asset_lane_custody_global_post_v2` replaces the physical balances and
positive supplies from an accepted custody-lane result, rewrites only the
ASSET_TRANSFER root, inserts the replay row and advances the height. Custody,
liabilities and terminals are retained, so margin claims are untouched. The
custody lane's own proofs cover the transfer decision; here the accepted lane
result is an input whose physical conservation is checked. -/

structure FrameUpdate where
  balances : List AmountRow
  supplies : List SupplyRow
  occurrence : Occurrence
  deriving DecidableEq, Repr

def assetKeys (frame : Frame) (u : FrameUpdate) : List Asset :=
  frame.custody.map AmountRow.asset ++ frame.reserves.map AmountRow.asset ++
    u.balances.map AmountRow.asset ++ u.supplies.map SupplyRow.asset

def FrameUpdateAdmitted (frame : Frame) (u : FrameUpdate) : Prop :=
  AmountRowsUnique u.balances ∧ SparseAmountRowsAdmitted u.balances ∧
    (u.supplies.map SupplyRow.asset).Nodup ∧ (∀ row ∈ u.supplies, FitsU128 row.amountAtoms) ∧
    (∀ a ∈ assetKeys frame u,
      amountForAsset u.balances a + amountForAsset frame.custody a +
        amountForAsset frame.reserves a = supplyFor (positiveSupplies u.supplies) a) ∧
    u.balances.length ≤ assetRowCeiling ∧ frame.replay.length + 1 ≤ globalRowCeiling

instance (frame : Frame) (u : FrameUpdate) : Decidable (FrameUpdateAdmitted frame u) := by
  unfold FrameUpdateAdmitted AmountRowsUnique SparseAmountRowsAdmitted FitsU128
  infer_instance

def frameAssets (pre : Joint) (u : FrameUpdate) : Assets :=
  { pre.assets with balances := u.balances, supplies := u.supplies }

def frameSuccessor (d : Digests) (pre : Joint) (u : FrameUpdate) : Frame :=
  { pre.frame with
    lanes := pre.frame.lanes.map (updateLane d (frameAssets pre u) pre.margin)
    balances := u.balances
    supplies := positiveSupplies u.supplies
    replay := insertReplay u.occurrence pre.frame.replay
    height := pre.frame.height + 1 }

def frameStep (d : Digests) (pre : Joint) (u : FrameUpdate) : Option Joint :=
  match contextReject d pre.frame u.occurrence with
  | some _ => none
  | none =>
    if FrameUpdateAdmitted pre.frame u then some ⟨frameAssets pre u, pre.margin, frameSuccessor d pre u⟩
    else none

theorem frameStep_some (d : Digests) (pre : Joint) (u : FrameUpdate) (post : Joint)
    (h : frameStep d pre u = some post) :
    contextReject d pre.frame u.occurrence = none ∧ FrameUpdateAdmitted pre.frame u ∧
      post = ⟨frameAssets pre u, pre.margin, frameSuccessor d pre u⟩ := by
  unfold frameStep at h
  cases hctx : contextReject d pre.frame u.occurrence with
  | some code => simp [hctx] at h
  | none =>
    simp only [hctx] at h
    split at h
    · rename_i hadm
      cases h
      exact ⟨rfl, hadm, rfl⟩
    · cases h

theorem amountForAsset_zero_of_absent (rows : List AmountRow) (a : Asset)
    (h : a ∉ rows.map AmountRow.asset) : amountForAsset rows a = 0 := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons] at h
    rw [amountForAsset_cons, if_neg (fun heq => h (List.mem_cons.mpr (Or.inl heq.symm))),
      ih (fun hm => h (List.mem_cons.mpr (Or.inr hm)))]
    rfl

theorem supplyFor_zero_of_absent (rows : List SupplyRow) (a : Asset)
    (h : a ∉ rows.map SupplyRow.asset) : supplyFor rows a = 0 := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons] at h
    simp only [supplyFor, List.map_cons, List.sum_cons] at ih ⊢
    rw [if_neg (fun heq => h (List.mem_cons.mpr (Or.inl heq.symm))),
      ih (fun hm => h (List.mem_cons.mpr (Or.inr hm)))]
    rfl

theorem positiveSupplies_sparse (rows : List SupplyRow) (hfits : ∀ row ∈ rows, FitsU128 row.amountAtoms) :
    SparseSupplyRowsAdmitted (positiveSupplies rows) := by
  intro row hrow
  obtain ⟨hmem, hne⟩ := List.mem_filter.mp hrow
  exact ⟨hfits row hmem, by simpa using hne⟩

theorem positiveSupplies_nodup (rows : List SupplyRow) (h : (rows.map SupplyRow.asset).Nodup) :
    ((positiveSupplies rows).map SupplyRow.asset).Nodup :=
  List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) h

theorem positiveSupplies_keys (rows : List SupplyRow) (a : Asset)
    (h : a ∉ rows.map SupplyRow.asset) : a ∉ (positiveSupplies rows).map SupplyRow.asset := by
  intro hm
  obtain ⟨row, hrow, hrowa⟩ := List.mem_map.mp hm
  exact h (List.mem_map.mpr ⟨row, (List.mem_filter.mp hrow).1, hrowa⟩)

theorem supplyFor_fits (rows : List SupplyRow) (hnodup : (rows.map SupplyRow.asset).Nodup)
    (hfits : ∀ row ∈ rows, FitsU128 row.amountAtoms) (a : Asset) : FitsU128 (supplyFor rows a) := by
  induction rows with
  | nil => exact zero_fits_u128
  | cons r rs ih =>
    rw [List.map_cons] at hnodup
    obtain ⟨hr, hrs⟩ := List.nodup_cons.mp hnodup
    have hfr := hfits r List.mem_cons_self
    have hrest := ih hrs fun x hx => hfits x (List.mem_cons_of_mem _ hx)
    simp only [supplyFor, List.map_cons, List.sum_cons] at hrest ⊢
    by_cases ha : r.asset = a
    · rw [if_pos ha]
      have hzero : supplyFor rs a = 0 := supplyFor_zero_of_absent rs a (ha ▸ hr)
      simp only [supplyFor] at hzero
      rw [hzero]
      simpa using hfr
    · rw [if_neg ha]
      simpa using hrest

theorem frame_owned_supply (d : Digests) (pre : Joint) (u : FrameUpdate)
    (hadm : FrameUpdateAdmitted pre.frame u) : OwnedMatchesSupply (view d (frameSuccessor d pre u)) := by
  intro a
  show amountForAsset u.balances a + amountForAsset pre.frame.custody a +
    amountForAsset pre.frame.reserves a = supplyFor (positiveSupplies u.supplies) a
  by_cases hkey : a ∈ assetKeys pre.frame u
  · exact hadm.2.2.2.2.1 a hkey
  · unfold assetKeys at hkey
    simp only [List.mem_append, not_or] at hkey
    rw [amountForAsset_zero_of_absent _ a hkey.1.1.1, amountForAsset_zero_of_absent _ a hkey.1.1.2,
      amountForAsset_zero_of_absent _ a hkey.1.2,
      supplyFor_zero_of_absent _ a (positiveSupplies_keys _ a hkey.2)]
    rfl

theorem frame_invariant (d : Digests) (pre : Joint) (u : FrameUpdate) (post : Joint)
    (inv : Invariant d pre) (h : frameStep d pre u = some post) : Invariant d post := by
  obtain ⟨hctx, hadm, rfl⟩ := frameStep_some d pre u post h
  obtain ⟨_, _, _, _, hheight, hu64, hreplay⟩ := context_guards d pre.frame u.occurrence hctx
  have hfresh := replayConsumed_false _ _ hreplay
  obtain ⟨hepoch, _, _, _, hsc, hsl, hsr, _, hnc, hnl, hnr, _, htot, htid, hterm, hinj, horacle⟩ :=
    inv.frame.quantities
  have howned := frame_owned_supply d pre u hadm
  refine ⟨inv.margin, ⟨?_, ?_, ?_, howned, ?_⟩, ?_, ?_⟩
  · show (pre.frame.lanes.map (updateLane d (frameAssets pre u) pre.margin)).map LaneRow.laneId =
      allLaneIds
    rw [List.map_map]
    have : LaneRow.laneId ∘ updateLane d (frameAssets pre u) pre.margin = LaneRow.laneId := by
      funext row
      exact updateLane_laneId _ _ _ row
    rw [this]
    exact inv.frame.lanes
  · exact insertReplay_nodup u.occurrence _ inv.frame.replayUnique
  · refine ⟨hepoch, ?_, hadm.2.1, positiveSupplies_sparse _ hadm.2.2.2.1, hsc, hsl, hsr, hadm.1,
      hnc, hnl, hnr, positiveSupplies_nodup _ hadm.2.2.1, ?_, htid, hterm, ?_, ?_⟩
    · show FitsU64 (pre.frame.height + 1)
      unfold FitsU64
      omega
    · intro a
      have hsup : FitsU128 (supplyFor (positiveSupplies u.supplies) a) :=
        supplyFor_fits _ (positiveSupplies_nodup _ hadm.2.2.1)
          (fun row hrow => hadm.2.2.2.1 row (List.mem_filter.mp hrow).1) a
      refine ⟨?_, (htot a).2.1, hsup⟩
      rw [howned a]
      exact hsup
    · exact replayLookup_injective_insert pre.frame.replay u.occurrence hinj hfresh
    · exact oracle_admitted_succ d pre.frame _ rfl rfl horacle
  · exact inv.frame.liabilities
  · obtain ⟨_, hcust, _, hres, hlane⟩ := inv.assetProjection
    refine ⟨rfl, hcust, rfl, hres, ?_⟩
    show laneRow (frameSuccessor d pre u) .assetTransfer = _
    unfold frameSuccessor laneRow
    simp only
    rw [find?_map_laneId _ _ (updateLane_laneId _ _ _) .assetTransfer]
    change (laneRow pre.frame .assetTransfer).map _ = _
    rw [hlane]
    simp only [Option.map_some]
    rw [updateLane_asset _ _ _ _ rfl]
    rfl
  · obtain ⟨hlane, hcust, hcustRows, hliab, hliabRows, hopen, hbind⟩ := inv.marginProjection
    refine ⟨?_, hcust, hcustRows, hliab, hliabRows, hopen, hbind⟩
    show laneRow (frameSuccessor d pre u) .perpsMarket = _
    unfold frameSuccessor laneRow
    simp only
    rw [find?_map_laneId _ _ (updateLane_laneId _ _ _) .perpsMarket]
    change (laneRow pre.frame .perpsMarket).map _ = _
    rw [hlane]
    simp only [Option.map_some]
    rw [updateLane_margin _ _ _ _ rfl]

/-! ## Interleaved histories -/

inductive Input where
  | margin (request : Request)
  | frame (update : FrameUpdate)
  deriving DecidableEq, Repr

def advance (d : Digests) (pre : Joint) : Input → Joint
  | .margin r => advanceMargin d pre r
  | .frame u => (frameStep d pre u).getD pre

def run (d : Digests) (inputs : List Input) (start : Joint) : Joint :=
  inputs.foldl (advance d) start

theorem advance_invariant (d : Digests) (pre : Joint) (input : Input) (inv : Invariant d pre) :
    Invariant d (advance d pre input) := by
  cases input with
  | margin r => exact advanceMargin_invariant d pre r inv
  | frame u =>
    show Invariant d ((frameStep d pre u).getD pre)
    cases h : frameStep d pre u with
    | none => exact inv
    | some post => exact frame_invariant d pre u post inv h

/-- The finite invariant survives every interleaving of margin commands,
rejected attempts and accepted asset-lane frames. -/
theorem run_invariant (d : Digests) (inputs : List Input) (start : Joint) (inv : Invariant d start) :
    Invariant d (run d inputs start) := by
  induction inputs generalizing start with
  | nil => exact inv
  | cons input rest ih =>
    exact ih (advance d start input) (advance_invariant d start input inv)

theorem inactive_terminal_survives_margin (d : Digests) (pre : Joint) (r : Request)
    (inv : Invariant d pre) (id : Identifier) (old : TerminalObligation)
    (record : terminalLookup pre.frame.terminals id = some old) (inactive : old.status ≠ .open) :
    terminalLookup (advanceMargin d pre r).frame.terminals id = some old := by
  unfold advanceMargin
  cases h : step d pre r with
  | error _ => exact record
  | ok acc =>
    obtain ⟨w, rfl⟩ := accepted_witness d pre r acc h
    exact K.inactive_history_preserved _ (invariant_wellFormed d pre inv) w.b (freshClaim d pre r) _
      id old record inactive (w.advance_eq inv)

theorem inactive_terminal_survives (d : Digests) (pre : Joint) (input : Input)
    (inv : Invariant d pre) (id : Identifier) (old : TerminalObligation)
    (record : terminalLookup pre.frame.terminals id = some old) (inactive : old.status ≠ .open) :
    terminalLookup (advance d pre input).frame.terminals id = some old := by
  cases input with
  | margin r => exact inactive_terminal_survives_margin d pre r inv id old record inactive
  | frame u =>
    show terminalLookup ((frameStep d pre u).getD pre).frame.terminals id = some old
    cases h : frameStep d pre u with
    | none => exact record
    | some post =>
      obtain ⟨_, _, rfl⟩ := frameStep_some d pre u post h
      exact record

/-- Drained and tombstoned claims are immutable across every later history:
no refill, transfer or rejected attempt reopens or reassigns them. -/
theorem inactive_terminal_history (d : Digests) (inputs : List Input) (start : Joint)
    (inv : Invariant d start) (id : Identifier) (old : TerminalObligation)
    (record : terminalLookup start.frame.terminals id = some old) (inactive : old.status ≠ .open) :
    terminalLookup (run d inputs start).frame.terminals id = some old := by
  induction inputs generalizing start with
  | nil => exact record
  | cons input rest ih =>
    exact ih (advance d start input) (advance_invariant d start input inv) (inactive_terminal_survives d start input inv id old record inactive)

theorem closed_account_survives_margin (d : Digests) (pre : Joint) (r : Request) (a : Account)
    (hl : lookupAccount a.id pre.margin.market.accounts = some a) (hc : a.closed = true) :
    lookupAccount a.id (advanceMargin d pre r).margin.market.accounts = some a := by
  unfold advanceMargin
  cases h : step d pre r with
  | error _ => exact hl
  | ok acc =>
    obtain ⟨w, rfl⟩ := accepted_witness d pre r acc h
    show lookupAccount a.id w.market.accounts = some a
    obtain ⟨b, hstep, hmat⟩ := T.accepted_market_materialization _ _ _ _ w.hmarket
    rw [hmat]
    by_cases hid : r.command.accountId = a.id
    · exfalso
      rw [hid, hl] at hstep
      exact T.closed_cannot_accept _ _ _ a b hc hstep
    · have hbid : b.id = r.command.accountId := (T.accepted_account_facts _ _ _ _ hstep).1
      rw [T.lookup_put_other b _ a.id (by rw [hbid]; exact Ne.symm hid)]
      exact hl

theorem closed_account_survives (d : Digests) (pre : Joint) (input : Input) (a : Account)
    (hl : lookupAccount a.id pre.margin.market.accounts = some a) (hc : a.closed = true) :
    lookupAccount a.id (advance d pre input).margin.market.accounts = some a := by
  cases input with
  | margin r => exact closed_account_survives_margin d pre r a hl hc
  | frame u =>
    show lookupAccount a.id ((frameStep d pre u).getD pre).margin.market.accounts = some a
    cases h : frameStep d pre u with
    | none => exact hl
    | some post =>
      obtain ⟨_, _, rfl⟩ := frameStep_some d pre u post h
      exact hl

/-- A closed account cannot reopen through any interleaved joint history. -/
theorem closed_account_history (d : Digests) (inputs : List Input) (start : Joint) (a : Account)
    (hl : lookupAccount a.id start.margin.market.accounts = some a) (hc : a.closed = true) :
    lookupAccount a.id (run d inputs start).margin.market.accounts = some a := by
  induction inputs generalizing start with
  | nil => exact hl
  | cons input rest ih =>
    exact ih (advance d start input) (closed_account_survives d start input a hl hc)

/-! ## Terminal-table capacity -/

theorem Witness.terminals_length (w : Witness d pre r) (inv : Invariant d pre) :
    w.terminals.length ≤ pre.frame.terminals.length + 1 ∧
      ((bindingOf pre.margin.bindings w.b.id).isSome = true ∨ w.b.collateral = 0 →
        w.terminals.length = pre.frame.terminals.length) := by
  have hpre : (pre.frame.terminals.map TerminalObligation.obligationId).Nodup :=
    quantities_terminal_ids _ inv.frame.quantities
  have hclaims := w.hclaims
  rw [w.market_asset] at hclaims
  rcases advanceClaims_cases _ _ _ _ _ _ _ hclaims with
    ⟨id, old, hbo, ht, hz, _, hterm⟩ | ⟨id, old, hbo, ht, hz, _, hterm⟩ | ⟨hbo, hz, _, hterm⟩ |
    ⟨hbo, hz, hfresh, _, hterm⟩
  · have hlen : w.terminals.length = pre.frame.terminals.length := by
      rw [hterm, putTerminal_length _ _ hpre]
      have hoid := (terminalLookup_mem _ _ _ ht).2
      simp only [hoid, ht]
      rfl
    exact ⟨by omega, fun _ => hlen⟩
  · have hlen : w.terminals.length = pre.frame.terminals.length := by
      rw [hterm, putTerminal_length _ _ hpre]
      have hoid := (terminalLookup_mem _ _ _ ht).2
      simp only [hoid, ht]
      rfl
    exact ⟨by omega, fun _ => hlen⟩
  · rw [hterm]
    exact ⟨by omega, fun _ => rfl⟩
  · rw [hterm, putTerminal_length _ _ hpre]
    simp only [K.openClaim, hfresh, if_true]
    refine ⟨Nat.le_refl _, ?_⟩
    intro h
    rcases h with h | h
    · rw [hbo] at h
      cases h
    · exact absurd h hz

/-- An accepted step at terminal capacity preserves the terminal count. This
conditional theorem does not establish acceptance or exit availability. -/
theorem capacity_keeps_lifecycle (d : Digests) (pre : Joint) (r : Request) (acc : Accepted)
    (inv : Invariant d pre) (hcap : pre.frame.terminals.length = globalRowCeiling)
    (h : step d pre r = .ok acc) : acc.post.frame.terminals.length = globalRowCeiling := by
  obtain ⟨w, rfl⟩ := accepted_witness d pre r acc h
  have hceil : w.terminals.length ≤ globalRowCeiling := w.hceil.2.2.2.2
  have := (w.terminals_length inv).1
  show w.terminals.length = globalRowCeiling
  rcases w.bindings_cases with ⟨_, hz, _⟩ | ⟨_, _, hsome⟩ | ⟨_, hz, _⟩ | ⟨fresh, _, hz, hnone, hfresh, hterm⟩
  · rw [(w.terminals_length inv).2 (Or.inr hz)]
    exact hcap
  · rw [(w.terminals_length inv).2 (Or.inl hsome)]
    exact hcap
  · rw [(w.terminals_length inv).2 (Or.inr hz)]
    exact hcap
  · exfalso
    have hpre : (pre.frame.terminals.map TerminalObligation.obligationId).Nodup :=
      quantities_terminal_ids _ inv.frame.quantities
    rw [hterm, putTerminal_length _ _ hpre] at hceil
    simp only [K.openClaim, hfresh, if_true] at hceil
    omega

/-- A deposit into an account without an active claim needs a fresh terminal
row, so it is rejected at capacity. -/
theorem refill_blocked_at_capacity (d : Digests) (pre : Joint) (r : Request) (acc : Accepted)
    (inv : Invariant d pre) (hcap : pre.frame.terminals.length = globalRowCeiling)
    (hunbound : bindingOf pre.margin.bindings r.command.accountId = none)
    (hk : r.command.kind = .deposit) : step d pre r ≠ .ok acc := by
  intro h
  obtain ⟨w, rfl⟩ := accepted_witness d pre r acc h
  have hceil : w.terminals.length ≤ globalRowCeiling := w.hceil.2.2.2.2
  have hpre : (pre.frame.terminals.map TerminalObligation.obligationId).Nodup :=
    quantities_terminal_ids _ inv.frame.quantities
  have hpos : w.b.collateral ≠ 0 := by
    have hcoll := w.facts.collateral
    have hzero := w.pre_account_zero inv (by rw [w.facts.id]; exact hunbound)
    have hamount := (w.facts.movement (by simp [hk])).1
    rw [hzero] at hcoll
    simp only [commandDelta, hk] at hcoll
    omega
  rcases w.bindings_cases with ⟨_, hz, _⟩ | ⟨_, _, hsome⟩ | ⟨_, hz, _⟩ | ⟨fresh, _, _, _, hfresh, hterm⟩
  · exact hpos hz
  · rw [w.facts.id, hunbound] at hsome
    cases hsome
  · exact hpos hz
  · rw [hterm, putTerminal_length _ _ hpre] at hceil
    simp only [K.openClaim, hfresh, if_true] at hceil
    omega


/-! ## Decided success witness and negative controls

The scenario uses noncryptographic witnesses for the opaque digest parameters;
general injectivity is not established. The concrete outcome statements in
this section are decided by kernel evaluation of the modeled step. -/

namespace Scenario

set_option maxRecDepth 100000

def nonceSum (m : Margin) : Nat := (m.market.accounts.map Account.nonce).sum
def collateralSum (m : Margin) : Nat := (m.market.accounts.map Account.collateral).sum
def amountSum (rows : List AmountRow) : Nat := (rows.map fun r => r.amountAtoms.toNat).sum

def kindTag : Kind → String
  | .deposit => "d"
  | .withdraw => "w"
  | .close => "c"
  | .unknown => "u"

/-- Noncryptographic scenario digests. These can collide on different states;
only adjacent accepted margin states need separation in `accepted_verified`.
No general digest injectivity or runtime hashing claim follows. -/
def digests : Digests :=
  ⟨fun a => "a" ++ toString (amountSum a.balances) ++ "/" ++ toString a.balances.length ++ "/" ++
      toString (amountSum a.custody),
    fun m => "m" ++ toString (nonceSum m) ++ "/" ++ toString (collateralSum m) ++ "/" ++
      toString m.bindings.length,
    fun f => "g" ++ toString f.height,
    fun c => "b" ++ kindTag c.kind ++ c.accountId ++ c.owner ++ toString c.amount ++ "/" ++
      toString c.nonce,
    fun _ acc occ => "c" ++ acc ++ occ⟩

def usd : Asset := "USD"

def assets0 : Assets :=
  ⟨"ra", [⟨usd, true, false, 8⟩], [⟨"alice", usd, accountsDomain, 100⟩], [⟨usd, 100⟩], []⟩

def market0 : MarketState := ⟨"rm", "mkt", usd, 100000000, 500, 100, 1000000, .active, []⟩

def margin0 : Margin := ⟨market0, []⟩

def lanes (assets : Assets) (margin : Margin) : List LaneRow :=
  allLaneIds.map fun lane =>
    match lane with
    | .assetTransfer => ⟨.assetTransfer, "ra", true, digests.assetRoot assets⟩
    | .perpsMarket => ⟨.perpsMarket, "rm", true, digests.marginRoot margin⟩
    | other => ⟨other, "0", false, "0"⟩

def frame0 : Frame :=
  ⟨"ch", "dp", 7, 0, "pf", lanes assets0 margin0, assets0.balances, [⟨usd, 100⟩], [], [], [], [],
    [], [], "0", []⟩

def start : Joint := ⟨assets0, margin0, frame0⟩

def command (kind : Kind) (account owner : String) (amount nonce : Nat) : Command :=
  ⟨kind, account, "mkt", owner, usd, amount, nonce⟩

def occurrence (height : Nat) (subject : String) (c : Command) : Occurrence :=
  ⟨"o" ++ toString height, "r" ++ toString height, "ch", "dp", "pf", "g" ++ toString (height - 1),
    height, subject, c.kind, digests.bodyHash c, []⟩

def request (height : Nat) (kind : Kind) (account : String) (amount nonce : Nat) : Request :=
  let c := command kind account "alice" amount nonce
  ⟨c, occurrence height "alice" c, none⟩

/-- Alice pays Bob 20 through the existing asset lane between margin episodes. -/
def transfer (height : Nat) : FrameUpdate :=
  ⟨[⟨"alice", usd, accountsDomain, 55⟩, ⟨"bob", usd, accountsDomain, 20⟩], [⟨usd, 100⟩],
    occurrence height "alice" (command .deposit "x" "alice" 0 0)⟩

/-- Deposit, same-owner second account at nonce 1, partial withdrawal, drain,
transfer, refill, drain, close, then a rejected reopen attempt. -/
def history : List Input :=
  [.margin (request 1 .deposit "acc-a" 25 1), .margin (request 2 .deposit "acc-b" 25 1),
    .margin (request 3 .withdraw "acc-a" 10 2), .margin (request 4 .withdraw "acc-a" 15 3),
    .frame (transfer 5), .margin (request 6 .deposit "acc-a" 20 4),
    .margin (request 7 .withdraw "acc-a" 20 5), .margin (request 8 .close "acc-a" 0 6),
    .margin (request 9 .deposit "acc-a" 1 7)]

def stage (n : Nat) : Joint := run digests (history.take n) start

def final : Joint := run digests history start

theorem history_accepted :
    [(step digests (stage 0) (request 1 .deposit "acc-a" 25 1)).toBool,
      (step digests (stage 1) (request 2 .deposit "acc-b" 25 1)).toBool,
      (step digests (stage 2) (request 3 .withdraw "acc-a" 10 2)).toBool,
      (step digests (stage 3) (request 4 .withdraw "acc-a" 15 3)).toBool,
      (frameStep digests (stage 4) (transfer 5)).isSome,
      (step digests (stage 5) (request 6 .deposit "acc-a" 20 4)).toBool,
      (step digests (stage 6) (request 7 .withdraw "acc-a" 20 5)).toBool,
      (step digests (stage 7) (request 8 .close "acc-a" 0 6)).toBool] =
    List.replicate 8 true := by decide

theorem closed_reopen_rejected :
    step digests (stage 8) (request 9 .deposit "acc-a" 1 7) = .error (.margin .accountClosed) ∧
      final = stage 8 := by decide

/-- Same owner, equal collateral, equal account nonce: two custody coordinates
and two distinct claims, one aggregated owner liability. -/
theorem same_owner_accounts_distinct :
    (stage 2).margin.bindings = [⟨"acc-a", "cacc-ao1"⟩, ⟨"acc-b", "cacc-bo2"⟩] ∧
      (stage 2).frame.custody = [⟨"acc-a", usd, marginDomain, 25⟩, ⟨"acc-b", usd, marginDomain, 25⟩] ∧
      (stage 2).frame.liabilities = [⟨"alice", usd, marginDomain, 50⟩] ∧
      (stage 2).margin.market.accounts.map Account.nonce = [1, 1] := by decide

theorem final_projection :
    final.margin.market.accounts.map (fun a => (a.id, a.owner, a.collateral, a.nonce, a.closed)) =
        [("acc-a", "alice", 0, 6, true), ("acc-b", "alice", 25, 1, false)] ∧
      final.frame.terminals.map (fun t => (t.obligationId, t.claimant, t.amountAtoms, t.status)) =
        [("cacc-ao1", "alice", 15, .drained), ("cacc-ao6", "alice", 20, .drained),
          ("cacc-bo2", "alice", 25, .open)] ∧
      final.frame.balances = [⟨"alice", usd, accountsDomain, 55⟩, ⟨"bob", usd, accountsDomain, 20⟩] ∧
      final.frame.custody = [⟨"acc-b", usd, marginDomain, 25⟩] ∧
      final.frame.liabilities = [⟨"alice", usd, marginDomain, 25⟩] ∧
      final.frame.supplies = [⟨usd, 100⟩] ∧
      final.margin.bindings = [⟨"acc-b", "cacc-bo2"⟩] ∧
      final.frame.replay.length = 8 ∧ final.frame.height = 8 := by decide

theorem start_market_admitted : MarketAdmitted market0 := by
  refine ⟨by unfold T.OrderedAccounts; decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_, by decide, by decide, by decide⟩
  intro a ha
  cases ha

theorem start_quantities : StateQuantitiesAdmitted (view digests frame0) := by
  refine ⟨by unfold FitsU64 maxU64; decide, by unfold FitsU64 maxU64; decide, ?_, ?_, ?_, ?_, ?_,
    by decide, by decide, by decide, by decide, by decide, ?_, by decide, ?_, ?_, ⟨?_, ?_⟩⟩
  · intro row hrow
    simp only [view, frame0, assets0, List.mem_singleton] at hrow
    subst hrow
    simp [FitsU128, maxU128]
  · intro row hrow
    simp only [view, frame0, List.mem_singleton] at hrow
    subst hrow
    simp [FitsU128, maxU128]
  · intro row hrow
    simp [view, frame0] at hrow
  · intro row hrow
    simp [view, frame0] at hrow
  · intro row hrow
    simp [view, frame0] at hrow
  · intro a
    simp only [view, ownedFor, liabilityFor, amountForAsset, supplyFor, frame0, assets0, List.map,
      List.sum_cons, List.sum_nil, FitsU128, maxU128]
    split <;> omega
  · intro row hrow
    simp [view, frame0] at hrow
  · intro left right occ hleft
    simp [view, replayLookup, lookupKey, frame0] at hleft
  · intro id occ hocc
    simp [view, lookupKey, frame0] at hocc
  · intro id occ hocc
    simp [view, lookupKey, frame0] at hocc

theorem start_invariant : Invariant digests start := by
  refine ⟨⟨start_market_admitted, by decide, by decide, ?_, ?_⟩,
    ⟨by decide, by decide, start_quantities, ?_, ⟨?_, ?_⟩⟩, by decide, by decide⟩
  · intro a ha
    cases ha
  · intro b hb
    cases hb
  · intro a
    simp only [view, ownedFor, amountForAsset, supplyFor, start, frame0, assets0, List.map,
      List.sum_cons, List.sum_nil]
    split <;> omega
  · intro a dm
    simp [view, amountForAssetDomain, start, frame0]
  · intro o a dm
    simp [view, openTerminalAmountFor, amountAt, start, frame0]

theorem final_invariant : Invariant digests final :=
  run_invariant digests history start start_invariant

theorem drained_claims_immutable :
    terminalLookup final.frame.terminals "cacc-ao1" =
        some ⟨"cacc-ao1", .perpsMarket, "alice", usd, marginDomain, 15, .drained⟩ ∧
      terminalLookup final.frame.terminals "cacc-ao6" =
        some ⟨"cacc-ao6", .perpsMarket, "alice", usd, marginDomain, 20, .drained⟩ := by decide

/-! ### Negative controls -/

def steal : Request :=
  ⟨command .withdraw "acc-a" "alice" 5 2,
    occurrence 3 "mallory" (command .withdraw "acc-a" "alice" 5 2), none⟩

def foreignOwner : Request :=
  ⟨command .withdraw "acc-a" "mallory" 5 2,
    occurrence 3 "mallory" (command .withdraw "acc-a" "mallory" 5 2), none⟩

/-- A conserving withdrawal signed by the wrong subject, and one naming a
foreign owner, both reject exactly. -/
theorem unauthorized_conserving_movement_rejected :
    step digests (stage 2) steal = .error (.margin .unauthorizedSubject) ∧
      advanceMargin digests (stage 2) steal = stage 2 ∧
      step digests (stage 2) foreignOwner = .error (.margin .accountOwnerMismatch) := by decide

/-- Per-account instead of per-owner liability rows fail the projection. -/
theorem omitted_owner_aggregation_fails_projection :
    ¬ MarginProjection digests (stage 2).margin
      { (stage 2).frame with
        liabilities := [⟨"acc-a", usd, marginDomain, 25⟩, ⟨"acc-b", usd, marginDomain, 25⟩] } ∧
    ¬ MarginProjection digests (stage 2).margin
      { (stage 2).frame with liabilities := [⟨"alice", usd, marginDomain, 25⟩] } := by decide

/-- A drained record reopened in place is an open claim without a binding. -/
theorem reopened_drained_claim_fails_projection :
    ¬ MarginProjection digests (stage 4).margin
      { (stage 4).frame with
        terminals := [⟨"cacc-ao1", .perpsMarket, "alice", usd, marginDomain, 15, .open⟩,
          ⟨"cacc-bo2", .perpsMarket, "alice", usd, marginDomain, 25, .open⟩] } := by decide

/-- A refill whose derived claim identifier collides with the drained record
is rejected instead of reusing the terminal row. -/
theorem refill_with_reused_claim_rejected :
    step { digests with claimId := fun _ _ _ => "cacc-ao1" } (stage 5)
      (request 6 .deposit "acc-a" 20 4) = .error .successorRejected := by decide

def changedBalances : List AmountRow := [⟨"alice", usd, accountsDomain, 49⟩]

def changedAssetsOnly : Joint :=
  ⟨{ (stage 2).assets with balances := changedBalances }, (stage 2).margin, (stage 2).frame⟩

def changedFrameOnly : Joint :=
  ⟨(stage 2).assets, (stage 2).margin, { (stage 2).frame with balances := changedBalances }⟩

def changedBoth : Joint :=
  ⟨{ (stage 2).assets with balances := changedBalances }, (stage 2).margin,
    { (stage 2).frame with balances := changedBalances }⟩

/-- Changed physical tables with the old asset root, in three shapes: lane
tables changed alone, global tables changed alone, both changed consistently
but the committed root retained. -/
theorem changed_tables_with_old_asset_root_rejected :
    step digests changedAssetsOnly (request 3 .withdraw "acc-a" 10 2) = .error .projectionMismatch ∧
      step digests changedFrameOnly (request 3 .withdraw "acc-a" 10 2) = .error .projectionMismatch ∧
      step digests changedBoth (request 3 .withdraw "acc-a" 10 2) = .error .projectionMismatch := by
  decide

def consumedMutant : Joint :=
  ⟨(stage 8).assets, (stage 8).margin,
    { (stage 8).frame with
      replay := insertReplay (request 9 .deposit "acc-a" 1 7).occurrence (stage 8).frame.replay }⟩

/-- Rejection consumes neither the account nonce nor a replay row; a mutant
that did would be a different state. -/
theorem rejection_consumes_nothing :
    advance digests (stage 8) (.margin (request 9 .deposit "acc-a" 1 7)) = stage 8 ∧
      (stage 8).margin.market.accounts.map Account.nonce = [6, 1] ∧
      (stage 8).frame.replay.length = 8 ∧ consumedMutant ≠ stage 8 := by decide

def bigAssets : Assets :=
  ⟨"ra", [⟨usd, true, false, 8⟩], [⟨"alice", usd, accountsDomain, maxU128⟩], [⟨usd, maxU128⟩], []⟩

def bigStart : Joint :=
  ⟨bigAssets, margin0,
    ⟨"ch", "dp", 7, 0, "pf", lanes bigAssets margin0, bigAssets.balances, [⟨usd, maxU128⟩], [], [],
      [], [], [], [], "0", []⟩⟩

def topStart : Joint := ⟨assets0, margin0, { frame0 with height := 2 ^ 64 - 1 }⟩

def topOccurrence : Occurrence := occurrence (2 ^ 64) "alice" (command .deposit "acc-a" "alice" 1 1)

def topRequest : Request :=
  ⟨command .deposit "acc-a" "alice" 1 1,
    { topOccurrence with preStateRoot := digests.globalRoot topStart.frame }, none⟩

/-- Finite-width neighbors: the largest admissible delta is accepted from a
maximal balance row; one atom more is the kernel's delta overflow; a balance
short of the amount is the producer's balance guard; the maximal u64 height
cannot be advanced. -/
theorem width_neighbors :
    (step digests bigStart (request 1 .deposit "acc-a" (2 ^ 127 - 1) 1)).toBool = true ∧
      step digests bigStart (request 1 .deposit "acc-a" (2 ^ 127) 1) =
        .error (.margin .effectDeltaOverflow) ∧
      step digests start (request 1 .deposit "acc-a" 101 1) = .error .insufficientBalance ∧
      step digests topStart topRequest = .error .occurrenceContextMismatch := by decide

end Scenario

end ZenoDEX.PerpsMarginGlobalV2
