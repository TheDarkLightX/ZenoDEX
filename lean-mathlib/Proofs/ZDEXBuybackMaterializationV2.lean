import Proofs.ZDEXAcquisitionBurnOccurrenceV2

/-!
Exact keyed accounting for the V2 buyback materializers. Effect identity includes
kind as well as principal, asset and custody domain. Fee-allocation rows remain
distinct from their physical custody mirrors. Coalescing and zero removal retain
every keyed signed sum; sorting is represented by permutation.

The executable model uses mathematical integers. Runtime i128 guards can reject
an intermediate prefix even when the final sum fits. Accepted-runtime/model
correspondence is tested on a finite corpus, not proved universally here.
Leaf ownership, receipt/terminal binding, canonical bytes, hash injectivity,
Python/Rust refinement, cryptography and publication authority are nonclaims.
-/
namespace Proofs.ZDEXBuybackMaterializationV2

open Proofs.ZDEXAcquisitionBurnOccurrenceV2

abbrev EffectKey := Kind × Key

def effectKey (row : Row) : EffectKey := (row.kind, row.key)

def keyedDelta (key : EffectKey) : Plan → Int
  | [] => 0
  | row :: rows => (if effectKey row = key then row.delta else 0) + keyedDelta key rows

def insertRow (row : Row) : Plan → Plan
  | [] => [row]
  | head :: tail =>
      if effectKey head = effectKey row then
        { head with delta := head.delta + row.delta } :: tail
      else head :: insertRow row tail

def coalesce : Plan → Plan
  | [] => []
  | row :: rows => insertRow row (coalesce rows)

def elideZero : Plan → Plan
  | [] => []
  | row :: rows => if row.delta = 0 then elideZero rows else row :: elideZero rows

def normalize (rows : Plan) : Plan := elideZero (coalesce rows)

theorem keyedDelta_append (key : EffectKey) (left right : Plan) :
    keyedDelta key (left ++ right) = keyedDelta key left + keyedDelta key right := by
  induction left with
  | nil => simp only [List.nil_append, keyedDelta, Int.zero_add]
  | cons row rows ih => simp only [List.cons_append, keyedDelta, ih]; omega

theorem keyedDelta_insertRow (key : EffectKey) (row : Row) (rows : Plan) :
    keyedDelta key (insertRow row rows) = keyedDelta key [row] + keyedDelta key rows := by
  induction rows with
  | nil => simp only [insertRow, keyedDelta, Int.add_zero]
  | cons head tail ih =>
      by_cases merge : effectKey head = effectKey row
      · rw [insertRow, if_pos merge]
        change (if effectKey head = key then head.delta + row.delta else 0) +
            keyedDelta key tail =
          ((if effectKey row = key then row.delta else 0) + 0) +
            ((if effectKey head = key then head.delta else 0) + keyedDelta key tail)
        rw [merge]
        split <;> omega
      · simp only [insertRow, if_neg merge, keyedDelta] at *
        rw [ih]
        omega

theorem keyedDelta_coalesce (key : EffectKey) (rows : Plan) :
    keyedDelta key (coalesce rows) = keyedDelta key rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rw [coalesce, keyedDelta_insertRow, ih]
      simp only [keyedDelta, Int.add_zero]

theorem keyedDelta_elideZero (key : EffectKey) (rows : Plan) :
    keyedDelta key (elideZero rows) = keyedDelta key rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases zero : row.delta = 0
      · simp [elideZero, zero, keyedDelta, ih]
      · simp only [elideZero, if_neg zero, keyedDelta, ih]

theorem keyedDelta_normalize (key : EffectKey) (rows : Plan) :
    keyedDelta key (normalize rows) = keyedDelta key rows := by
  rw [normalize, keyedDelta_elideZero, keyedDelta_coalesce]

theorem mem_insertRow_keys (key : EffectKey) (row : Row) (rows : Plan) :
    key ∈ (insertRow row rows).map effectKey ↔
      key = effectKey row ∨ key ∈ rows.map effectKey := by
  induction rows with
  | nil => simp [insertRow]
  | cons head tail ih =>
      by_cases merge : effectKey head = effectKey row
      · simp only [insertRow, if_pos merge, List.map_cons, List.mem_cons]
        change key = effectKey head ∨ key ∈ tail.map effectKey ↔
          key = effectKey row ∨ key = effectKey head ∨ key ∈ tail.map effectKey
        rw [merge]
        simp
      · simp only [insertRow, if_neg merge, List.map_cons, List.mem_cons, ih]
        exact or_left_comm

theorem unique_keys_insertRow (row : Row) (rows : Plan)
    (unique : (rows.map effectKey).Nodup) :
    ((insertRow row rows).map effectKey).Nodup := by
  induction rows with
  | nil => simp [insertRow]
  | cons head tail ih =>
      have parts := List.nodup_cons.mp unique
      by_cases merge : effectKey head = effectKey row
      · rw [insertRow, if_pos merge]
        exact unique
      · rw [insertRow, if_neg merge, List.map_cons]
        apply List.nodup_cons.mpr
        constructor
        · intro present
          rcases (mem_insertRow_keys _ _ _).mp present with same | inTail
          · exact merge same
          · exact parts.1 inTail
        · exact ih parts.2

theorem unique_keys_coalesce (rows : Plan) :
    ((coalesce rows).map effectKey).Nodup := by
  induction rows with
  | nil => simp [coalesce]
  | cons row rows ih => exact unique_keys_insertRow row (coalesce rows) ih

theorem unique_keys_elideZero (rows : Plan) (unique : (rows.map effectKey).Nodup) :
    ((elideZero rows).map effectKey).Nodup := by
  induction rows with
  | nil => simp [elideZero]
  | cons row rows ih =>
      have parts := List.nodup_cons.mp unique
      by_cases zero : row.delta = 0
      · simpa [elideZero, zero] using ih parts.2
      · simp only [elideZero, if_neg zero, List.map_cons]
        apply List.nodup_cons.mpr
        refine ⟨?_, ih parts.2⟩
        intro present
        apply parts.1
        rcases List.mem_map.mp present with ⟨other, member, same⟩
        have subset : ∀ (xs : Plan) (r : Row), r ∈ elideZero xs → r ∈ xs := by
          intro xs r
          induction xs with
          | nil => simp [elideZero]
          | cons h t ih =>
              by_cases hz : h.delta = 0
              · simpa [elideZero, hz] using fun m => List.mem_cons_of_mem h (ih m)
              · simp only [elideZero, if_neg hz, List.mem_cons]
                exact Or.imp_right ih
        exact List.mem_map.mpr ⟨other, subset rows other member, same⟩

theorem normalized_keys_unique (rows : Plan) :
    ((normalize rows).map effectKey).Nodup :=
  unique_keys_elideZero (coalesce rows) (unique_keys_coalesce rows)

theorem elideZero_nonzero (rows : Plan) (row : Row) (member : row ∈ elideZero rows) :
    row.delta ≠ 0 := by
  induction rows with
  | nil => simp [elideZero] at member
  | cons head tail ih =>
      by_cases zero : head.delta = 0
      · exact ih (by simpa [elideZero, zero] using member)
      · simp only [elideZero, if_neg zero, List.mem_cons] at member
        rcases member with same | rest
        · simpa [same] using zero
        · exact ih rest

theorem keyedDelta_of_absent (key : EffectKey) (rows : Plan)
    (absent : key ∉ rows.map effectKey) : keyedDelta key rows = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have parts : key ≠ effectKey row ∧ key ∉ rows.map effectKey := by
        simpa only [List.map_cons, List.mem_cons, not_or] using absent
      simp only [keyedDelta, if_neg (Ne.symm parts.1), ih parts.2, Int.zero_add]

theorem unique_member_delta (rows : Plan) (row : Row)
    (unique : (rows.map effectKey).Nodup) (member : row ∈ rows) :
    keyedDelta (effectKey row) rows = row.delta := by
  induction rows with
  | nil => simp at member
  | cons head tail ih =>
      have parts := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | rest
      · subst row
        simp only [keyedDelta, ↓reduceIte, keyedDelta_of_absent _ _ parts.1, Int.add_zero]
      · have different : effectKey head ≠ effectKey row := by
          intro same
          exact parts.1 (same ▸ List.mem_map.mpr ⟨row, rest, rfl⟩)
        simp only [keyedDelta, if_neg different, ih parts.2 rest, Int.zero_add]

theorem normalized_zero_key_absent (rows : Plan) (row : Row)
    (zero : keyedDelta (effectKey row) (normalize rows) = 0) :
    row ∉ normalize rows := by
  intro member
  have delta := unique_member_delta (normalize rows) row (normalized_keys_unique rows) member
  exact elideZero_nonzero (coalesce rows) row member (delta.symm.trans zero)

theorem keyedDelta_perm (key : EffectKey) {rows other : Plan} (h : rows.Perm other) :
    keyedDelta key rows = keyedDelta key other := by
  induction h with
  | nil => rfl
  | cons row _ ih => simp only [keyedDelta, ih]
  | swap a b rows => simp only [keyedDelta]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def mirrorFees : Plan → Plan
  | [] => []
  | row :: rows =>
      if row.kind = .feeAllocation then
        row :: { row with kind := .custody } :: mirrorFees rows
      else row :: mirrorFees rows

theorem fee_mirror_custody_delta (key : Key) (rows : Plan) :
    keyedDelta (.custody, key) (mirrorFees rows) =
      keyedDelta (.custody, key) rows + keyedDelta (.feeAllocation, key) rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rcases row with ⟨kind, rowKey, delta⟩
      cases kind <;> by_cases same : rowKey = key <;>
        simp [mirrorFees, keyedDelta, effectKey, same, ih] <;> omega

theorem fee_mirror_preserves_non_custody (kind : Kind) (key : Key) (rows : Plan)
    (notCustody : kind ≠ .custody) :
    keyedDelta (kind, key) (mirrorFees rows) = keyedDelta (kind, key) rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases fee : row.kind = .feeAllocation
      · simp [mirrorFees, fee, keyedDelta, effectKey, Ne.symm notCustody, ih]
      · simp only [mirrorFees, if_neg fee, keyedDelta, ih]

def materializeFees (rows : Plan) : Plan := normalize (mirrorFees rows)

theorem materialized_custody_exact (key : Key) (rows : Plan) :
    keyedDelta (.custody, key) (materializeFees rows) =
      keyedDelta (.custody, key) rows + keyedDelta (.feeAllocation, key) rows := by
  rw [materializeFees, keyedDelta_normalize, fee_mirror_custody_delta]

theorem materialized_fee_allocation_is_separate (key : Key) (rows : Plan) :
    keyedDelta (.feeAllocation, key) (materializeFees rows) =
      keyedDelta (.feeAllocation, key) rows := by
  rw [materializeFees, keyedDelta_normalize]
  exact fee_mirror_preserves_non_custody .feeAllocation key rows (by decide)

structure LanePlan where
  rows : Plan
  occurrences : List Nat
  deriving DecidableEq, Repr

def compose (spot tokenomics : LanePlan) : LanePlan where
  rows := normalize (spot.rows ++ tokenomics.rows)
  occurrences := tokenomics.occurrences

def admissibleOccurrence (occurrence : Nat) (spot tokenomics : LanePlan) : Bool :=
  decide (spot.occurrences = [] ∧ tokenomics.occurrences = [occurrence])

theorem composed_keyed_delta (key : EffectKey) (spot tokenomics : LanePlan) :
    keyedDelta key (compose spot tokenomics).rows =
      keyedDelta key spot.rows + keyedDelta key tokenomics.rows := by
  rw [compose, keyedDelta_normalize, keyedDelta_append]

theorem admitted_occurrence_consumed_once (occurrence : Nat) (spot tokenomics : LanePlan)
    (admitted : admissibleOccurrence occurrence spot tokenomics = true) :
    (compose spot tokenomics).occurrences = [occurrence] ∧
      (compose spot tokenomics).occurrences.length = 1 := by
  have h : spot.occurrences = [] ∧ tokenomics.occurrences = [occurrence] := by
    simpa only [admissibleOccurrence, decide_eq_true_eq] using admitted
  simp only [compose, h.2, List.length_singleton, and_self]

/-! The existing route model provides the leaf ownership shape. Normalization
now preserves its full keyed footprint, beyond per-asset conservation. -/
theorem normalized_route_zdex_footprint
    (poolId gross purchased burned fee allocation otherAllocations residue spend tag : Nat)
    (kind : Kind) (key : Key) (assetBound : key.asset = zdexAsset) :
    keyedDelta (kind, key)
      (normalize (routePlan poolId gross purchased burned fee allocation
        otherAllocations residue spend tag)) =
      (if (kind, key) = (.custody, poolZdexKey poolId) then -(purchased : Int) else 0) +
      (if (kind, key) = (.burn, zdexSupplyKey) then -(burned : Int) else 0) := by
  rw [keyedDelta_normalize]
  rcases key with ⟨principal, asset, domain⟩
  dsimp only at assetBound
  subst asset
  cases kind <;>
    simp [routePlan, acquisitionLeg, burnLeg, keyedDelta, effectKey,
      poolQuoteKey, poolZdexKey, zdexSupplyKey, feeIngressKey, buybackReserveKey,
      feeSinkKey, feeResidueKey, zdexAsset, quoteAsset, eq_comm]

theorem normalized_route_no_foreign_zdex_key
    (poolId gross purchased burned fee allocation otherAllocations residue spend tag : Nat)
    (kind : Kind) (key : Key) (assetBound : key.asset = zdexAsset)
    (notPool : (kind, key) ≠ (.custody, poolZdexKey poolId))
    (notSupply : (kind, key) ≠ (.burn, zdexSupplyKey)) :
    keyedDelta (kind, key)
      (normalize (routePlan poolId gross purchased burned fee allocation
        otherAllocations residue spend tag)) = 0 := by
  rw [normalized_route_zdex_footprint _ _ _ _ _ _ _ _ _ _ _ _ assetBound,
    if_neg notPool, if_neg notSupply, Int.add_zero]

theorem normalized_route_no_foreign_zdex_row
    (poolId gross purchased burned fee allocation otherAllocations residue spend tag : Nat)
    (row : Row) (assetBound : row.key.asset = zdexAsset)
    (notPool : effectKey row ≠ (.custody, poolZdexKey poolId))
    (notSupply : effectKey row ≠ (.burn, zdexSupplyKey)) :
    row ∉ normalize (routePlan poolId gross purchased burned fee allocation
      otherAllocations residue spend tag) := by
  apply normalized_zero_key_absent
  exact normalized_route_no_foreign_zdex_key _ _ _ _ _ _ _ _ _ _ _ _
    assetBound notPool notSupply

/-! This terminal model makes matching identities and acquired/burned amounts
explicit; those data are not cryptographic witnesses. Other runtime receipt,
context, profile, lane-write, and state checks remain outside this constructor. -/
structure TerminalPair where
  occurrence : Nat
  spotOccurrence : Nat
  burnOccurrence : Nat
  terminal : Nat
  discharged : Nat
  spotPool : Nat
  burnPool : Nat
  acquired : Nat
  reportedAcquired : Nat
  burned : Nat
  deriving DecidableEq, Repr

def terminalMatches (pair : TerminalPair) : Bool := decide (
  pair.spotOccurrence = pair.occurrence ∧ pair.burnOccurrence = pair.occurrence ∧
  pair.discharged = pair.terminal ∧ pair.burnPool = pair.spotPool ∧
  pair.reportedAcquired = pair.acquired ∧ pair.burned = pair.acquired ∧ 0 < pair.acquired)

def boundRoute (pair : TerminalPair)
    (gross fee allocation otherAllocations residue spend tag : Nat) : Option LanePlan :=
  if terminalMatches pair then some {
    rows := normalize (routePlan pair.spotPool gross pair.acquired pair.burned
      fee allocation otherAllocations residue spend tag)
    occurrences := [pair.occurrence] }
  else none

theorem accepted_bound_route_exact_footprint
    (pair : TerminalPair) (gross fee allocation otherAllocations residue spend tag : Nat)
    (plan : LanePlan)
    (accepted : boundRoute pair gross fee allocation otherAllocations residue spend tag = some plan)
    (kind : Kind) (key : Key) (assetBound : key.asset = zdexAsset) :
    keyedDelta (kind, key) plan.rows =
      (if (kind, key) = (.custody, poolZdexKey pair.spotPool) then -(pair.acquired : Int) else 0) +
      (if (kind, key) = (.burn, zdexSupplyKey) then -(pair.acquired : Int) else 0) ∧
    plan.occurrences = [pair.occurrence] ∧ pair.burnPool = pair.spotPool ∧
    pair.discharged = pair.terminal ∧ pair.burnOccurrence = pair.spotOccurrence := by
  unfold boundRoute at accepted
  split at accepted
  next admitted =>
    have boundFacts : pair.spotOccurrence = pair.occurrence ∧
        pair.burnOccurrence = pair.occurrence ∧ pair.discharged = pair.terminal ∧
        pair.burnPool = pair.spotPool ∧ pair.reportedAcquired = pair.acquired ∧
        pair.burned = pair.acquired ∧ 0 < pair.acquired := by
      simpa only [terminalMatches, decide_eq_true_eq] using admitted
    cases accepted
    refine ⟨?_, rfl, boundFacts.2.2.2.1, boundFacts.2.2.1, boundFacts.2.1.trans boundFacts.1.symm⟩
    rw [normalized_route_zdex_footprint _ _ _ _ _ _ _ _ _ _ _ _ assetBound,
      boundFacts.2.2.2.2.2.1]
  next rejected => contradiction

def witnessPair : TerminalPair := ⟨42, 42, 42, 19, 19, 7, 7, 111, 111, 111⟩

theorem matching_terminal_is_nonvacuous :
    (boundRoute witnessPair 125 125 25 67 33 125 9).isSome = true ∧
    boundRoute {witnessPair with discharged := 20} 125 125 25 67 33 125 9 = none ∧
    boundRoute {witnessPair with burnPool := 8} 125 125 25 67 33 125 9 = none ∧
    boundRoute {witnessPair with spotOccurrence := 43} 125 125 25 67 33 125 9 = none ∧
    boundRoute {witnessPair with burnOccurrence := 43} 125 125 25 67 33 125 9 = none ∧
    boundRoute {witnessPair with reportedAcquired := 110} 125 125 25 67 33 125 9 = none ∧
    boundRoute {witnessPair with acquired := 0, reportedAcquired := 0, burned := 0}
      125 125 25 67 33 125 9 = none ∧
    boundRoute {witnessPair with burned := 110} 125 125 25 67 33 125 9 = none := by decide

def witnessKey : Key := ⟨.feeBuyback, quoteAsset, protocolBuybackDomain⟩

theorem mirror_netting_preserves_distinct_effect_kinds :
    keyedDelta (.custody, witnessKey) (materializeFees
      [⟨.feeAllocation, witnessKey, 7⟩, ⟨.custody, witnessKey, -7⟩]) = 0 ∧
    keyedDelta (.feeAllocation, witnessKey) (materializeFees
      [⟨.feeAllocation, witnessKey, 7⟩, ⟨.custody, witnessKey, -7⟩]) = 7 := by
  decide

theorem distinct_domains_do_not_net :
    (normalize [⟨.custody, ⟨.feeBuyback, quoteAsset, 1⟩, 7⟩,
      ⟨.custody, ⟨.feeBuyback, quoteAsset, 2⟩, -7⟩]).length = 2 := by decide

theorem positive_route_and_occurrence_witness :
    keyedDelta (.custody, poolZdexKey 7)
      (normalize (routePlan 7 125 111 111 125 25 67 33 125 9)) = -111 ∧
    keyedDelta (.burn, zdexSupplyKey)
      (normalize (routePlan 7 125 111 111 125 25 67 33 125 9)) = -111 ∧
    admissibleOccurrence 42 ⟨acquisitionLeg 7 125 111, []⟩
      ⟨burnLeg 111 125 25 67 33 125 9, [42]⟩ = true ∧
    admissibleOccurrence 42 ⟨[], []⟩ ⟨[], [42, 42]⟩ = false ∧
    admissibleOccurrence 42 ⟨[], []⟩ ⟨[], [43]⟩ = false := by decide

end Proofs.ZDEXBuybackMaterializationV2
