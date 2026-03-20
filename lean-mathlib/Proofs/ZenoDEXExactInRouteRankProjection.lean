import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.NodupEquivFin
import Proofs.ZenoDEXExactInRouteCertificate

open scoped Classical

namespace TauSwap
namespace Routing
namespace ExactInRouteRankProjection

open ExactInRouteCertificate

variable {α : Type} [LinearOrder α]

/-- The Lean model of the Python `sorted(set(keys))` projection. -/
def orderedUniqueKeys (keys : List α) : List α :=
  keys.toFinset.sort

/-- The rank assigned by the sorted unique key projection. -/
def rankOf (keys : List α) (k : α) : Nat :=
  (orderedUniqueKeys keys).idxOf k

/-- True semantic route-key order before projection. -/
def trueKeyLe (keys : List α) (i j : Fin keys.length) : Prop :=
  keys.get i < keys.get j ∨ (keys.get i = keys.get j ∧ i.1 ≤ j.1)

/-- The ranked candidate surface consumed by the exact-in certificate shell. -/
def projectedCandidate (keys : List α) (i : Fin keys.length) : Candidate :=
  {
    candidateIndex := i.1
    routeKeyRank := rankOf keys (keys.get i)
  }

theorem mem_orderedUniqueKeys_iff {keys : List α} {k : α} :
    k ∈ orderedUniqueKeys keys ↔ k ∈ keys := by
  simp [orderedUniqueKeys]

theorem sortedLT_orderedUniqueKeys (keys : List α) :
    (orderedUniqueKeys keys).SortedLT := by
  simpa [orderedUniqueKeys] using (Finset.sortedLT_sort (s := keys.toFinset))

theorem rankOf_eq_iff_eq {keys : List α} {a b : α}
    (ha : a ∈ keys) (hb : b ∈ keys) :
    rankOf keys a = rankOf keys b ↔ a = b := by
  let l := orderedUniqueKeys keys
  have ha' : a ∈ l := (mem_orderedUniqueKeys_iff (keys := keys) (k := a)).2 ha
  have hb' : b ∈ l := (mem_orderedUniqueKeys_iff (keys := keys) (k := b)).2 hb
  constructor
  · intro h
    exact (List.idxOf_inj (l := l) (x := a) (y := b) ha').1 <| by
      simpa [rankOf, l] using h
  · intro h
    subst b
    rfl

theorem rankOf_lt_rankOf_of_lt {keys : List α} {a b : α}
    (ha : a ∈ keys) (hb : b ∈ keys) (hab : a < b) :
    rankOf keys a < rankOf keys b := by
  let l := orderedUniqueKeys keys
  have hSorted : l.SortedLT := by
    simpa [l] using sortedLT_orderedUniqueKeys keys
  have ha' : a ∈ l := (mem_orderedUniqueKeys_iff (keys := keys) (k := a)).2 ha
  have hb' : b ∈ l := (mem_orderedUniqueKeys_iff (keys := keys) (k := b)).2 hb
  have hia : l.idxOf a < l.length := List.idxOf_lt_length_iff.2 ha'
  have hib : l.idxOf b < l.length := List.idxOf_lt_length_iff.2 hb'
  have hget : l[l.idxOf a] < l[l.idxOf b] := by
    simpa [List.getElem_idxOf, hia, hib] using hab
  have hidx : l.idxOf a < l.idxOf b :=
    (List.SortedLT.getElem_lt_getElem_iff (hl := hSorted) (i := l.idxOf a) (j := l.idxOf b)
      (hi := hia) (hj := hib)).1 hget
  simpa [rankOf, l] using hidx

theorem lt_of_rankOf_lt_rankOf {keys : List α} {a b : α}
    (ha : a ∈ keys) (hb : b ∈ keys) (hab : rankOf keys a < rankOf keys b) :
    a < b := by
  let l := orderedUniqueKeys keys
  have hSorted : l.SortedLT := by
    simpa [l] using sortedLT_orderedUniqueKeys keys
  have ha' : a ∈ l := (mem_orderedUniqueKeys_iff (keys := keys) (k := a)).2 ha
  have hb' : b ∈ l := (mem_orderedUniqueKeys_iff (keys := keys) (k := b)).2 hb
  have hia : l.idxOf a < l.length := List.idxOf_lt_length_iff.2 ha'
  have hib : l.idxOf b < l.length := List.idxOf_lt_length_iff.2 hb'
  have hidx : l.idxOf a < l.idxOf b := by
    simpa [rankOf, l] using hab
  have hget : l[l.idxOf a] < l[l.idxOf b] :=
    (List.SortedLT.getElem_lt_getElem_iff (hl := hSorted) (i := l.idxOf a) (j := l.idxOf b)
      (hi := hia) (hj := hib)).2 hidx
  simpa [List.getElem_idxOf, hia, hib] using hget

theorem projectedCandidate_keyLe_iff_trueKeyLe
    (keys : List α) (i j : Fin keys.length) :
    keyLe (projectedCandidate keys i) (projectedCandidate keys j) ↔
      trueKeyLe keys i j := by
  constructor
  · intro hij
    rcases hij with hij | ⟨hRankEq, hIdxLe⟩
    · exact Or.inl <|
        lt_of_rankOf_lt_rankOf
          (keys := keys)
          (a := keys.get i)
          (b := keys.get j)
          (List.get_mem _ _)
          (List.get_mem _ _)
          hij
    · exact Or.inr ⟨
        (rankOf_eq_iff_eq
          (keys := keys)
          (a := keys.get i)
          (b := keys.get j)
          (List.get_mem _ _)
          (List.get_mem _ _)).1 hRankEq,
        hIdxLe
      ⟩
  · intro hij
    rcases hij with hij | ⟨hKeyEq, hIdxLe⟩
    · exact Or.inl <|
        rankOf_lt_rankOf_of_lt
          (keys := keys)
          (a := keys.get i)
          (b := keys.get j)
          (List.get_mem _ _)
          (List.get_mem _ _)
          hij
    · exact Or.inr ⟨
        (rankOf_eq_iff_eq
          (keys := keys)
          (a := keys.get i)
          (b := keys.get j)
          (List.get_mem _ _)
          (List.get_mem _ _)).2 hKeyEq,
        hIdxLe
      ⟩

end ExactInRouteRankProjection
end Routing
end TauSwap
