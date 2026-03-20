import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Proofs.ZenoDEXExactOutManyPoolRemainingCapacityEnvelope

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolRemainingCapacityTopSum

open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolSupportTailRecursion
open ExactOutManyPoolSupportHeadBounds
open ExactOutManyPoolRemainingCapacityEnvelope

/-- Concrete suffix-capacity list for the many-pool selected-domain builder:
indices after the chosen head, mapped to capacities in canonical pool order. -/
def suffixCapacityList {n : ℕ}
    (cap : Fin n → ℕ)
    (headIdx : Fin n) : List ℕ :=
  ((suffixSet headIdx).sort).map cap

/-- Concrete top-`slots` suffix capacity bound matching the Python
`remaining_capacity` shape: sort suffix capacities descending, take `slots`, sum. -/
def remainingCapacityTopSum {n : ℕ}
    (cap : Fin n → ℕ)
    (headIdx : Fin n)
    (slots : ℕ) : ℕ :=
  (((suffixCapacityList cap headIdx).mergeSort (· ≥ ·)).take slots).sum

lemma tail_sortedGE_of_cons_sortedGE
    {α : Type} [Preorder α] {head : α} {tail : List α}
    (hSorted : (head :: tail).SortedGE) :
    tail.SortedGE := by
  rw [List.sortedGE_iff_getElem_ge_getElem_of_le]
  intro i j hi hj hij
  have h' := List.sortedGE_iff_getElem_ge_getElem_of_le.mp hSorted
  simpa using h' (i := i + 1) (j := j + 1)
    (hi := by simpa using Nat.succ_lt_succ hi)
    (hj := by simpa using Nat.succ_lt_succ hj)
    (Nat.succ_le_succ hij)

lemma mem_le_head_of_cons_sortedGE
    {α : Type} [Preorder α] {head x : α} {tail : List α}
    (hSorted : (head :: tail).SortedGE)
    (hx : x ∈ tail) :
    x ≤ head := by
  obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_iff_get.1 hx
  have h' := List.sortedGE_iff_getElem_ge_getElem_of_le.mp hSorted
  simpa using h' (i := j + 1) (j := 0)
    (hi := by simpa using Nat.succ_lt_succ hj)
    (hj := by simp)
    (by omega)

lemma forall₂_le_take_of_sublist_sortedGE :
    ∀ {l₁ l₂ : List ℕ}, l₁.Sublist l₂ → l₁.SortedGE → l₂.SortedGE →
      List.Forall₂ (· ≤ ·) l₁ (l₂.take l₁.length)
  | [], l₂, hSub, h₁, h₂ => by simp
  | _ :: _, [], hSub, h₁, h₂ => by cases hSub
  | b :: tl, a :: l₂, hSub, h₁, h₂ => by
      cases hSub with
      | @cons l₁ l₂' c hSub' =>
          have hb : b ≤ a := by
            have hbMem : b ∈ l₂ := hSub'.subset (by simp)
            exact mem_le_head_of_cons_sortedGE h₂ hbMem
          have hTlSub : tl.Sublist l₂ := by
            exact (List.Sublist.cons b (List.Sublist.refl tl)).trans hSub'
          have hTl : tl.SortedGE := tail_sortedGE_of_cons_sortedGE h₁
          have hL₂ : l₂.SortedGE := tail_sortedGE_of_cons_sortedGE h₂
          simpa [hb] using
            List.Forall₂.cons hb (forall₂_le_take_of_sublist_sortedGE hTlSub hTl hL₂)
      | @cons₂ l₁ l₂' c hSub' =>
          have hTl : tl.SortedGE := tail_sortedGE_of_cons_sortedGE h₁
          have hL₂ : l₂.SortedGE := tail_sortedGE_of_cons_sortedGE h₂
          simpa using
            List.Forall₂.cons (show b ≤ b by rfl)
              (forall₂_le_take_of_sublist_sortedGE hSub' hTl hL₂)

lemma forall₂_sum_le_sum_nat
    {l₁ l₂ : List ℕ}
    (h : List.Forall₂ (· ≤ ·) l₁ l₂) :
    l₁.sum ≤ l₂.sum := by
  induction h with
  | nil => simp
  | cons hab hrest ih =>
      simp
      exact Nat.add_le_add hab ih

lemma sum_le_sum_take_of_sublist_sortedGE
    {l₁ l₂ : List ℕ}
    (hSub : l₁.Sublist l₂)
    (h₁ : l₁.SortedGE)
    (h₂ : l₂.SortedGE) :
    l₁.sum ≤ (l₂.take l₁.length).sum := by
  exact forall₂_sum_le_sum_nat (forall₂_le_take_of_sublist_sortedGE hSub h₁ h₂)

lemma sum_take_mono_nat (l : List ℕ) :
    Monotone fun i => (l.take i).sum := by
  intro i j hij
  induction hij with
  | refl => rfl
  | @step j hij ih =>
      exact le_trans ih <| by
        show (l.take j).sum ≤ (l.take (j + 1)).sum
        by_cases hj : j < l.length
        · rw [List.sum_take_succ _ _ hj]
          exact Nat.le_add_right _ _
        · rw [List.take_of_length_le (Nat.not_lt.mp hj)]
          rw [List.take_of_length_le (le_trans (Nat.not_lt.mp hj) (Nat.le_succ _))]

lemma sort_sublist_of_subset
    {n : ℕ} {s t : Finset (Fin n)}
    (hst : s ⊆ t) :
    List.Sublist (s.sort) (t.sort) := by
  apply (List.sublist_of_subperm_of_pairwise (r := (· < ·)))
  · apply List.subperm_of_subset (Finset.sort_nodup s (fun a b => a ≤ b))
    intro a ha
    exact (Finset.mem_sort (s := t) (r := fun a b => a ≤ b)).2
      (hst ((Finset.mem_sort (s := s) (r := fun a b => a ≤ b)).1 ha))
  · exact (Finset.sortedLT_sort s).pairwise
  · exact (Finset.sortedLT_sort t).pairwise

lemma sort_map_sum_eq_finset_sum
    {n : ℕ} (s : Finset (Fin n)) (cap : Fin n → ℕ) :
    ((s.sort).map cap).sum = Finset.sum s cap := by
  calc
    ((s.sort).map cap).sum = (s.toList.map cap).sum := by
      exact ((Finset.sort_perm_toList s (fun a b => a ≤ b)).map cap).sum_eq
    _ = (s.val.map cap).sum := by
      exact Multiset.sum_map_toList s.val cap
    _ = Finset.sum s cap := by
      rfl

lemma mergeSort_map_length_eq_card
    {n : ℕ} (s : Finset (Fin n)) (cap : Fin n → ℕ) :
    (((s.sort).map cap).mergeSort (· ≥ ·)).length = s.card := by
  calc
    (((s.sort).map cap).mergeSort (· ≥ ·)).length = ((s.sort).map cap).length := by
      exact List.Perm.length_eq (List.mergeSort_perm _ _)
    _ = (s.sort).length := by simp
    _ = s.toList.length := by
      exact List.Perm.length_eq (Finset.sort_perm_toList s (fun a b => a ≤ b))
    _ = s.card := by simp

/-- Any suffix subset with at most `slots` legs has total capacity bounded by the
concrete sorted-top-`slots` suffix sum used by the Python builder. -/
theorem sum_subset_le_remainingCapacityTopSum
    {n : ℕ}
    {cap : Fin n → ℕ}
    {headIdx : Fin n}
    {slots : ℕ}
    {s : Finset (Fin n)}
    (hs : s ⊆ suffixSet headIdx)
    (hSlots : s.card ≤ slots) :
    Finset.sum s cap ≤ remainingCapacityTopSum cap headIdx slots := by
  let sortedSubset : List ℕ := ((s.sort).map cap).mergeSort (· ≥ ·)
  let sortedSuffix : List ℕ := (suffixCapacityList cap headIdx).mergeSort (· ≥ ·)
  have hIndexSub : List.Sublist (s.sort) ((suffixSet headIdx).sort) :=
    sort_sublist_of_subset hs
  have hCapsSub : List.Sublist ((s.sort).map cap) (suffixCapacityList cap headIdx) := by
    simpa [suffixCapacityList] using hIndexSub.map cap
  have hSortedSubperm : List.Subperm sortedSubset sortedSuffix := by
    exact
      (List.Perm.subperm (List.mergeSort_perm _ _)).trans <|
        (List.Sublist.subperm hCapsSub).trans <|
          List.Perm.subperm (List.mergeSort_perm _ _).symm
  have hSortedSub : List.Sublist sortedSubset sortedSuffix := by
    apply List.sublist_of_subperm_of_sortedGE hSortedSubperm
    · simpa [sortedSubset] using (List.sortedGE_mergeSort : sortedSubset.SortedGE)
    · simpa [sortedSuffix] using (List.sortedGE_mergeSort : sortedSuffix.SortedGE)
  have hPrefix : sortedSubset.sum ≤ (sortedSuffix.take sortedSubset.length).sum :=
    sum_le_sum_take_of_sublist_sortedGE hSortedSub
      (by simpa [sortedSubset] using (List.sortedGE_mergeSort : sortedSubset.SortedGE))
      (by simpa [sortedSuffix] using (List.sortedGE_mergeSort : sortedSuffix.SortedGE))
  have hLen : sortedSubset.length ≤ slots := by
    rw [mergeSort_map_length_eq_card s cap]
    exact hSlots
  have hTakeMono : (sortedSuffix.take sortedSubset.length).sum ≤
      (sortedSuffix.take slots).sum :=
    sum_take_mono_nat sortedSuffix hLen
  calc
    Finset.sum s cap = ((s.sort).map cap).sum := by
      exact (sort_map_sum_eq_finset_sum s cap).symm
    _ = sortedSubset.sum := by
      dsimp [sortedSubset]
      exact (List.mergeSort_perm _ _).symm.sum_eq
    _ ≤ (sortedSuffix.take sortedSubset.length).sum := hPrefix
    _ ≤ (sortedSuffix.take slots).sum := hTakeMono
    _ = remainingCapacityTopSum cap headIdx slots := by
      rfl

/-- The finite-set suffix-capacity envelope is bounded by the concrete
sorted-top-`slots` implementation model. -/
theorem remainingCapacityEnvelope_le_remainingCapacityTopSum
    {n : ℕ}
    {cap : Fin n → ℕ}
    {headIdx : Fin n}
    {slots : ℕ} :
    remainingCapacityEnvelope cap headIdx slots ≤
      remainingCapacityTopSum cap headIdx slots := by
  apply Finset.sup_le
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_powerset] at hs
  exact sum_subset_le_remainingCapacityTopSum hs.1 hs.2

/-- Any feasible residual support after fixing the head leg is bounded by the
concrete `remaining_capacity` top-sum model. -/
theorem residualSupportCap_le_remainingCapacityTopSum
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ} {tail : List (Fin n × ℕ)}
    {slots : ℕ}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = head :: tail)
    (hSlots : tail.length ≤ slots) :
    residualSupportCap cap alloc head.1 ≤
      remainingCapacityTopSum cap head.1 slots := by
  exact le_trans
    (residualSupportCap_le_remainingCapacityEnvelope (hFeas := hFeas) (hLegs := hLegs) hSlots)
    remainingCapacityEnvelope_le_remainingCapacityTopSum

/-- If the concrete suffix top-sum model is used as `futureMax`, the chosen head
leg lies inside the exact recursive range checked by the Python builder. -/
theorem feasible_support_cons_head_within_top_sum_range
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ} {tail : List (Fin n × ℕ)}
    {slots : ℕ}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = head :: tail)
    (hSlots : tail.length ≤ slots) :
    max 1 (Q - remainingCapacityTopSum cap head.1 slots) ≤ head.2 ∧
      head.2 ≤ min (cap head.1) Q := by
  apply feasible_support_cons_head_within_envelope_range
    (hFeas := hFeas) (hLegs := hLegs) (hSlots := hSlots)
  exact remainingCapacityEnvelope_le_remainingCapacityTopSum

end ExactOutManyPoolRemainingCapacityTopSum
end ZenoDEX
end TauSwap
