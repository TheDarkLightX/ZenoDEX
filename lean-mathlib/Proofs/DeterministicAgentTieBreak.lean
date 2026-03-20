import Mathlib.Data.Finset.Max

/-!
Deterministic tie-break certificate shape.

For any finite nonempty candidate set under a total order, there is a unique
minimal element. This is the proof shape used by "winner <= every candidate"
certificates.
-/

open scoped Classical

namespace TauSwap
namespace Agent

variable {α : Type} [LinearOrder α]

theorem exists_unique_min_of_finset_nonempty (S : Finset α) (hS : S.Nonempty) :
    ∃! m, m ∈ S ∧ ∀ x ∈ S, m ≤ x := by
  apply ExistsUnique.intro (S.min' hS)
  · constructor
    · exact Finset.min'_mem S hS
    · intro x hx
      exact Finset.min'_le S x hx
  · intro m hm
    have hm_le : m ≤ S.min' hS := hm.2 (S.min' hS) (Finset.min'_mem S hS)
    have hmin_le : S.min' hS ≤ m := Finset.min'_le S m hm.1
    exact le_antisymm hm_le hmin_le

end Agent
end TauSwap
