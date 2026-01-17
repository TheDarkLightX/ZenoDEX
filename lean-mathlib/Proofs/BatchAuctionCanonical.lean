import Mathlib.Order.Synonym
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.Lex

/-!
Batch auction canonicalization (Mathlib-backed).

We model the deterministic “(A,B) objective + canonical tie-break” pattern used throughout the DEX:

  (A) maximize executed input volume
  (B) maximize surplus
  tie-break: choose the lexicographically smallest `order`

Encode this as a single **total key** and select the unique minimum key from a finite nonempty set.

This is the core theorem needed for a hybrid Rust/Tau system:

- Rust computes a candidate set (or a claimed winner).
- Tau/Lean verifies the claimed winner is the minimum under a total order.

The key is designed so that **minimizing** it is equivalent to maximizing (volume, surplus) and
minimizing the order among maximizers.
-/

open scoped Classical

namespace TauSwap
namespace Batch

abbrev Volume := Nat
abbrev Surplus := Nat
abbrev Order := List Nat

-- Total key: primary = volume (descending), secondary = surplus (descending), tertiary = order (ascending).
--
-- We build a 3-level lex key as `((vol, surplus), order)`:
--   Key := (Volumeᵒᵈ ×ₗ Surplusᵒᵈ) ×ₗ Order
abbrev Key := (Volumeᵒᵈ ×ₗ Surplusᵒᵈ) ×ₗ Order

def key (v : Volume) (s : Surplus) (o : Order) : Key :=
  toLex (toLex (OrderDual.toDual v, OrderDual.toDual s), o)

def vol (k : Key) : Volume :=
  OrderDual.ofDual (ofLex (ofLex k).1).1

def sur (k : Key) : Surplus :=
  OrderDual.ofDual (ofLex (ofLex k).1).2

def ord (k : Key) : Order :=
  (ofLex k).2

theorem key_le_iff (v₁ v₂ s₁ s₂ : Nat) (o₁ o₂ : Order) :
    key v₁ s₁ o₁ ≤ key v₂ s₂ o₂ ↔
      (v₂ < v₁) ∨ (v₁ = v₂ ∧ ((s₂ < s₁) ∨ (s₁ = s₂ ∧ o₁ ≤ o₂))) := by
  -- Expand both lex layers (`×ₗ`) and discharge `OrderDual` rewrites.
  -- Outer: ((v,s),o) ; Inner: (v,s)
  simp [key, Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_lt_toLex]
  tauto

theorem exists_unique_min_of_finset_nonempty {α : Type} [LinearOrder α] (S : Finset α) (hS : S.Nonempty) :
    ∃! m, m ∈ S ∧ ∀ x ∈ S, m ≤ x := by
  classical
  refine ⟨S.min' hS, ?_, ?_⟩
  · refine ⟨Finset.min'_mem S hS, ?_⟩
    intro x hx
    exact Finset.min'_le S x hx
  · intro m hm
    have hm_le : m ≤ S.min' hS := hm.2 (S.min' hS) (Finset.min'_mem S hS)
    have hmin_le : S.min' hS ≤ m := Finset.min'_le S m hm.1
    exact le_antisymm hm_le hmin_le

theorem exists_unique_canonical (S : Finset Key) (hS : S.Nonempty) :
    ∃! k, k ∈ S ∧ ∀ x ∈ S, k ≤ x :=
  exists_unique_min_of_finset_nonempty S hS

theorem canonical_dominates (S : Finset Key) (hS : S.Nonempty) :
    let k := S.min' hS
    (k ∈ S) ∧ (∀ x ∈ S, vol k ≥ vol x) ∧
      (∀ x ∈ S, vol k = vol x → sur k ≥ sur x) ∧
      (∀ x ∈ S, vol k = vol x → sur k = sur x → ord k ≤ ord x) := by
  classical
  intro k
  refine ⟨Finset.min'_mem S hS, ?_, ?_, ?_⟩
  · intro x hx
    have hkx : k ≤ x := Finset.min'_le S x hx
    -- From key ordering, k ≤ x implies vol k ≥ vol x.
    -- We expand `k ≤ x` to the lex statement.
    have : (vol x < vol k) ∨ (vol k = vol x ∧ ((sur x < sur k) ∨ (sur k = sur x ∧ ord k ≤ ord x))) := by
      simpa [vol, sur, ord, key] using
        (key_le_iff (v₁ := vol k) (v₂ := vol x) (s₁ := sur k) (s₂ := sur x) (o₁ := ord k) (o₂ := ord x)).1 (by
          simpa [key, vol, sur, ord] using hkx)
    cases this with
    | inl hlt =>
        exact Nat.le_of_lt hlt
    | inr hrest =>
        exact Nat.le_of_eq hrest.1.symm
  · intro x hx hv
    have hkx : k ≤ x := Finset.min'_le S x hx
    have : (vol x < vol k) ∨ (vol k = vol x ∧ ((sur x < sur k) ∨ (sur k = sur x ∧ ord k ≤ ord x))) := by
      simpa [vol, sur, ord, key] using
        (key_le_iff (v₁ := vol k) (v₂ := vol x) (s₁ := sur k) (s₂ := sur x) (o₁ := ord k) (o₂ := ord x)).1 (by
          simpa [key, vol, sur, ord] using hkx)
    have : (sur x < sur k) ∨ (sur k = sur x ∧ ord k ≤ ord x) := by
      cases this with
      | inl hvol_lt =>
          -- contradicts hv
          exact False.elim ((Nat.lt_irrefl (vol k)) (by simpa [hv] using hvol_lt))
      | inr hvol_eq =>
          -- v equal; extract the surplus/order part
          have h' := hvol_eq.2
          cases h' with
          | inl hsur_lt => exact Or.inl hsur_lt
          | inr hsur_eq => exact Or.inr hsur_eq
    cases this with
    | inl hsur_lt => exact Nat.le_of_lt hsur_lt
    | inr hsur_eq => exact Nat.le_of_eq hsur_eq.1.symm
  · intro x hx hv hs
    have hkx : k ≤ x := Finset.min'_le S x hx
    have : (vol x < vol k) ∨ (vol k = vol x ∧ ((sur x < sur k) ∨ (sur k = sur x ∧ ord k ≤ ord x))) := by
      simpa [vol, sur, ord, key] using
        (key_le_iff (v₁ := vol k) (v₂ := vol x) (s₁ := sur k) (s₂ := sur x) (o₁ := ord k) (o₂ := ord x)).1 (by
          simpa [key, vol, sur, ord] using hkx)
    cases this with
    | inl hvol_lt =>
        exact False.elim ((Nat.lt_irrefl (vol k)) (by simpa [hv] using hvol_lt))
    | inr hvol_eq =>
        have h' := hvol_eq.2
        cases h' with
        | inl hsur_lt =>
            exact False.elim ((Nat.lt_irrefl (sur k)) (by simpa [hs] using hsur_lt))
        | inr hsur_eq =>
            exact hsur_eq.2

end Batch
end TauSwap

