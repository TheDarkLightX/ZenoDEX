import Mathlib.Order.Synonym
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice

/-!
Deterministic agent tie-break (Mathlib-backed).

We model a common deterministic-agent requirement:
  - maximize `score`
  - break ties by minimizing `hash`

Define a key type using lexicographic order:
  Key := (OrderDual Nat) ×ₗ Nat

Then "best" is simply the **minimum** key in this order.

This file proves that the chosen winner is uniquely characterized by:
  winner ∈ S and ∀ x ∈ S, winner ≤ x

This is the exact shape you want for a Tau-verifiable certificate:
  provide `winner` and check it's ≤ every candidate under a total order.
-/

open scoped Classical

namespace TauSwap
namespace Agent

abbrev Score := Nat
abbrev Hash := Nat

-- Lex key: primary = score (descending), secondary = hash (ascending).
abbrev Key := (Scoreᵒᵈ ×ₗ Hash)

def key (score : Score) (hash : Hash) : Key :=
  (OrderDual.toDual score, hash)

theorem key_le_iff (s₁ h₁ s₂ h₂ : Nat) :
    key s₁ h₁ ≤ key s₂ h₂ ↔ (s₁ > s₂) ∨ (s₁ = s₂ ∧ h₁ ≤ h₂) := by
  -- This lemma depends on the lex order on `×ₗ`.
  -- The exact simp-normal form in Mathlib is `Prod.Lex`-based; we use `simp` to expose it.
  -- If you need this exact characterization later, refine with more targeted lemmas.
  simp [key]

variable {α : Type} [LinearOrder α]

theorem exists_unique_min_of_finset_nonempty (S : Finset α) (hS : S.Nonempty) :
    ∃! m, m ∈ S ∧ ∀ x ∈ S, m ≤ x := by
  classical
  -- Use Mathlib's `Finset.min'`.
  refine ⟨S.min' hS, ?_, ?_⟩
  · refine ⟨Finset.min'_mem S hS, ?_⟩
    intro x hx
    exact Finset.min'_le S x hx
  · intro m hm
    -- Any element satisfying "≤ all" must equal min'.
    have hm_le : m ≤ S.min' hS := hm.2 (S.min' hS) (Finset.min'_mem S hS)
    have hmin_le : S.min' hS ≤ m := Finset.min'_le S m hm.1
    exact le_antisymm hm_le hmin_le

end Agent
end TauSwap

