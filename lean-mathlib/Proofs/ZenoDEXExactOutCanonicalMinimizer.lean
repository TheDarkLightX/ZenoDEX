import Mathlib.Order.Synonym
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.Lex

open scoped Classical

namespace TauSwap
namespace ZenoDEX
namespace ExactOutCanonicalMinimizer

abbrev Leg (PoolId : Type) [LinearOrder PoolId] := PoolId ×ₗ Nat
abbrev Legs (PoolId : Type) [LinearOrder PoolId] := List (Leg PoolId)
abbrev Key (PoolId : Type) [LinearOrder PoolId] := (Nat ×ₗ Nat) ×ₗ Legs PoolId

def key {PoolId : Type} [LinearOrder PoolId]
    (inputTotal legCount : Nat) (legsLex : Legs PoolId) : Key PoolId :=
  toLex (toLex (inputTotal, legCount), legsLex)

def inputTotal {PoolId : Type} [LinearOrder PoolId] (k : Key PoolId) : Nat :=
  (ofLex (ofLex k).1).1

def legCount {PoolId : Type} [LinearOrder PoolId] (k : Key PoolId) : Nat :=
  (ofLex (ofLex k).1).2

def legsLex {PoolId : Type} [LinearOrder PoolId] (k : Key PoolId) : Legs PoolId :=
  (ofLex k).2

@[simp] theorem key_unpack {PoolId : Type} [LinearOrder PoolId] (k : Key PoolId) :
    key (inputTotal k) (legCount k) (legsLex k) = k := by
  cases k
  rfl

theorem key_le_iff {PoolId : Type} [LinearOrder PoolId]
    (input₁ input₂ legCount₁ legCount₂ : Nat)
    (legs₁ legs₂ : Legs PoolId) :
    key input₁ legCount₁ legs₁ ≤ key input₂ legCount₂ legs₂ ↔
      (input₁ < input₂) ∨
        (input₁ = input₂ ∧
          ((legCount₁ < legCount₂) ∨ (legCount₁ = legCount₂ ∧ legs₁ ≤ legs₂))) := by
  simp [key, Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_lt_toLex]
  tauto

theorem equal_input_key_le_iff {PoolId : Type} [LinearOrder PoolId]
    (inputTotal legCount₁ legCount₂ : Nat)
    (legs₁ legs₂ : Legs PoolId) :
    key inputTotal legCount₁ legs₁ ≤ key inputTotal legCount₂ legs₂ ↔
      (legCount₁ < legCount₂) ∨ (legCount₁ = legCount₂ ∧ legs₁ ≤ legs₂) := by
  simpa using key_le_iff inputTotal inputTotal legCount₁ legCount₂ legs₁ legs₂

theorem equal_input_equal_leg_count_key_le_iff {PoolId : Type} [LinearOrder PoolId]
    (inputTotal legCount : Nat)
    (legs₁ legs₂ : Legs PoolId) :
    key inputTotal legCount legs₁ ≤ key inputTotal legCount legs₂ ↔ legs₁ ≤ legs₂ := by
  simpa using equal_input_key_le_iff inputTotal legCount legCount legs₁ legs₂

theorem exists_unique_min_of_finset_nonempty
    {α : Type} [LinearOrder α] (S : Finset α) (hS : S.Nonempty) :
    ∃! m, m ∈ S ∧ ∀ x ∈ S, m ≤ x := by
  exact ⟨S.min' hS,
    by
      constructor
      · exact Finset.min'_mem S hS
      · intro x hx
        exact Finset.min'_le S x hx,
    by
      intro m hm
      have hm_le : m ≤ S.min' hS := hm.2 (S.min' hS) (Finset.min'_mem S hS)
      have hmin_le : S.min' hS ≤ m := Finset.min'_le S m hm.1
      exact le_antisymm hm_le hmin_le⟩

theorem exists_unique_canonical {PoolId : Type} [LinearOrder PoolId]
    (S : Finset (Key PoolId)) (hS : S.Nonempty) :
    ∃! k, k ∈ S ∧ ∀ x ∈ S, k ≤ x :=
  exists_unique_min_of_finset_nonempty S hS

theorem eq_min_of_mem_of_le_all {PoolId : Type} [LinearOrder PoolId]
    {S : Finset (Key PoolId)} (hS : S.Nonempty) {k : Key PoolId}
    (hkMem : k ∈ S) (hkLe : ∀ x ∈ S, k ≤ x) :
    k = S.min' hS := by
  have hkMin : k ≤ S.min' hS := hkLe (S.min' hS) (Finset.min'_mem S hS)
  have hMinK : S.min' hS ≤ k := Finset.min'_le S k hkMem
  exact le_antisymm hkMin hMinK

theorem mem_and_le_all_iff_eq_min {PoolId : Type} [LinearOrder PoolId]
    {S : Finset (Key PoolId)} (hS : S.Nonempty) {k : Key PoolId} :
    (k ∈ S ∧ ∀ x ∈ S, k ≤ x) ↔ k = S.min' hS := by
  constructor
  · intro hk
    exact eq_min_of_mem_of_le_all hS hk.1 hk.2
  · intro hkEq
    constructor
    · simpa [hkEq] using Finset.min'_mem S hS
    · intro x hx
      simpa [hkEq] using Finset.min'_le S x hx

theorem canonical_prefers_fewer_legs_then_lex {PoolId : Type} [LinearOrder PoolId]
    (S : Finset (Key PoolId)) (hS : S.Nonempty) :
    let k : Key PoolId := S.min' hS
    (k ∈ S) ∧
      (∀ x ∈ S, inputTotal k ≤ inputTotal x) ∧
      (∀ x ∈ S, inputTotal k = inputTotal x → legCount k ≤ legCount x) ∧
      (∀ x ∈ S, inputTotal k = inputTotal x → legCount k = legCount x → legsLex k ≤ legsLex x) := by
  intro k
  constructor
  · exact Finset.min'_mem S hS
  constructor
  · intro x hx
    have hkx : k ≤ x := Finset.min'_le S x hx
    have hkx' :
        key (inputTotal k) (legCount k) (legsLex k) ≤
          key (inputTotal x) (legCount x) (legsLex x) := by
      simpa using hkx
    have horder :=
      (key_le_iff (inputTotal k) (inputTotal x) (legCount k) (legCount x) (legsLex k) (legsLex x)).1 hkx'
    cases horder with
    | inl hlt =>
        exact Nat.le_of_lt hlt
    | inr hrest =>
        exact Nat.le_of_eq hrest.1
  constructor
  · intro x hx hinput
    have hkx : k ≤ x := Finset.min'_le S x hx
    have hkx' :
        key (inputTotal k) (legCount k) (legsLex k) ≤
          key (inputTotal x) (legCount x) (legsLex x) := by
      simpa using hkx
    have horder :=
      (key_le_iff (inputTotal k) (inputTotal x) (legCount k) (legCount x) (legsLex k) (legsLex x)).1 hkx'
    have hlegs :
        (legCount k < legCount x) ∨ (legCount k = legCount x ∧ legsLex k ≤ legsLex x) := by
      cases horder with
      | inl hlt =>
          have hFalse : False := by
            simp [hinput] at hlt
          exact False.elim hFalse
      | inr hrest =>
          exact hrest.2
    cases hlegs with
    | inl hlt =>
        exact Nat.le_of_lt hlt
    | inr hrest =>
        exact Nat.le_of_eq hrest.1
  · intro x hx hinput hcount
    have hkx : k ≤ x := Finset.min'_le S x hx
    have hkx' :
        key (inputTotal k) (legCount k) (legsLex k) ≤
          key (inputTotal x) (legCount x) (legsLex x) := by
      simpa using hkx
    have horder :=
      (key_le_iff (inputTotal k) (inputTotal x) (legCount k) (legCount x) (legsLex k) (legsLex x)).1 hkx'
    cases horder with
    | inl hlt =>
        have hFalse : False := by
          simp [hinput] at hlt
        exact False.elim hFalse
    | inr hrest =>
        cases hrest.2 with
        | inl hlt =>
            have hFalse : False := by
              simp [hcount] at hlt
            exact False.elim hFalse
        | inr hrest' =>
            exact hrest'.2

end ExactOutCanonicalMinimizer
end ZenoDEX
end TauSwap
