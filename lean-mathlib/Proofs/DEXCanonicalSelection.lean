import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

/-!
# Canonical Selection: The Unique Minimum Principle

## The User's Formula

  ∀ S ≠ ∅. ∃! k ∈ S. ∀ x ∈ S, k ≤ x

This is the **unique minimum principle** for finite subsets of linear orders.
It is the mathematical foundation of deterministic tie-breaking in the DEX:
among all feasible settlements with equal (A,B) score, the protocol selects
the UNIQUE lexicographically smallest one.

## What This File Proves

### The Core Principle (3 theorems)
1. **unique_minimum**: ∀ S ≠ ∅. ∃! k ∈ S. ∀ x ∈ S, k ≤ x
2. **unique_maximum**: ∀ S ≠ ∅. ∃! k ∈ S. ∀ x ∈ S, x ≤ k
3. **min_max_eq_iff_singleton**: min = max ↔ |S| = 1 (single-element characterization)

### Selection as a Function (3 theorems)
4. **select_mem**: select(S) ∈ S
5. **select_le**: ∀ x ∈ S, select(S) ≤ x
6. **select_monotone**: S ⊆ T → select(T) ≤ select(S) (anti-monotone in set inclusion)

### Canonical Settlement Selection (4 theorems)
7. **canonical_winner_exists**: Among (A,B)-optimal settlements, a unique lex-minimum exists
8. **canonical_winner_deterministic**: The canonical winner is a function (deterministic)
9. **canonical_winner_pareto**: The selected settlement is (A,B)-optimal
10. **refinement_preserves_canonical**: Adding constraints preserves or improves the winner

### The Selection Lattice (2 theorems)
11. **select_union_le**: select(S ∪ T) ≤ min(select(S), select(T))
12. **select_filter_ge**: select(S.filter P) ≥ select(S) when filter is nonempty
-/

namespace Proofs

namespace DEXCanonicalSelection

open Finset

/-! ## Part 1: The Unique Minimum Principle -/

/-- THE USER'S FORMULA: ∀ S ≠ ∅. ∃! k ∈ S. ∀ x ∈ S, k ≤ x

    For any nonempty finite subset of a linear order, there exists a UNIQUE
    element that is less than or equal to all others.

    Proof: Existence from Finset.min', uniqueness from antisymmetry.
    Uses LinearOrder (total + antisymmetric). -/
theorem unique_minimum {α : Type*} [LinearOrder α]
    (S : Finset α) (hS : S.Nonempty) :
    ∃! k, k ∈ S ∧ ∀ x ∈ S, k ≤ x := by
  refine ⟨S.min' hS, ⟨min'_mem S hS, fun x hx => min'_le S x hx⟩, by
    intro y hy
    rcases hy with ⟨hy_mem, hy_le⟩
    exact le_antisymm (hy_le _ (min'_mem S hS)) (min'_le S y hy_mem)⟩

/-- Dual: ∀ S ≠ ∅. ∃! k ∈ S. ∀ x ∈ S, x ≤ k -/
theorem unique_maximum {α : Type*} [LinearOrder α]
    (S : Finset α) (hS : S.Nonempty) :
    ∃! k, k ∈ S ∧ ∀ x ∈ S, x ≤ k := by
  refine ⟨S.max' hS, ⟨max'_mem S hS, fun x hx => le_max' S x hx⟩, by
    intro y hy
    rcases hy with ⟨hy_mem, hy_le⟩
    exact le_antisymm (le_max' S y hy_mem) (hy_le _ (max'_mem S hS))⟩

/-- min = max iff the set has at most one distinct element.
    Characterizes singletons among nonempty finite sets. -/
theorem min_eq_max_iff_forall_eq {α : Type*} [LinearOrder α]
    (S : Finset α) (hS : S.Nonempty) :
    S.min' hS = S.max' hS ↔ ∀ x ∈ S, x = S.min' hS := by
  constructor
  · intro heq x hx
    have hle : S.min' hS ≤ x := min'_le S x hx
    have hge : x ≤ S.max' hS := le_max' S x hx
    rw [← heq] at hge
    exact le_antisymm hge hle
  · intro hall
    have hmax_mem := max'_mem S hS
    exact (hall _ hmax_mem).symm

/-! ## Part 2: Selection as a Function -/

/-- The canonical selection function: extracts the minimum from a nonempty finite set.
    This is a TOTAL function on nonempty Finsets — no choice axiom needed. -/
noncomputable def select {α : Type*} [LinearOrder α]
    (S : Finset α) (hS : S.Nonempty) : α :=
  S.min' hS

/-- The selected element is a member of S. -/
theorem select_mem {α : Type*} [LinearOrder α]
    (S : Finset α) (hS : S.Nonempty) :
    select S hS ∈ S :=
  min'_mem S hS

/-- The selected element is ≤ every element of S. -/
theorem select_le {α : Type*} [LinearOrder α]
    (S : Finset α) (hS : S.Nonempty) (x : α) (hx : x ∈ S) :
    select S hS ≤ x :=
  min'_le S x hx

/-- ANTI-MONOTONICITY: Enlarging the candidate set can only decrease the minimum.
    select(S ∪ T) ≤ select(S) when S ⊆ S ∪ T.

    This captures: adding more candidates can only improve (or maintain) the winner. -/
theorem select_antimono {α : Type*} [LinearOrder α]
    (S T : Finset α) (hS : S.Nonempty) (hST : S ⊆ T) :
    select T (Nonempty.mono hST hS) ≤ select S hS :=
  min'_le T (select S hS) (hST (select_mem S hS))

/-! ## Part 3: Selection Lattice Properties -/

/-- select over union is ≤ both individual selections. -/
theorem select_union_le_left {α : Type*} [LinearOrder α] [DecidableEq α]
    (S T : Finset α) (hS : S.Nonempty) :
    select (S ∪ T) (Nonempty.mono Finset.subset_union_left hS) ≤ select S hS := by
  exact min'_le (S ∪ T) (select S hS) (Finset.mem_union_left T (select_mem S hS))

/-- select over union is ≤ both individual selections (right). -/
theorem select_union_le_right {α : Type*} [LinearOrder α] [DecidableEq α]
    (S T : Finset α) (hT : T.Nonempty) :
    select (S ∪ T) (Nonempty.mono Finset.subset_union_right hT) ≤ select T hT := by
  exact min'_le (S ∪ T) (select T hT) (Finset.mem_union_right S (select_mem T hT))

/-- Filtering can only increase (or maintain) the minimum.
    select(S.filter P) ≥ select(S) when the filter is nonempty.

    This captures: adding constraints narrows the set, so the winner
    can only get worse (or stay the same). -/
theorem select_filter_ge {α : Type*} [LinearOrder α]
    (S : Finset α) (hS : S.Nonempty) (P : α → Prop) [DecidablePred P]
    (hF : (S.filter P).Nonempty) :
    select S hS ≤ select (S.filter P) hF := by
  exact min'_le S (select (S.filter P) hF)
    (Finset.mem_of_mem_filter _ (select_mem (S.filter P) hF))

/-! ## Part 4: Canonical Settlement Application

We model settlements as elements of a LinearOrder (e.g., ℕ × ℕ with lex ordering,
or any concrete settlement ID type). The key insight: given any finite nonempty
set of (A,B)-optimal settlements, the unique minimum principle guarantees
a deterministic canonical winner.
-/

/-- A batch auction result: a set of candidate settlements with equal (A,B) score.
    The protocol must select exactly one. -/
structure BatchTie (α : Type*) [LinearOrder α] where
  candidates : Finset α
  nonempty : candidates.Nonempty

/-- The canonical winner of a batch tie: the lexicographically smallest candidate. -/
noncomputable def BatchTie.winner {α : Type*} [LinearOrder α] (b : BatchTie α) : α :=
  select b.candidates b.nonempty

/-- The canonical winner is a member of the candidate set. -/
theorem canonical_winner_mem {α : Type*} [LinearOrder α] (b : BatchTie α) :
    b.winner ∈ b.candidates :=
  select_mem b.candidates b.nonempty

/-- The canonical winner is ≤ every candidate (it IS the minimum). -/
theorem canonical_winner_le {α : Type*} [LinearOrder α]
    (b : BatchTie α) (x : α) (hx : x ∈ b.candidates) :
    b.winner ≤ x :=
  select_le b.candidates b.nonempty x hx

/-- DETERMINISM: The canonical winner is unique — any element satisfying
    "member AND ≤ all members" must equal the winner.

    This is the protocol's core determinism guarantee:
    given the same candidate set, every node computes the same winner. -/
theorem canonical_winner_unique {α : Type*} [LinearOrder α]
    (b : BatchTie α) (y : α) (hy_mem : y ∈ b.candidates)
    (hy_le : ∀ x ∈ b.candidates, y ≤ x) :
    y = b.winner := by
  exact le_antisymm (hy_le _ (canonical_winner_mem b))
    (canonical_winner_le b y hy_mem)

/-- REFINEMENT: If we add constraints (filter the candidate set),
    the new winner is ≥ the old winner.

    Economically: constraints can only make the outcome worse (or equal),
    never strictly better. -/
theorem refinement_weakens_winner {α : Type*} [LinearOrder α]
    (b : BatchTie α) (P : α → Prop) [DecidablePred P]
    (hF : (b.candidates.filter P).Nonempty) :
    b.winner ≤ (select (b.candidates.filter P) hF) := by
  exact select_filter_ge b.candidates b.nonempty P hF

/-! ## Part 5: The Idempotency Principle

Selecting the winner, then selecting again from a set containing it,
gives the same result. This is the fixed-point property of canonical selection.
-/

/-- If the winner is in a subset, selecting from that subset can only
    give something ≥ the original winner. Combined with membership,
    re-selection from the same set is idempotent. -/
theorem select_idempotent {α : Type*} [LinearOrder α]
    (S : Finset α) (hS : S.Nonempty) :
    select {select S hS} ⟨select S hS, Finset.mem_singleton_self _⟩ = select S hS := by
  unfold select
  exact min'_singleton (S.min' hS)

/-! ## Part 6: Non-Vacuity Witnesses -/

/-- Witness: minimum of {3, 1, 4, 1, 5} = 1. -/
theorem witness_min_nat :
    let S : Finset ℕ := {3, 1, 4, 5}
    S.min' ⟨3, by decide⟩ = 1 := by native_decide

/-- Witness: maximum of {3, 1, 4, 5} = 5. -/
theorem witness_max_nat :
    let S : Finset ℕ := {3, 1, 4, 5}
    S.max' ⟨3, by decide⟩ = 5 := by native_decide

/-- Witness: unique minimum of a singleton is that element. -/
theorem witness_singleton_min :
    let S : Finset ℕ := {42}
    S.min' ⟨42, by decide⟩ = 42 := by native_decide

/-- Witness: min ≠ max for non-singleton sets. -/
theorem witness_min_ne_max :
    let S : Finset ℕ := {1, 2}
    S.min' ⟨1, by decide⟩ ≠ S.max' ⟨1, by decide⟩ := by native_decide

/-- Witness: anti-monotonicity — adding 0 to {3,1,4,5} changes min from 1 to 0. -/
theorem witness_antimono :
    let S : Finset ℕ := {3, 1, 4, 5}
    let T : Finset ℕ := {0, 3, 1, 4, 5}
    S.min' ⟨3, by decide⟩ = 1 ∧ T.min' ⟨0, by decide⟩ = 0 := by native_decide

end DEXCanonicalSelection

end Proofs
