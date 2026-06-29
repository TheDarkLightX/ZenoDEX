import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

import Proofs.SettlementAlgebra
import Proofs.CPMMSettlement
import Proofs.CPMMInvariants

/-!
# Phase 7A: End-to-End Settlement Pipeline Composition

This file composes the existing component-level proofs into a single
end-to-end settlement pipeline theorem. The pipeline stages are:

1. Intent validation (modeled as a guard predicate)
2. Batch clearing (modeled as a list of valid CPMM swaps)
3. Swap execution (each swap produces a settlement)
4. Delta aggregation (settlement addition is additive via Δ homomorphism)
5. Conservation check (balanced composition preserves Δ = 0)

## What This File Proves

1. **Pipeline conservation**: If every swap in a batch produces a balanced
   settlement, the composed batch settlement is balanced. This follows from
   the Δ homomorphism and the kernel being an AddSubgroup.

2. **Pipeline non-negativity**: If every swap has `amount_in >= amount_out`
   (safe scalar flow), the composed batch settlement has non-negative net
   flow. This follows from `Settlement.safe_comp_safe` and induction.

3. **Pipeline K-preservation (swap chain)**: If every swap in a chain is a
   valid CPMM swap, the K-value is non-decreasing across the entire chain.
   This follows by induction from `valid_swap_preserves_K`.

## What This File Does NOT Prove (Non-claims)

- Intent validation logic: the guard predicate is an external hypothesis.
- Batch clearing objective: the (A,B) optimality of the swap ordering is
  not proven here. It lives in `SettlementCanonicalExecution.lean`.
- Fee handling: the pipeline theorem uses the zero-fee CPMM model.
- Multi-pool routing: the pipeline theorem models a single pool.
- LP operations: LP mint/burn composition is in `CPMMSettlement.lean`.
- Tau spec equivalence: the Python implementation equivalence is Phase 7B.
- Integer rounding in production: the theorem uses the continuous CPMM model.
- Permutation invariance (determinism): pair-level commutativity is proven
  (`Settlement.comp_comm`) but arbitrary-permutation fold invariance is an
  open gap; it requires Multiset fold with AddCommGroup structure.

## Mathematical Structure

```
  Intent ──guard──► ValidCPMMSwap ──exec──► Settlement ──compose──► BatchSettlement
    │                    │                      │                       │
    │ (external)         │ (K-preserving)       │ (balanced if equal)   │ (Δ = 0)
    ▼                    ▼                      ▼                       ▼
  validated          K non-decreasing       Δ = 0 per swap         Δ = 0 for batch
```

The key compositionality property is that Δ is an AddMonoidHom, so
conservation is preserved under composition without re-verification.
-/

namespace SettlementPipeline

open SettlementAlgebra
open CPMMSettlement
open CPMMInvariants

/-! ## Part 1: Pipeline Types

We model the settlement pipeline as a list of valid CPMM swaps over a
single pool. Each swap produces a settlement, and the batch settlement
is the sum of all individual swap settlements.
-/

/-- A batch of validated swaps, all operating on the same pool state. -/
abbrev Batch (s : CPMMState) : Type := List (ValidCPMMSwap s)

/-! ## Part 2: Delta Aggregation

The batch settlement is the sum of individual swap settlements.
Since Δ is an AddMonoidHom, the net flow of the batch is the sum
of individual net flows.
-/

/-- Convert a batch of valid swaps to a list of settlements. -/
def batchToSettlements {s : CPMMState} : Batch s → List Settlement
  | [] => []
  | swap :: rest => validSwapToSettlement swap :: batchToSettlements rest

/-- Fold a list of settlements into a single composed settlement
    using settlement addition. -/
def foldSettlements : List Settlement → Settlement
  | [] => 0
  | s :: rest => s + foldSettlements rest

/-- The batch settlement: sum all swap settlements in order. -/
def batchSettlement {s : CPMMState} (batch : Batch s) : Settlement :=
  foldSettlements (batchToSettlements batch)

/-! ## Part 3: Conservation (Balanced Composition)

If every swap in the batch produces a balanced settlement (Δ = 0),
the composed batch settlement is also balanced. This follows from
the Δ homomorphism and the kernel being closed under addition.
-/

/-- The net flow of a folded list of settlements is the sum of individual
    flows. This follows from the Δ AddMonoidHom property. -/
theorem foldSettlements_netFlow (settlements : List Settlement) :
    Δ (foldSettlements settlements) = (settlements.map Δ).sum := by
  induction settlements with
  | nil =>
    unfold foldSettlements
    exact Δ.map_zero
  | cons s rest ih =>
    unfold foldSettlements
    rw [Δ.map_add, ih, List.map_cons, List.sum_cons]

/-- If every settlement in a list is balanced, the folded settlement
    is balanced. This is the conservation composition theorem. -/
theorem foldSettlements_balanced (settlements : List Settlement)
    (hAll : ∀ st ∈ settlements, st.isBalanced) :
    (foldSettlements settlements).isBalanced := by
  induction settlements with
  | nil =>
    unfold foldSettlements Settlement.isBalanced
    exact Δ.map_zero
  | cons s rest ih =>
    unfold foldSettlements Settlement.isBalanced
    rw [Δ.map_add]
    rw [hAll s (by simp : s ∈ s :: rest)]
    rw [ih (fun st hst => hAll st (List.mem_cons_of_mem s hst))]
    ring

/-- Membership in `batchToSettlements` decomposes via `List.mem_map`. -/
theorem mem_batchToSettlements {s : CPMMState} : ∀ (batch : Batch s) (st : Settlement),
    st ∈ batchToSettlements batch ↔
      ∃ swap ∈ batch, validSwapToSettlement swap = st
  | [], st => by simp [batchToSettlements]
  | swap :: rest, st => by
    simp only [batchToSettlements, List.mem_cons]
    constructor
    · intro h
      cases h with
      | inl h => exact ⟨swap, by simp, h.symm⟩
      | inr h => obtain ⟨sw, hmem, heq⟩ := (mem_batchToSettlements rest st).mp h
                 exact ⟨sw, Or.inr hmem, heq⟩
    · rintro ⟨sw, hmem, heq⟩
      cases hmem with
      | inl heq2 => left; rw [← heq2, heq]
      | inr hmem' => right; exact (mem_batchToSettlements rest st).mpr ⟨sw, hmem', heq⟩

/-- THE PIPELINE CONSERVATION THEOREM: If every swap in a batch
    produces a balanced settlement, the composed batch settlement
    is balanced (Δ = 0).

    This composes the component-level balanced-composition property
    across an arbitrary-length batch by induction. -/
theorem pipeline_conservation {s : CPMMState} (batch : Batch s)
    (hAllBalanced :
      ∀ swap ∈ batch, (validSwapToSettlement swap).isBalanced) :
    (batchSettlement batch).isBalanced := by
  unfold batchSettlement
  apply foldSettlements_balanced
  intro st hst
  obtain ⟨swap, hmem, heq⟩ := (mem_batchToSettlements batch st).mp hst
  rw [← heq]
  exact hAllBalanced swap hmem

/-! ## Part 4: Non-Negativity (Safe Scalar Flow)

If every swap has `amount_in >= amount_out`, the composed batch
settlement has non-negative net flow. This follows from
`Settlement.safe_comp_safe` and induction.
-/

/-- If every settlement in a list is safe (Δ >= 0), the folded
    settlement is safe. -/
theorem foldSettlements_safe (settlements : List Settlement)
    (hAll : ∀ st ∈ settlements, st.isSafe) :
    (foldSettlements settlements).isSafe := by
  induction settlements with
  | nil =>
    unfold foldSettlements Settlement.isSafe
    exact le_of_eq Δ.map_zero
  | cons s rest ih =>
    unfold foldSettlements Settlement.isSafe
    rw [Δ.map_add]
    have hs := hAll s (by simp : s ∈ s :: rest)
    have hr := ih (fun st hst => hAll st (List.mem_cons_of_mem s hst))
    unfold Settlement.isSafe at hs hr
    linarith

/-- THE PIPELINE NON-NEGATIVITY THEOREM: If every swap in a batch
    has `amount_in >= amount_out` (safe scalar flow), the composed
    batch settlement has non-negative net flow (Δ >= 0). -/
theorem pipeline_non_negativity {s : CPMMState} (batch : Batch s)
    (hAllSafe :
      ∀ swap ∈ batch, (validSwapToSettlement swap).isSafe) :
    (batchSettlement batch).isSafe := by
  unfold batchSettlement
  apply foldSettlements_safe
  intro st hst
  obtain ⟨swap, hmem, heq⟩ := (mem_batchToSettlements batch st).mp hst
  rw [← heq]
  exact hAllSafe swap hmem

/-! ## Part 5: K-Preservation (Swap Chain)

Since each `ValidCPMMSwap` is parameterized by the state it operates on,
and the swap produces a new state, we model the batch as a chain where
each swap's output state feeds into the next swap's input state.
-/

/-- A chain of valid CPMM swaps: each swap operates on the state
    produced by the previous swap. -/
inductive SwapChain : CPMMState → Type
  | nil : SwapChain s
  | cons (swap : ValidCPMMSwap s) (rest : SwapChain swap.newState) :
      SwapChain s

/-- The final state after processing a swap chain. -/
def SwapChain.finalState : SwapChain s → CPMMState
  | nil => s
  | cons _ rest => rest.finalState

/-- K is non-decreasing across a swap chain.

    This is the pipeline K-preservation theorem: each valid CPMM swap
    preserves K (non-decreasing), so the entire chain preserves K
    by transitive induction. -/
theorem SwapChain.K_non_decreasing : ∀ (s : CPMMState) (chain : SwapChain s),
    chain.finalState.K ≥ s.K
  | _, nil => by simp [SwapChain.finalState, CPMMState.K]
  | _, cons swap rest => by
    simp only [SwapChain.finalState]
    have ih := SwapChain.K_non_decreasing swap.newState rest
    calc rest.finalState.K
        ≥ swap.newState.K := ih
      _ ≥ _ := valid_swap_preserves_K swap

/-! ## Part 6: End-to-End Pipeline Theorem

The main theorem: if a batch of valid CPMM swaps satisfies
(1) each swap is balanced (equal in/out), and
(2) each swap is safe (amount_in >= amount_out),
then the composed batch settlement is both balanced and safe.
-/

/-- THE END-TO-END PIPELINE THEOREM: If every swap in a batch
    is a valid CPMM swap that is both balanced and safe, the
    composed batch settlement is both balanced and safe.

    This composes:
    - Intent validation (external guard -> ValidCPMMSwap)
    - Swap execution (validSwapToSettlement)
    - Delta aggregation (foldSettlements)
    - Conservation check (pipeline_conservation)
    - Non-negativity check (pipeline_non_negativity)

    Non-claims:
    - Intent validation rules are external hypotheses.
    - Batch clearing objective (A,B optimality) is not proven here.
    - Fee handling uses the zero-fee model.
    - Multi-pool routing is not composed.
    - LP operations are not composed.
    - Permutation invariance (determinism) is an open gap. -/
theorem end_to_end_pipeline {s : CPMMState} (batch : Batch s)
    (hAllBalanced :
      ∀ swap ∈ batch, (validSwapToSettlement swap).isBalanced)
    (hAllSafe :
      ∀ swap ∈ batch, (validSwapToSettlement swap).isSafe) :
    (batchSettlement batch).isBalanced ∧
    (batchSettlement batch).isSafe := by
  refine ⟨?_, ?_⟩
  · exact pipeline_conservation batch hAllBalanced
  · exact pipeline_non_negativity batch hAllSafe

/-! ## Part 7: Non-Vacuity Witnesses

Concrete examples showing the pipeline theorems are not vacuous.
-/

/-- Witness: empty batch is trivially balanced. -/
theorem witness_empty_batch_balanced :
    let s : CPMMState := ⟨1000, 1000⟩
    let batch : Batch s := []
    (batchSettlement batch).isBalanced := by
  unfold batchSettlement foldSettlements batchToSettlements
    Settlement.isBalanced
  exact Δ.map_zero

/-- Witness: empty batch is trivially safe. -/
theorem witness_empty_batch_safe :
    let s : CPMMState := ⟨1000, 1000⟩
    let batch : Batch s := []
    (batchSettlement batch).isSafe := by
  unfold batchSettlement foldSettlements batchToSettlements
    Settlement.isSafe
  exact le_of_eq Δ.map_zero

/-- Witness: single-swap chain preserves K.
    swap.amount_out = (1000 * 100) / 1100 = 90
    new K = 1100 * 910 = 1,001,000 >= 1,000,000 = old K -/
theorem witness_chain_K_single :
    let s : CPMMState := ⟨1000, 1000⟩
    let swap : ValidCPMMSwap s := ⟨100, by decide, by decide, by decide⟩
    let chain : SwapChain s := SwapChain.cons swap SwapChain.nil
    chain.finalState.K ≥ s.K := by
  simp only [SwapChain.finalState, CPMMState.K, ValidCPMMSwap.newState,
             ValidCPMMSwap.amount_out, swapOutputZeroFee, kValue]
  native_decide

/-- Witness: two-swap chain preserves K.
    swap1: amount_out = 90, s1 = ⟨1100, 910⟩, K1 = 1,001,000
    swap2: amount_out = (910*50)/(1100+50) = 39, s2 = ⟨1150, 871⟩
    K2 = 1150 * 871 = 1,001,650 >= 1,000,000 -/
theorem witness_chain_K_double :
    let s : CPMMState := ⟨1000, 1000⟩
    let swap1 : ValidCPMMSwap s := ⟨100, by decide, by decide, by decide⟩
    let s1 := swap1.newState
    let swap2 : ValidCPMMSwap s1 := ⟨50, by decide, by decide, by decide⟩
    let chain : SwapChain s :=
      SwapChain.cons swap1 (SwapChain.cons swap2 SwapChain.nil)
    chain.finalState.K ≥ s.K := by
  simp only [SwapChain.finalState, CPMMState.K, ValidCPMMSwap.newState,
             ValidCPMMSwap.amount_out, swapOutputZeroFee, kValue]
  native_decide

end SettlementPipeline
