import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

-- Import our modules
import Proofs.SettlementAlgebra
import Proofs.BatchOptimality
import Proofs.CPMMSettlement

/-!
# Batch-CPMM Unification

This file unifies the two algebraic structures of DeFi:
1. **Conservation** (from SettlementAlgebra): Δ : Settlement →+ ℤ
2. **Optimality** (from BatchOptimality): AB : Intent × Outcome → ℕ × ℕ

The key insight: A valid batch settlement must satisfy BOTH:
- Conservation: K(final_state) ≥ K(initial_state) (true CPMM invariant)
  — and the weaker scalar check Δ ≥ 0 (unit-mixing, not economic safety)
- Optimality: AB is computed and can be compared lexicographically

## The Two Homomorphisms Together

```
                    ┌───────────────────┐
                    │  Batch Settlement │
                    └────────┬──────────┘
                             │
              ┌──────────────┼──────────────┐
              │              │              │
              ▼              │              ▼
     ┌─────────────┐         │      ┌─────────────┐
     │ Conservation│         │      │  Optimality │
     │   Δ ≥ 0     │         │      │  max(A,B)   │
     └─────────────┘         │      └─────────────┘
                             │
                             ▼
                    ┌───────────────────┐
                    │  Valid Settlement │
                    │  (both satisfied) │
                    └───────────────────┘
```

## Key Results (Proved)

1. **Compositional Conservation**: If each swap is safe, batch is safe
2. **AB Additivity**: AB is additive over batch append
3. **Dominance/Pareto**: Definitions provided; connecting lex-max to
   Pareto or proving argmax existence over a finite candidate set is future work
-/

namespace BatchCPMMUnification

open SettlementAlgebra
open BatchOptimality
open CPMMSettlement
open CPMMInvariants

/-! ## Part 1: Batch as Multiple Intent-Outcome Pairs

A batch settlement consists of multiple intents, each with an outcome.
-/

/-- A batch settlement: list of (intent, outcome) pairs -/
structure BatchSettlement where
  pairs : List (Sigma fun i : BatchOptimality.Intent => BatchOptimality.ValidOutcome i)

/-- Empty batch -/
def BatchSettlement.empty : BatchSettlement := ⟨[]⟩

/-- Single intent batch -/
def BatchSettlement.single (i : BatchOptimality.Intent) (o : BatchOptimality.ValidOutcome i) : BatchSettlement :=
  ⟨[⟨i, o⟩]⟩

/-- Combine two batches -/
def BatchSettlement.append (b₁ b₂ : BatchSettlement) : BatchSettlement :=
  ⟨b₁.pairs ++ b₂.pairs⟩

/-! ## Part 2: Batch → Settlement (Conservation View)

Convert a batch to a single Settlement for conservation analysis.
Each executed intent contributes to the total settlement.
-/

/-- Convert an intent-outcome pair to a settlement.
    Pattern-matches on ValidOutcome to align with CBC design:
    - unfilled → zero settlement
    - filled → cpmmSwapToSettlement amt_in output -/
def pairToSettlement (io : Sigma fun i : BatchOptimality.Intent => BatchOptimality.ValidOutcome i) : Settlement :=
  match io.2 with
  | .unfilled => (0 : Settlement)
  | .filled output _ => cpmmSwapToSettlement io.1.amt_in output

/-- Fold a batch into a single settlement -/
def batchToSettlement (b : BatchSettlement) : Settlement :=
  b.pairs.foldl (fun acc io => acc ∘ₛ pairToSettlement io) (0 : Settlement)

/-- Empty batch has zero settlement -/
theorem batchToSettlement_empty : batchToSettlement BatchSettlement.empty = (0 : Settlement) := by
  rfl

/-! ## Part 3: Batch → (A,B) (Optimality View)

Compute the total (Volume, Surplus) for a batch.
-/

/-- Total (A,B) for a batch -/
def batchAB (b : BatchSettlement) : ℕ × ℕ :=
  b.pairs.foldl (fun acc io => pairAdd acc (AB io.2)) (0, 0)

/-- Empty batch has (0,0) -/
theorem batchAB_empty : batchAB BatchSettlement.empty = (0, 0) := by
  rfl

/-- Single batch has same AB as the pair -/
theorem batchAB_single (i : BatchOptimality.Intent) (o : BatchOptimality.ValidOutcome i) :
    batchAB (BatchSettlement.single i o) = AB o := by
  simp only [batchAB, BatchSettlement.single, pairAdd]
  simp only [List.foldl, Nat.zero_add]

/-! ## Part 4: Conservation Property

If each swap satisfies amt_in ≥ output, the batch is safe.
-/

/-- Zero settlement is safe (Δ(0) = 0 ≥ 0) -/
theorem zero_settlement_safe : (0 : Settlement).isSafe := by
  unfold Settlement.isSafe Δ netFlow
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  decide

/-- A pair is safe if amt_in ≥ output (when executed).
    Matches ValidOutcome pattern: unfilled is trivially safe. -/
def pairIsSafe (io : Sigma fun i : BatchOptimality.Intent => BatchOptimality.ValidOutcome i) : Prop :=
  match io.2 with
  | .unfilled => True
  | .filled output _ => io.1.amt_in ≥ output

/-- A batch is safe if all pairs are safe -/
def batchIsSafe (b : BatchSettlement) : Prop :=
  ∀ io ∈ b.pairs, pairIsSafe io

/-- Safe pair produces safe settlement -/
theorem safe_pair_safe_settlement (io : Sigma fun i : BatchOptimality.Intent => BatchOptimality.ValidOutcome i)
    (h : pairIsSafe io) : (pairToSettlement io).isSafe := by
  cases io with | mk i o =>
  cases o with
  | unfilled => exact zero_settlement_safe
  | filled output _ => exact cpmm_swap_safe i.amt_in output h

/-! ## Part 5: Compositional Safety (THE KEY THEOREM)

This is the theorem that was previously claimed but not proved:
If every pair in a batch is safe, the combined settlement is safe.
-/

/-- Helper: foldl with safe start and safe pairs produces safe result -/
theorem foldl_safe_settlement_aux
    (start : Settlement)
    (h_start : start.isSafe)
    (pairs : List (Sigma fun i : BatchOptimality.Intent => BatchOptimality.ValidOutcome i))
    (h_all_safe : ∀ io ∈ pairs, pairIsSafe io) :
    (pairs.foldl (fun acc io => acc ∘ₛ pairToSettlement io) start).isSafe := by
  induction pairs generalizing start with
  | nil =>
    simp only [List.foldl_nil]
    exact h_start
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h_hd_mem : hd ∈ hd :: tl := List.mem_cons_self
    have h_hd_safe : pairIsSafe hd := h_all_safe hd h_hd_mem
    have h_tl_safe : ∀ io ∈ tl, pairIsSafe io := fun io hio =>
      h_all_safe io (List.mem_cons_of_mem hd hio)
    have h_pair_safe : (pairToSettlement hd).isSafe := safe_pair_safe_settlement hd h_hd_safe
    have h_comp_safe : (start ∘ₛ pairToSettlement hd).isSafe :=
      Settlement.safe_comp_safe h_start h_pair_safe
    exact ih (start ∘ₛ pairToSettlement hd) h_comp_safe h_tl_safe

/-- foldl from zero with safe pairs is safe -/
theorem foldl_safe_settlement
    (pairs : List (Sigma fun i : BatchOptimality.Intent => BatchOptimality.ValidOutcome i))
    (h_all_safe : ∀ io ∈ pairs, pairIsSafe io) :
    (pairs.foldl (fun acc io => acc ∘ₛ pairToSettlement io) (0 : Settlement)).isSafe :=
  foldl_safe_settlement_aux 0 zero_settlement_safe pairs h_all_safe

/-- THE KEY COMPOSITIONAL THEOREM: batchIsSafe implies batchToSettlement is safe -/
theorem batch_safe_implies_settlement_safe (b : BatchSettlement) (h : batchIsSafe b) :
    (batchToSettlement b).isSafe := by
  simp only [batchToSettlement, batchIsSafe] at *
  exact foldl_safe_settlement b.pairs h

/-! ## Part 5b: Optimality Properties

Volume and surplus are both additive, so AB is additive over batches.
-/

/-- Helper: foldl with pairAdd shifts the starting point -/
theorem foldl_pairAdd_shift (start : ℕ × ℕ)
    (xs : List (Sigma fun i : BatchOptimality.Intent => BatchOptimality.ValidOutcome i)) :
    List.foldl (fun acc io => pairAdd acc (AB io.2)) start xs =
    pairAdd start (List.foldl (fun acc io => pairAdd acc (AB io.2)) (0, 0) xs) := by
  induction xs generalizing start with
  | nil => simp [pairAdd]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih (pairAdd start (AB hd.2))]
    rw [ih (pairAdd (0, 0) (AB hd.2))]
    simp only [pairAdd, Nat.zero_add]
    ext <;> omega

/-- AB is additive: combining batches adds their ABs -/
theorem batchAB_append (b₁ b₂ : BatchSettlement) :
    batchAB (b₁.append b₂) = pairAdd (batchAB b₁) (batchAB b₂) := by
  simp only [batchAB, BatchSettlement.append]
  rw [List.foldl_append]
  rw [foldl_pairAdd_shift]

/-! ## Part 5c: Batch Homomorphism Lemmas

batchToSettlement and batchIsSafe respect batch append,
enabling compositional reasoning about batches.
-/

/-- Helper: settlement fold shifts by the starting value (additive shift) -/
theorem foldl_settlement_shift (start : Settlement)
    (pairs : List (Sigma fun i : BatchOptimality.Intent => BatchOptimality.ValidOutcome i)) :
    List.foldl (fun acc io => acc ∘ₛ pairToSettlement io) start pairs =
    start ∘ₛ List.foldl (fun acc io => acc ∘ₛ pairToSettlement io) (0 : Settlement) pairs := by
  induction pairs generalizing start with
  | nil => simp only [List.foldl_nil, Settlement.comp, add_zero]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih (start ∘ₛ pairToSettlement hd)]
    rw [ih ((0 : Settlement) ∘ₛ pairToSettlement hd)]
    simp only [Settlement.comp, zero_add, add_assoc]

/-- batchToSettlement is homomorphic over append -/
theorem batchToSettlement_append (b₁ b₂ : BatchSettlement) :
    batchToSettlement (b₁.append b₂) = batchToSettlement b₁ ∘ₛ batchToSettlement b₂ := by
  simp only [batchToSettlement, BatchSettlement.append]
  rw [List.foldl_append]
  rw [foldl_settlement_shift]

/-- batchIsSafe splits over append -/
theorem batchIsSafe_append (b₁ b₂ : BatchSettlement) :
    batchIsSafe (b₁.append b₂) ↔ batchIsSafe b₁ ∧ batchIsSafe b₂ := by
  simp only [batchIsSafe, BatchSettlement.append, List.mem_append]
  constructor
  · intro h; exact ⟨fun io hio => h io (Or.inl hio), fun io hio => h io (Or.inr hio)⟩
  · rintro ⟨h₁, h₂⟩ io (hio | hio)
    · exact h₁ io hio
    · exact h₂ io hio

/-! ## Part 5d: Compositional K-Monotonicity (State Transition Model)

The ACTUAL safety property of CPMM is K-monotonicity (`K = reserve_in × reserve_out`
never decreases). Here we model batch execution as iterated state transitions
and prove K-monotonicity composes across the batch.

This upgrades from the scalar-flow view (`Δ ≥ 0`, which is semantically weak)
to the true CPMM invariant applied compositionally.
-/

/-- Execute a single zero-fee swap on a CPMM state -/
def executeSwap (s : CPMMState) (amount_in : ℕ) : CPMMState :=
  { reserve_in := s.reserve_in + amount_in
    reserve_out := s.reserve_out - swapOutputZeroFee s.reserve_in s.reserve_out amount_in }

/-- Execute a batch of swaps sequentially on a CPMM state -/
def executeBatchSwaps (initial : CPMMState) (amounts : List ℕ) : CPMMState :=
  amounts.foldl executeSwap initial

/-- Zero-fee swap output is strictly less than output reserve -/
private theorem swapOutputZeroFee_lt {rin rout ain : ℕ}
    (hrin : 0 < rin) (_hrout : 0 < rout) (_hain : 0 < ain) :
    swapOutputZeroFee rin rout ain < rout := by
  simp [swapOutputZeroFee]; apply Nat.div_lt_of_lt_mul; ring_nf; nlinarith

/-- Single swap preserves K-monotonicity -/
theorem executeSwap_K_mono (s : CPMMState) (a : ℕ)
    (hrin : 0 < s.reserve_in) (hrout : 0 < s.reserve_out) (ha : 0 < a) :
    (executeSwap s a).K ≥ s.K := by
  simp only [executeSwap, CPMMState.K]
  exact k_monotone_zero_fee hrin hrout ha

/-- Single swap preserves positive reserves -/
theorem executeSwap_reserves_pos (s : CPMMState) (a : ℕ)
    (hrin : 0 < s.reserve_in) (hrout : 0 < s.reserve_out) (ha : 0 < a) :
    0 < (executeSwap s a).reserve_in ∧ 0 < (executeSwap s a).reserve_out := by
  constructor
  · simp only [executeSwap]; omega
  · simp only [executeSwap]
    have hlt := swapOutputZeroFee_lt hrin hrout ha
    omega

/-- THE KEY THEOREM: Compositional K-Monotonicity.
    Executing a batch of swaps (all with positive input) on a pool with
    positive reserves yields a final state with K ≥ initial K.
    Each step preserves K (k_monotone_zero_fee) and positive reserves
    (swapOutputZeroFee_lt), so the invariant propagates by induction. -/
theorem executeBatchSwaps_K_mono
    (initial : CPMMState)
    (amounts : List ℕ)
    (hrin : 0 < initial.reserve_in)
    (hrout : 0 < initial.reserve_out)
    (h_pos : ∀ a ∈ amounts, 0 < a) :
    (executeBatchSwaps initial amounts).K ≥ initial.K := by
  induction amounts generalizing initial with
  | nil => exact le_refl _
  | cons a rest ih =>
    show (executeBatchSwaps (executeSwap initial a) rest).K ≥ initial.K
    have ha_mem : a ∈ a :: rest := List.mem_cons_self
    have ha : 0 < a := h_pos a ha_mem
    have h_rest : ∀ a' ∈ rest, 0 < a' := fun a' ha' =>
      h_pos a' (List.mem_cons_of_mem a ha')
    have h_step := executeSwap_K_mono initial a hrin hrout ha
    have ⟨hrin', hrout'⟩ := executeSwap_reserves_pos initial a hrin hrout ha
    have h_batch := ih (executeSwap initial a) hrin' hrout' h_rest
    omega

/-! ## Part 5e: Exact Batch K-Gap via Closed Form

The K-gap closed form `K_new - K_old = (y * a) % (x + a)` gives us the
EXACT K-increase per swap. For a batch, the total K-gap equals the sum of
per-step remainders (telescoping).

**Single step**: `K(swap(s, a)) = K(s) + (s.y * a) % (s.x + a)`
**Batch**: `K(batch(s, [a₁,...,aₙ])) = K(s) + Σᵢ remainder(sᵢ, aᵢ)`
-/

/-- Per-step K-gap remainder for a single swap -/
def swapKGapRemainder (s : CPMMState) (a : ℕ) : ℕ :=
  (s.reserve_out * a) % (s.reserve_in + a)

/-- The K-gap of a single executeSwap is exactly the Euclidean remainder.
    This bridges the compositional K-mono theorem to the closed-form K-gap. -/
theorem executeSwap_K_gap_exact (s : CPMMState) (a : ℕ) :
    (executeSwap s a).K = s.K + swapKGapRemainder s a := by
  simp only [executeSwap, CPMMState.K, kValue, swapKGapRemainder]
  exact k_gap_exact s.reserve_in s.reserve_out a

/-- Non-vacuity: exact K-gap for a concrete single swap -/
theorem witness_executeSwap_K_gap :
    let s : CPMMState := ⟨1000, 1000⟩
    let a := 100
    (executeSwap s a).K = s.K + swapKGapRemainder s a ∧
    swapKGapRemainder s a = 1000 := by
  native_decide

/-- Sum of per-step K-gap remainders across a batch of swaps -/
def batchKGapSum : CPMMState → List ℕ → ℕ
  | _, [] => 0
  | s, a :: rest => swapKGapRemainder s a + batchKGapSum (executeSwap s a) rest

/-- **Batch K-Gap Telescoping**: the final K equals the initial K plus the
    sum of per-step Euclidean remainders. This is the batch generalization
    of `executeSwap_K_gap_exact`: each swap contributes its own remainder,
    and the total K-increase is their sum. -/
theorem executeBatchSwaps_K_gap_sum (s : CPMMState) (amounts : List ℕ) :
    (executeBatchSwaps s amounts).K = s.K + batchKGapSum s amounts := by
  induction amounts generalizing s with
  | nil => simp [executeBatchSwaps, batchKGapSum]
  | cons a rest ih =>
    show (executeBatchSwaps (executeSwap s a) rest).K =
         s.K + (swapKGapRemainder s a + batchKGapSum (executeSwap s a) rest)
    rw [ih (executeSwap s a)]
    have := executeSwap_K_gap_exact s a
    omega

/-- Non-vacuity: batch K-gap sum for a concrete 3-swap batch -/
theorem witness_batch_K_gap_sum :
    let s : CPMMState := ⟨1000, 1000⟩
    let amounts := [100, 50, 200]
    (executeBatchSwaps s amounts).K = s.K + batchKGapSum s amounts ∧
    batchKGapSum s amounts > 0 := by
  native_decide

/-! ## Part 5f: Refinement Bridge — Two Models, One Verification

The proof stack has two batch models:
1. **Intent/Outcome** (Parts 1-5c): `BatchSettlement` with Δ (conservation) and AB (optimality)
2. **State Transition** (Parts 5d-5e): `executeBatchSwaps` with K-mono and K-gap

This section bridges them. When intents are realized as CPMM swaps (outputs
computed by sequential `swapOutputZeroFee`), the state-transition properties
(K-mono, K-gap) hold for the same execution that feeds into the settlement
model (Δ, AB). The key link is `realizeBatch_final_state`, which proves the
output-computing model and the state-transition model reach the same final state.
-/

/-- Realize a single swap: compute output via swapOutputZeroFee and advance state -/
def realizeSwap (s : CPMMState) (amt_in : ℕ) : ℕ × CPMMState :=
  (swapOutputZeroFee s.reserve_in s.reserve_out amt_in, executeSwap s amt_in)

/-- Realize a batch of swaps sequentially on a CPMM pool.
    Returns the list of computed outputs and the final pool state. -/
def realizeBatchAmounts : CPMMState → List ℕ → List ℕ × CPMMState
  | s, [] => ([], s)
  | s, a :: rest =>
    let (output, s') := realizeSwap s a
    let (outputs, final) := realizeBatchAmounts s' rest
    (output :: outputs, final)

/-- **Key Bridge**: the final state of realizeBatchAmounts equals executeBatchSwaps.
    This connects the output-computing model (which feeds settlements) to the
    state-transition model (where K-mono and K-gap are proved). -/
theorem realizeBatch_final_state (s : CPMMState) (amounts : List ℕ) :
    (realizeBatchAmounts s amounts).2 = executeBatchSwaps s amounts := by
  induction amounts generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [realizeBatchAmounts, realizeSwap, executeBatchSwaps, List.foldl]
    exact ih (executeSwap s a)

/-- Outputs have the same length as inputs -/
theorem realizeBatch_length (s : CPMMState) (amounts : List ℕ) :
    (realizeBatchAmounts s amounts).1.length = amounts.length := by
  induction amounts generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [realizeBatchAmounts, realizeSwap, List.length_cons]
    exact congrArg (· + 1) (ih (executeSwap s a))

/-- Reserve-in grows by the sum of input amounts across a batch -/
theorem executeBatchSwaps_reserve_in (s : CPMMState) (amounts : List ℕ) :
    (executeBatchSwaps s amounts).reserve_in = s.reserve_in + amounts.sum := by
  induction amounts generalizing s with
  | nil => simp [executeBatchSwaps]
  | cons a rest ih =>
    show (executeBatchSwaps (executeSwap s a) rest).reserve_in =
         s.reserve_in + ((a :: rest).sum)
    rw [List.sum_cons, ih (executeSwap s a)]
    simp [executeSwap]; omega

/-- **Unified Safety Theorem**: For a batch of swaps realized on a CPMM pool,
    ALL safety layers hold simultaneously for the same execution:
    - **Layer 1 (K-mono)**: K(final) ≥ K(initial) — LP funds never decrease
    - **Layer 2 (K-gap)**: K(final) = K(initial) + Σ remainders — exact accounting
    - **Layer 3 (reserves)**: reserve_in tracks total deposited
    This is the theorem that unifies the intent/outcome model (where each output
    feeds into Δ and AB) with the state-transition model (where K is tracked). -/
theorem unified_batch_safety (s : CPMMState) (amounts : List ℕ)
    (hrin : 0 < s.reserve_in) (hrout : 0 < s.reserve_out)
    (h_pos : ∀ a ∈ amounts, 0 < a) :
    let final := (realizeBatchAmounts s amounts).2
    -- Layer 1: K-monotonicity (LP safety)
    final.K ≥ s.K ∧
    -- Layer 2: K-gap exact (precise accounting)
    final.K = s.K + batchKGapSum s amounts ∧
    -- Layer 3: Reserve tracking
    final.reserve_in = s.reserve_in + amounts.sum := by
  refine ⟨?_, ?_, ?_⟩
  · rw [realizeBatch_final_state]
    exact executeBatchSwaps_K_mono s amounts hrin hrout h_pos
  · rw [realizeBatch_final_state]
    exact executeBatchSwaps_K_gap_sum s amounts
  · rw [realizeBatch_final_state]
    exact executeBatchSwaps_reserve_in s amounts

/-- Non-vacuity: unified safety for a concrete 3-swap batch on pool (1000, 1000) -/
theorem witness_unified_batch :
    let s : CPMMState := ⟨1000, 1000⟩
    let amounts := [100, 50, 200]
    let (outputs, final) := realizeBatchAmounts s amounts
    -- All three layers verified on concrete values
    final.K ≥ s.K ∧
    final.K = s.K + batchKGapSum s amounts ∧
    final.reserve_in = s.reserve_in + amounts.sum ∧
    -- Concrete output values
    outputs = [90, 39, 129] ∧
    outputs.length = amounts.length := by
  native_decide

/-! ## Part 6: The Two Homomorphisms

The key insight: both Δ and AB are homomorphisms!

- Δ : Settlement →+ ℤ (additive homomorphism)
- AB extends additively over batches

This means we can verify complex batches by verifying individual operations.
-/

/-- Conservation is homomorphic: Δ(s₁ + s₂) = Δ(s₁) + Δ(s₂)
    (This is conservation_homomorphism from SettlementAlgebra) -/
theorem conservation_is_homomorphic (s₁ s₂ : Settlement) :
    Δ (s₁ ∘ₛ s₂) = Δ s₁ + Δ s₂ :=
  conservation_homomorphism s₁ s₂

/-! ## Part 7: Dominance and Pareto Efficiency (Definitions Only)

These definitions enable comparing batch settlements via lexicographic
dominance. Connecting lex-max to Pareto efficiency or proving argmax
existence over a finite candidate set is left for future work.
-/

/-- A batch dominates another if it has strictly better (A,B) -/
def dominates (b₁ b₂ : BatchSettlement) : Prop :=
  lexLt (batchAB b₂) (batchAB b₁)

/-- A batch is Pareto efficient among a set if nothing dominates it -/
def isParetoEfficient (b : BatchSettlement) (candidates : List BatchSettlement) : Prop :=
  ∀ c ∈ candidates, ¬dominates c b

/-! ## Part 8: Non-vacuity Witnesses -/

/-- Witness: Concrete batch with computable (A,B) -/
theorem witness_batch_ab :
    let i₁ : BatchOptimality.Intent := ⟨100, 90⟩
    let o₁ : BatchOptimality.ValidOutcome i₁ := BatchOptimality.ValidOutcome.filled 95 (by decide)
    let i₂ : BatchOptimality.Intent := ⟨50, 45⟩
    let o₂ : BatchOptimality.ValidOutcome i₂ := BatchOptimality.ValidOutcome.filled 48 (by decide)
    let b := BatchSettlement.mk [⟨i₁, o₁⟩, ⟨i₂, o₂⟩]
    batchAB b = (150, 8) := by
  native_decide

/-- Witness: Safe batch has safe settlement -/
theorem witness_safe_batch :
    let i : BatchOptimality.Intent := ⟨100, 90⟩
    let o : BatchOptimality.ValidOutcome i := BatchOptimality.ValidOutcome.filled 95 (by decide)
    pairIsSafe ⟨i, o⟩ ∧ (pairToSettlement ⟨i, o⟩).isSafe := by
  refine ⟨?_, ?_⟩
  · show (100 : ℕ) ≥ 95; omega
  · exact safe_pair_safe_settlement _ (show (100 : ℕ) ≥ 95 by omega)

/-- Witness: Lexicographic comparison of batches -/
theorem witness_batch_dominance :
    let b₁ :=
      BatchSettlement.mk
        [⟨⟨100, 90⟩, BatchOptimality.ValidOutcome.filled 95 (by decide)⟩]  -- (100, 5)
    let b₂ :=
      BatchSettlement.mk
        [⟨⟨50, 45⟩, BatchOptimality.ValidOutcome.filled 48 (by decide)⟩]   -- (50, 3)
    dominates b₁ b₂ := by
  simp only [dominates, batchAB, AB, volume, surplus, lexLt, pairAdd]
  simp only [List.foldl]
  left; native_decide

/-- Witness: batchToSettlement is homomorphic over append -/
theorem witness_batchToSettlement_append :
    let i₁ : BatchOptimality.Intent := ⟨100, 90⟩
    let o₁ : BatchOptimality.ValidOutcome i₁ := BatchOptimality.ValidOutcome.filled 95 (by decide)
    let i₂ : BatchOptimality.Intent := ⟨50, 45⟩
    let o₂ : BatchOptimality.ValidOutcome i₂ := BatchOptimality.ValidOutcome.filled 48 (by decide)
    let b₁ := BatchSettlement.mk [⟨i₁, o₁⟩]
    let b₂ := BatchSettlement.mk [⟨i₂, o₂⟩]
    batchToSettlement (b₁.append b₂) = batchToSettlement b₁ ∘ₛ batchToSettlement b₂ := by
  exact batchToSettlement_append _ _

/-- Witness: Compositional K-monotonicity — all hypotheses satisfied and conclusion holds -/
theorem witness_batch_K_mono :
    let s : CPMMState := ⟨1000, 1000⟩
    let amounts := [100, 50, 200]
    0 < s.reserve_in ∧ 0 < s.reserve_out ∧
    (∀ a ∈ amounts, 0 < a) ∧
    (executeBatchSwaps s amounts).K ≥ s.K := by
  native_decide

/-- Witness: Batch execution preserves positive reserves -/
theorem witness_batch_reserves :
    let s : CPMMState := ⟨1000, 1000⟩
    let amounts := [100, 50]
    let final := executeBatchSwaps s amounts
    0 < final.reserve_in ∧ 0 < final.reserve_out := by
  native_decide

/-! ## Part 9: Summary

### The Three Verified Layers

| Layer | Invariant | Proved Where |
|-------|-----------|--------------|
| **K-Monotonicity** | `K(new) ≥ K(old)` per swap and per batch | `executeBatchSwaps_K_mono` |
| **Scalar Flow** | `Δ(batch) ≥ 0` when each `amt_in ≥ amt_out` | `batch_safe_implies_settlement_safe` |
| **Optimality** | `AB(b₁++b₂) = AB(b₁)+AB(b₂)` | `batchAB_append` |

### Key Properties (Proved)

| Property | Formula | Status |
|----------|---------|--------|
| **K-gap exact** | `K(swap) = K(old) + (y*a) % (x+a)` | Proved (`executeSwap_K_gap_exact`) |
| **K-gap telescoping** | `K(batch) = K(init) + Σ remainders` | Proved (`executeBatchSwaps_K_gap_sum`) |
| K-mono (single) | `K(executeSwap s a) ≥ K(s)` | Proved (`executeSwap_K_mono`) |
| K-mono (batch) | `K(executeBatchSwaps s as) ≥ K(s)` | Proved (`executeBatchSwaps_K_mono`) |
| Reserves stay positive | Reserves > 0 propagates through batch | Proved (`executeSwap_reserves_pos`) |
| Settlement homomorphism | `batchToSettlement(b₁++b₂) = batchToSettlement(b₁) + batchToSettlement(b₂)` | Proved (`batchToSettlement_append`) |
| Safety splits | `batchIsSafe(b₁++b₂) ↔ batchIsSafe(b₁) ∧ batchIsSafe(b₂)` | Proved (`batchIsSafe_append`) |
| Compositional Δ-safety | all safe → batch safe | Proved (`batch_safe_implies_settlement_safe`) |
| AB additive | `AB(b₁++b₂) = AB(b₁)+AB(b₂)` | Proved (`batchAB_append`) |
| **Refinement bridge** | `realizeBatch` final state = `executeBatchSwaps` | Proved (`realizeBatch_final_state`) |
| **Unified safety** | K-mono + K-gap + reserve tracking in one theorem | Proved (`unified_batch_safety`) |
| **Reserve tracking** | `reserve_in(final) = reserve_in(init) + Σ amounts` | Proved (`executeBatchSwaps_reserve_in`) |
| Dominance | lexLt comparison | Defined, witnesses provided |
| Pareto / argmax | lex-max over candidates | **Not proved** (future work) |

### The Refinement Bridge (Part 5f)

The two batch models are unified via `realizeBatchAmounts`:
```
  Intent/Outcome Model              State-Transition Model
  (Δ, AB properties)                (K-mono, K-gap properties)
          │                                    │
          └──── realizeBatchAmounts ────────────┘
                        │
              realizeBatch_final_state
              (proves same final state)
                        │
                        ▼
              unified_batch_safety
              (all layers hold simultaneously)
```

### The DeFi Safety Theorem (Proved)

> **Unified view** (`unified_batch_safety`):
> For any batch of swaps realized on a CPMM pool with positive reserves,
> ALL safety layers hold simultaneously:
> - K(final) ≥ K(initial) (LP funds never decrease)
> - K(final) = K(initial) + Σ remainders (exact K accounting)
> - reserve_in(final) = reserve_in(initial) + Σ amounts (deposit tracking)
>
> **State-transition view** (Part 5d):
> K is nondecreasing across the entire batch (`executeBatchSwaps_K_mono`).
>
> **Scalar-flow view** (Part 4):
> Δ(batch) ≥ 0 when each `amt_in ≥ amt_out` (`batch_safe_implies_settlement_safe`),
> and AB is additive (`batchAB_append`).
>
> **Note**: Δ measures net scalar flow, not value. K-monotonicity is
> the true CPMM invariant. Both layers are proved compositionally.
-/

end BatchCPMMUnification
