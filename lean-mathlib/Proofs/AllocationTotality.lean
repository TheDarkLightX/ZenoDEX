import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Proofs.AntiFragmentation

/-!
# Routing Allocation Totality (ShapeForge: split_routing_allocation_contract)

For an exact-in split-route with demand D, the router must produce an allocation
(a list of per-leg input amounts) satisfying two properties simultaneously:

  1. **Full input consumption**: the leg amounts sum to D.
  2. **Non-degenerate legs**: every leg carries strictly positive input.

We model a valid allocation as `ValidAllocation D legs` where `legs : List Nat`
has every element positive and `legs.sum = D`.

## Substantive Theorems

| # | Name | Statement |
|---|------|-----------|
| 1 | `pos_legs_sum_pos` | Non-empty positive-leg list sums to a positive number |
| 2 | `singleton_partition_unique` | The only 1-leg allocation of D is [D] |
| 3 | `leg_le_total` | Every individual leg is bounded by D |
| 4 | `length_le_total` | A valid allocation has at most D legs |
| 5 | `tight_leg_bound` | Every leg satisfies l + (k-1) ≤ D (accounts for other legs) |
| 6 | `split_leg_preserves_valid` | Splitting one leg into two positive parts preserves validity |
| 7 | `merge_legs_preserves_valid` | Merging two adjacent legs preserves validity |
| 8 | `concat_valid` | Concatenating two valid allocations yields combined allocation |
| 9 | `prepend_valid` | Prepending a positive leg preserves validity |
| 10 | `remove_head_valid` | Removing the first leg produces a valid allocation of the remainder |
| 11 | `validAllocation_cons_iff` | Iff characterization: cons ↔ positive head ∧ head ≤ D ∧ valid tail |
| 12 | `allocation_rec` | Structural induction principle for valid allocations |
| 13 | `validAllocation_singleton_iff` | Iff characterization: [a] valid for D ↔ a = D ∧ 0 < D |
| 14 | `single_leg_maximizes_output` | Cross-file bridge: multi-leg output ≤ single swap |
| 15 | `allocation_output_le_reserve` | Output bounded by reserve regardless of allocation |

## Non-vacuity witnesses (native_decide)

| # | Name | Scenario |
|---|------|----------|
| W1 | `witness_validity` | Valid allocations accepted; sum mismatches and zero legs rejected |
| W2 | `witness_operations` | Splitting preserves validity; split loses CPMM output |

## Evidence chain

- Python: `src/core/split_routing.py` enforces `sum(amounts) == total_in` and all amounts > 0
- ESSO: `src/kernels/dex/split_router_ternary_v1.yaml` verifies bounded allocation invariants
- This file: Lean proof (formal, no placeholders)
-/

namespace Proofs
namespace AllocationTotality

/-! ## Core definition -/

/-- A valid allocation of demand `D` across routing legs.
    Every leg carries strictly positive input and the legs sum exactly to `D`. -/
structure ValidAllocation (D : ℕ) (legs : List ℕ) : Prop where
  all_pos : ∀ l ∈ legs, 0 < l
  sum_eq  : legs.sum = D

/-! ## Decidability (needed for native_decide witnesses) -/

instance instDecidableValidAllocation (D : ℕ) (legs : List ℕ) :
    Decidable (ValidAllocation D legs) :=
  have : Decidable (∀ l ∈ legs, 0 < l) := List.decidableBAll (fun l => 0 < l) legs
  have : Decidable (legs.sum = D) := decEq legs.sum D
  if hp : (∀ l ∈ legs, 0 < l) then
    if hs : legs.sum = D then isTrue ⟨hp, hs⟩
    else isFalse (fun h => hs h.sum_eq)
  else isFalse (fun h => hp h.all_pos)

/-! ## Helper lemma: positive legs imply length bounded by sum -/

/-- If every element of a list is positive, then the list length is at most the sum.
    Derived by induction: each element contributes at least 1 to the sum.
    This is the key arithmetic fact behind `length_le_total`. -/
private lemma length_le_sum_of_pos (legs : List ℕ) (hpos : ∀ l ∈ legs, 0 < l) :
    legs.length ≤ legs.sum := by
  induction legs with
  | nil => simp
  | cons h t ih =>
    simp only [List.sum_cons, List.length_cons]
    have hh : 1 ≤ h := hpos h List.mem_cons_self
    have iht : t.length ≤ t.sum :=
      ih (fun l hl => hpos l (List.mem_cons_of_mem h hl))
    omega

/-! ## Theorem 1: Non-empty positive-leg list sums positive

A non-empty list where every element is positive necessarily has a positive sum.
This is the "non-degenerate allocation implies non-zero demand" direction. -/

/-- A non-empty list of positive naturals sums to a positive number.
    Proof: the head contributes at least 1, and the tail contributes at least 0. -/
theorem pos_legs_sum_pos (legs : List ℕ) (hne : legs ≠ [])
    (hpos : ∀ l ∈ legs, 0 < l) : 0 < legs.sum := by
  induction legs with
  | nil => exact absurd rfl hne
  | cons h t _ =>
    simp only [List.sum_cons]
    have hh : 0 < h := hpos h List.mem_cons_self
    omega

/-! ## Theorem 2: Unique singleton partition

If D > 0 and the allocation has exactly one leg, that leg must equal D.
This captures the base case: unsplit routing uses the full demand. -/

/-- The only valid 1-leg allocation of D is the list [D].
    Proof: `legs.sum = D` with `legs = [x]` forces `x = D`. -/
theorem singleton_partition_unique (D : ℕ) (legs : List ℕ)
    (hv : ValidAllocation D legs) (hlen : legs.length = 1) :
    legs = [D] := by
  match legs, hlen with
  | [x], _ =>
    have hsum := hv.sum_eq
    simp only [List.sum_cons, List.sum_nil] at hsum
    subst hsum; rfl

/-! ## Theorem 3: Individual leg bounded by total demand

Every leg in a valid allocation is at most D.  This follows from `l <= sum(legs) = D`
via `List.single_le_sum`.  Operationally: no leg routes more than the user's total input. -/

/-- Every leg in a valid allocation is at most D.
    Proof: `l <= List.sum legs` (each element bounded by sum of non-negatives)
    combined with `legs.sum = D`. -/
theorem leg_le_total (D : ℕ) (legs : List ℕ) (hv : ValidAllocation D legs)
    (l : ℕ) (hl : l ∈ legs) : l ≤ D := by
  have hle : l ≤ legs.sum := List.single_le_sum (fun x _ => Nat.zero_le x) l hl
  linarith [hv.sum_eq]

/-! ## Theorem 4: Length bounded by demand

A valid allocation of D has at most D legs.  Since each leg is at least 1
(from `all_pos`), the number of legs cannot exceed the total.
Operationally: a router splitting 100 units can produce at most 100 legs. -/

/-- A valid allocation of D has at most D legs.
    Proof: each leg >= 1, so `legs.length <= legs.sum = D`. -/
theorem length_le_total (D : ℕ) (legs : List ℕ) (hv : ValidAllocation D legs) :
    legs.length ≤ D := by
  have h := length_le_sum_of_pos legs hv.all_pos
  linarith [hv.sum_eq]

/-! ## Theorem 4b: Tight individual leg bound

Each leg in a valid k-leg allocation is at most D - (k-1).
This is TIGHTER than `leg_le_total` (which gives l ≤ D) because it accounts
for the k-1 other legs each contributing at least 1 to the total.

Proof: decompose the list at the leg position via `List.mem_split`, apply
`length_le_sum_of_pos` to both halves, and combine. -/

/-- Tight per-leg bound: l + (k - 1) ≤ D, where k = legs.length.
    Derived from list decomposition and positivity of the other legs.
    Stated additively to avoid ℕ subtraction pitfalls. -/
theorem tight_leg_bound (D : ℕ) (legs : List ℕ)
    (hv : ValidAllocation D legs) (l : ℕ) (hl : l ∈ legs) :
    l + (legs.length - 1) ≤ D := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hl
  have hsum := hv.sum_eq
  simp only [List.sum_append, List.sum_cons, List.length_append,
             List.length_cons] at hsum ⊢
  have hps : s.length ≤ s.sum :=
    length_le_sum_of_pos s (fun x hx => hv.all_pos x
      (List.mem_append_left _ hx))
  have hts : t.length ≤ t.sum :=
    length_le_sum_of_pos t (fun x hx => hv.all_pos x
      (List.mem_append_right s (List.mem_cons_of_mem l hx)))
  omega

/-! ## Theorem 5: Splitting a leg preserves validity

Replacing a single leg of value `a + b` with two legs `a, b` (both positive)
preserves the allocation total and the all-positive property.
This models the router's split operation: refining a route by splitting one
leg into two sub-routes. -/

/-- Splitting one leg `a + b` into two legs `[a, b]` preserves `ValidAllocation`.
    Proof: sum is preserved by `(a+b) = a + b`, and positivity of `a`, `b` is given. -/
theorem split_leg_preserves_valid
    (prefix_ suffix_ : List ℕ) (a b D : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hv : ValidAllocation D (prefix_ ++ [a + b] ++ suffix_)) :
    ValidAllocation D (prefix_ ++ [a, b] ++ suffix_) := by
  constructor
  · intro l hl
    have : l ∈ prefix_ ∨ l = a ∨ l = b ∨ l ∈ suffix_ := by
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hl
      tauto
    rcases this with hp | rfl | rfl | hs
    · exact hv.all_pos l (List.mem_append_left _ (List.mem_append_left _ hp))
    · exact ha
    · exact hb
    · exact hv.all_pos l (List.mem_append_right _ hs)
  · have hsum := hv.sum_eq
    simp only [List.sum_append, List.sum_cons, List.sum_nil] at hsum ⊢
    omega

/-! ## Theorem 6: Merging two adjacent legs preserves validity

The reverse of splitting: combining two adjacent legs into one preserves
the allocation total. The merged leg inherits positivity from `a + b > 0`
when both `a > 0` and `b > 0`. -/

/-- Merging two adjacent legs `[a, b]` into a single leg `[a + b]` preserves
    `ValidAllocation`. Proof: sum preserved; positivity of `a + b` follows from
    positivity of the original legs `a` and `b`. -/
theorem merge_legs_preserves_valid
    (prefix_ suffix_ : List ℕ) (a b D : ℕ)
    (hv : ValidAllocation D (prefix_ ++ [a, b] ++ suffix_)) :
    ValidAllocation D (prefix_ ++ [a + b] ++ suffix_) := by
  constructor
  · intro l hl
    have : l ∈ prefix_ ∨ l = a + b ∨ l ∈ suffix_ := by
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hl
      tauto
    rcases this with hp | rfl | hs
    · exact hv.all_pos l (List.mem_append_left _ (List.mem_append_left _ hp))
    · have ha : 0 < a := hv.all_pos a (by simp [List.mem_append, List.mem_cons])
      have hb : 0 < b := hv.all_pos b (by simp [List.mem_append, List.mem_cons])
      omega
    · exact hv.all_pos l (List.mem_append_right _ hs)
  · have hsum := hv.sum_eq
    simp only [List.sum_append, List.sum_cons, List.sum_nil] at hsum ⊢
    omega

/-! ## Theorem 7: Concatenation of valid allocations

If route segment 1 consumes D1 and segment 2 consumes D2, then the
combined route consumes D1 + D2.  This models multi-hop composition:
each hop is a valid sub-allocation and the total is their sum. -/

/-- Concatenating two valid allocations yields a valid allocation of the
    combined demand. Proof: positivity propagates through `List.mem_append`;
    sum distributes over `++`. -/
theorem concat_valid (D₁ D₂ : ℕ) (legs₁ legs₂ : List ℕ)
    (hv₁ : ValidAllocation D₁ legs₁) (hv₂ : ValidAllocation D₂ legs₂) :
    ValidAllocation (D₁ + D₂) (legs₁ ++ legs₂) := by
  constructor
  · intro l hl
    rw [List.mem_append] at hl
    rcases hl with h1 | h2
    · exact hv₁.all_pos l h1
    · exact hv₂.all_pos l h2
  · rw [List.sum_append]
    linarith [hv₁.sum_eq, hv₂.sum_eq]

/-! ## Theorem 8: Prepend a leg to a sub-allocation

Adding a new routing leg of size `a` to a valid allocation of `D - a`
produces a valid allocation of `D`. This is the inductive constructor
for building allocations leg by leg. -/

/-- Prepending a positive leg to a valid sub-allocation yields a valid
    allocation of the full demand.
    Proof: positivity of the new head is given; sum is `a + (D - a) = D`. -/
theorem prepend_valid (D a : ℕ) (legs : List ℕ)
    (ha : 0 < a) (hle : a ≤ D) (hv : ValidAllocation (D - a) legs) :
    ValidAllocation D (a :: legs) := by
  constructor
  · intro l hl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hmem
    · exact ha
    · exact hv.all_pos l hmem
  · simp only [List.sum_cons]
    have hsum := hv.sum_eq
    omega

/-! ## Theorem 9: Remove a leg from a valid allocation

Removing the head leg from a valid allocation of D yields a valid allocation
of `D - head`. This is the inductive destructor, dual to `prepend_valid`. -/

/-- Removing the first leg from a valid allocation produces a valid allocation
    of the remainder `D - a`.
    Proof: tail elements inherit positivity; sum decreases by `a`. -/
theorem remove_head_valid (D : ℕ) (a : ℕ) (rest : List ℕ)
    (hv : ValidAllocation D (a :: rest)) :
    ValidAllocation (D - a) rest := by
  constructor
  · intro l hl
    exact hv.all_pos l (List.mem_cons_of_mem a hl)
  · have hsum := hv.sum_eq
    simp only [List.sum_cons] at hsum
    omega

 theorem validAllocation_cons_iff (D a : ℕ) (legs : List ℕ) :
    ValidAllocation D (a :: legs) ↔ 0 < a ∧ a ≤ D ∧ ValidAllocation (D - a) legs := by
  constructor
  · intro hv
    refine ⟨hv.all_pos a (by simp), leg_le_total D (a :: legs) hv a (by simp), remove_head_valid D a legs hv⟩
  · rintro ⟨ha, hle, hv⟩
    exact prepend_valid D a legs ha hle hv

 private theorem validAllocation_zero_iff_nil_of_valid (D : ℕ) (legs : List ℕ) (hv : ValidAllocation D legs) :
    D = 0 ↔ legs = [] := by
  constructor
  · intro hD
    cases legs with
    | nil => rfl
    | cons a rest =>
        have ha : 0 < a := hv.all_pos a (by simp)
        have hsum := hv.sum_eq
        simp only [List.sum_cons, hD] at hsum
        omega
  · intro hlegs
    subst hlegs
    simpa using hv.sum_eq.symm

 private theorem validAllocation_nil_iff (D : ℕ) :
    ValidAllocation D [] ↔ D = 0 := by
  constructor
  · intro hv
    simpa using hv.sum_eq.symm
  · intro hD
    constructor
    · intro l hl
      cases hl
    · simp [hD]

 private theorem validAllocation_zero_iff_nil (legs : List ℕ) :
    ValidAllocation 0 legs ↔ legs = [] := by
  constructor
  · intro hv
    exact (validAllocation_zero_iff_nil_of_valid 0 legs hv).1 rfl
  · intro hlegs
    subst hlegs
    exact (validAllocation_nil_iff 0).2 rfl

 private theorem proper_prefix_sum_lt_total (D : ℕ) (pref suff : List ℕ) (a : ℕ)
    (hv : ValidAllocation D (pref ++ a :: suff)) :
    pref.sum < D := by
  have ha : 0 < a := hv.all_pos a (by simp [List.mem_append])
  have hsum := hv.sum_eq
  simp only [List.sum_append, List.sum_cons] at hsum
  omega

 private theorem remove_head_strictly_reduces_demand (D a : ℕ) (rest : List ℕ)
    (hv : ValidAllocation D (a :: rest)) :
    D - a < D := by
  have ha : 0 < a := hv.all_pos a (by simp)
  have hle : a ≤ D := leg_le_total D (a :: rest) hv a (by simp)
  omega

/-! ## Structural Induction Principle for Valid Allocations

The elimination principle for `ValidAllocation`: to prove a property P holds
for ALL valid allocations (D, legs), it suffices to show:
  (base) P holds for the trivial allocation (0, [])
  (step) If P holds for (D-a, rest), it holds for (D, a::rest)

This is the allocation analogue of `Nat.rec` — it captures the recursive
structure of valid allocations. Every non-empty allocation is a positive
head prepended to a smaller valid allocation, and the demand decreases
strictly at each step (from `remove_head_strictly_reduces_demand`).

The proof uses `generalizing D` so that the inductive hypothesis applies
to the REDUCED demand D-a, not the original D. -/

/-- Structural induction on valid allocations: base case (0, []),
    inductive step (D, a :: rest) from (D - a, rest).
    Proof: list induction with `generalizing D`, using `remove_head_valid`
    and `leg_le_total` to extract the inductive hypothesis at demand D - a. -/
theorem allocation_rec {P : (D : ℕ) → (legs : List ℕ) → Prop}
    (base : P 0 [])
    (step : ∀ D a rest, 0 < a → a ≤ D → ValidAllocation (D - a) rest →
            P (D - a) rest → P D (a :: rest))
    (D : ℕ) (legs : List ℕ) (hv : ValidAllocation D legs) : P D legs := by
  induction legs generalizing D with
  | nil =>
    have hD : D = 0 := by simpa using hv.sum_eq.symm
    subst hD; exact base
  | cons a rest ih =>
    have ha : 0 < a := hv.all_pos a (by simp)
    have hle : a ≤ D := leg_le_total D (a :: rest) hv a (by simp)
    have hv_rest : ValidAllocation (D - a) rest := remove_head_valid D a rest hv
    exact step D a rest ha hle hv_rest (ih (D - a) hv_rest)

/-! ## Theorem 10: Existence of valid allocations

For any positive demand, a valid allocation exists (the trivial singleton [D]).
This establishes that `ValidAllocation D` is a non-empty predicate when D > 0. -/

/-- For any positive demand, a valid single-leg allocation exists.
    Proof: [D] has one element (D itself) which is positive, and sums to D. -/
theorem exists_valid_allocation (D : ℕ) (hD : 0 < D) :
    ∃ legs, ValidAllocation D legs :=
  ⟨[D], ⟨fun l hl => by simp at hl; subst hl; exact hD, by simp⟩⟩

/-- Iff characterization of singleton allocations: [a] is valid for D iff a = D and D > 0. -/
theorem validAllocation_singleton_iff (D a : ℕ) :
    ValidAllocation D [a] ↔ a = D ∧ 0 < D := by
  constructor
  · intro hv
    have hsum := hv.sum_eq
    simp at hsum
    have ha := hv.all_pos a (by simp)
    exact ⟨hsum, by omega⟩
  · rintro ⟨rfl, hD⟩
    exact ⟨fun l hl => by simp at hl; subst hl; exact hD, by simp⟩

/-! ## Cross-file bridge: Allocation × Anti-Fragmentation

This section connects the routing model (ValidAllocation) to the CPMM output
model (AntiFragmentation). The key insight: splitting demand across multiple
legs can only decrease total output. Therefore the single-leg allocation
(no splitting) is output-optimal.

**Model scope**: Zero-fee integer CPMM on a single pool. Multi-pool routing
with heterogeneous rates is a separate (harder) problem. -/

/-- Any valid multi-leg allocation produces at most the single-swap output.
    This bridges AllocationTotality to AntiFragmentation: splitting input
    across multiple legs never improves total CPMM output on a single pool.

    Proof: substitutes `legs.sum = D` into `batchOutput_le_single_swap`. -/
theorem single_leg_maximizes_output (D x y : ℕ) (legs : List ℕ)
    (hv : ValidAllocation D legs) :
    AntiFragmentation.batchOutput x y legs ≤ AntiFragmentation.swapOut x y D := by
  rw [← hv.sum_eq]
  exact AntiFragmentation.batchOutput_le_single_swap x y legs

/-- Output is bounded by the reserve regardless of allocation.
    Composition of `single_leg_maximizes_output` and `swapOut_le_reserve`. -/
theorem allocation_output_le_reserve (D x y : ℕ) (legs : List ℕ)
    (hv : ValidAllocation D legs) :
    AntiFragmentation.batchOutput x y legs ≤ y :=
  le_trans (single_leg_maximizes_output D x y legs hv)
    (AntiFragmentation.swapOut_le_reserve x y D)

/-- PAIRWISE ALLOCATION GAP: any two valid allocations of the same demand D
    produce batch outputs that differ by at most (k-1) where k is the
    number of legs. Both allocations are within k-1 of the shared optimal
    (single swap), so they're within k-1 of each other.

    This is the "stability" result: no matter how you split the demand,
    outputs are close. Proof routes through the common single-swap optimal
    via batchOutput_le_single_swap (legs₁ ≤ optimal) and
    batchGap_bound (optimal ≤ legs₂ + rounding). -/
theorem allocation_pair_output_gap (D x y : ℕ) (legs₁ legs₂ : List ℕ)
    (hv₁ : ValidAllocation D legs₁) (hv₂ : ValidAllocation D legs₂) :
    AntiFragmentation.batchOutput x y legs₁ ≤
      AntiFragmentation.batchOutput x y legs₂ + legs₂.length.pred := by
  have h1 := AntiFragmentation.batchOutput_le_single_swap x y legs₁
  have h2 := AntiFragmentation.batchGap_bound x y legs₂
  rw [hv₁.sum_eq] at h1
  rw [hv₂.sum_eq] at h2
  omega

/-! ## Non-vacuity witnesses -/

/-- Validity core: valid allocations accepted, sum mismatches and zero legs rejected. -/
theorem witness_validity :
    -- Singleton, 2-leg, and 3-leg allocations all valid
    ValidAllocation 100 [100] ∧
    ValidAllocation 100 [60, 40] ∧
    ValidAllocation 1000 [400, 350, 250] ∧
    -- Sum mismatch: [60,50] rejected for D=100 (sum=110)
    ¬ ValidAllocation 100 [60, 50] ∧
    -- Zero leg: [100,0] rejected for D=100 (non-degenerate violation)
    ¬ ValidAllocation 100 [100, 0] := by native_decide

/-- Operation witnesses: splitting preserves validity but loses CPMM output. -/
theorem witness_operations :
    -- Splitting [100] into [60,40] preserves validity
    ValidAllocation 100 ([] ++ [60, 40] ++ []) ∧
    -- Split 200→[100,100] on pool (1000,1000): 165 < 166 (gap=1)
    AntiFragmentation.batchOutput 1000 1000 [100, 100] <
      AntiFragmentation.swapOut 1000 1000 200 := by
  native_decide

end AllocationTotality
end Proofs
