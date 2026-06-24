/-!
k-Pool staircase candidate completeness.

This file proves the reusable selection obligation behind the k-pool staircase
optimizer. The two-pool version (`SplitRoutingStaircase.lean`) shows that a
left-covering candidate set for pool0 dominates all splits because pool1 output
is monotone in the remaining input. This file generalizes the core dominance
fact to the k-pool setting:

* if a non-interior pool's allocation is left-covered by a jump candidate with
  the same output, and
* the interior pool's output is monotone nondecreasing in its own input,

then replacing the non-interior allocation with its left-covering candidate and
routing the freed input to the interior pool weakly increases the total output.

We prove two results:

1. `candidate_dominates_single_pool`: the pool-by-pool dominance building block.
2. `candidate_dominates_two_pool_composition`: the two-pool composition, which
   shows that left-covering one non-interior pool and routing the freed input
   to the interior pool weakly increases the combined output. This is the
   smallest non-trivial composition and the direct generalization of the
   two-pool staircase proof to the "one interior + one left-covered" structure.

The full k-pool composition (iterating across k-1 non-interior pools) follows
by induction on the number of left-covered pools; the induction step is
`candidate_dominates_single_pool` applied to the next non-interior pool with
the already-improved interior residual. The runtime parity tests against brute
force provide empirical evidence for the composition while the inductive
mechanization is completed.

The closed-form CPMM jump formula used to build the candidate set remains a
separate arithmetic obligation, checked today by runtime parity tests against
brute force.
-/

namespace Proofs
namespace KPoolStaircase

/-- Monotone nondecreasing output in the pool's own input amount. -/
def Nondecreasing (f : Nat → Nat) : Prop :=
  ∀ ⦃x y : Nat⦄, x ≤ y → f x ≤ f y

/-- A pool's allocation is left-covered by a candidate with the same output. -/
def LeftCovers (poolOut : Nat → Nat) (D : Nat) (candidate : Nat) (a : Nat) : Prop :=
  candidate ≤ D ∧ candidate ≤ a ∧ poolOut candidate = poolOut a

/-- Moving input left (from a to c ≤ a) frees input for the interior pool. -/
theorem remaining_input_antitone {c a D : Nat} (hca : c ≤ a) :
    D - a ≤ D - c := by
  exact Nat.sub_le_sub_left hca D

/--
A left-covered non-interior allocation is dominated by the candidate allocation.

If pool i's allocation `a_i` is left-covered by candidate `c_i ≤ a_i` with the
same output, then moving the freed input `(a_i - c_i)` to the interior pool does
not decrease the interior pool's output (by monotonicity), and pool i's output
is unchanged. So the candidate combination weakly dominates the original.

This is the core pool-by-pool dominance fact for the k-pool staircase optimizer.
-/
theorem candidate_dominates_single_pool
    (poolOut_i interiorOut : Nat → Nat)
    (a_i c_i r_interior : Nat)
    (hcover : LeftCovers poolOut_i a_i c_i a_i)
    (hinterior : Nondecreasing interiorOut) :
    ∃ r_interior',
      r_interior' ≥ r_interior ∧
      poolOut_i c_i = poolOut_i a_i ∧
      interiorOut r_interior' ≥ interiorOut r_interior ∧
      poolOut_i c_i + interiorOut r_interior' ≥ poolOut_i a_i + interiorOut r_interior := by
  -- The freed input from pool i goes to the interior pool.
  let freed := a_i - c_i
  let r_interior' := r_interior + freed
  refine ⟨r_interior', ?_, ?_, ?_, ?_⟩
  · -- r_interior' ≥ r_interior
    omega
  · -- poolOut_i c_i = poolOut_i a_i (from left-cover)
    exact hcover.2.2
  · -- interiorOut r_interior' ≥ interiorOut r_interior (monotonicity)
    have h_le : r_interior ≤ r_interior' := by omega
    exact hinterior h_le
  · -- poolOut_i c_i + interiorOut r_interior' ≥ poolOut_i a_i + interiorOut r_interior
    have h_interior_ge : interiorOut r_interior' ≥ interiorOut r_interior := hinterior (by omega)
    have h_pool_same : poolOut_i c_i = poolOut_i a_i := hcover.2.2
    omega

/--
Two-pool composition: left-covering the non-interior pool weakly dominates.

Given two pools where pool 0 is non-interior (left-covered by candidate c_0)
and pool 1 is interior (monotone output), replacing a_0 with c_0 and routing
the freed input to pool 1 weakly increases the total output.

This is the smallest non-trivial k-pool composition and the direct
generalization of the two-pool staircase proof. The full k-pool composition
follows by induction: apply `candidate_dominates_single_pool` to each
non-interior pool in turn, accumulating freed input into the interior pool's
residual. The induction step is exactly `candidate_dominates_single_pool` with
the improved residual from the previous step.
-/
theorem candidate_dominates_two_pool_composition
    (poolOut_0 poolOut_1 : Nat → Nat)
    (D a_0 a_1 c_0 : Nat)
    (hcover : LeftCovers poolOut_0 D c_0 a_0)
    (hinterior : Nondecreasing poolOut_1) :
    ∃ r_1',
      r_1' ≥ a_1 ∧
      poolOut_0 c_0 = poolOut_0 a_0 ∧
      poolOut_1 r_1' ≥ poolOut_1 a_1 ∧
      poolOut_0 c_0 + poolOut_1 r_1' ≥ poolOut_0 a_0 + poolOut_1 a_1 := by
  -- The freed input from pool 0 goes to pool 1 (the interior pool).
  let freed := a_0 - c_0
  let r_1' := a_1 + freed
  refine ⟨r_1', ?_, ?_, ?_, ?_⟩
  · -- r_1' ≥ a_1
    omega
  · -- poolOut_0 c_0 = poolOut_0 a_0 (from left-cover)
    exact hcover.2.2
  · -- poolOut_1 r_1' ≥ poolOut_1 a_1 (monotonicity)
    have h_le : a_1 ≤ r_1' := by omega
    exact hinterior h_le
  · -- poolOut_0 c_0 + poolOut_1 r_1' ≥ poolOut_0 a_0 + poolOut_1 a_1
    have h_interior_ge : poolOut_1 r_1' ≥ poolOut_1 a_1 := hinterior (by omega)
    have h_pool_same : poolOut_0 c_0 = poolOut_0 a_0 := hcover.2.2
    omega

/--
Three-pool composition: left-covering two non-interior pools weakly dominates.

Given three pools where pools 0 and 1 are non-interior (left-covered by
candidates c_0 and c_1) and pool 2 is interior (monotone output), replacing
a_0 with c_0 and a_1 with c_1 and routing all freed input to pool 2 weakly
increases the total output.

This is the key inductive step: it shows that the composition of two
left-covering steps (pool 0 then pool 1) preserves the dominance property.
The proof applies `candidate_dominates_single_pool` twice:
  1. First left-cover pool 0, freeing input to the interior pool (r_2 improves).
  2. Then left-cover pool 1, freeing more input to the already-improved r_2.

The full k-pool composition follows by induction on the number of non-interior
pools, with each step being `candidate_dominates_single_pool` applied to the
next non-interior pool with the already-improved interior residual.
-/
theorem candidate_dominates_three_pool_composition
    (poolOut_0 poolOut_1 poolOut_2 : Nat → Nat)
    (D a_0 a_1 a_2 c_0 c_1 : Nat)
    (hcover_0 : LeftCovers poolOut_0 D c_0 a_0)
    (hcover_1 : LeftCovers poolOut_1 D c_1 a_1)
    (hinterior : Nondecreasing poolOut_2) :
    ∃ r_2',
      r_2' ≥ a_2 ∧
      poolOut_0 c_0 = poolOut_0 a_0 ∧
      poolOut_1 c_1 = poolOut_1 a_1 ∧
      poolOut_2 r_2' ≥ poolOut_2 a_2 ∧
      poolOut_0 c_0 + poolOut_1 c_1 + poolOut_2 r_2' ≥
        poolOut_0 a_0 + poolOut_1 a_1 + poolOut_2 a_2 := by
  -- Step 1: left-cover pool 0, freeing input to the interior pool.
  let freed_0 := a_0 - c_0
  let r_2_after_0 := a_2 + freed_0
  -- Step 2: left-cover pool 1, freeing more input to the improved r_2.
  let freed_1 := a_1 - c_1
  let r_2' := r_2_after_0 + freed_1
  refine ⟨r_2', ?_, ?_, ?_, ?_, ?_⟩
  · -- r_2' ≥ a_2
    omega
  · -- poolOut_0 c_0 = poolOut_0 a_0
    exact hcover_0.2.2
  · -- poolOut_1 c_1 = poolOut_1 a_1
    exact hcover_1.2.2
  · -- poolOut_2 r_2' ≥ poolOut_2 a_2 (monotonicity: r_2' ≥ a_2)
    have h_le : a_2 ≤ r_2' := by omega
    exact hinterior h_le
  · -- poolOut_0 c_0 + poolOut_1 c_1 + poolOut_2 r_2' ≥
    -- poolOut_0 a_0 + poolOut_1 a_1 + poolOut_2 a_2
    have h_pool_0_same : poolOut_0 c_0 = poolOut_0 a_0 := hcover_0.2.2
    have h_pool_1_same : poolOut_1 c_1 = poolOut_1 a_1 := hcover_1.2.2
    have h_interior_ge : poolOut_2 r_2' ≥ poolOut_2 a_2 := hinterior (by omega)
    omega

/-- A non-interior pool entry: (poolOut function, original allocation, candidate). -/
abbrev PoolEntry := (Nat → Nat) × Nat × Nat

/--
Auxiliary: total freed input from left-covering a list of non-interior pools.

`freedInput pools = Σ (a_i - c_i)` for each (poolOut, a_i, c_i) in the list.
This is the amount of input redirected to the interior pool.
-/
def freedInput (pools : List PoolEntry) : Nat :=
  pools.foldr (fun (_poolOut, a, c) acc => acc + (a - c)) 0

/--
Auxiliary: sum of outputs from non-interior pools at their candidate allocations.

`candidateOutput pools = Σ poolOut_i c_i` for each (poolOut_i, a_i, c_i).
-/
def candidateOutput (pools : List PoolEntry) : Nat :=
  pools.foldr (fun (poolOut, _a, c) acc => acc + poolOut c) 0

/--
Auxiliary: sum of outputs from non-interior pools at their original allocations.

`originalOutput pools = Σ poolOut_i a_i` for each (poolOut_i, a_i, c_i).
-/
def originalOutput (pools : List PoolEntry) : Nat :=
  pools.foldr (fun (poolOut, a, _c) acc => acc + poolOut a) 0

/--
Auxiliary: sum of original allocations (input spent on non-interior pools).
-/
def originalSpent (pools : List PoolEntry) : Nat :=
  pools.foldr (fun (_poolOut, a, _c) acc => acc + a) 0

/--
Auxiliary: sum of candidate allocations (input spent on non-interior pools after left-covering).
-/
def candidateSpent (pools : List PoolEntry) : Nat :=
  pools.foldr (fun (_poolOut, _a, c) acc => acc + c) 0

/--
Lemma: candidate spent ≤ original spent when all pools are left-covered.

Each LeftCovers guarantees c_i ≤ a_i, so Σ c_i ≤ Σ a_i.
-/
theorem candidate_spent_le_original_spent
    (pools : List PoolEntry)
    (D : Nat)
    (hcover : ∀ (poolOut : Nat → Nat) (a c : Nat),
      (poolOut, a, c) ∈ pools → LeftCovers poolOut D c a) :
    candidateSpent pools ≤ originalSpent pools := by
  induction pools with
  | nil => simp [candidateSpent, originalSpent]
  | cons head rest ih =>
    obtain ⟨poolOut, a, c⟩ := head
    have h_cover_head : LeftCovers poolOut D c a := hcover poolOut a c (by simp)
    have h_c_le_a : c ≤ a := h_cover_head.2.1
    have h_rest : candidateSpent rest ≤ originalSpent rest := by
      apply ih
      intro poolOut' a' c' h
      exact hcover poolOut' a' c' (by simp [h])
    show candidateSpent rest + c ≤ originalSpent rest + a
    omega

/--
Lemma: candidate output equals original output when all pools are left-covered.

If every non-interior pool i has LeftCovers poolOut_i D c_i a_i, then
poolOut_i c_i = poolOut_i a_i for each i, so the sum of outputs is unchanged.
-/
theorem candidate_output_eq_original_output
    (pools : List PoolEntry)
    (D : Nat)
    (hcover : ∀ (poolOut : Nat → Nat) (a c : Nat),
      (poolOut, a, c) ∈ pools → LeftCovers poolOut D c a) :
    candidateOutput pools = originalOutput pools := by
  induction pools with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨poolOut, a, c⟩ := head
    have h_cover_head : LeftCovers poolOut D c a := hcover poolOut a c (by simp)
    have h_head : poolOut c = poolOut a := h_cover_head.2.2
    have h_rest : candidateOutput rest = originalOutput rest := by
      apply ih
      intro poolOut' a' c' h
      exact hcover poolOut' a' c' (by simp [h])
    show candidateOutput rest + poolOut c = originalOutput rest + poolOut a
    rw [h_head, h_rest]

/--
Lemma: freed input equals the difference between original and candidate spent.

`freedInput pools = originalSpent pools - candidateSpent pools`

This follows because a_i - c_i summed equals (Σ a_i) - (Σ c_i) when c_i ≤ a_i
for all i (which is guaranteed by LeftCovers).
-/
theorem freed_input_eq_spent_diff
    (pools : List PoolEntry)
    (D : Nat)
    (hcover : ∀ (poolOut : Nat → Nat) (a c : Nat),
      (poolOut, a, c) ∈ pools → LeftCovers poolOut D c a) :
    freedInput pools = originalSpent pools - candidateSpent pools := by
  induction pools with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨poolOut, a, c⟩ := head
    have h_cover_head : LeftCovers poolOut D c a := hcover poolOut a c (by simp)
    have h_c_le_a : c ≤ a := h_cover_head.2.1
    have h_rest : freedInput rest = originalSpent rest - candidateSpent rest := by
      apply ih
      intro poolOut' a' c' h
      exact hcover poolOut' a' c' (by simp [h])
    have h_rest_cand_le_rest_orig : candidateSpent rest ≤ originalSpent rest := by
      apply candidate_spent_le_original_spent rest D
      intro poolOut' a' c' h
      exact hcover poolOut' a' c' (by simp [h])
    show freedInput rest + (a - c) = (originalSpent rest + a) - (candidateSpent rest + c)
    rw [h_rest]
    omega

/--
Full k-pool inductive composition: left-covering all non-interior pools weakly
dominates the original allocation.

Given a list of non-interior pools (each with poolOut, original allocation a_i,
and candidate c_i) and one interior pool with monotone output, replacing each
a_i with c_i and routing all freed input to the interior pool:

1. Weakly increases total output (dominance).
2. Preserves total spent (conservation: candidate spent + improved interior = original spent + original interior).

This is the full arbitrary-k theorem. The proof uses list induction:
  Base case (empty list): no non-interior pools, trivially true.
  Inductive step: the freed input from the head pool plus the freed input from
    the tail equals the total freed input. By monotonicity, the interior pool's
    output at (a_interior + total_freed) ≥ output at a_interior. Each non-interior
    pool's output is unchanged (LeftCovers). So total output weakly increases.

Conservation: candidateSpent + (a_interior + freedInput) = originalSpent + a_interior,
because freedInput = originalSpent - candidateSpent (proven by
freed_input_eq_spent_diff) and candidateSpent ≤ originalSpent (proven by
candidate_spent_le_original_spent).
-/
theorem candidate_dominates_k_pool_composition
    (pools : List PoolEntry)
    (interiorOut : Nat → Nat)
    (D a_interior : Nat)
    (hcover : ∀ (poolOut : Nat → Nat) (a c : Nat),
      (poolOut, a, c) ∈ pools → LeftCovers poolOut D c a)
    (hinterior : Nondecreasing interiorOut) :
    ∃ r_interior',
      r_interior' = a_interior + freedInput pools ∧
      r_interior' ≥ a_interior ∧
      candidateOutput pools = originalOutput pools ∧
      interiorOut r_interior' ≥ interiorOut a_interior ∧
      candidateOutput pools + interiorOut r_interior' ≥
        originalOutput pools + interiorOut a_interior ∧
      candidateSpent pools + r_interior' = originalSpent pools + a_interior := by
  let r_interior' := a_interior + freedInput pools
  refine ⟨r_interior', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- r_interior' = a_interior + freedInput pools
    rfl
  · -- r_interior' ≥ a_interior
    have h_freed_ge_0 : freedInput pools ≥ 0 := by omega
    omega
  · -- candidateOutput pools = originalOutput pools
    exact candidate_output_eq_original_output pools D hcover
  · -- interiorOut r_interior' ≥ interiorOut a_interior (monotonicity)
    have h_le : a_interior ≤ r_interior' := by
      have h_freed_ge_0 : freedInput pools ≥ 0 := by omega
      omega
    exact hinterior h_le
  · -- candidateOutput pools + interiorOut r_interior' ≥
    -- originalOutput pools + interiorOut a_interior
    have h_out_eq : candidateOutput pools = originalOutput pools :=
      candidate_output_eq_original_output pools D hcover
    have h_interior_ge : interiorOut r_interior' ≥ interiorOut a_interior := by
      have h_le : a_interior ≤ r_interior' := by
        have h_freed_ge_0 : freedInput pools ≥ 0 := by omega
        omega
      exact hinterior h_le
    omega
  · -- candidateSpent pools + r_interior' = originalSpent pools + a_interior
    have h_freed : freedInput pools = originalSpent pools - candidateSpent pools :=
      freed_input_eq_spent_diff pools D hcover
    have h_cand_le_orig : candidateSpent pools ≤ originalSpent pools :=
      candidate_spent_le_original_spent pools D hcover
    show candidateSpent pools + (a_interior + freedInput pools) =
      originalSpent pools + a_interior
    rw [h_freed]
    omega

end KPoolStaircase
end Proofs
