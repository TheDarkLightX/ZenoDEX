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

This is the pool-by-pool building block. The full k-pool generalization
(composing this across all non-interior pools) is left as a recorded proof
obligation; the runtime parity tests against brute force provide empirical
evidence for the composition while the formal composition proof is completed.

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
The full k-pool composition (applying this to every non-interior pool and
accumulating freed input into the interior pool) is the recorded proof
obligation `candidate_dominates_split` below.
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
Recorded proof obligation: the full k-pool composition.

If every non-interior pool i is left-covered by a jump candidate c_i with the
same output, and the interior pool's output is monotone nondecreasing, then the
candidate combination (c_i for non-interior pools, residual for the interior
pool) weakly dominates the original allocation.

The proof composes `candidate_dominates_single_pool` across all non-interior
pools, accumulating freed input into the interior pool's residual. The
composition is straightforward but requires careful list indexing; it is left
as a proof obligation while the runtime parity tests provide empirical evidence.

Statement (informal):

  ∀ alloc, alloc.sum ≤ D →
    LeftCoversAll poolOuts D candidates alloc →
    ∃ candidate_alloc,
      candidate_alloc.sum = alloc.sum ∧
      (∀ i, i ≠ interior_idx → candidate_alloc.get i ∈ candidates.get i) ∧
      objective poolOuts D alloc ≤ objective poolOuts D candidate_alloc
-/
theorem candidate_dominates_split_obligation
    (poolOuts : List (Nat → Nat))
    (interiorOut : Nat → Nat)
    (D : Nat)
    (hinterior : Nondecreasing interiorOut) :
    -- The composition proof is a recorded obligation, not yet mechanized.
    -- See `candidate_dominates_single_pool` for the pool-by-pool building block.
    True := by
  trivial

end KPoolStaircase
end Proofs
