/-!
# Uniform Batch Clearing V1

This file formalizes the small algebraic shape used by the UPBA v1 runtime
certificate verifier:

* fills are reduced to aggregate reserve deltas;
* execution applies the aggregate deltas once;
* any permutation of the fill list yields the same final state.

The theorem is intentionally scoped. It does not prove price optimality,
admission fairness, oracle safety, or multi-hop clearing.
-/

namespace UniformBatchClearingV1

/-- Abstract reserve state for a single two-asset pool. -/
structure PoolState where
  reserve0 : Int
  reserve1 : Int
deriving DecidableEq, Repr

/-- Abstract per-fill reserve delta. -/
structure FillDelta where
  delta0 : Int
  delta1 : Int
deriving DecidableEq, Repr

/-- Aggregate the first asset reserve deltas. -/
def sumDelta0 : List FillDelta → Int
  | [] => 0
  | fill :: fills => fill.delta0 + sumDelta0 fills

/-- Aggregate the second asset reserve deltas. -/
def sumDelta1 : List FillDelta → Int
  | [] => 0
  | fill :: fills => fill.delta1 + sumDelta1 fills

/-- Uniform execution applies aggregate deltas once. -/
def executeUniform (state : PoolState) (fills : List FillDelta) : PoolState :=
  {
    reserve0 := state.reserve0 + sumDelta0 fills
    reserve1 := state.reserve1 + sumDelta1 fills
  }

theorem sumDelta0_perm {fillsA fillsB : List FillDelta}
    (h : fillsA.Perm fillsB) :
    sumDelta0 fillsA = sumDelta0 fillsB := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [sumDelta0, ih]
  | swap _ _ _ => simp [sumDelta0, Int.add_left_comm]
  | trans _ _ ihAB ihBC => exact Eq.trans ihAB ihBC

theorem sumDelta1_perm {fillsA fillsB : List FillDelta}
    (h : fillsA.Perm fillsB) :
    sumDelta1 fillsA = sumDelta1 fillsB := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [sumDelta1, ih]
  | swap _ _ _ => simp [sumDelta1, Int.add_left_comm]
  | trans _ _ ihAB ihBC => exact Eq.trans ihAB ihBC

/--
UPBA v1 permutation invariance.

If two certificate fill lists are permutations of each other, uniform execution
returns the same aggregate state transition.
-/
theorem uniform_execution_permutation_invariant
    (state : PoolState)
    {fillsA fillsB : List FillDelta}
    (h : fillsA.Perm fillsB) :
    executeUniform state fillsA = executeUniform state fillsB := by
  cases state
  simp [executeUniform, sumDelta0_perm h, sumDelta1_perm h]

/--
Uniform execution is exactly linear aggregation followed by one state update.

This theorem pins the runtime design choice: the batch is not interpreted as a
sequential fold over intermediate pool states.
-/
theorem uniform_execution_is_linear_aggregation
    (state : PoolState)
    (fills : List FillDelta) :
    executeUniform state fills =
      {
        reserve0 := state.reserve0 + sumDelta0 fills
        reserve1 := state.reserve1 + sumDelta1 fills
      } := by
  rfl

end UniformBatchClearingV1
