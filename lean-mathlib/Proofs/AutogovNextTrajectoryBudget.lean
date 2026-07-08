/-!
# AutoGovNEXT Trajectory Budget

This file isolates the arithmetic law behind the AutoGovNEXT trajectory
accumulator.

The runtime path stores a per-parameter `trajectory_used` value and advances it
by the absolute movement of each admitted governance step. This proof models the
absolute movement as a natural number `delta` and proves the narrow law needed
by the mechanism-design document: if every admitted step is checked against the
same carried accumulator and limit, total movement from a zero accumulator is at
most that limit.

The proof intentionally does not specify reset/window policy. A reset is a new
trajectory and must be governed by a separate runtime rule.
-/

namespace Proofs
namespace AutogovNextTrajectoryBudget

/-- Final accumulator after applying a list of admitted absolute movements. -/
def usedAfter : Nat → List Nat → Nat
  | used, [] => used
  | used, delta :: rest => usedAfter (used + delta) rest

/-- Sum of absolute movement across a trace. -/
def totalMovement : List Nat → Nat
  | [] => 0
  | delta :: rest => delta + totalMovement rest

/-- Runtime-style carried-budget predicate.

Each admitted step must fit in the current accumulator, then the accumulator is
advanced before the next step is checked. -/
def carriesBudget (limit : Nat) : Nat → List Nat → Prop
  | used, [] => used ≤ limit
  | used, delta :: rest => used + delta ≤ limit ∧ carriesBudget limit (used + delta) rest

/-- The recursive accumulator equals the start value plus total movement. -/
theorem usedAfter_eq_start_plus_totalMovement
    (start : Nat) (deltas : List Nat) :
    usedAfter start deltas = start + totalMovement deltas := by
  induction deltas generalizing start with
  | nil =>
      simp [usedAfter, totalMovement]
  | cons delta rest ih =>
      calc
        usedAfter start (delta :: rest)
            = usedAfter (start + delta) rest := by
              simp [usedAfter]
        _ = (start + delta) + totalMovement rest := by
              exact ih (start + delta)
        _ = start + totalMovement (delta :: rest) := by
              simp [totalMovement, Nat.add_assoc]

/-- Carrying the accumulator through every admitted step keeps the final
accumulator within the configured trajectory limit. -/
theorem carriesBudget_final_used_le_limit
    {limit start : Nat} {deltas : List Nat}
    (h : carriesBudget limit start deltas) :
    usedAfter start deltas ≤ limit := by
  induction deltas generalizing start with
  | nil =>
      simpa [usedAfter, carriesBudget] using h
  | cons delta rest ih =>
      exact ih h.2

/-- From a zero accumulator, the total admitted movement is bounded by the same
configured trajectory limit. -/
theorem zero_start_totalMovement_le_limit
    {limit : Nat} {deltas : List Nat}
    (h : carriesBudget limit 0 deltas) :
    totalMovement deltas ≤ limit := by
  have hFinal : usedAfter 0 deltas ≤ limit := carriesBudget_final_used_le_limit h
  simpa [usedAfter_eq_start_plus_totalMovement] using hFinal

/-- A rejected/no-op step modeled as zero movement does not change the
accumulator. -/
theorem zero_delta_preserves_used (used : Nat) :
    usedAfter used [0] = used := by
  simp [usedAfter]

end AutogovNextTrajectoryBudget
end Proofs
