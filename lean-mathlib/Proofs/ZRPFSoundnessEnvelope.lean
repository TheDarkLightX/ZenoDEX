/-!
# ZRPF finite-union soundness envelope

This module proves only composition algebra. `risk` and `union` are abstract;
the caller must supply the empty-event and subadditivity obligations. In
particular, this file does not prove RISC Zero's per-proof soundness bounds,
Fiat--Shamir security, implementation refinement, or event-log completeness.

The proof contains no placeholders or extra logical assumptions.
-/

import Mathlib

namespace ZRPF.Soundness

variable {Event : Type*}

/-- Right-associated union of a finite event list. -/
def unionAll (empty : Event) (union : Event → Event → Event) : List Event → Event
  | [] => empty
  | event :: events => union event (unionAll empty union events)

/-- Subadditivity extends from a binary union to an arbitrary finite list. -/
theorem risk_unionAll_le_sum
    (empty : Event)
    (union : Event → Event → Event)
    (risk : Event → ℝ)
    (risk_empty : risk empty ≤ 0)
    (risk_union_le : ∀ left right, risk (union left right) ≤ risk left + risk right)
    (events : List Event) :
    risk (unionAll empty union events) ≤ (events.map risk).sum := by
  induction events with
  | nil =>
      simpa [unionAll] using risk_empty
  | cons event events ih =>
      calc
        risk (unionAll empty union (event :: events))
            ≤ risk event + risk (unionAll empty union events) := by
                simpa [unionAll] using risk_union_le event (unionAll empty union events)
        _ ≤ risk event + (events.map risk).sum := add_le_add_left ih (risk event)
        _ = ((event :: events).map risk).sum := by simp

/-- Pointwise homogeneous bounds sum to `length * epsilon`. -/
theorem sum_risk_le_count_mul
    (risk : Event → ℝ)
    (epsilon : ℝ)
    (events : List Event)
    (bounded : ∀ event ∈ events, risk event ≤ epsilon) :
    (events.map risk).sum ≤ (events.length : ℝ) * epsilon := by
  induction events with
  | nil => simp
  | cons event events ih =>
      have head_bound : risk event ≤ epsilon := bounded event (by simp)
      have tail_bound : ∀ item ∈ events, risk item ≤ epsilon := by
        intro item item_mem
        exact bounded item (by simp [item_mem])
      calc
        ((event :: events).map risk).sum = risk event + (events.map risk).sum := by simp
        _ ≤ epsilon + (events.length : ℝ) * epsilon :=
          add_le_add head_bound (ih tail_bound)
        _ = ((event :: events).length : ℝ) * epsilon := by
          simp
          ring

/-- Finite union bound with one common cap for every listed event. -/
theorem risk_unionAll_le_count_mul
    (empty : Event)
    (union : Event → Event → Event)
    (risk : Event → ℝ)
    (risk_empty : risk empty ≤ 0)
    (risk_union_le : ∀ left right, risk (union left right) ≤ risk left + risk right)
    (epsilon : ℝ)
    (events : List Event)
    (bounded : ∀ event ∈ events, risk event ≤ epsilon) :
    risk (unionAll empty union events) ≤ (events.length : ℝ) * epsilon :=
  (risk_unionAll_le_sum empty union risk risk_empty risk_union_le events).trans
    (sum_risk_le_count_mul risk epsilon events bounded)

/--
Two-class envelope used by the profile:

`base_count * epsilonBase + recursion_count * epsilonRecursion`.

No independence premise is needed; binary subadditivity is the only union
property used here.
-/
theorem two_class_union_envelope
    (empty : Event)
    (union : Event → Event → Event)
    (risk : Event → ℝ)
    (risk_empty : risk empty ≤ 0)
    (risk_union_le : ∀ left right, risk (union left right) ≤ risk left + risk right)
    (epsilonBase epsilonRecursion : ℝ)
    (baseEvents recursionEvents : List Event)
    (base_bounded : ∀ event ∈ baseEvents, risk event ≤ epsilonBase)
    (recursion_bounded : ∀ event ∈ recursionEvents, risk event ≤ epsilonRecursion) :
    risk
        (union
          (unionAll empty union baseEvents)
          (unionAll empty union recursionEvents))
      ≤ (baseEvents.length : ℝ) * epsilonBase
        + (recursionEvents.length : ℝ) * epsilonRecursion := by
  have base_union_bound :
      risk (unionAll empty union baseEvents)
        ≤ (baseEvents.length : ℝ) * epsilonBase :=
    risk_unionAll_le_count_mul
      empty union risk risk_empty risk_union_le epsilonBase baseEvents base_bounded
  have recursion_union_bound :
      risk (unionAll empty union recursionEvents)
        ≤ (recursionEvents.length : ℝ) * epsilonRecursion :=
    risk_unionAll_le_count_mul
      empty union risk risk_empty risk_union_le epsilonRecursion recursionEvents recursion_bounded
  calc
    risk
        (union
          (unionAll empty union baseEvents)
          (unionAll empty union recursionEvents))
      ≤ risk (unionAll empty union baseEvents)
        + risk (unionAll empty union recursionEvents) :=
          risk_union_le _ _
    _ ≤ (baseEvents.length : ℝ) * epsilonBase
        + (recursionEvents.length : ℝ) * epsilonRecursion :=
          add_le_add base_union_bound recursion_union_bound

/-- Total ZRPF guest nodes in a tree with explicit leaf and internal counts. -/
def nodeCount (leaves internalNodes : ℕ) : ℕ := leaves + internalNodes

/-- Every finite nonempty tree has one fewer edge than nodes. -/
def edgeCount (leaves internalNodes : ℕ) : ℕ := nodeCount leaves internalNodes - 1

/-- One RISC-V base proof per node in the one-segment minimum model. -/
def oneSegmentBaseEventCount (leaves internalNodes : ℕ) : ℕ :=
  nodeCount leaves internalNodes

/-- One lift per node plus one resolve per parent-child edge. -/
def oneSegmentRecursionEventCount (leaves internalNodes : ℕ) : ℕ :=
  nodeCount leaves internalNodes + edgeCount leaves internalNodes

/-- For a positive tree, `lifts + resolves = 2 * nodes - 1`. -/
theorem oneSegmentRecursionEventCount_eq
    (leaves internalNodes : ℕ)
    (positive : 0 < nodeCount leaves internalNodes) :
    oneSegmentRecursionEventCount leaves internalNodes
      = 2 * nodeCount leaves internalNodes - 1 := by
  simp only [oneSegmentRecursionEventCount, edgeCount]
  omega

/-- The minimum model has `3 * nodes - 1` total base-plus-recursion events. -/
theorem oneSegmentTotalEventCount_eq
    (leaves internalNodes : ℕ)
    (positive : 0 < nodeCount leaves internalNodes) :
    oneSegmentBaseEventCount leaves internalNodes
        + oneSegmentRecursionEventCount leaves internalNodes
      = 3 * nodeCount leaves internalNodes - 1 := by
  rw [oneSegmentRecursionEventCount_eq leaves internalNodes positive]
  simp only [oneSegmentBaseEventCount]
  omega

/--
Specialization of the two-class list theorem to the one-segment tree counts.
The list-length hypotheses are the event-log completeness seam.
-/
theorem one_segment_tree_envelope
    (empty : Event)
    (union : Event → Event → Event)
    (risk : Event → ℝ)
    (risk_empty : risk empty ≤ 0)
    (risk_union_le : ∀ left right, risk (union left right) ≤ risk left + risk right)
    (epsilonBase epsilonRecursion : ℝ)
    (leaves internalNodes : ℕ)
    (baseEvents recursionEvents : List Event)
    (base_length : baseEvents.length = oneSegmentBaseEventCount leaves internalNodes)
    (recursion_length :
      recursionEvents.length = oneSegmentRecursionEventCount leaves internalNodes)
    (base_bounded : ∀ event ∈ baseEvents, risk event ≤ epsilonBase)
    (recursion_bounded : ∀ event ∈ recursionEvents, risk event ≤ epsilonRecursion) :
    risk
        (union
          (unionAll empty union baseEvents)
          (unionAll empty union recursionEvents))
      ≤ (oneSegmentBaseEventCount leaves internalNodes : ℝ) * epsilonBase
        + (oneSegmentRecursionEventCount leaves internalNodes : ℝ) * epsilonRecursion := by
  simpa [base_length, recursion_length] using
    two_class_union_envelope
      empty union risk risk_empty risk_union_le epsilonBase epsilonRecursion
      baseEvents recursionEvents base_bounded recursion_bounded

end ZRPF.Soundness
