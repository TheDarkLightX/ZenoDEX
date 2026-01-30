import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Batch Optimality: The (Volume, Surplus) Objective

This file formalizes the optimality objective for batch auction settlements.

## Design: Correctness-by-Construction (CBC)

Invalid states are **unrepresentable**:
- `ValidOutcome` is a sum type: either `unfilled` or `filled` with proof that `output ≥ min_out`
- This ensures surplus is always non-negative by construction

## Mathematical Structure

```
                    (A,B)
  BatchSettlement  ─────────►  ℕ × ℕ
       │                      (ordered monoid)
       │ composition              │
       ▼                          ▼ lexicographic
  Combined settlements      (A₁+A₂, B₁+B₂) with lex comparison
```

## Key Theorems (proved in this file)

1. Lexicographic ordering is reflexive, transitive, total, antisymmetric
2. Surplus is non-negative by construction (via ValidOutcome type)
3. Pair addition is associative, commutative, with identity (0,0)
4. Volume/surplus additivity over batches is proved in `BatchCPMMUnification.lean`

-/

namespace BatchOptimality

/-! ## Part 1: Intent Structure

An intent represents a user's swap request:
- `amt_in`: Amount user is willing to spend
- `min_out`: Minimum output user will accept
-/

/-- A swap intent: user commits `amt_in` and requires at least `min_out` -/
structure Intent where
  amt_in : ℕ
  min_out : ℕ
  deriving Repr, DecidableEq

/-! ## Part 2: Valid Execution Outcome (CBC Design)

**Key insight**: Make invalid states unrepresentable.
A valid outcome is either:
- `unfilled`: Intent was not executed
- `filled output h`: Intent was executed with `output ≥ min_out` (proof required!)
-/

/-- Valid execution outcome for an intent (CBC: invalid states unrepresentable).
    Note: When `min_out = 0`, `filled 0 _` is representable but semantically
    degenerate. Downstream code should use `isFilled` or pattern match to
    distinguish execution from non-execution. -/
inductive ValidOutcome (i : Intent) where
  | unfilled : ValidOutcome i
  | filled (output : ℕ) (h : output ≥ i.min_out) : ValidOutcome i

/-- Get the output amount (0 if unfilled) -/
def ValidOutcome.outputAmt {i : Intent} : ValidOutcome i → ℕ
  | unfilled => 0
  | filled output _ => output

/-- Check if outcome is filled -/
def ValidOutcome.isFilled {i : Intent} : ValidOutcome i → Bool
  | unfilled => false
  | filled _ _ => true

/-! ## Part 3: Volume and Surplus

These are the two objective functions for batch optimization.
**Surplus is non-negative by construction** (no Nat subtraction underflow possible).
-/

/-- Volume: amt_in if filled, 0 otherwise -/
def volume {i : Intent} (o : ValidOutcome i) : ℕ :=
  match o with
  | .unfilled => 0
  | .filled _ _ => i.amt_in

/-- Surplus: output - min_out (guaranteed ≥ 0 by ValidOutcome.filled proof) -/
def surplus {i : Intent} (o : ValidOutcome i) : ℕ :=
  match o with
  | .unfilled => 0
  | .filled output _h => output - i.min_out

/-- Surplus is non-negative BY CONSTRUCTION (no theorem needed, but stating for clarity) -/
theorem surplus_nonneg {i : Intent} (o : ValidOutcome i) : surplus o ≥ 0 := by
  exact Nat.zero_le (surplus o)

/-- For filled outcomes, surplus equals output - min_out -/
theorem surplus_filled {i : Intent} (output : ℕ) (h : output ≥ i.min_out) :
    surplus (ValidOutcome.filled output h : ValidOutcome i) = output - i.min_out := by
  rfl

/-- Volume is 0 when unfilled -/
theorem volume_unfilled (i : Intent) : volume (ValidOutcome.unfilled : ValidOutcome i) = 0 := by
  rfl

/-- Surplus is 0 when unfilled -/
theorem surplus_unfilled (i : Intent) : surplus (ValidOutcome.unfilled : ValidOutcome i) = 0 := by
  rfl

/-! ## Part 4: The (A,B) Pair

The objective function returns (Volume, Surplus) as a pair.
-/

/-- The (A,B) objective for a single intent-outcome pair -/
def AB {i : Intent} (o : ValidOutcome i) : ℕ × ℕ :=
  (volume o, surplus o)

/-- AB for unfilled is (0, 0) -/
theorem AB_unfilled (i : Intent) : AB (ValidOutcome.unfilled : ValidOutcome i) = (0, 0) := by
  rfl

/-- AB for filled is (amt_in, output - min_out) -/
theorem AB_filled {i : Intent} (output : ℕ) (h : output ≥ i.min_out) :
    AB (ValidOutcome.filled output h : ValidOutcome i) = (i.amt_in, output - i.min_out) := by
  rfl

/-! ## Part 5: Lexicographic Ordering

The key insight: we use lexicographic ordering on ℕ × ℕ to compare settlements.
-/

/-- Lexicographic ordering on ℕ × ℕ -/
def lexLe (p q : ℕ × ℕ) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

/-- Strict lexicographic ordering -/
def lexLt (p q : ℕ × ℕ) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- lexLe is reflexive -/
theorem lexLe_refl (p : ℕ × ℕ) : lexLe p p := by
  unfold lexLe
  right
  exact ⟨rfl, le_refl p.2⟩

/-- lexLe is transitive -/
theorem lexLe_trans (p q r : ℕ × ℕ) (hpq : lexLe p q) (hqr : lexLe q r) :
    lexLe p r := by
  simp only [lexLe] at *
  cases hpq with
  | inl h1 =>
    cases hqr with
    | inl h2 => left; omega
    | inr h2 => left; omega
  | inr h1 =>
    cases hqr with
    | inl h2 => left; omega
    | inr h2 => right; constructor <;> omega

/-- lexLe is total -/
theorem lexLe_total (p q : ℕ × ℕ) : lexLe p q ∨ lexLe q p := by
  simp only [lexLe]
  by_cases h : p.1 < q.1
  · left; left; exact h
  · by_cases h2 : q.1 < p.1
    · right; left; exact h2
    · have heq : p.1 = q.1 := by omega
      by_cases h3 : p.2 ≤ q.2
      · left; right; exact ⟨heq, h3⟩
      · right; right; constructor; omega; omega

/-- lexLe is antisymmetric -/
theorem lexLe_antisymm (p q : ℕ × ℕ) (hpq : lexLe p q) (hqp : lexLe q p) : p = q := by
  simp only [lexLe] at *
  cases hpq with
  | inl h1 => cases hqp with
    | inl h2 => omega
    | inr h2 => omega
  | inr h1 => cases hqp with
    | inl h2 => omega
    | inr h2 => ext <;> omega

/-! ## Part 6: Component-wise Addition (Monoid Structure) -/

/-- Component-wise addition of ℕ × ℕ pairs -/
def pairAdd (p q : ℕ × ℕ) : ℕ × ℕ := (p.1 + q.1, p.2 + q.2)

/-- Pair addition is associative -/
theorem pairAdd_assoc (p q r : ℕ × ℕ) :
    pairAdd (pairAdd p q) r = pairAdd p (pairAdd q r) := by
  simp only [pairAdd, Nat.add_assoc]

/-- Pair addition is commutative -/
theorem pairAdd_comm (p q : ℕ × ℕ) : pairAdd p q = pairAdd q p := by
  simp only [pairAdd, Nat.add_comm]

/-- (0,0) is the identity for pair addition -/
theorem pairAdd_zero_left (p : ℕ × ℕ) : pairAdd (0, 0) p = p := by
  simp only [pairAdd, Nat.zero_add]

/-- (0,0) is the identity for pair addition -/
theorem pairAdd_zero_right (p : ℕ × ℕ) : pairAdd p (0, 0) = p := by
  simp only [pairAdd, Nat.add_zero]

/-! ## Part 7: Non-vacuity Witnesses -/

/-- Witness: valid execution produces correct (A,B) -/
theorem witness_filled_AB :
    let i : Intent := ⟨100, 90⟩
    let h : 95 ≥ 90 := by decide
    let o : ValidOutcome i := ValidOutcome.filled 95 h
    volume o = 100 ∧ surplus o = 5 ∧ AB o = (100, 5) := by
  simp only [volume, surplus, AB]
  decide

/-- Witness: lexicographic comparison -/
theorem witness_lex_compare :
    lexLt (50, 100) (100, 0) ∧    -- Higher volume wins
    lexLt (100, 50) (100, 100) ∧  -- Same volume, higher surplus wins
    ¬lexLt (100, 50) (100, 50) := by  -- Equal is not strictly less
  simp only [lexLt]
  constructor
  · left; decide
  · constructor
    · right; constructor <;> decide
    · intro h; cases h <;> omega

/-- Witness: (0,0) is the minimum -/
theorem witness_zero_minimum :
    let p : ℕ × ℕ := (0, 0)
    let q : ℕ × ℕ := (1, 0)
    lexLe p q ∧ ¬lexLe q p := by
  simp only [lexLe]
  constructor
  · left; decide
  · intro h; cases h <;> omega

/-! ## Part 8: Legacy Compatibility (for downstream files)

These definitions maintain compatibility with code that uses the old `Outcome` type.
-/

/-- Legacy Outcome type (for compatibility) -/
structure Outcome where
  output : ℕ
  deriving Repr, DecidableEq

/-- Convert legacy Outcome to ValidOutcome (partial: requires proof) -/
def Outcome.toValid (o : Outcome) (i : Intent) (h : o.output = 0 ∨ o.output ≥ i.min_out) :
    ValidOutcome i :=
  if ho : o.output = 0 then
    ValidOutcome.unfilled
  else
    ValidOutcome.filled o.output (by
      cases h with
      | inl h0 => exact absurd h0 ho
      | inr hge => exact hge)

/-- Legacy volume function -/
def volume_legacy (i : Intent) (o : Outcome) : ℕ :=
  if o.output > 0 then i.amt_in else 0

/-- Legacy surplus function -/
def surplus_legacy (i : Intent) (o : Outcome) : ℕ :=
  if o.output > 0 then o.output - i.min_out else 0

/-- Legacy AB function -/
def AB_legacy (i : Intent) (o : Outcome) : ℕ × ℕ :=
  (volume_legacy i o, surplus_legacy i o)

/-- Witness: Legacy AB computation -/
theorem witness_AB_legacy :
    let i₁ : Intent := ⟨100, 90⟩
    let o₁ : Outcome := ⟨95⟩
    let i₂ : Intent := ⟨50, 45⟩
    let o₂ : Outcome := ⟨48⟩
    pairAdd (AB_legacy i₁ o₁) (AB_legacy i₂ o₂) = (150, 8) := by
  native_decide

/-! ## Summary

### CBC Design
- `ValidOutcome` is a sum type: `unfilled | filled output (h : output ≥ min_out)`
- Invalid states (filled with output < min_out) are **unrepresentable**
- Surplus is non-negative by construction

### Key Properties (Proved)
- Lexicographic ordering is reflexive, transitive, total, antisymmetric
- Pair addition is associative, commutative, with identity (0,0)
- Surplus ≥ 0 follows from type structure

### What This File Does NOT Prove
- Existence of unique maximum (requires finite candidate set + construction)
- Pareto efficiency (requires defining the feasible set)
These are left for future work with explicit finite-set machinery.
-/

end BatchOptimality
