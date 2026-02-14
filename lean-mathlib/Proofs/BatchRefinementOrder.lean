import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Batch Refinement Order

Manual proof skeleton for AB-style lexicographic refinement used in batch ordering.

`better x y` means objective pair `x = (A, B)` is strictly better than `y`:
1. larger `A`, or
2. same `A` and larger `B`.

`noWorse x y` is the step invariant used by refinement passes:
either unchanged or strictly better.
-/

namespace Proofs
namespace BatchRefinementOrder

abbrev AB := Nat × Nat

/-- Strict AB improvement relation (lexicographic on `(A, B)`, maximizing both). -/
def better (x y : AB) : Prop :=
  y.1 < x.1 ∨ (x.1 = y.1 ∧ y.2 < x.2)

/-- Non-degradation relation used by refinement passes. -/
def noWorse (x y : AB) : Prop :=
  x = y ∨ better x y

theorem better_irrefl (x : AB) : ¬ better x x := by
  intro h
  rcases h with hA | ⟨hEq, hB⟩
  · omega
  · omega

theorem better_trans {a b c : AB}
    (hab : better a b) (hbc : better b c) :
    better a c := by
  rcases hab with habA | ⟨habEq, habB⟩
  · rcases hbc with hbcA | ⟨hbcEq, hbcB⟩
    · left
      omega
    · left
      omega
  · rcases hbc with hbcA | ⟨hbcEq, hbcB⟩
    · left
      omega
    · right
      constructor
      · omega
      · omega

/-- Composition law: two no-worse refinement steps imply no-worse end-to-end. -/
theorem noWorse_trans {a b c : AB}
    (hba : noWorse b a) (hcb : noWorse c b) :
    noWorse c a := by
  rcases hba with rfl | hBetterBA
  · simpa using hcb
  · rcases hcb with rfl | hBetterCB
    · exact Or.inr hBetterBA
    · exact Or.inr (better_trans hBetterCB hBetterBA)

/-- Two-step refinement cannot degrade the AB objective. -/
theorem two_step_refinement_never_degrades
    (x0 x1 x2 : AB)
    (h1 : noWorse x1 x0)
    (h2 : noWorse x2 x1) :
    noWorse x2 x0 := by
  exact noWorse_trans h1 h2

/-- Non-vacuity witness: strict B-improvement then strict A-improvement. -/
theorem witness_refinement_chain :
    noWorse (8, 17) (8, 12) ∧
    noWorse (9, 1) (8, 17) ∧
    noWorse (9, 1) (8, 12) := by
  constructor
  · right
    right
    constructor <;> norm_num
  constructor
  · right
    left
    norm_num
  · exact two_step_refinement_never_degrades (8, 12) (8, 17) (9, 1)
      (by
        right
        right
        constructor <;> norm_num)
      (by
        right
        left
        norm_num)

end BatchRefinementOrder
end Proofs
