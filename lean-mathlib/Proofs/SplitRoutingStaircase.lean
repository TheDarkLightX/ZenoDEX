/-!
Split-routing staircase candidate completeness.

The runtime staircase optimizer enumerates the left edge of each reachable
pool0 output plateau, plus the endpoints. This file proves the reusable
selection obligation behind that algorithm:

* if every split is left-covered by a candidate with the same pool0 output, and
* pool1 output is monotone in the remaining input,

then optimizing over candidates is globally exact. The second theorem preserves
the canonical leftmost tie-break among global optima.

This is intentionally scoped to the algorithmic skeleton. The closed-form CPMM
jump formula used to build the candidate set remains a separate arithmetic
obligation, checked today by runtime parity tests against brute force.
-/

namespace Proofs
namespace SplitRoutingStaircase

/-- Objective for split `a`: pool0 receives `a`; pool1 receives `D - a`. -/
def objective (pool0Out pool1Out : Nat → Nat) (D a : Nat) : Nat :=
  pool0Out a + pool1Out (D - a)

/-- Monotone nondecreasing output in the pool's own input amount. -/
def Nondecreasing (f : Nat → Nat) : Prop :=
  ∀ ⦃x y : Nat⦄, x ≤ y → f x ≤ f y

/--
Every split `a` has a candidate `c ≤ a` with the same pool0 output. For a
staircase output function, `c` is the left edge of `a`'s plateau.
-/
def LeftCovers (pool0Out : Nat → Nat) (D : Nat) (candidates : List Nat) : Prop :=
  ∀ a, a ≤ D → ∃ c, c ∈ candidates ∧ c ≤ D ∧ c ≤ a ∧ pool0Out c = pool0Out a

/-- Moving split input left gives pool1 weakly more remaining input. -/
theorem remaining_input_antitone {c a D : Nat} (hca : c ≤ a) :
    D - a ≤ D - c := by
  exact Nat.sub_le_sub_left hca D

/--
Any split is dominated by a left-covering candidate. This is the core
candidate-completeness fact for the staircase optimizer.
-/
theorem candidate_dominates_split
    (pool0Out pool1Out : Nat → Nat)
    (D : Nat)
    (candidates : List Nat)
    (hcover : LeftCovers pool0Out D candidates)
    (hpool1 : Nondecreasing pool1Out) :
    ∀ a, a ≤ D →
      ∃ c, c ∈ candidates ∧ c ≤ D ∧ c ≤ a ∧
        objective pool0Out pool1Out D a ≤ objective pool0Out pool1Out D c := by
  intro a ha
  rcases hcover a ha with ⟨c, hmem, hcD, hca, hsame⟩
  have hremaining : D - a ≤ D - c := remaining_input_antitone hca
  have hpool1_le : pool1Out (D - a) ≤ pool1Out (D - c) := hpool1 hremaining
  have hdominates :
      objective pool0Out pool1Out D a ≤ objective pool0Out pool1Out D c := by
    simp [objective, hsame, hpool1_le]
  exact ⟨c, hmem, hcD, hca, hdominates⟩

/--
If `best` is maximal among the candidate splits, then `best` is maximal among
all splits in `[0, D]`.
-/
theorem candidate_best_is_global
    (pool0Out pool1Out : Nat → Nat)
    (D best : Nat)
    (candidates : List Nat)
    (hcover : LeftCovers pool0Out D candidates)
    (hpool1 : Nondecreasing pool1Out)
    (hbest : ∀ c, c ∈ candidates → c ≤ D →
      objective pool0Out pool1Out D c ≤ objective pool0Out pool1Out D best) :
    ∀ a, a ≤ D →
      objective pool0Out pool1Out D a ≤ objective pool0Out pool1Out D best := by
  intro a ha
  rcases candidate_dominates_split pool0Out pool1Out D candidates hcover hpool1 a ha with
    ⟨c, hmem, hcD, _hca, hdom⟩
  exact Nat.le_trans hdom (hbest c hmem hcD)

/--
If `best` is the smallest candidate attaining the candidate maximum, it is also
the smallest global maximizer. This mirrors the runtime's deterministic
smallest-split tie-break.
-/
theorem smallest_candidate_best_is_leftmost_global
    (pool0Out pool1Out : Nat → Nat)
    (D best : Nat)
    (candidates : List Nat)
    (hcover : LeftCovers pool0Out D candidates)
    (hpool1 : Nondecreasing pool1Out)
    (hbest : ∀ c, c ∈ candidates → c ≤ D →
      objective pool0Out pool1Out D c ≤ objective pool0Out pool1Out D best)
    (hsmall : ∀ c, c ∈ candidates → c ≤ D →
      objective pool0Out pool1Out D c = objective pool0Out pool1Out D best → best ≤ c) :
    ∀ a, a ≤ D →
      objective pool0Out pool1Out D a = objective pool0Out pool1Out D best → best ≤ a := by
  intro a ha hopt
  rcases candidate_dominates_split pool0Out pool1Out D candidates hcover hpool1 a ha with
    ⟨c, hmem, hcD, hca, hdom⟩
  have hc_le_best :
      objective pool0Out pool1Out D c ≤ objective pool0Out pool1Out D best :=
    hbest c hmem hcD
  have hbest_le_c :
      objective pool0Out pool1Out D best ≤ objective pool0Out pool1Out D c := by
    simpa [hopt] using hdom
  have hc_eq_best :
      objective pool0Out pool1Out D c = objective pool0Out pool1Out D best :=
    Nat.le_antisymm hc_le_best hbest_le_c
  exact Nat.le_trans (hsmall c hmem hcD hc_eq_best) hca

end SplitRoutingStaircase
end Proofs
