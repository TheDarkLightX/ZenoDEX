/-!
Math-first assurance layer for DEX integer arithmetic.

This file is intentionally minimal: it proves a core lemma about `ceilDiv` over `Nat`.

Why this matters:
- CPMM and related kernels are *integer* math with deterministic rounding.
- The "business logic" is often reducible to lemmas about `ceil`/`floor` division.
- These lemmas can be imported into more detailed proofs (e.g., minimality of exact-out quotes).

Lean role in the workflow:
- Lean proves universal theorems about rounding and invariants.
- Counterexample mining (with shrinking) is useful when a conjecture is misstated.
-/

namespace ZenoDEX

def ceilDiv (a b : Nat) : Nat :=
  (a + b - 1) / b

-- Standard bound: ceilDiv over-approximates division with remainder bounded by (b-1).
-- This is often the *right* property for integer-kernel assurance: rounding error ≤ b-1.
theorem ceilDiv_mul_ge (a b : Nat) (hb : 0 < b) : a ≤ ceilDiv a b * b + (b - 1) := by
  unfold ceilDiv
  have hb1 : 1 ≤ b := Nat.succ_le_iff.mp hb
  -- Monotonicity of division: if a ≤ a+b-1 then a/b ≤ (a+b-1)/b
  have hle_num : a ≤ a + b - 1 := by
    have h0 : a ≤ a + (b - 1) := Nat.le_add_right _ _
    -- a + b - 1 = a + (b - 1) when 1 ≤ b
    have hab : a + b - 1 = a + (b - 1) := Nat.add_sub_assoc hb1 a
    simpa [hab] using h0
  have hdiv : a / b ≤ (a + b - 1) / b := Nat.div_le_div_right hle_num
  -- Convert division inequality to multiplication inequality:
  have hmul : a ≤ (a + b - 1) / b * b + b - 1 := (Nat.div_le_iff_le_mul hb).1 hdiv
  have hadd : (a + b - 1) / b * b + b - 1 = (a + b - 1) / b * b + (b - 1) :=
    Nat.add_sub_assoc hb1 ((a + b - 1) / b * b)
  simpa [hadd] using hmul

end ZenoDEX
