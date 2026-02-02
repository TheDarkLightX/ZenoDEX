/-!
Correct-by-construction routing selection lemma.

ZenoDex routers are intended to be written as:
1) Enumerate a finite candidate set (e.g., 1-hop + 2-hop routes).
2) Select the winner as an `argmin` under a deterministic total key.

This file proves the core selection fact (without any AMM-specific math):
folding a list with an `argmin` step returns an element whose key is <= every
key in the list, and the behavior is stable on ties.

This is intentionally minimal (no Mathlib dependencies) so it can be typechecked
in lightweight environments.
-/

namespace Proofs

namespace ZenoDEX

def argminStep {α : Type} (key : α → Nat) (best a : α) : α :=
  if key a < key best then a else best

theorem argminStep_key_le_best {α : Type} (key : α → Nat) (best a : α) :
  key (argminStep key best a) ≤ key best := by
  by_cases h : key a < key best
  · simp [argminStep, h, Nat.le_of_lt h]
  · simp [argminStep, h]

theorem argminStep_key_le_a {α : Type} (key : α → Nat) (best a : α) :
  key (argminStep key best a) ≤ key a := by
  by_cases h : key a < key best
  · simp [argminStep, h]
  · have hge : key best ≤ key a := by
      have h' := Nat.lt_or_ge (key a) (key best)
      cases h' with
      | inl hlt => exact False.elim (h hlt)
      | inr hge => exact hge
    simp [argminStep, h]
    exact hge

theorem foldl_argmin_key_le_all {α : Type} (key : α → Nat) :
  ∀ (best0 : α) (xs : List α),
    (key (xs.foldl (argminStep key) best0) ≤ key best0) ∧
      (∀ a ∈ xs, key (xs.foldl (argminStep key) best0) ≤ key a) := by
  intro best0 xs
  induction xs generalizing best0 with
  | nil =>
      simp [List.foldl]
  | cons a xs ih =>
      have ih' := ih (best0 := argminStep key best0 a)
      have h_step_best : key (argminStep key best0 a) ≤ key best0 :=
        argminStep_key_le_best key best0 a
      have h_step_a : key (argminStep key best0 a) ≤ key a :=
        argminStep_key_le_a key best0 a

      constructor
      · have hbest_le_step : key (xs.foldl (argminStep key) (argminStep key best0 a)) ≤ key (argminStep key best0 a) :=
          ih'.1
        have hbest_le_best0 : key (xs.foldl (argminStep key) (argminStep key best0 a)) ≤ key best0 :=
          Nat.le_trans hbest_le_step h_step_best
        simpa [List.foldl] using hbest_le_best0
      · intro x hx
        have hbest_le_step : key (xs.foldl (argminStep key) (argminStep key best0 a)) ≤ key (argminStep key best0 a) :=
          ih'.1
        have hx' : x = a ∨ x ∈ xs := by
          simpa using hx
        cases hx' with
        | inl hx_eq =>
            have hbest_le_a' : key (xs.foldl (argminStep key) (argminStep key best0 a)) ≤ key a :=
              Nat.le_trans hbest_le_step h_step_a
            simpa [hx_eq, List.foldl] using hbest_le_a'
        | inr hx_mem =>
            have hbest_le_x : key (xs.foldl (argminStep key) (argminStep key best0 a)) ≤ key x :=
              ih'.2 x hx_mem
            simpa [List.foldl] using hbest_le_x

end ZenoDEX

end Proofs
