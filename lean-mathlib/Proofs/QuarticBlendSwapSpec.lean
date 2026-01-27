import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

import Proofs.QuarticBlendK

/-!
# Quartic-blend swap specs (existence + minimality objects)

This file deepens the `QuarticBlendK` lemmas by constructing *minimal* reserve values
as mathematical objects (via `Nat.find`) and proving their key properties.

These objects match the DEX kernel intent:
- exact-in: choose the **minimal** post-swap out-reserve `y₁` such that `K(x₁,y₁) ≥ K(x₀,y₀)`.
- exact-out: choose the **minimal** post-swap in-reserve `x₁` (above a baseline `x₀`) such that
  `K(x₁,y₁) ≥ K(x₀,y₀)` for a target out-reserve `y₁`.

The implementation uses bisection to compute these minima; here we certify the *mathematical*
minima and their characterizations (without tying to a particular search algorithm).
-/

namespace TauSwap
namespace QuarticBlend

open TauSwap.QuarticBlend

/-! ## Growth lower bound (for existence) -/

theorem kScaled_ge_x3 (x y c_num c_den : Nat) (hy : 0 < y) (hc : 0 < c_den) :
    x ^ 3 ≤ kScaled x y c_num c_den := by
  -- `quadScaled ≥ c_den * x^2` and `x*y ≥ x` when `y ≥ 1`, so:
  --   K = (x*y) * quadScaled ≥ (x) * (x^2) = x^3.
  have hy1 : 1 ≤ y := Nat.succ_le_iff.mp hy
  have hc1 : 1 ≤ c_den := Nat.succ_le_iff.mp hc

  have hxx : x * x ≤ x * x + y * y := by
    exact Nat.le_add_right _ _
  have hterm1 : c_den * (x * x) ≤ c_den * (x * x + y * y) :=
    Nat.mul_le_mul_left c_den hxx
  have hquad_ge : c_den * (x * x) ≤ quadScaled x y c_num c_den := by
    -- `c_den*(x^2+y^2) ≤ c_den*(x^2+y^2) + c_num*x*y`
    have : c_den * (x * x + y * y) ≤ quadScaled x y c_num c_den := by
      unfold quadScaled
      exact Nat.le_add_right _ _
    exact le_trans hterm1 this

  have hmul1 : (x * y) * (c_den * (x * x)) ≤ (x * y) * quadScaled x y c_num c_den :=
    Nat.mul_le_mul_left (x * y) hquad_ge
  have hmul2 : x * (c_den * (x * x)) ≤ (x * y) * (c_den * (x * x)) := by
    have : x ≤ x * y := by
      -- x = x*1 ≤ x*y
      have : x * 1 ≤ x * y := Nat.mul_le_mul_left x hy1
      simpa using this
    exact Nat.mul_le_mul_right (c_den * (x * x)) this
  have hmul3 : x * (x * x) ≤ x * (c_den * (x * x)) := by
    have : x * x ≤ c_den * (x * x) := by
      -- x^2 = 1*x^2 ≤ c_den*x^2
      have : 1 * (x * x) ≤ c_den * (x * x) := Nat.mul_le_mul_right (x * x) hc1
      simpa using this
    exact Nat.mul_le_mul_left x this

  have hx3 : x ^ 3 = x * (x * x) := by
    calc
      x ^ 3 = (x * x) * x := by
        simp [pow_succ]
      _ = x * (x * x) := by
        simp [Nat.mul_assoc]

  -- Chain everything.
  calc
    x ^ 3 = x * (x * x) := hx3
    _ ≤ x * (c_den * (x * x)) := hmul3
    _ ≤ (x * y) * (c_den * (x * x)) := hmul2
    _ ≤ (x * y) * quadScaled x y c_num c_den := hmul1
    _ = kScaled x y c_num c_den := by
      unfold kScaled
      rfl


theorem exists_x_ge_kScaled (k0 y c_num c_den : Nat) (hy : 0 < y) (hc : 0 < c_den) :
    ∃ x, k0 ≤ kScaled x y c_num c_den := by
  refine ⟨k0 + 1, ?_⟩
  have hx : k0 ≤ k0 + 1 := Nat.le_succ k0
  have hxpow : k0 + 1 ≤ (k0 + 1) ^ 3 := Nat.le_pow (a := k0 + 1) (b := 3) (by decide)
  have hk0 : k0 ≤ (k0 + 1) ^ 3 := le_trans hx hxpow
  have hk : (k0 + 1) ^ 3 ≤ kScaled (k0 + 1) y c_num c_den :=
    kScaled_ge_x3 (x := k0 + 1) (y := y) (c_num := c_num) (c_den := c_den) hy hc
  exact le_trans hk0 hk


/-! ## Minimal x above a baseline (Nat.find) -/

noncomputable def minXFrom
    (x0 y1 k0 c_num c_den : Nat)
    (hexists : ∃ x, x0 ≤ x ∧ k0 ≤ kScaled x y1 c_num c_den) : Nat :=
  Nat.find hexists

theorem minXFrom_ge {x0 y1 k0 c_num c_den : Nat}
    (hexists : ∃ x, x0 ≤ x ∧ k0 ≤ kScaled x y1 c_num c_den) :
    x0 ≤ minXFrom x0 y1 k0 c_num c_den hexists :=
  (Nat.find_spec hexists).1

theorem minXFrom_spec {x0 y1 k0 c_num c_den : Nat}
    (hexists : ∃ x, x0 ≤ x ∧ k0 ≤ kScaled x y1 c_num c_den) :
    k0 ≤ kScaled (minXFrom x0 y1 k0 c_num c_den hexists) y1 c_num c_den :=
  (Nat.find_spec hexists).2

theorem lt_minXFrom_imp_kScaled_lt {x0 y1 k0 c_num c_den m : Nat}
    (hexists : ∃ x, x0 ≤ x ∧ k0 ≤ kScaled x y1 c_num c_den)
    (hm : m < minXFrom x0 y1 k0 c_num c_den hexists) :
    ¬(x0 ≤ m ∧ k0 ≤ kScaled m y1 c_num c_den) :=
  Nat.find_min (p := fun x => x0 ≤ x ∧ k0 ≤ kScaled x y1 c_num c_den) hexists hm

theorem minXFrom_le_of_pred {x0 y1 k0 c_num c_den m : Nat}
    (hexists : ∃ x, x0 ≤ x ∧ k0 ≤ kScaled x y1 c_num c_den)
    (hm : x0 ≤ m ∧ k0 ≤ kScaled m y1 c_num c_den) :
    minXFrom x0 y1 k0 c_num c_den hexists ≤ m :=
  Nat.find_le (h := hexists) hm

theorem pred_of_minXFrom_le {x0 y1 k0 c_num c_den m : Nat}
    (hexists : ∃ x, x0 ≤ x ∧ k0 ≤ kScaled x y1 c_num c_den)
    (hm : minXFrom x0 y1 k0 c_num c_den hexists ≤ m) :
    x0 ≤ m ∧ k0 ≤ kScaled m y1 c_num c_den := by
  have hx0 : x0 ≤ minXFrom x0 y1 k0 c_num c_den hexists := minXFrom_ge (x0 := x0) (y1 := y1) (k0 := k0) (c_num := c_num) (c_den := c_den) hexists
  have hk0 : k0 ≤ kScaled (minXFrom x0 y1 k0 c_num c_den hexists) y1 c_num c_den :=
    minXFrom_spec (x0 := x0) (y1 := y1) (k0 := k0) (c_num := c_num) (c_den := c_den) hexists
  have hx0m : x0 ≤ m := le_trans hx0 hm
  have hmono :
      kScaled (minXFrom x0 y1 k0 c_num c_den hexists) y1 c_num c_den ≤ kScaled m y1 c_num c_den :=
    kScaled_mono_x hm
  exact ⟨hx0m, le_trans hk0 hmono⟩

theorem minXFrom_le_iff_pred {x0 y1 k0 c_num c_den m : Nat}
    (hexists : ∃ x, x0 ≤ x ∧ k0 ≤ kScaled x y1 c_num c_den) :
    (minXFrom x0 y1 k0 c_num c_den hexists ≤ m) ↔ (x0 ≤ m ∧ k0 ≤ kScaled m y1 c_num c_den) := by
  constructor
  · intro h
    exact pred_of_minXFrom_le (x0 := x0) (y1 := y1) (k0 := k0) (c_num := c_num) (c_den := c_den) (m := m) hexists h
  · intro h
    exact minXFrom_le_of_pred (x0 := x0) (y1 := y1) (k0 := k0) (c_num := c_num) (c_den := c_den) (m := m) hexists h


/-! ## Existence for exact-out (baseline + growth) -/

theorem exists_x_from (x0 y1 k0 c_num c_den : Nat) (hy1 : 0 < y1) (hc : 0 < c_den) :
    ∃ x, x0 ≤ x ∧ k0 ≤ kScaled x y1 c_num c_den := by
  have hx : ∃ x, k0 ≤ kScaled x y1 c_num c_den :=
    exists_x_ge_kScaled (k0 := k0) (y := y1) (c_num := c_num) (c_den := c_den) hy1 hc
  rcases hx with ⟨x, hk⟩
  refine ⟨max x0 x, ?_, ?_⟩
  · exact Nat.le_max_left _ _
  · have : k0 ≤ kScaled x y1 c_num c_den := hk
    have hxle : x ≤ max x0 x := Nat.le_max_right _ _
    have hmono : kScaled x y1 c_num c_den ≤ kScaled (max x0 x) y1 c_num c_den :=
      kScaled_mono_x hxle
    exact le_trans this hmono

end QuarticBlend
end TauSwap
