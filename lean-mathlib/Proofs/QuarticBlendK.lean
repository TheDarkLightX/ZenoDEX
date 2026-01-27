import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Quartic-blend invariant facts (Nat / integer-kernel oriented)

This file provides small, reusable lemmas about the quartic-blend invariant used by the DEX
kernel `src/kernels/python/quartic_blend_swap_v1.py`.

We work with the **scaled** invariant (all-integer arithmetic):

`K_scaled(x,y) = x*y*(c_den*(x^2 + y^2) + c_num*x*y)`

The key properties we need for deterministic kernels are monotonicity in each reserve and the
existence/characterization of the minimal `y` satisfying `K_scaled(x1,y) ≥ K0` (i.e., the
post-swap out-reserve computed via bisection in the implementation).
-/

namespace TauSwap
namespace QuarticBlend

/-! ## Definitions -/

def quadScaled (x y c_num c_den : Nat) : Nat :=
  c_den * (x * x + y * y) + c_num * x * y

def kScaled (x y c_num c_den : Nat) : Nat :=
  (x * y) * quadScaled x y c_num c_den

/-! ## Symmetry -/

theorem quadScaled_symm (x y c_num c_den : Nat) :
    quadScaled x y c_num c_den = quadScaled y x c_num c_den := by
  unfold quadScaled
  ring

theorem kScaled_symm (x y c_num c_den : Nat) :
    kScaled x y c_num c_den = kScaled y x c_num c_den := by
  unfold kScaled quadScaled
  ring

/-! ## Monotonicity -/

theorem quadScaled_mono_y {x y1 y2 c_num c_den : Nat} (hy : y1 ≤ y2) :
    quadScaled x y1 c_num c_den ≤ quadScaled x y2 c_num c_den := by
  unfold quadScaled
  have hyy : y1 * y1 ≤ y2 * y2 := Nat.mul_le_mul hy hy
  have hsum : x * x + y1 * y1 ≤ x * x + y2 * y2 := Nat.add_le_add_left hyy (x * x)
  have hterm1 : c_den * (x * x + y1 * y1) ≤ c_den * (x * x + y2 * y2) :=
    Nat.mul_le_mul_left c_den hsum
  have hterm2 : c_num * x * y1 ≤ c_num * x * y2 := by
    have : (c_num * x) * y1 ≤ (c_num * x) * y2 := Nat.mul_le_mul_left (c_num * x) hy
    simpa [Nat.mul_assoc] using this
  exact Nat.add_le_add hterm1 (by simpa [Nat.mul_assoc] using hterm2)

theorem quadScaled_mono_x {x1 x2 y c_num c_den : Nat} (hx : x1 ≤ x2) :
    quadScaled x1 y c_num c_den ≤ quadScaled x2 y c_num c_den := by
  unfold quadScaled
  have hxx : x1 * x1 ≤ x2 * x2 := Nat.mul_le_mul hx hx
  have hsum : x1 * x1 + y * y ≤ x2 * x2 + y * y := Nat.add_le_add_right hxx (y * y)
  have hterm1 : c_den * (x1 * x1 + y * y) ≤ c_den * (x2 * x2 + y * y) :=
    Nat.mul_le_mul_left c_den hsum
  have hterm2 : c_num * x1 * y ≤ c_num * x2 * y := by
    have : (c_num * x1) * y ≤ (c_num * x2) * y :=
      Nat.mul_le_mul_right y (Nat.mul_le_mul_left c_num hx)
    simpa [Nat.mul_assoc] using this
  exact Nat.add_le_add hterm1 (by simpa [Nat.mul_assoc] using hterm2)

theorem kScaled_mono_y {x y1 y2 c_num c_den : Nat} (hy : y1 ≤ y2) :
    kScaled x y1 c_num c_den ≤ kScaled x y2 c_num c_den := by
  unfold kScaled
  have ha : x * y1 ≤ x * y2 := Nat.mul_le_mul_left x hy
  have hb : quadScaled x y1 c_num c_den ≤ quadScaled x y2 c_num c_den := quadScaled_mono_y hy
  have h1 :
      (x * y1) * quadScaled x y1 c_num c_den ≤ (x * y2) * quadScaled x y1 c_num c_den :=
    Nat.mul_le_mul_right (quadScaled x y1 c_num c_den) ha
  have h2 :
      (x * y2) * quadScaled x y1 c_num c_den ≤ (x * y2) * quadScaled x y2 c_num c_den :=
    Nat.mul_le_mul_left (x * y2) hb
  exact le_trans h1 h2

theorem kScaled_mono_x {x1 x2 y c_num c_den : Nat} (hx : x1 ≤ x2) :
    kScaled x1 y c_num c_den ≤ kScaled x2 y c_num c_den := by
  unfold kScaled
  have ha : x1 * y ≤ x2 * y := Nat.mul_le_mul_right y hx
  have hb : quadScaled x1 y c_num c_den ≤ quadScaled x2 y c_num c_den := quadScaled_mono_x hx
  have h1 :
      (x1 * y) * quadScaled x1 y c_num c_den ≤ (x2 * y) * quadScaled x1 y c_num c_den :=
    Nat.mul_le_mul_right (quadScaled x1 y c_num c_den) ha
  have h2 :
      (x2 * y) * quadScaled x1 y c_num c_den ≤ (x2 * y) * quadScaled x2 y c_num c_den :=
    Nat.mul_le_mul_left (x2 * y) hb
  exact le_trans h1 h2

/-! ## Minimal post-swap out-reserve (spec) -/

noncomputable def minY
    (x1 yMax k0 c_num c_den : Nat)
    (hyMax : k0 ≤ kScaled x1 yMax c_num c_den) : Nat :=
  Nat.find (⟨yMax, hyMax⟩ : ∃ y, k0 ≤ kScaled x1 y c_num c_den)

theorem minY_spec {x1 yMax k0 c_num c_den : Nat} (hyMax : k0 ≤ kScaled x1 yMax c_num c_den) :
    k0 ≤ kScaled x1 (minY x1 yMax k0 c_num c_den hyMax) c_num c_den :=
  Nat.find_spec (⟨yMax, hyMax⟩ : ∃ y, k0 ≤ kScaled x1 y c_num c_den)

theorem minY_le_yMax {x1 yMax k0 c_num c_den : Nat} (hyMax : k0 ≤ kScaled x1 yMax c_num c_den) :
    minY x1 yMax k0 c_num c_den hyMax ≤ yMax :=
  Nat.find_le (n := yMax) (p := fun y => k0 ≤ kScaled x1 y c_num c_den) hyMax

theorem lt_minY_imp_kScaled_lt {x1 yMax k0 c_num c_den m : Nat}
    (hyMax : k0 ≤ kScaled x1 yMax c_num c_den)
    (hm : m < minY x1 yMax k0 c_num c_den hyMax) :
    kScaled x1 m c_num c_den < k0 := by
  have hnot : ¬k0 ≤ kScaled x1 m c_num c_den :=
    Nat.find_min (p := fun y => k0 ≤ kScaled x1 y c_num c_den) (⟨yMax, hyMax⟩ : ∃ y, k0 ≤ kScaled x1 y c_num c_den) hm
  exact Nat.lt_of_not_ge hnot

theorem kScaled_ge_of_minY_le {x1 yMax k0 c_num c_den m : Nat}
    (hyMax : k0 ≤ kScaled x1 yMax c_num c_den)
    (hm : minY x1 yMax k0 c_num c_den hyMax ≤ m) :
    k0 ≤ kScaled x1 m c_num c_den := by
  have hmono :
      kScaled x1 (minY x1 yMax k0 c_num c_den hyMax) c_num c_den ≤ kScaled x1 m c_num c_den :=
    kScaled_mono_y hm
  exact le_trans (minY_spec hyMax) hmono

end QuarticBlend
end TauSwap

