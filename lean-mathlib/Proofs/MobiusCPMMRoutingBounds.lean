import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Möbius CPMM Routing Bounds

This file upgrades the "Matrix/Möbius AMM" idea into a sound, useful lemma:

For 2-hop CPMM exact-in swaps with per-hop integer `floor` rounding (modeled as `Int.floor`),
the sequential floor-per-hop output is bounded above by flooring the fully continuous 2-hop
composition once at the end (closed form).

This supports a **relax + refine** routing posture:
- Use Möbius/continuous collapse as an optimistic upper bound for pruning or seeding.
- Refine any candidate route/amount by re-simulating with the exact integer kernel semantics.

The stronger equality claim is false and must not be assumed.
-/

noncomputable section

namespace Proofs
namespace MobiusCPMMRoutingBounds

/-- The standard continuous CPMM output function. -/
def cpmm_out (X Y Δx : ℝ) : ℝ :=
  (Y * Δx) / (Δx + X)

theorem cpmm_out_comp_closed_form
  (X1 Y1 X2 Y2 z : ℝ)
  (h1 : z + X1 ≠ 0)
  (h2 : (Y1 * z) / (z + X1) + X2 ≠ 0) :
  cpmm_out X2 Y2 (cpmm_out X1 Y1 z) = (Y2 * Y1 * z) / ((Y1 + X2) * z + X2 * X1) :=
by
  have h2' : (Y1 * z) / (z + X1) + X2 ≠ 0 := h2
  simp [cpmm_out] at h2 ⊢
  field_simp [h1, h2']
  ring

theorem cpmm_out_mono_nonneg
  {X Y a b : ℝ}
  (hX : 0 < X)
  (hY : 0 ≤ Y)
  (ha : 0 ≤ a)
  (hab : a ≤ b) :
  cpmm_out X Y a ≤ cpmm_out X Y b :=
by
  have hb : 0 ≤ b := le_trans ha hab
  have haX : 0 < a + X := add_pos_of_nonneg_of_pos ha hX
  have hbX : 0 < b + X := add_pos_of_nonneg_of_pos hb hX

  have hfrac : a / (a + X) ≤ b / (b + X) := by
    apply (div_le_div_iff₀ haX hbX).2
    calc
      a * (b + X) = a * b + a * X := by ring
      _ ≤ a * b + b * X := by
        have hax : a * X ≤ b * X :=
          mul_le_mul_of_nonneg_right hab (le_of_lt hX)
        exact add_le_add_right hax (a * b)
      _ = b * (a + X) := by ring

  have hscaled : Y * (a / (a + X)) ≤ Y * (b / (b + X)) :=
    mul_le_mul_of_nonneg_left hfrac hY

  simpa [cpmm_out, mul_div_assoc] using hscaled

theorem two_hop_floor_upper_bound
  (X1 Y1 X2 Y2 z : ℝ)
  (hz : 0 ≤ z)
  (hX1 : 0 < X1)
  (hX2 : 0 < X2)
  (hY1 : 0 ≤ Y1)
  (hY2 : 0 ≤ Y2) :
  ⌊cpmm_out X2 Y2 ((⌊cpmm_out X1 Y1 z⌋ : ℤ) : ℝ)⌋ ≤
    ⌊cpmm_out X2 Y2 (cpmm_out X1 Y1 z)⌋ :=
by
  have hfloor_le : ((⌊cpmm_out X1 Y1 z⌋ : ℤ) : ℝ) ≤ cpmm_out X1 Y1 z :=
    Int.floor_le _

  have hz1_nonneg : 0 ≤ cpmm_out X1 Y1 z := by
    have hzX1 : 0 < z + X1 := add_pos_of_nonneg_of_pos hz hX1
    have hnum : 0 ≤ Y1 * z := mul_nonneg hY1 hz
    exact div_nonneg hnum (le_of_lt hzX1)

  have hfloor_nonneg_int : 0 ≤ ⌊cpmm_out X1 Y1 z⌋ :=
    (Int.floor_nonneg).2 hz1_nonneg

  have hfloor_nonneg : 0 ≤ ((⌊cpmm_out X1 Y1 z⌋ : ℤ) : ℝ) := by
    exact_mod_cast hfloor_nonneg_int

  have hmono :
      cpmm_out X2 Y2 ((⌊cpmm_out X1 Y1 z⌋ : ℤ) : ℝ) ≤
        cpmm_out X2 Y2 (cpmm_out X1 Y1 z) :=
    cpmm_out_mono_nonneg (X := X2) (Y := Y2) (a := ((⌊cpmm_out X1 Y1 z⌋ : ℤ) : ℝ))
      (b := cpmm_out X1 Y1 z) hX2 hY2 hfloor_nonneg hfloor_le

  exact Int.floor_le_floor hmono

theorem two_hop_floor_upper_bound_closed_form
  (X1 Y1 X2 Y2 z : ℝ)
  (hz : 0 ≤ z)
  (hX1 : 0 < X1)
  (hX2 : 0 < X2)
  (hY1 : 0 ≤ Y1)
  (hY2 : 0 ≤ Y2) :
  ⌊cpmm_out X2 Y2 ((⌊cpmm_out X1 Y1 z⌋ : ℤ) : ℝ)⌋ ≤
    ⌊(Y2 * Y1 * z) / ((Y1 + X2) * z + X2 * X1)⌋ :=
by
  have hzX1 : z + X1 ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hz hX1)
  have hzY1X2 : (Y1 * z) / (z + X1) + X2 ≠ 0 := by
    have hzX1_pos : 0 < z + X1 := add_pos_of_nonneg_of_pos hz hX1
    have hnum : 0 ≤ Y1 * z := mul_nonneg hY1 hz
    have hz1 : 0 ≤ (Y1 * z) / (z + X1) := div_nonneg hnum (le_of_lt hzX1_pos)
    exact ne_of_gt (add_pos_of_nonneg_of_pos hz1 hX2)

  have hub :
      ⌊cpmm_out X2 Y2 ((⌊cpmm_out X1 Y1 z⌋ : ℤ) : ℝ)⌋ ≤
        ⌊cpmm_out X2 Y2 (cpmm_out X1 Y1 z)⌋ :=
    two_hop_floor_upper_bound (X1 := X1) (Y1 := Y1) (X2 := X2) (Y2 := Y2) (z := z)
      hz hX1 hX2 hY1 hY2

  have hcf :
      cpmm_out X2 Y2 (cpmm_out X1 Y1 z) =
        (Y2 * Y1 * z) / ((Y1 + X2) * z + X2 * X1) :=
    cpmm_out_comp_closed_form (X1 := X1) (Y1 := Y1) (X2 := X2) (Y2 := Y2) (z := z) hzX1 hzY1X2

  simpa [hcf] using hub

end MobiusCPMMRoutingBounds
end Proofs
