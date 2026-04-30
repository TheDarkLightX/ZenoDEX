import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Fixed-Point Interval Bridge

This packet turns the numerical-analysis source shelf into a reusable runtime
bridge for ZenoDEX.

If a real-valued proof establishes `x ∈ [L, U]`, then floor/ceil fixed-point
integer encoding and decoding stays inside the same interval expanded by at
most one tick. This is the basic continuous-to-integer envelope needed before
continuous AMM, payoff, or risk math can safely drive integer runtime checks.
-/

namespace Proofs
namespace FixedPointIntervalBridge

noncomputable section

def tick (scale : ℝ) : ℝ := 1 / scale

def floorScaled (scale x : ℝ) : ℤ := ⌊scale * x⌋

def ceilScaled (scale x : ℝ) : ℤ := ⌈scale * x⌉

def decode (scale : ℝ) (z : ℤ) : ℝ := (z : ℝ) / scale

def floorDecode (scale x : ℝ) : ℝ :=
  decode scale (floorScaled scale x)

def ceilDecode (scale x : ℝ) : ℝ :=
  decode scale (ceilScaled scale x)

theorem floorDecode_le_original
    {scale x : ℝ} (hscale : 0 < scale) :
    floorDecode scale x ≤ x := by
  unfold floorDecode decode floorScaled
  rw [div_le_iff₀ hscale]
  simpa [mul_comm] using (Int.floor_le (scale * x))

theorem original_sub_tick_lt_floorDecode
    {scale x : ℝ} (hscale : 0 < scale) :
    x - tick scale < floorDecode scale x := by
  unfold floorDecode decode floorScaled
  rw [lt_div_iff₀ hscale]
  have hfloor :
      scale * x - 1 < ((⌊scale * x⌋ : ℤ) : ℝ) :=
    Int.sub_one_lt_floor (scale * x)
  have hleft : (x - tick scale) * scale = scale * x - 1 := by
    unfold tick
    field_simp [ne_of_gt hscale]
  rw [hleft]
  exact hfloor

theorem floorDecode_mem_expanded_interval
    {scale x L U : ℝ} (hscale : 0 < scale)
    (hx : L ≤ x ∧ x ≤ U) :
    L - tick scale < floorDecode scale x ∧ floorDecode scale x ≤ U := by
  constructor
  · have h := original_sub_tick_lt_floorDecode (scale := scale) (x := x) hscale
    linarith
  · exact (floorDecode_le_original (scale := scale) (x := x) hscale).trans hx.2

theorem original_le_ceilDecode
    {scale x : ℝ} (hscale : 0 < scale) :
    x ≤ ceilDecode scale x := by
  unfold ceilDecode decode ceilScaled
  rw [le_div_iff₀ hscale]
  simpa [mul_comm] using (Int.le_ceil (scale * x))

theorem ceilDecode_lt_original_add_tick
    {scale x : ℝ} (hscale : 0 < scale) :
    ceilDecode scale x < x + tick scale := by
  unfold ceilDecode decode ceilScaled
  rw [div_lt_iff₀ hscale]
  have hceil :
      ((⌈scale * x⌉ : ℤ) : ℝ) < scale * x + 1 :=
    Int.ceil_lt_add_one (scale * x)
  have hright : (x + tick scale) * scale = scale * x + 1 := by
    unfold tick
    field_simp [ne_of_gt hscale]
  rw [hright]
  exact hceil

theorem ceilDecode_mem_expanded_interval
    {scale x L U : ℝ} (hscale : 0 < scale)
    (hx : L ≤ x ∧ x ≤ U) :
    L ≤ ceilDecode scale x ∧ ceilDecode scale x < U + tick scale := by
  constructor
  · exact hx.1.trans (original_le_ceilDecode (scale := scale) (x := x) hscale)
  · have h := ceilDecode_lt_original_add_tick (scale := scale) (x := x) hscale
    linarith

theorem floorDecode_abs_error_lt_tick
    {scale x : ℝ} (hscale : 0 < scale) :
    |x - floorDecode scale x| < tick scale := by
  have hLe := floorDecode_le_original (scale := scale) (x := x) hscale
  have hLt := original_sub_tick_lt_floorDecode (scale := scale) (x := x) hscale
  have hNonneg : 0 ≤ x - floorDecode scale x := sub_nonneg.mpr hLe
  rw [abs_of_nonneg hNonneg]
  linarith

theorem ceilDecode_abs_error_lt_tick
    {scale x : ℝ} (hscale : 0 < scale) :
    |ceilDecode scale x - x| < tick scale := by
  have hLe := original_le_ceilDecode (scale := scale) (x := x) hscale
  have hLt := ceilDecode_lt_original_add_tick (scale := scale) (x := x) hscale
  have hNonneg : 0 ≤ ceilDecode scale x - x := sub_nonneg.mpr hLe
  rw [abs_of_nonneg hNonneg]
  linarith

end

end FixedPointIntervalBridge
end Proofs
