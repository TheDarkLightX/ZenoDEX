import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic

/-!
# Perpetual margin rounding safety

The legacy v3 isolated-perps runtime floors notional and then floors the margin
rate application. This file records the exact dust counterexample and proves
the single-step ceiling contract used by v4.

The safe requirement is the least quote-unit integer whose scaled value covers
the unrounded product `|position| * price_e8 * margin_bps`.

The executable v4 formula is also proved definitionally equal to `Nat.ceilDiv`,
linking the Python/YAML expression `(n + d - 1) / d` to the coverage and
minimality theorems below.
-/

namespace Proofs
namespace PerpMarginRoundingSafety

def priceScale : ℕ := 100_000_000
def bpsScale : ℕ := 10_000
def marginDenominator : ℕ := priceScale * bpsScale

/-- Current runtime behavior: floor the quote notional, then floor the margin. -/
def nestedFloorMargin (positionAbs priceE8 marginBps : ℕ) : ℕ :=
  ((positionAbs * priceE8) / priceScale * marginBps) / bpsScale

def rawMarginNumerator (positionAbs priceE8 marginBps : ℕ) : ℕ :=
  positionAbs * priceE8 * marginBps

/-- Proposed v4 behavior: one ceiling division over the full scaled product. -/
def safeCeilMargin (positionAbs priceE8 marginBps : ℕ) : ℕ :=
  rawMarginNumerator positionAbs priceE8 marginBps ⌈/⌉ marginDenominator

/-- Arithmetic form executed by the v4 Python runtime and ESSO kernel. -/
def implementationSafeCeilMargin (positionAbs priceE8 marginBps : ℕ) : ℕ :=
  (rawMarginNumerator positionAbs priceE8 marginBps + marginDenominator - 1) /
    marginDenominator

theorem implementationSafeCeilMargin_eq_safeCeilMargin
    (positionAbs priceE8 marginBps : ℕ) :
    implementationSafeCeilMargin positionAbs priceE8 marginBps =
      safeCeilMargin positionAbs priceE8 marginBps := by
  rfl

theorem marginDenominator_pos : 0 < marginDenominator := by
  decide

/-- A one-base-unit position at a one-quote price and 10% initial margin has a
zero requirement under the current nested-floor arithmetic. -/
theorem nested_floor_dust_witness :
    nestedFloorMargin 1 100_000_000 1_000 = 0 := by
  decide

/-- The current collateral guard therefore admits zero collateral for the dust
position represented by `nested_floor_dust_witness`. -/
theorem zero_collateral_passes_nested_floor_guard :
    nestedFloorMargin 1 100_000_000 1_000 ≤ 0 := by
  decide

/-- Single-step ceiling assigns one quote unit to the same positive risk. -/
theorem safe_ceil_dust_witness :
    safeCeilMargin 1 100_000_000 1_000 = 1 := by
  decide

theorem zero_collateral_fails_safe_ceil_guard :
    ¬ safeCeilMargin 1 100_000_000 1_000 ≤ 0 := by
  decide

/-- Ceiling margin covers the exact unrounded numerator after rescaling. -/
theorem safeCeilMargin_covers_raw
    (positionAbs priceE8 marginBps : ℕ) :
    rawMarginNumerator positionAbs priceE8 marginBps ≤
      marginDenominator * safeCeilMargin positionAbs priceE8 marginBps := by
  simpa [safeCeilMargin] using
    (le_smul_ceilDiv
      (a := marginDenominator)
      (b := rawMarginNumerator positionAbs priceE8 marginBps)
      marginDenominator_pos)

/-- `safeCeilMargin` is the least integer quote requirement that covers the raw
risk numerator. -/
theorem safeCeilMargin_minimal
    (positionAbs priceE8 marginBps candidateQuote : ℕ)
    (hCovers :
      rawMarginNumerator positionAbs priceE8 marginBps ≤
        candidateQuote * marginDenominator) :
    safeCeilMargin positionAbs priceE8 marginBps ≤ candidateQuote := by
  apply (ceilDiv_le_iff_le_mul marginDenominator_pos).2
  simpa [safeCeilMargin, Nat.mul_comm] using hCovers

/-- Every positive raw risk numerator produces a positive safe requirement. -/
theorem safeCeilMargin_pos_of_raw_pos
    (positionAbs priceE8 marginBps : ℕ)
    (hRaw : 0 < rawMarginNumerator positionAbs priceE8 marginBps) :
    0 < safeCeilMargin positionAbs priceE8 marginBps := by
  by_contra hNotPos
  have hZero : safeCeilMargin positionAbs priceE8 marginBps = 0 := by
    omega
  have hCover := safeCeilMargin_covers_raw positionAbs priceE8 marginBps
  rw [hZero] at hCover
  simp at hCover
  omega

end PerpMarginRoundingSafety
end Proofs
