import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exact-Out Adaptive Two-Hop Gate

Arithmetic lemmas for the adaptive exact-out routing gate:

- Base gate: `stress >= stress_threshold OR pressure >= pressure_threshold`
- Adaptive gate: same stress branch, but pressure threshold is lifted by
  `slope * max(0, stress_threshold - stress)`.

These lemmas formalize that for nonnegative slope, the adaptive gate is a
conservative refinement of the base OR gate.
-/

namespace Proofs
namespace ExactOutAdaptiveGate

def baseGate
    (stress pressure stressThreshold pressureThreshold : Real) : Prop :=
  stress ≥ stressThreshold ∨ pressure ≥ pressureThreshold

def adaptiveGate
    (stress pressure stressThreshold pressureThreshold slope : Real) : Prop :=
  stress ≥ stressThreshold ∨
    pressure ≥ pressureThreshold + slope * max 0 (stressThreshold - stress)

def piecewiseGate
    (stress pressure stressThreshold stressCutoff pressureMid pressureLow : Real) : Prop :=
  stress ≥ stressThreshold ∨
    ((stress ≥ stressCutoff ∧ pressure ≥ pressureMid) ∨
      (stress < stressCutoff ∧ pressure ≥ pressureLow))

def piecewiseFeeGate
    (stress pressure stressThreshold stressCutoff pressureMid pressureLow feeSlope feeFrac : Real) : Prop :=
  stress ≥ stressThreshold ∨
    ((stress ≥ stressCutoff ∧ pressure ≥ pressureMid) ∨
      (stress < stressCutoff ∧ pressure ≥ pressureLow + feeSlope * feeFrac))

def triPieceGate
    (stress pressure stressThreshold lowCutoff upperCutoff
      pressureUpper pressureMid pressureLow feeSlope feeFrac : Real) : Prop :=
  stress ≥ stressThreshold ∨
    ((stress ≥ upperCutoff ∧ pressure ≥ pressureUpper) ∨
      ((stress ≥ lowCutoff ∧ stress < upperCutoff ∧ pressure ≥ pressureMid) ∨
        (stress < lowCutoff ∧ pressure ≥ pressureLow + feeSlope * feeFrac)))

theorem adaptive_threshold_ge_base
    (stress stressThreshold pressureThreshold slope : Real)
    (hSlope : 0 ≤ slope) :
    pressureThreshold ≤
      pressureThreshold + slope * max 0 (stressThreshold - stress) := by
  have hMax : 0 ≤ max 0 (stressThreshold - stress) := by
    exact le_max_left 0 (stressThreshold - stress)
  have hMul : 0 ≤ slope * max 0 (stressThreshold - stress) := by
    exact mul_nonneg hSlope hMax
  linarith

theorem adaptive_implies_base
    (stress pressure stressThreshold pressureThreshold slope : Real)
    (hSlope : 0 ≤ slope)
    (hAdaptive : adaptiveGate stress pressure stressThreshold pressureThreshold slope) :
    baseGate stress pressure stressThreshold pressureThreshold := by
  rcases hAdaptive with hStress | hPressure
  · exact Or.inl hStress
  · right
    have hThreshold :
        pressureThreshold ≤
          pressureThreshold + slope * max 0 (stressThreshold - stress) := by
      exact adaptive_threshold_ge_base stress stressThreshold pressureThreshold slope hSlope
    exact le_trans hThreshold hPressure

theorem adaptive_threshold_monotone_in_slope
    (stress stressThreshold pressureThreshold slope0 slope1 : Real)
    (hSlope01 : slope0 ≤ slope1) :
    pressureThreshold + slope0 * max 0 (stressThreshold - stress) ≤
      pressureThreshold + slope1 * max 0 (stressThreshold - stress) := by
  have hMax : 0 ≤ max 0 (stressThreshold - stress) := by
    exact le_max_left 0 (stressThreshold - stress)
  have hMul : slope0 * max 0 (stressThreshold - stress) ≤
      slope1 * max 0 (stressThreshold - stress) := by
    exact mul_le_mul_of_nonneg_right hSlope01 hMax
  linarith

theorem low_stress_strictly_raises_threshold
    (stress stressThreshold pressureThreshold slope : Real)
    (hStress : stress < stressThreshold)
    (hSlope : 0 < slope) :
    pressureThreshold <
      pressureThreshold + slope * max 0 (stressThreshold - stress) := by
  have hDiffPos : 0 < stressThreshold - stress := by
    linarith
  have hDiffNonneg : 0 ≤ stressThreshold - stress := by
    linarith
  have hMaxEq : max 0 (stressThreshold - stress) = stressThreshold - stress := by
    exact max_eq_right hDiffNonneg
  have hMulPos : 0 < slope * max 0 (stressThreshold - stress) := by
    rw [hMaxEq]
    exact mul_pos hSlope hDiffPos
  linarith

theorem piecewise_implies_base
    (stress pressure stressThreshold pressureThreshold stressCutoff pressureMid pressureLow : Real)
    (hMidGe : pressureThreshold ≤ pressureMid)
    (hLowGe : pressureThreshold ≤ pressureLow)
    (hPiece : piecewiseGate stress pressure stressThreshold stressCutoff pressureMid pressureLow) :
    baseGate stress pressure stressThreshold pressureThreshold := by
  rcases hPiece with hStress | hTail
  · exact Or.inl hStress
  · rcases hTail with hMid | hLow
    · rcases hMid with ⟨hStressGeCutoff, hPressureGeMid⟩
      by_cases hStress : stress ≥ stressThreshold
      · exact Or.inl hStress
      · right
        exact le_trans hMidGe hPressureGeMid
    · rcases hLow with ⟨_hStressLtCutoff, hPressureGeLow⟩
      right
      exact le_trans hLowGe hPressureGeLow

theorem piecewise_low_band_requires_low_threshold
    (stress pressure stressThreshold stressCutoff pressureMid pressureLow : Real)
    (hStressLt : stress < stressCutoff)
    (hPressureLow : pressure ≥ pressureLow) :
    piecewiseGate stress pressure stressThreshold stressCutoff pressureMid pressureLow := by
  by_cases hStressTop : stress ≥ stressThreshold
  · exact Or.inl hStressTop
  · exact Or.inr (Or.inr ⟨hStressLt, hPressureLow⟩)

theorem piecewise_fee_implies_base
    (stress pressure stressThreshold pressureThreshold stressCutoff pressureMid pressureLow feeSlope feeFrac : Real)
    (hMidGe : pressureThreshold ≤ pressureMid)
    (hLowGe : pressureThreshold ≤ pressureLow)
    (hFeeSlope : 0 ≤ feeSlope)
    (hFeeFrac : 0 ≤ feeFrac)
    (hPiece : piecewiseFeeGate stress pressure stressThreshold stressCutoff pressureMid pressureLow feeSlope feeFrac) :
    baseGate stress pressure stressThreshold pressureThreshold := by
  rcases hPiece with hStress | hTail
  · exact Or.inl hStress
  · rcases hTail with hMid | hLow
    · rcases hMid with ⟨_hStressGeCutoff, hPressureGeMid⟩
      by_cases hStressTop : stress ≥ stressThreshold
      · exact Or.inl hStressTop
      · right
        exact le_trans hMidGe hPressureGeMid
    · rcases hLow with ⟨_hStressLtCutoff, hPressureGeLowFee⟩
      right
      have hLowFeeGe : pressureThreshold ≤ pressureLow + feeSlope * feeFrac := by
        have hMulNonneg : 0 ≤ feeSlope * feeFrac := mul_nonneg hFeeSlope hFeeFrac
        linarith
      exact le_trans hLowFeeGe hPressureGeLowFee

theorem tri_piece_implies_base
    (stress pressure stressThreshold pressureThreshold lowCutoff upperCutoff
      pressureUpper pressureMid pressureLow feeSlope feeFrac : Real)
    (hUpperGe : pressureThreshold ≤ pressureUpper)
    (hMidGe : pressureThreshold ≤ pressureMid)
    (hLowGe : pressureThreshold ≤ pressureLow)
    (hFeeSlope : 0 ≤ feeSlope)
    (hFeeFrac : 0 ≤ feeFrac)
    (hTri : triPieceGate stress pressure stressThreshold lowCutoff upperCutoff
      pressureUpper pressureMid pressureLow feeSlope feeFrac) :
    baseGate stress pressure stressThreshold pressureThreshold := by
  rcases hTri with hStress | hTail
  · exact Or.inl hStress
  · rcases hTail with hUpper | hRest
    · rcases hUpper with ⟨_hStressGeUpper, hPressureGeUpper⟩
      by_cases hStressTop : stress ≥ stressThreshold
      · exact Or.inl hStressTop
      · right
        exact le_trans hUpperGe hPressureGeUpper
    · rcases hRest with hMid | hLow
      · rcases hMid with ⟨_hStressGeLow, _hStressLtUpper, hPressureGeMid⟩
        by_cases hStressTop : stress ≥ stressThreshold
        · exact Or.inl hStressTop
        · right
          exact le_trans hMidGe hPressureGeMid
      · rcases hLow with ⟨_hStressLtLow, hPressureGeLowFee⟩
        right
        have hLowFeeGe : pressureThreshold ≤ pressureLow + feeSlope * feeFrac := by
          have hMulNonneg : 0 ≤ feeSlope * feeFrac := mul_nonneg hFeeSlope hFeeFrac
          linarith
        exact le_trans hLowFeeGe hPressureGeLowFee

end ExactOutAdaptiveGate
end Proofs
