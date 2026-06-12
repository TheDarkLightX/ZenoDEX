import Mathlib

/-!
# UPBA Grid Epsilon

This file records the small arithmetic bridge used by the UPBA economic
sufficiency policy checker. It proves only the budget composition step:
if the model-side grid approximation loss is bounded by the checker-computed
ceiling term, and that ceiling term plus rounding is within budget, then the
actual loss plus rounding is within budget.

It does not prove that a deployed grid is economically sufficient by itself, nor
does it prove unbounded rational optimality, UPBA v2 partial-fill economics,
oracle fairness, or inclusion fairness.
-/

namespace Proofs
namespace UPBAGridEpsilon

/-- Natural-number ceiling division used by the policy checker. -/
def ceilDiv (num den : Nat) : Nat :=
  (num + den - 1) / den

/-- Conservative raw tick-loss bound for a max input and scaled half tick. -/
def rawGridLossBound (maxInputAtoms halfTickErrorScaled economicPriceScale : Nat) : Nat :=
  ceilDiv (maxInputAtoms * halfTickErrorScaled) economicPriceScale

/-- Absolute loss bound after adding declared rounding loss. -/
def absoluteLossBound
    (maxInputAtoms halfTickErrorScaled economicPriceScale roundingLossAtoms : Nat) : Nat :=
  rawGridLossBound maxInputAtoms halfTickErrorScaled economicPriceScale + roundingLossAtoms

/--
If the model bounds actual grid loss by the checker-computed raw loss term, and
the checker has accepted that term plus rounding under the policy budget, then
the actual loss plus rounding is also inside the same budget.
-/
theorem actual_loss_plus_rounding_le_budget
    {actualGridLossAtoms maxInputAtoms halfTickErrorScaled economicPriceScale
      roundingLossAtoms maxAbsoluteLossAtoms : Nat}
    (hActual :
      actualGridLossAtoms ≤
        rawGridLossBound maxInputAtoms halfTickErrorScaled economicPriceScale)
    (hBudget :
      absoluteLossBound
        maxInputAtoms halfTickErrorScaled economicPriceScale roundingLossAtoms ≤
        maxAbsoluteLossAtoms) :
    actualGridLossAtoms + roundingLossAtoms ≤ maxAbsoluteLossAtoms := by
  unfold absoluteLossBound at hBudget
  omega

/--
Relative-loss budgets are checked by cross multiplication in integer space,
once, against the MINIMUM notional. This lemma is the report interpretation:
the single checked inequality transfers to every actual execution — any loss
below the absolute bound and any notional above the minimum satisfy the same
ppm constraint `loss/notional ≤ maxRelativeLossPpm/ppmDenom` (in cross-
multiplied integer form, so no rational arithmetic is needed on-chain).
-/
theorem relative_loss_cross_mul_budget
    {absoluteLossBoundAtoms minNotionalOutputAtoms maxRelativeLossPpm ppmDenom : Nat}
    (hCross :
      absoluteLossBoundAtoms * ppmDenom ≤
        maxRelativeLossPpm * minNotionalOutputAtoms)
    {lossAtoms notionalOutputAtoms : Nat}
    (hLoss : lossAtoms ≤ absoluteLossBoundAtoms)
    (hNotional : minNotionalOutputAtoms ≤ notionalOutputAtoms) :
    lossAtoms * ppmDenom ≤ maxRelativeLossPpm * notionalOutputAtoms :=
  calc lossAtoms * ppmDenom
      ≤ absoluteLossBoundAtoms * ppmDenom := Nat.mul_le_mul_right _ hLoss
    _ ≤ maxRelativeLossPpm * minNotionalOutputAtoms := hCross
    _ ≤ maxRelativeLossPpm * notionalOutputAtoms := Nat.mul_le_mul_left _ hNotional

end UPBAGridEpsilon
end Proofs
