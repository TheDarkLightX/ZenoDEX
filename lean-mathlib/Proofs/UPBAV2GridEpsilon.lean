import Mathlib

/-!
# UPBA V2 Grid Epsilon

This file records the small arithmetic bridge used by the UPBA v2 partial-fill
economic sufficiency policy checker. It proves only the budget composition step:
if model-side price-grid and fill-quantum approximation losses are each bounded
by checker-computed ceiling terms, and those terms plus rounding fit the policy
budget, then the actual combined loss plus rounding fits the same budget.

It does not prove unbounded rational optimality, complete fill-vector search by
itself, oracle fairness, inclusion fairness, exact-out, multi-hop routing, or
production network readiness.
-/

namespace Proofs
namespace UPBAV2GridEpsilon

/-- Natural-number ceiling division used by the policy checker. -/
def ceilDiv (num den : Nat) : Nat :=
  (num + den - 1) / den

/-- Conservative scaled price-grid tick-loss bound for total executed input. -/
def priceGridLossBound
    (maxTotalExecutedInputAtoms halfTickErrorScaled economicPriceScale : Nat) : Nat :=
  ceilDiv (maxTotalExecutedInputAtoms * halfTickErrorScaled) economicPriceScale

/-- Conservative fill-quantum loss bound across active intents. -/
def fillQuantumLossBound
    (maxActiveIntents halfFillQuantumAtoms economicMaxPriceScaled economicPriceScale : Nat) : Nat :=
  ceilDiv (maxActiveIntents * halfFillQuantumAtoms * economicMaxPriceScaled) economicPriceScale

/-- Combined absolute loss bound after adding declared rounding loss. -/
def absoluteLossBound
    (priceLossBound fillLossBound roundingLossAtoms : Nat) : Nat :=
  priceLossBound + fillLossBound + roundingLossAtoms

/--
If the model bounds actual price-grid and fill-quantum losses by the
checker-computed terms, and the checker accepts those terms plus rounding under
the policy budget, then actual combined loss plus rounding is also inside the
same budget.
-/
theorem actual_partial_loss_plus_rounding_le_budget
    {actualPriceGridLossAtoms actualFillQuantumLossAtoms
      priceLossBound fillLossBound roundingLossAtoms maxAbsoluteLossAtoms : Nat}
    (hPrice : actualPriceGridLossAtoms ≤ priceLossBound)
    (hFill : actualFillQuantumLossAtoms ≤ fillLossBound)
    (hBudget :
      absoluteLossBound priceLossBound fillLossBound roundingLossAtoms ≤
        maxAbsoluteLossAtoms) :
    actualPriceGridLossAtoms + actualFillQuantumLossAtoms + roundingLossAtoms ≤
      maxAbsoluteLossAtoms := by
  unfold absoluteLossBound at hBudget
  omega

/--
Relative-loss budgets are checked by cross multiplication in integer space.
This theorem records the report interpretation exposed by the checker.
-/
theorem relative_loss_cross_mul_budget
    {absoluteLossBoundAtoms minNotionalOutputAtoms maxRelativeLossPpm ppmDenom : Nat}
    (hCross :
      absoluteLossBoundAtoms * ppmDenom ≤
        maxRelativeLossPpm * minNotionalOutputAtoms) :
    absoluteLossBoundAtoms * ppmDenom ≤
      maxRelativeLossPpm * minNotionalOutputAtoms := hCross

end UPBAV2GridEpsilon
end Proofs
