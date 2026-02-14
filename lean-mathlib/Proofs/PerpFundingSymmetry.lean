import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Perp Funding Symmetry

Arithmetic lemmas for the v2 funding transfer design:
- account A pays `funding_a`
- account B receives exactly `funding_a`
- funding paid accumulators update with opposite signs

This proves conservation-style identities used by the perp funding split checks.
-/

namespace Proofs
namespace PerpFundingSymmetry

def fundingTransfer (positionBase markPriceE8 fundingRateBps : Int) : Int :=
  (((positionBase * markPriceE8) / 100000000) * fundingRateBps) / 10000

def nextCollateralA (collateralA transfer : Int) : Int := collateralA - transfer
def nextCollateralB (collateralB transfer : Int) : Int := collateralB + transfer

def nextFundingPaidA (fundingPaidA transfer : Int) : Int := fundingPaidA + transfer
def nextFundingPaidB (fundingPaidB transfer : Int) : Int := fundingPaidB - transfer

theorem collateral_total_preserved
    {collateralA collateralB transfer : Int} :
    nextCollateralA collateralA transfer + nextCollateralB collateralB transfer =
      collateralA + collateralB := by
  simp [nextCollateralA, nextCollateralB]

theorem funding_paid_sum_preserved
    {fundingPaidA fundingPaidB transfer : Int} :
    nextFundingPaidA fundingPaidA transfer + nextFundingPaidB fundingPaidB transfer =
      fundingPaidA + fundingPaidB := by
  simp [nextFundingPaidA, nextFundingPaidB]

theorem funding_net_delta_zero
    {fundingPaidA fundingPaidB transfer : Int} :
    (nextFundingPaidA fundingPaidA transfer - fundingPaidA) +
      (nextFundingPaidB fundingPaidB transfer - fundingPaidB) = 0 := by
  simp [nextFundingPaidA, nextFundingPaidB]

theorem funding_b_is_neg_funding_a {transfer : Int} :
    0 - transfer = -transfer := by
  ring

theorem witness_funding_paid_update :
    nextFundingPaidA 7 3 = 10 ∧ nextFundingPaidB (-4) 3 = -7 := by
  native_decide

theorem witness_collateral_conservation :
    nextCollateralA 25 9 + nextCollateralB 13 9 = 38 := by
  native_decide

end PerpFundingSymmetry
end Proofs
