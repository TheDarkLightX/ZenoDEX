import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Perp Liquidation Insurance Bound

Arithmetic lemmas for liquidation-state updates:
- insurance update formula is explicit
- upper-bound preservation from guard assumptions
- nonnegativity from claims bound

These mirror the v2 liquidation overflow-guard obligations.
-/

namespace Proofs
namespace PerpLiquidationInsuranceBound

def nextInsuranceBalance
    (initialInsurance feeIncome liquidationPenalty claimsPaid : Int) : Int :=
  (initialInsurance + (feeIncome + liquidationPenalty)) - claimsPaid

def preLiquidationInsurance
    (initialInsurance feeIncome claimsPaid : Int) : Int :=
  (initialInsurance + feeIncome) - claimsPaid

theorem next_insurance_eq_pre_plus_penalty
    {initialInsurance feeIncome liquidationPenalty claimsPaid : Int} :
    nextInsuranceBalance initialInsurance feeIncome liquidationPenalty claimsPaid =
      preLiquidationInsurance initialInsurance feeIncome claimsPaid + liquidationPenalty := by
  simp [nextInsuranceBalance, preLiquidationInsurance]
  ring

theorem next_insurance_le_cap
    {initialInsurance feeIncome liquidationPenalty claimsPaid cap : Int}
    (hBase : initialInsurance + (feeIncome + liquidationPenalty) ≤ cap)
    (hClaimsNonneg : 0 ≤ claimsPaid) :
    nextInsuranceBalance initialInsurance feeIncome liquidationPenalty claimsPaid ≤ cap := by
  unfold nextInsuranceBalance
  linarith

theorem next_insurance_nonneg
    {initialInsurance feeIncome liquidationPenalty claimsPaid : Int}
    (hClaimsBound : claimsPaid ≤ initialInsurance + (feeIncome + liquidationPenalty)) :
    0 ≤ nextInsuranceBalance initialInsurance feeIncome liquidationPenalty claimsPaid := by
  unfold nextInsuranceBalance
  linarith

theorem state_guard_implies_next_cap
    {initialInsurance feeIncome liquidationPenalty claimsPaid cap : Int}
    (hGuard : preLiquidationInsurance initialInsurance feeIncome claimsPaid + liquidationPenalty ≤ cap) :
    nextInsuranceBalance initialInsurance feeIncome liquidationPenalty claimsPaid ≤ cap := by
  rw [next_insurance_eq_pre_plus_penalty]
  exact hGuard

theorem witness_next_insurance_eval :
    nextInsuranceBalance 1000 50 10 20 = 1040 := by
  native_decide

theorem witness_bound_example :
    nextInsuranceBalance 100 5 2 3 ≤ 110 := by
  native_decide

end PerpLiquidationInsuranceBound
end Proofs
