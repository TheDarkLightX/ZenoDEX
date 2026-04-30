import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Cross-Surface Benefit Budget

A small checked accounting anchor for the post-AGI role-collapse discussion.

The purpose is to stop treating settlement, liquidity, oracle, and governance
transfers as if each had an independent reward budget. A single principal should
be bounded by one shared verified-benefit budget after overlap removal.
-/

namespace Proofs
namespace CrossSurfaceBenefitBudget

/-- Shared verified benefit budget after overlap removal. -/
def sharedVerifiedBudget
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int) : Int :=
  settlementBenefit + liquidityBenefit + oracleBenefit + governanceBenefit - overlap

/-- Combined take across settlement, liquidity, oracle, and governance transfer surfaces. -/
def totalCrossSurfaceTake
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int) : Int :=
  rewardSettlement + rewardLiquidity + rewardOracle + governanceTransfer

/-- Increasing overlap can only reduce the shared verified budget. -/
theorem shared_budget_antitone_in_overlap
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap₁ overlap₂ : Int)
    (hOverlap : overlap₁ ≤ overlap₂) :
    sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap₂ ≤
      sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap₁ := by
  unfold sharedVerifiedBudget
  linarith

/-- If total cross-surface take is bounded by shared verified budget, then any positive
    surface reward requires the shared budget itself to be positive once the other
    surfaces are nonnegative. -/
theorem positive_settlement_reward_requires_positive_shared_budget
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (hLiq : 0 ≤ rewardLiquidity)
    (hOracle : 0 ≤ rewardOracle)
    (hGov : 0 ≤ governanceTransfer)
    (hSettlePos : 0 < rewardSettlement)
    (hBound : totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer ≤
      sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap) :
    0 < sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
  unfold totalCrossSurfaceTake at hBound
  linarith

/-- Governance transfer is not special: a positive governance-side extraction also requires
    strictly positive shared verified budget once the other surfaces are nonnegative. -/
theorem positive_governance_transfer_requires_positive_shared_budget
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (hSettle : 0 ≤ rewardSettlement)
    (hLiq : 0 ≤ rewardLiquidity)
    (hOracle : 0 ≤ rewardOracle)
    (hGovPos : 0 < governanceTransfer)
    (hBound : totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer ≤
      sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap) :
    0 < sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
  unfold totalCrossSurfaceTake at hBound
  linarith

/-- If the shared verified budget is non-positive, then every nonnegative surface take must be zero. -/
theorem nonpositive_shared_budget_forces_zero_take
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (hSettle : 0 ≤ rewardSettlement)
    (hLiq : 0 ≤ rewardLiquidity)
    (hOracle : 0 ≤ rewardOracle)
    (hGov : 0 ≤ governanceTransfer)
    (hBound : totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer ≤
      sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap)
    (hBudgetNonpos : sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap ≤ 0) :
    rewardSettlement = 0 ∧ rewardLiquidity = 0 ∧ rewardOracle = 0 ∧ governanceTransfer = 0 := by
  have hTotalNonneg :
      0 ≤ rewardSettlement + rewardLiquidity + rewardOracle + governanceTransfer := by
    linarith
  have hBound' :
      rewardSettlement + rewardLiquidity + rewardOracle + governanceTransfer ≤
        settlementBenefit + liquidityBenefit + oracleBenefit + governanceBenefit - overlap := by
    simpa [totalCrossSurfaceTake, sharedVerifiedBudget] using hBound
  have hBudgetNonpos' :
      settlementBenefit + liquidityBenefit + oracleBenefit + governanceBenefit - overlap ≤ 0 := by
    simpa [sharedVerifiedBudget] using hBudgetNonpos
  have hTotalZero : rewardSettlement + rewardLiquidity + rewardOracle + governanceTransfer = 0 := by
    linarith
  have hSettleZero : rewardSettlement = 0 := by linarith
  have hLiqZero : rewardLiquidity = 0 := by linarith
  have hOracleZero : rewardOracle = 0 := by linarith
  have hGovZero : governanceTransfer = 0 := by linarith
  exact ⟨hSettleZero, hLiqZero, hOracleZero, hGovZero⟩

/-- If overlap is already reserved in the source accounting, total take is bounded by shared budget. -/
theorem total_take_le_shared_budget_if_overlap_reserved
    (settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap : Int)
    (rewardSettlement rewardLiquidity rewardOracle governanceTransfer : Int)
    (hReserve :
      totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer + overlap ≤
        settlementBenefit + liquidityBenefit + oracleBenefit + governanceBenefit) :
    totalCrossSurfaceTake rewardSettlement rewardLiquidity rewardOracle governanceTransfer ≤
      sharedVerifiedBudget settlementBenefit liquidityBenefit oracleBenefit governanceBenefit overlap := by
  have hReserve' :
      rewardSettlement + rewardLiquidity + rewardOracle + governanceTransfer + overlap ≤
        settlementBenefit + liquidityBenefit + oracleBenefit + governanceBenefit := by
    simpa [totalCrossSurfaceTake] using hReserve
  have :
      rewardSettlement + rewardLiquidity + rewardOracle + governanceTransfer ≤
        settlementBenefit + liquidityBenefit + oracleBenefit + governanceBenefit - overlap := by
    linarith
  simpa [totalCrossSurfaceTake, sharedVerifiedBudget] using this

/-- Concrete witness: positive settlement reward implies positive shared budget under the bound. -/
theorem witness_positive_settlement_reward :
    let budget := sharedVerifiedBudget 4 3 2 1 2
    let take := totalCrossSurfaceTake 1 0 0 0
    0 < budget ∧ take ≤ budget := by
  constructor <;> norm_num [sharedVerifiedBudget, totalCrossSurfaceTake]

/-- Concrete witness: zero shared budget blocks all nonnegative take. -/
theorem witness_zero_budget_case :
    sharedVerifiedBudget 3 2 1 0 6 = 0 := by
  norm_num [sharedVerifiedBudget]

end CrossSurfaceBenefitBudget
end Proofs
