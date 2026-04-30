import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Oracle Benefit Accounting

A small checked anchor for the post-AGI mechanism-design discussion.

The intended reading is:
- reward only verified risk reduction
- subtract same-event self-position gain and frequency-farming value
- reserve explicit safety margin
- if no net benefit remains, no positive oracle reward is admissible

This file does not solve the full post-AGI game.
It proves the first local arithmetic obligations that any tighter oracle reward law
would need to satisfy.
-/

namespace Proofs
namespace OracleBenefitAccounting

/-- Oracle-side recapturable or reserved value that must be subtracted before any
oracle reward is admissible. -/
def oracleRecapturableTerms
    (sameUpdatePnL spamValue overlap safetyMargin : Int) : Int :=
  sameUpdatePnL + spamValue + overlap + safetyMargin

/-- Oracle-side net benefit after subtracting recapturable value and safety reserves. -/
def oracleNetBenefit
    (riskReduction sameUpdatePnL spamValue overlap safetyMargin : Int) : Int :=
  riskReduction - oracleRecapturableTerms sameUpdatePnL spamValue overlap safetyMargin

/-- Aggregate verified benefit available to allocate across reward surfaces. -/
def totalVerifiedBenefit
    (settlement liquidity oracle proof repair overlap : Int) : Int :=
  settlement + liquidity + oracle + proof + repair - overlap

/-- Total rewards actually allocated across the same surfaces. -/
def totalReward
    (settlement liquidity oracle proof repair : Int) : Int :=
  settlement + liquidity + oracle + proof + repair

/-- Net oracle benefit is exactly risk reduction minus recapturable terms. -/
theorem oracleNetBenefit_eq_risk_minus_recapturable
    (riskReduction sameUpdatePnL spamValue overlap safetyMargin : Int) :
    oracleNetBenefit
        riskReduction
        sameUpdatePnL
        spamValue
        overlap
        safetyMargin =
      riskReduction -
        oracleRecapturableTerms sameUpdatePnL spamValue overlap safetyMargin := by
  rfl

/-- Verified total benefit is the gross reward surface minus reserved overlap. -/
theorem totalVerifiedBenefit_eq_totalReward_minus_overlap
    (settlement liquidity oracle proof repair overlap : Int) :
    totalVerifiedBenefit settlement liquidity oracle proof repair overlap =
      totalReward settlement liquidity oracle proof repair - overlap := by
  unfold totalVerifiedBenefit totalReward
  ring

/-- Positive oracle reward requires strict surplus after subtracting recapturable terms. -/
theorem positive_oracle_reward_requires_surplus
    (riskReduction sameUpdatePnL spamValue overlap safetyMargin reward : Int)
    (hPos : 0 < reward)
    (hUpper :
      reward ≤
        oracleNetBenefit
          riskReduction
          sameUpdatePnL
          spamValue
          overlap
          safetyMargin) :
    oracleRecapturableTerms sameUpdatePnL spamValue overlap safetyMargin < riskReduction := by
  rw [oracleNetBenefit_eq_risk_minus_recapturable] at hUpper
  linarith

/-- If recapturable terms dominate verified risk reduction, a non-negative oracle reward must be zero. -/
theorem oracle_reward_zero_if_recapturable_dominates
    (riskReduction sameUpdatePnL spamValue overlap safetyMargin reward : Int)
    (hDom :
      riskReduction ≤
        oracleRecapturableTerms sameUpdatePnL spamValue overlap safetyMargin)
    (hLower : 0 ≤ reward)
    (hUpper :
      reward ≤
        oracleNetBenefit
          riskReduction
          sameUpdatePnL
          spamValue
          overlap
          safetyMargin) :
    reward = 0 := by
  rw [oracleNetBenefit_eq_risk_minus_recapturable] at hUpper
  linarith

/-- Enlarging the safety margin can only reduce net oracle benefit. -/
theorem oracle_net_benefit_antitone_in_safety_margin
    (riskReduction sameUpdatePnL spamValue overlap safetyMargin₁ safetyMargin₂ : Int)
    (hMargin : safetyMargin₁ ≤ safetyMargin₂) :
    oracleNetBenefit riskReduction sameUpdatePnL spamValue overlap safetyMargin₂ ≤
      oracleNetBenefit riskReduction sameUpdatePnL spamValue overlap safetyMargin₁ := by
  unfold oracleNetBenefit oracleRecapturableTerms
  linarith

/-- If total verified benefit is non-positive, any non-negative total reward bounded by it must be zero. -/
theorem total_reward_zero_if_verified_nonpositive
    (settlement liquidity oracle proof repair overlap
      rewardSettlement rewardLiquidity rewardOracle rewardProof rewardRepair : Int)
    (hLower :
      0 ≤
        totalReward
          rewardSettlement
          rewardLiquidity
          rewardOracle
          rewardProof
          rewardRepair)
    (hUpper :
      totalReward
          rewardSettlement
          rewardLiquidity
          rewardOracle
          rewardProof
          rewardRepair ≤
        totalVerifiedBenefit settlement liquidity oracle proof repair overlap)
    (hVerifiedNonpos : totalVerifiedBenefit settlement liquidity oracle proof repair overlap ≤ 0) :
    totalReward rewardSettlement rewardLiquidity rewardOracle rewardProof rewardRepair = 0 := by
  rw [totalVerifiedBenefit_eq_totalReward_minus_overlap] at hUpper hVerifiedNonpos
  linarith

/-- If overlap has already been reserved before payout, total rewards are bounded by verified benefit. -/
theorem total_reward_le_verified_total_if_overlap_reserved
    (settlement liquidity oracle proof repair overlap
      rewardSettlement rewardLiquidity rewardOracle rewardProof rewardRepair : Int)
    (hReserve :
      totalReward
          rewardSettlement
          rewardLiquidity
          rewardOracle
          rewardProof
          rewardRepair +
        overlap ≤
        settlement + liquidity + oracle + proof + repair) :
    totalReward rewardSettlement rewardLiquidity rewardOracle rewardProof rewardRepair ≤
      totalVerifiedBenefit settlement liquidity oracle proof repair overlap := by
  rw [totalVerifiedBenefit_eq_totalReward_minus_overlap]
  have hGross :
      totalReward
          rewardSettlement
          rewardLiquidity
          rewardOracle
          rewardProof
          rewardRepair +
        overlap ≤
        totalReward settlement liquidity oracle proof repair := by
    simpa [totalReward] using hReserve
  linarith

/-- Concrete witness: positive reward is allowed only because surplus is genuine. -/
theorem witness_positive_oracle_reward_case :
    let net := oracleNetBenefit 100 15 5 10 20
    0 < net ∧
    oracleRecapturableTerms 15 5 10 20 < 100 := by
  constructor <;> norm_num [oracleNetBenefit, oracleRecapturableTerms]

/-- Concrete witness: when same-event gain plus spam dominates the claimed benefit,
    non-negative reward collapses to zero. -/
theorem witness_blocked_oracle_reward_case :
    let reward := (0 : Int)
    reward = oracleNetBenefit 40 15 10 5 10 := by
  norm_num [oracleNetBenefit, oracleRecapturableTerms]

/-- Concrete witness for aggregate reward blocking under non-positive verified benefit. -/
theorem witness_total_reward_blocked_case :
    totalVerifiedBenefit 3 2 1 0 0 6 = 0 := by
  norm_num [totalVerifiedBenefit]

end OracleBenefitAccounting
end Proofs
