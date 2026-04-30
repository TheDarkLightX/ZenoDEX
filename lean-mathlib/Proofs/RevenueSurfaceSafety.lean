import Mathlib

/-!
# Revenue Surface Safety

Small algebraic facts used by the FIRE revenue-surface model.

The file deliberately proves only the invariant skeleton:

* a fee-capped surface leaves the user nonnegative relative to measured value;
* fee-capped rebates cannot make wash trading profitable when execution drag is
  nonnegative;
* total-supply deflation requires burn to exceed emissions.

It does not prove that the measured value, fee, or execution-drag inputs are
truthful. Those are receipt/runtime obligations.
-/

namespace Proofs
namespace RevenueSurfaceSafety

/-- If a fee is at most the measured user value, the user's net value is
nonnegative. -/
theorem user_net_nonnegative_of_fee_le_value
    {value fee : ℝ} (hfee : fee ≤ value) :
    0 ≤ value - fee := by
  linarith

/-- If rewards are capped by paid fees, and wash execution has nonnegative
extra drag, the wash loop cannot have positive profit. -/
theorem wash_profit_nonpositive_of_reward_le_fee
    {reward fee executionDrag : ℝ}
    (hreward : reward ≤ fee) (hdrag : 0 ≤ executionDrag) :
    reward - (fee + executionDrag) ≤ 0 := by
  linarith

/-- If the combined rebate and usage reward is capped by the fee, the same
nonprofitability law applies. -/
theorem wash_profit_nonpositive_of_combined_rewards_le_fee
    {rebate usageReward fee executionDrag : ℝ}
    (hreward : rebate + usageReward ≤ fee) (hdrag : 0 ≤ executionDrag) :
    rebate + usageReward - (fee + executionDrag) ≤ 0 := by
  linarith

/-- Locking tokens does not reduce total supply. Supply decreases only when
burn exceeds emissions. -/
theorem supply_decreases_of_burn_gt_emission
    {supply emissions burn : ℝ} (hburn : emissions < burn) :
    supply + emissions - burn < supply := by
  linarith

/-- If burn at least covers emissions, next supply is no larger than current
supply. -/
theorem supply_nonincreasing_of_burn_ge_emission
    {supply emissions burn : ℝ} (hburn : emissions ≤ burn) :
    supply + emissions - burn ≤ supply := by
  linarith

/-- A funded reward pool cannot authorize more lock rewards than the pool size
when the lock-reward spend is capped by that pool. -/
theorem lock_reward_spend_le_pool
    {lockRewardSpend lockRewardPool : ℝ}
    (hcap : lockRewardSpend ≤ lockRewardPool) :
    lockRewardSpend ≤ lockRewardPool := hcap

end RevenueSurfaceSafety
end Proofs
