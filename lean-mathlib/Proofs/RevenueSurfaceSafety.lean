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

/-! ## Evidence-meet fee caps

The fee-cap calibration experiments combine independent recommendation
artifacts by taking the minimum available cap. These lemmas capture the small
algebraic spine: a meet cap never exceeds any source cap, and if any source cap
was already safe relative to measured user value, then charging below the meet
is also safe.
-/

/-- The meet of two candidate caps cannot exceed the left cap. -/
theorem cap_meet_le_left {capA capB : ℝ} :
    min capA capB ≤ capA :=
  min_le_left _ _

/-- The meet of two candidate caps cannot exceed the right cap. -/
theorem cap_meet_le_right {capA capB : ℝ} :
    min capA capB ≤ capB :=
  min_le_right _ _

/-- Charging below the meet of two caps is safe whenever the left cap is safe
relative to measured value. -/
theorem user_net_nonnegative_of_fee_le_cap_meet_left
    {value fee capA capB : ℝ}
    (hfee : fee ≤ min capA capB) (hcapA : capA ≤ value) :
    0 ≤ value - fee := by
  have hmeet_le_capA : min capA capB ≤ capA := cap_meet_le_left
  have hfee_le_value : fee ≤ value := le_trans hfee (le_trans hmeet_le_capA hcapA)
  exact user_net_nonnegative_of_fee_le_value hfee_le_value

/-- Charging below the meet of two caps is safe whenever the right cap is safe
relative to measured value. -/
theorem user_net_nonnegative_of_fee_le_cap_meet_right
    {value fee capA capB : ℝ}
    (hfee : fee ≤ min capA capB) (hcapB : capB ≤ value) :
    0 ≤ value - fee := by
  have hmeet_le_capB : min capA capB ≤ capB := cap_meet_le_right
  have hfee_le_value : fee ≤ value := le_trans hfee (le_trans hmeet_le_capB hcapB)
  exact user_net_nonnegative_of_fee_le_value hfee_le_value

/-- Adding a third cap to the meet cannot loosen the composed cap relative to
the original left cap. -/
theorem cap_meet3_le_first {capA capB capC : ℝ} :
    min (min capA capB) capC ≤ capA := by
  exact le_trans (min_le_left _ _) (min_le_left _ _)

/-! ## Launch/config guard facts

The launch/config lint experiment compiles review caps into a fail-closed guard:
under-cap fees may claim the current evidence-backed user-net property, while
over-cap fees need an explicit assumption-change override and cannot inherit
that property automatically.
-/

/-- If the guard accepts either an under-cap fee or an override, then an over-cap
fee can only be accepted through the override branch. -/
theorem launch_overcap_requires_override
    {fee cap : ℝ} {overrideRecorded : Prop}
    (hok : fee ≤ cap ∨ overrideRecorded) (hover : cap < fee) :
    overrideRecorded := by
  rcases hok with hcap | hoverride
  · linarith
  · exact hoverride

/-- A launch/config fee that is below a cap already known safe relative to
measured value leaves user net nonnegative. -/
theorem launch_user_net_nonnegative_without_override
    {value fee cap : ℝ}
    (hfee : fee ≤ cap) (hcap : cap ≤ value) :
    0 ≤ value - fee := by
  exact user_net_nonnegative_of_fee_le_value (le_trans hfee hcap)

end RevenueSurfaceSafety
end Proofs
