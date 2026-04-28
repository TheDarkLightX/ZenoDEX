import Proofs.TokenomicsTraceSafety
import Mathlib.Tactic

/-!
# Tokenomics Mechanism Safety

This packet isolates a trace-level fail-closed law for post-AGI tokenomics
controllers.  Reward, rebate, bounty, and buyback mechanisms may choose complex
policies, but admitted traces must satisfy one budget law:

`reward spend ≤ verified value gained + explicit treasury/resource budget`.

The theorem is deliberately generic over a transition system, so a DEX fee
controller, proof-mining bounty auction, buyback/burn controller, or future FIRE
incentive mechanism can instantiate it with its own state and step relation.
-/

namespace Proofs
namespace TokenomicsMechanismSafety

open TokenomicsTraceSafety
open TokenomicsTraceSafety.MarketSystem

variable {σ : Type _}

/-- Cumulative reward/rebate/bounty spend is stepwise funded by newly verified
value plus treasury/resource drawdown. -/
def StepRewardFunded
    (M : MarketSystem σ) (R V T : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → R t - R s ≤ (V t - V s) + (T s - T t)

/-- Verified value is nondecreasing along each admitted transition. -/
def StepVerifiedValueNondecreasing
    (M : MarketSystem σ) (V : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → V s ≤ V t

/-- Cumulative reward spend is nondecreasing along each admitted transition. -/
def StepRewardNondecreasing
    (M : MarketSystem σ) (R : σ → Rat) : Prop :=
  ∀ {s t : σ}, M.Step s t → R s ≤ R t

/-- Aggregate reward spend over a trace. -/
def traceRewardSpend {M : MarketSystem σ} (R : σ → Rat)
    {n : Nat} {s t : σ} (_hTrace : TraceN M n s t) : Rat :=
  R t - R s

/-- Aggregate verified value gained over a trace. -/
def traceVerifiedGain {M : MarketSystem σ} (V : σ → Rat)
    {n : Nat} {s t : σ} (_hTrace : TraceN M n s t) : Rat :=
  V t - V s

theorem reward_le_of_traceN_stepRewardNondecreasing
    (M : MarketSystem σ) (R : σ → Rat)
    (hReward : StepRewardNondecreasing M R)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    R s ≤ R t := by
  induction hTrace with
  | nil =>
      exact le_rfl
  | snoc hTrace hStep ih =>
      exact ih.trans (hReward hStep)

theorem verifiedValue_le_of_traceN_stepVerifiedValueNondecreasing
    (M : MarketSystem σ) (V : σ → Rat)
    (hValue : StepVerifiedValueNondecreasing M V)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    V s ≤ V t := by
  induction hTrace with
  | nil =>
      exact le_rfl
  | snoc hTrace hStep ih =>
      exact ih.trans (hValue hStep)

/-- Stepwise reward funding lifts to any finite admitted trace. -/
theorem traceRewardSpend_le_verifiedGain_plus_treasuryDrop
    (M : MarketSystem σ) (R V T : σ → Rat)
    (hFunded : StepRewardFunded M R V T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    traceRewardSpend R hTrace ≤ traceVerifiedGain V hTrace + (T s - T t) := by
  induction hTrace with
  | nil =>
      simp [traceRewardSpend, traceVerifiedGain]
  | snoc hTrace hStep ih =>
      have hStepFunded := hFunded hStep
      unfold traceRewardSpend traceVerifiedGain at ih ⊢
      linarith

/-- If treasury is nonnegative at the terminal state, total reward spend is
bounded by verified value gained plus initial treasury. -/
theorem traceRewardSpend_le_verifiedGain_plus_initialTreasury
    (M : MarketSystem σ) (R V T : σ → Rat)
    (hFunded : StepRewardFunded M R V T)
    (hTreasury : TreasuryNonnegative T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    traceRewardSpend R hTrace ≤ traceVerifiedGain V hTrace + T s := by
  have h :=
    traceRewardSpend_le_verifiedGain_plus_treasuryDrop
      M R V T hFunded hTrace
  have hTerminal := hTreasury t
  unfold traceRewardSpend traceVerifiedGain at h ⊢
  linarith

/-- Reward spend cannot be negative when reward counters are stepwise
nondecreasing. -/
theorem traceRewardSpend_nonneg
    (M : MarketSystem σ) (R : σ → Rat)
    (hReward : StepRewardNondecreasing M R)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    0 ≤ traceRewardSpend R hTrace := by
  have h := reward_le_of_traceN_stepRewardNondecreasing M R hReward hTrace
  unfold traceRewardSpend
  exact sub_nonneg.mpr h

/-- Verified value gain cannot be negative when verified-value counters are
stepwise nondecreasing. -/
theorem traceVerifiedGain_nonneg
    (M : MarketSystem σ) (V : σ → Rat)
    (hValue : StepVerifiedValueNondecreasing M V)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    0 ≤ traceVerifiedGain V hTrace := by
  have h := verifiedValue_le_of_traceN_stepVerifiedValueNondecreasing M V hValue hTrace
  unfold traceVerifiedGain
  exact sub_nonneg.mpr h

/-- If a trace creates no verified value and consumes no treasury/resource
budget, then a funded nondecreasing reward counter cannot increase. -/
theorem traceRewardSpend_eq_zero_of_no_value_gain_no_treasury_drop
    (M : MarketSystem σ) (R V T : σ → Rat)
    (hReward : StepRewardNondecreasing M R)
    (hFunded : StepRewardFunded M R V T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hValueClosed : V t = V s)
    (hTreasuryClosed : T t = T s) :
    traceRewardSpend R hTrace = 0 := by
  have hUpper :=
    traceRewardSpend_le_verifiedGain_plus_treasuryDrop
      M R V T hFunded hTrace
  have hLower := traceRewardSpend_nonneg M R hReward hTrace
  unfold traceRewardSpend at hUpper hLower ⊢
  unfold traceVerifiedGain at hUpper
  rw [hValueClosed, hTreasuryClosed] at hUpper
  linarith

/-- A positive payout over a no-value/no-budget loop proves the step-funding
rule was violated somewhere in the trace. -/
theorem positive_reward_closed_loop_implies_not_stepwise_funded
    (M : MarketSystem σ) (R V T : σ → Rat)
    (hReward : StepRewardNondecreasing M R)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hValueClosed : V t = V s)
    (hTreasuryClosed : T t = T s)
    (hPositiveReward : 0 < traceRewardSpend R hTrace) :
    ¬ StepRewardFunded M R V T := by
  intro hFunded
  have hZero :=
    traceRewardSpend_eq_zero_of_no_value_gain_no_treasury_drop
      M R V T hReward hFunded hTrace hValueClosed hTreasuryClosed
  linarith

/-- No unfunded-reward theorem: if a terminal trace pays more than verified
value gained plus initial treasury, then at least one admitted transition must
violate the step funding rule. -/
theorem excess_reward_implies_not_stepwise_funded
    (M : MarketSystem σ) (R V T : σ → Rat)
    (hTreasury : TreasuryNonnegative T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t)
    (hExcess : traceVerifiedGain V hTrace + T s < traceRewardSpend R hTrace) :
    ¬ StepRewardFunded M R V T := by
  intro hFunded
  have h :=
    traceRewardSpend_le_verifiedGain_plus_initialTreasury
      M R V T hFunded hTreasury hTrace
  linarith

/-- A compact controller guard combining the useful assumptions. -/
structure RewardControllerGuard
    (M : MarketSystem σ) (R V T : σ → Rat) : Prop where
  rewardNondecreasing : StepRewardNondecreasing M R
  valueNondecreasing : StepVerifiedValueNondecreasing M V
  rewardFunded : StepRewardFunded M R V T
  treasuryNonnegative : TreasuryNonnegative T

namespace RewardControllerGuard

/-- Full fail-closed trace theorem for reward/bounty/buyback controllers. -/
theorem trace_safety
    {M : MarketSystem σ} {R V T : σ → Rat}
    (G : RewardControllerGuard M R V T)
    {n : Nat} {s t : σ} (hTrace : TraceN M n s t) :
    0 ≤ traceRewardSpend R hTrace ∧
      0 ≤ traceVerifiedGain V hTrace ∧
      traceRewardSpend R hTrace ≤ traceVerifiedGain V hTrace + T s := by
  exact
    ⟨traceRewardSpend_nonneg M R G.rewardNondecreasing hTrace,
      traceVerifiedGain_nonneg M V G.valueNondecreasing hTrace,
      traceRewardSpend_le_verifiedGain_plus_initialTreasury
        M R V T G.rewardFunded G.treasuryNonnegative hTrace⟩

end RewardControllerGuard

end TokenomicsMechanismSafety
end Proofs
