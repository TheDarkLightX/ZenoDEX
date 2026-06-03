import Mathlib

/-!
# ZenoDEX Staking Share Safety

This packet proves the core arithmetic laws for the conservative staking
shapes in `docs/VERIFIED_STAKING_DESIGN.md`.

The model is deliberately small:

* commitment shares are floor-divided accounting units;
* principal has no nonlinear size multiplier;
* reward claims are pro-rata against a funded epoch reward pool;
* same-epoch deposits are pending and receive no current-epoch claim;
* fee routes, penalties, and direct payouts are capped by explicit budgets.

These theorems are arithmetic and mechanism-safety claims. They do not prove
legal compliance, wallet security, oracle truth, Tau Net production readiness,
or public launch readiness.
-/

namespace Proofs
namespace ZenoDEXStakingShareSafety

def BPS : Nat := 10000

def rawWeight (principal bonusBps scale : Nat) : Nat :=
  principal * bonusBps * scale

def shareDenom (shareRate : Nat) : Nat :=
  BPS * shareRate

def cShares (principal bonusBps scale shareRate : Nat) : Nat :=
  rawWeight principal bonusBps scale / shareDenom shareRate

def rewardClaim (epochReward activeShares totalActiveShares : Nat) : Nat :=
  epochReward * activeShares / totalActiveShares

def rewardClaimsSum
    (epochReward totalActiveShares : Nat) (weights : List Nat) : Nat :=
  (weights.map fun w => rewardClaim epochReward w totalActiveShares).sum

def cappedFeeRoute (fee vaultFeeShareBps : Nat) : Nat :=
  fee * vaultFeeShareBps / BPS

def earlyExitPenalty (principal penaltyBps : Nat) : Nat :=
  principal * penaltyBps / BPS

inductive Eligibility where
  | active
  | pending
  deriving DecidableEq, Repr

def eligibilityClaim
    (epochReward shares totalActiveShares : Nat) : Eligibility -> Nat
  | .active => rewardClaim epochReward shares totalActiveShares
  | .pending => 0

structure StakingPayoutCert where
  payment : Nat
  userCap : Nat
  vaultSpendable : Nat
  verifiedValue : Nat
  budgetedSubsidy : Nat
  hUserCap : payment <= userCap
  hVaultCap : payment <= vaultSpendable
  hSourceCap : payment <= verifiedValue + budgetedSubsidy

/-! ## Commitment-share arithmetic -/

theorem rawWeight_add_principal
    (p q bonusBps scale : Nat) :
    rawWeight (p + q) bonusBps scale =
      rawWeight p bonusBps scale + rawWeight q bonusBps scale := by
  unfold rawWeight
  ring

theorem rawWeight_bonus_monotone
    (principal bonusA bonusB scale : Nat)
    (hBonus : bonusA <= bonusB) :
    rawWeight principal bonusA scale <= rawWeight principal bonusB scale := by
  unfold rawWeight
  exact Nat.mul_le_mul_right scale (Nat.mul_le_mul_left principal hBonus)

theorem cShares_bonus_monotone
    (principal bonusA bonusB scale shareRate : Nat)
    (hBonus : bonusA <= bonusB) :
    cShares principal bonusA scale shareRate <=
      cShares principal bonusB scale shareRate := by
  unfold cShares
  exact Nat.div_le_div_right
    (rawWeight_bonus_monotone principal bonusA bonusB scale hBonus)

theorem cShares_bonus_cap
    (principal bonusBps bonusCapBps scale shareRate : Nat)
    (hCap : bonusBps <= bonusCapBps) :
    cShares principal bonusBps scale shareRate <=
      cShares principal bonusCapBps scale shareRate :=
  cShares_bonus_monotone principal bonusBps bonusCapBps scale shareRate hCap

theorem same_bonus_split_does_not_increase_shares
    (p q bonusBps scale shareRate : Nat) :
    cShares p bonusBps scale shareRate +
      cShares q bonusBps scale shareRate <=
      cShares (p + q) bonusBps scale shareRate := by
  unfold cShares
  rw [rawWeight_add_principal]
  exact Nat.add_div_le_add_div
    (rawWeight p bonusBps scale)
    (rawWeight q bonusBps scale)
    (shareDenom shareRate)

theorem share_rate_ratchet_nonincreasing
    (principal bonusBps scale oldRate newRate : Nat)
    (hOldRate : 0 < oldRate)
    (hRatchet : oldRate <= newRate) :
    cShares principal bonusBps scale newRate <=
      cShares principal bonusBps scale oldRate := by
  unfold cShares shareDenom
  apply Nat.div_le_div_left
  . exact Nat.mul_le_mul_left BPS hRatchet
  . unfold BPS
    exact Nat.mul_pos (by decide) hOldRate

/-! ## Pro-rata floor reward safety -/

theorem rewardClaim_le_epochReward
    (epochReward activeShares totalActiveShares : Nat)
    (hActive : activeShares <= totalActiveShares) :
    rewardClaim epochReward activeShares totalActiveShares <= epochReward := by
  unfold rewardClaim
  apply Nat.div_le_of_le_mul
  calc
    epochReward * activeShares <= epochReward * totalActiveShares := by
      exact Nat.mul_le_mul_left epochReward hActive
    _ = totalActiveShares * epochReward := by ring

theorem two_claims_sum_le_epochReward
    (epochReward w1 w2 totalActiveShares : Nat)
    (hTotal : 0 < totalActiveShares)
    (hSum : w1 + w2 = totalActiveShares) :
    rewardClaim epochReward w1 totalActiveShares +
      rewardClaim epochReward w2 totalActiveShares <= epochReward := by
  unfold rewardClaim
  suffices
      totalActiveShares *
          (epochReward * w1 / totalActiveShares +
            epochReward * w2 / totalActiveShares) <=
        totalActiveShares * epochReward by
    exact Nat.le_of_mul_le_mul_left this hTotal
  have h1 := Nat.div_mul_le_self (epochReward * w1) totalActiveShares
  have h2 := Nat.div_mul_le_self (epochReward * w2) totalActiveShares
  calc
    totalActiveShares *
        (epochReward * w1 / totalActiveShares +
          epochReward * w2 / totalActiveShares)
        =
        totalActiveShares * (epochReward * w1 / totalActiveShares) +
          totalActiveShares * (epochReward * w2 / totalActiveShares) := by ring
    _ <= epochReward * w1 + epochReward * w2 := by
        have h1' :
            totalActiveShares * (epochReward * w1 / totalActiveShares) <=
              epochReward * w1 := by
          simpa [Nat.mul_comm] using h1
        have h2' :
            totalActiveShares * (epochReward * w2 / totalActiveShares) <=
              epochReward * w2 := by
          simpa [Nat.mul_comm] using h2
        omega
    _ = epochReward * (w1 + w2) := by ring
    _ = epochReward * totalActiveShares := by rw [hSum]
    _ = totalActiveShares * epochReward := by ring

theorem rewardClaimsSum_mul_total_le_reward_mul_sum
    (epochReward totalActiveShares : Nat) (weights : List Nat) :
    totalActiveShares *
        rewardClaimsSum epochReward totalActiveShares weights <=
      epochReward * weights.sum := by
  induction weights with
  | nil =>
      simp [rewardClaimsSum]
  | cons w ws ih =>
      unfold rewardClaimsSum at ih ⊢
      simp only [List.map_cons, List.sum_cons]
      unfold rewardClaim
      have hHead0 :=
        Nat.div_mul_le_self (epochReward * w) totalActiveShares
      have hHead :
          totalActiveShares *
              (epochReward * w / totalActiveShares) <=
            epochReward * w := by
        simpa [Nat.mul_comm] using hHead0
      calc
        totalActiveShares *
            (epochReward * w / totalActiveShares +
              (ws.map fun w =>
                epochReward * w / totalActiveShares).sum)
            =
            totalActiveShares *
                (epochReward * w / totalActiveShares) +
              totalActiveShares *
                (ws.map fun w =>
                  epochReward * w / totalActiveShares).sum := by ring
        _ <= epochReward * w + epochReward * ws.sum := by
            exact Nat.add_le_add hHead ih
        _ = epochReward * (w + ws.sum) := by ring

theorem rewardClaimsSum_le_epochReward
    (epochReward totalActiveShares : Nat) (weights : List Nat)
    (hTotal : 0 < totalActiveShares)
    (hSum : weights.sum = totalActiveShares) :
    rewardClaimsSum epochReward totalActiveShares weights <= epochReward := by
  have h :=
    rewardClaimsSum_mul_total_le_reward_mul_sum
      epochReward totalActiveShares weights
  rw [hSum] at h
  have h' :
      totalActiveShares *
          rewardClaimsSum epochReward totalActiveShares weights <=
        totalActiveShares * epochReward := by
    simpa [Nat.mul_comm] using h
  exact Nat.le_of_mul_le_mul_left h' hTotal

theorem zero_active_shares_claim_zero
    (epochReward totalActiveShares : Nat) :
    rewardClaim epochReward 0 totalActiveShares = 0 := by
  simp [rewardClaim]

theorem pending_position_claim_zero
    (epochReward shares totalActiveShares : Nat) :
    eligibilityClaim epochReward shares totalActiveShares Eligibility.pending = 0 := by
  rfl

theorem same_epoch_pending_deposit_cannot_capture_reward
    (epochReward attackerPendingShares totalActiveShares : Nat) :
    eligibilityClaim epochReward attackerPendingShares totalActiveShares
        Eligibility.pending = 0 := by
  rfl

/-! ## Funded payout, fee-route, and penalty caps -/

theorem staking_payout_respects_caps
    (cert : StakingPayoutCert) :
    cert.payment <= cert.userCap /\
      cert.payment <= cert.vaultSpendable /\
      cert.payment <= cert.verifiedValue + cert.budgetedSubsidy :=
  ⟨cert.hUserCap, cert.hVaultCap, cert.hSourceCap⟩

theorem zero_vault_spendable_forces_zero_payment
    (cert : StakingPayoutCert)
    (hZero : cert.vaultSpendable = 0) :
    cert.payment = 0 := by
  apply Nat.eq_zero_of_le_zero
  have hVault := cert.hVaultCap
  rw [hZero] at hVault
  exact hVault

theorem no_positive_payment_from_empty_vault
    (cert : StakingPayoutCert)
    (hZero : cert.vaultSpendable = 0) :
    Not (0 < cert.payment) := by
  intro hPositive
  have hPaymentZero :=
    zero_vault_spendable_forces_zero_payment cert hZero
  omega

theorem capped_fee_route_le_fee
    (fee vaultFeeShareBps : Nat)
    (hCap : vaultFeeShareBps <= BPS) :
    cappedFeeRoute fee vaultFeeShareBps <= fee := by
  unfold cappedFeeRoute
  apply Nat.div_le_of_le_mul
  calc
    fee * vaultFeeShareBps <= fee * BPS := by
      exact Nat.mul_le_mul_left fee hCap
    _ = BPS * fee := by ring

theorem early_exit_penalty_le_principal
    (principal penaltyBps : Nat)
    (hCap : penaltyBps <= BPS) :
    earlyExitPenalty principal penaltyBps <= principal := by
  unfold earlyExitPenalty
  apply Nat.div_le_of_le_mul
  calc
    principal * penaltyBps <= principal * BPS := by
      exact Nat.mul_le_mul_left principal hCap
    _ = BPS * principal := by ring

/-! ## Deterministic active-participant reward claims -/

def claimSpendAfter (spent claim : Nat) : Nat :=
  spent + claim

def claimRemainingAfter (budget spent claim : Nat) : Nat :=
  budget - claimSpendAfter spent claim

def rewardSourceAfter (source claim : Nat) : Nat :=
  source - claim

def rewardReserveAfterEpoch (reserve refill epochBudget : Nat) : Nat :=
  reserve + refill - epochBudget

theorem deterministic_claim_amount_bound
    (programClaim claim : Nat)
    (hAmount : claim = programClaim) :
    claim = programClaim := hAmount

theorem accepted_claim_preserves_program_budget
    (budget spent claim : Nat)
    (hWithinBudget : claimSpendAfter spent claim <= budget) :
    claimSpendAfter spent claim <= budget /\
      claimRemainingAfter budget spent claim +
        claimSpendAfter spent claim = budget := by
  constructor
  . exact hWithinBudget
  . unfold claimRemainingAfter
    exact Nat.sub_add_cancel hWithinBudget

theorem accepted_claim_preserves_reward_source
    (source claim : Nat)
    (hFunded : claim <= source) :
    rewardSourceAfter source claim + claim = source := by
  unfold rewardSourceAfter
  exact Nat.sub_add_cancel hFunded

theorem active_emission_epoch_preserves_reward_floor
    (reserve refill floor epochBudget : Nat)
    (hBudget : epochBudget + floor <= reserve + refill) :
    floor <= rewardReserveAfterEpoch reserve refill epochBudget := by
  unfold rewardReserveAfterEpoch
  have hBudget' : floor + epochBudget <= reserve + refill := by
    simpa [Nat.add_comm] using hBudget
  exact Nat.le_sub_of_add_le hBudget'

theorem active_emission_epoch_budget_le_burn
    (burn rewardToBurnBps epochBudget : Nat)
    (hRatio : rewardToBurnBps <= BPS)
    (hBudget : epochBudget <= burn * rewardToBurnBps / BPS) :
    epochBudget <= burn := by
  have hCap : burn * rewardToBurnBps / BPS <= burn := by
    unfold BPS
    apply Nat.div_le_of_le_mul
    calc
      burn * rewardToBurnBps <= burn * BPS := by
        exact Nat.mul_le_mul_left burn hRatio
      _ = BPS * burn := by ring
  exact le_trans hBudget hCap

theorem active_participant_claim_admission_preserves_accounting
    (budget spent source programClaim claim : Nat)
    (hAmount : claim = programClaim)
    (hWithinBudget : claimSpendAfter spent claim <= budget)
    (hFunded : claim <= source) :
    claim = programClaim /\
      claimSpendAfter spent claim <= budget /\
      claimRemainingAfter budget spent claim +
        claimSpendAfter spent claim = budget /\
      rewardSourceAfter source claim + claim = source := by
  refine ⟨hAmount, ?_, ?_, ?_⟩
  . exact hWithinBudget
  . exact (accepted_claim_preserves_program_budget budget spent claim hWithinBudget).2
  . exact accepted_claim_preserves_reward_source source claim hFunded

/-! ## Non-vacuity witnesses -/

theorem witness_split_not_profitable :
    cShares 400 10000 1 10 + cShares 600 10000 1 10 <=
      cShares (400 + 600) 10000 1 10 := by
  norm_num [cShares, rawWeight, shareDenom, BPS]

theorem witness_ratchet_reduces_shares :
    cShares 1000 10000 1 20 <= cShares 1000 10000 1 10 := by
  norm_num [cShares, rawWeight, shareDenom, BPS]

theorem witness_two_claims_exact :
    rewardClaim 1000 25 100 + rewardClaim 1000 75 100 = 1000 := by
  norm_num [rewardClaim]

theorem witness_list_claims_exact :
    rewardClaimsSum 1000 100 [25, 25, 50] = 1000 := by
  norm_num [rewardClaimsSum, rewardClaim]

theorem witness_floor_dust_remains_in_pool :
    rewardClaim 10 1 3 + rewardClaim 10 2 3 = 9 := by
  norm_num [rewardClaim]

theorem witness_pending_claim_zero :
    eligibilityClaim 1000 999 1000 Eligibility.pending = 0 := by
  rfl

theorem witness_fee_route_cap :
    cappedFeeRoute 1000 3000 <= 1000 := by
  norm_num [cappedFeeRoute, BPS]

theorem witness_penalty_cap :
    earlyExitPenalty 1000 2500 <= 1000 := by
  norm_num [earlyExitPenalty, BPS]

theorem witness_active_participant_claim_preserves_accounting :
    claimSpendAfter 25 25 <= 30000 /\
      claimRemainingAfter 30000 25 25 + claimSpendAfter 25 25 = 30000 /\
      rewardSourceAfter 100000 25 + 25 = 100000 := by
  norm_num [claimSpendAfter, claimRemainingAfter, rewardSourceAfter]

theorem witness_active_emission_epoch_floor_preserved :
    10000 <= rewardReserveAfterEpoch 8000 17000 41 := by
  norm_num [rewardReserveAfterEpoch]

theorem witness_active_emission_epoch_budget_le_burn :
    25 <= 100 := by
  exact active_emission_epoch_budget_le_burn 100 2500 25 (by norm_num [BPS]) (by norm_num [BPS])

end ZenoDEXStakingShareSafety
end Proofs
