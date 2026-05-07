import Mathlib

/-!
# ZenoDEX Yield-like Funding Safety

This file refines the S-tier funding posture from a blanket passive-yield ban
into a typed whitelist. Earned, source-bounded, service-like or rebate-like
flows can be admitted. Hold-to-earn, guaranteed-return, profit-share, future
entrant, and discretionary managerial-yield flows are rejected by construction.

The theorems are mathematical gate laws. They do not prove legal compliance,
tax treatment, securities status, oracle truth, cryptographic security, or
production readiness.
-/

namespace Proofs
namespace ZenoDEXYieldLikeFundingSafety

/-! ## Source taxonomy -/

inductive YieldSourceKind where
  | protocolServiceReward
  | protocolFeeRebate
  | liquidityServiceFee
  | protocolStakingSecurityReward
  | verifiedWorkBounty
  | treasuryOperatingRevenue
  | liquidStakingPassThrough
  | deflationaryBurnSource
  | holdToEarn
  | guaranteedAPY
  | profitShareRight
  | futureEntrantInflow
  | discretionaryManagerialYield
  deriving DecidableEq, Repr

def YieldSourceKind.allowed : YieldSourceKind → Prop
  | .protocolServiceReward => True
  | .protocolFeeRebate => True
  | .liquidityServiceFee => True
  | .protocolStakingSecurityReward => True
  | .verifiedWorkBounty => True
  | .treasuryOperatingRevenue => True
  | .liquidStakingPassThrough => True
  | .deflationaryBurnSource => True
  | .holdToEarn => False
  | .guaranteedAPY => False
  | .profitShareRight => False
  | .futureEntrantInflow => False
  | .discretionaryManagerialYield => False

def YieldSourceKind.requiresWork : YieldSourceKind → Prop
  | .protocolServiceReward => True
  | .protocolStakingSecurityReward => True
  | .verifiedWorkBounty => True
  | _ => False

structure YieldSource where
  kind : YieldSourceKind
  sourceVerified : Bool
  earnedByService : Bool
  sourceBounded : Bool
  noGuaranteedReturn : Bool
  noProfitShare : Bool
  noFutureEntrant : Bool
  ministerialOnly : Bool
  disclosureMet : Bool
  deriving Repr

def YieldSource.admitted (s : YieldSource) : Prop :=
  s.kind.allowed ∧
    s.sourceVerified = true ∧
    (s.kind.requiresWork → s.earnedByService = true) ∧
    s.sourceBounded = true ∧
    s.noGuaranteedReturn = true ∧
    s.noProfitShare = true ∧
    s.noFutureEntrant = true ∧
    (s.kind = .liquidStakingPassThrough → s.ministerialOnly = true) ∧
    s.disclosureMet = true

theorem admitted_kind_allowed (s : YieldSource) (h : s.admitted) :
    s.kind.allowed :=
  h.1

theorem admitted_source_is_bounded (s : YieldSource) (h : s.admitted) :
    s.sourceBounded = true :=
  h.2.2.2.1

theorem admitted_source_has_no_passive_return_right (s : YieldSource)
    (h : s.admitted) :
    s.noGuaranteedReturn = true ∧ s.noProfitShare = true ∧
      s.noFutureEntrant = true := by
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem required_work_source_is_earned
    (s : YieldSource) (h : s.admitted) (hWork : s.kind.requiresWork) :
    s.earnedByService = true :=
  h.2.2.1 hWork

theorem liquid_staking_pass_through_requires_ministerial
    (s : YieldSource) (h : s.admitted)
    (hKind : s.kind = .liquidStakingPassThrough) :
    s.ministerialOnly = true :=
  h.2.2.2.2.2.2.2.1 hKind

theorem forbidden_kind_not_admitted
    (s : YieldSource) (hForbidden : ¬ s.kind.allowed) :
    ¬ s.admitted := by
  intro h
  exact hForbidden h.1

theorem hold_to_earn_not_admitted
    (s : YieldSource) (hKind : s.kind = .holdToEarn) :
    ¬ s.admitted := by
  apply forbidden_kind_not_admitted
  rw [hKind]
  simp [YieldSourceKind.allowed]

theorem guaranteed_apy_kind_not_admitted
    (s : YieldSource) (hKind : s.kind = .guaranteedAPY) :
    ¬ s.admitted := by
  apply forbidden_kind_not_admitted
  rw [hKind]
  simp [YieldSourceKind.allowed]

theorem profit_share_kind_not_admitted
    (s : YieldSource) (hKind : s.kind = .profitShareRight) :
    ¬ s.admitted := by
  apply forbidden_kind_not_admitted
  rw [hKind]
  simp [YieldSourceKind.allowed]

theorem future_entrant_kind_not_admitted
    (s : YieldSource) (hKind : s.kind = .futureEntrantInflow) :
    ¬ s.admitted := by
  apply forbidden_kind_not_admitted
  rw [hKind]
  simp [YieldSourceKind.allowed]

theorem discretionary_managerial_yield_kind_not_admitted
    (s : YieldSource) (hKind : s.kind = .discretionaryManagerialYield) :
    ¬ s.admitted := by
  apply forbidden_kind_not_admitted
  rw [hKind]
  simp [YieldSourceKind.allowed]

theorem guaranteed_return_flag_not_admitted
    (s : YieldSource) (hBad : s.noGuaranteedReturn = false) :
    ¬ s.admitted := by
  intro h
  rw [h.2.2.2.2.1] at hBad
  contradiction

theorem profit_share_flag_not_admitted
    (s : YieldSource) (hBad : s.noProfitShare = false) :
    ¬ s.admitted := by
  intro h
  rw [h.2.2.2.2.2.1] at hBad
  contradiction

theorem future_entrant_flag_not_admitted
    (s : YieldSource) (hBad : s.noFutureEntrant = false) :
    ¬ s.admitted := by
  intro h
  rw [h.2.2.2.2.2.2.1] at hBad
  contradiction

def admissibleWitness (kind : YieldSourceKind) : YieldSource where
  kind := kind
  sourceVerified := true
  earnedByService := true
  sourceBounded := true
  noGuaranteedReturn := true
  noProfitShare := true
  noFutureEntrant := true
  ministerialOnly := true
  disclosureMet := true

theorem allowed_shape_has_admissible_witness
    (kind : YieldSourceKind) (hAllowed : kind.allowed) :
    ∃ source : YieldSource, source.kind = kind ∧ source.admitted := by
  refine ⟨admissibleWitness kind, rfl, ?_⟩
  cases kind <;>
    simp [admissibleWitness, YieldSource.admitted,
      YieldSourceKind.allowed, YieldSourceKind.requiresWork] at hAllowed ⊢

/-! ## Reserve-first payout formula -/

structure WaterfallCert where
  realizedSurplus : Nat
  reserveTopup : Nat
  insuranceTopup : Nat
  allocableBudget : Nat
  residual : Nat
  reserveDeficit : Nat
  balance :
    reserveTopup + insuranceTopup + allocableBudget + residual = realizedSurplus
  reserveFirst :
    reserveTopup < reserveDeficit → allocableBudget = 0

structure PayoutCaps where
  payment : Nat
  verifiedValue : Nat
  sourceCap : Nat
  treasuryCap : Nat
  sybilCap : Nat
  scopeCap : Nat
  allocableCap : Nat
  hVerified : payment ≤ verifiedValue
  hSource : payment ≤ sourceCap
  hTreasury : payment ≤ treasuryCap
  hSybil : payment ≤ sybilCap
  hScope : payment ≤ scopeCap
  hAllocable : payment ≤ allocableCap

theorem positive_yield_like_payout_gate
    (source : YieldSource) (w : WaterfallCert) (cap : PayoutCaps)
    (hSource : source.admitted)
    (hLink : cap.allocableCap ≤ w.allocableBudget)
    (hPay : cap.payment > 0) :
    source.kind.allowed ∧
      source.sourceBounded = true ∧
      source.noGuaranteedReturn = true ∧
      source.noProfitShare = true ∧
      source.noFutureEntrant = true ∧
      w.reserveTopup ≥ w.reserveDeficit ∧
      cap.payment ≤ w.realizedSurplus := by
  have hReserve : w.reserveTopup ≥ w.reserveDeficit := by
    by_contra hNot
    have hLt : w.reserveTopup < w.reserveDeficit := Nat.lt_of_not_ge hNot
    have hAllocZero : w.allocableBudget = 0 := w.reserveFirst hLt
    have hPaymentZero : cap.payment = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact le_trans cap.hAllocable (le_trans hLink (by omega))
    omega
  have hAllocableLeSurplus : w.allocableBudget ≤ w.realizedSurplus := by
    have hBal := w.balance
    omega
  exact ⟨hSource.1, hSource.2.2.2.1, hSource.2.2.2.2.1,
    hSource.2.2.2.2.2.1, hSource.2.2.2.2.2.2.1,
    hReserve, le_trans cap.hAllocable (le_trans hLink hAllocableLeSurplus)⟩

theorem zero_allocable_budget_forces_zero_payment
    (cap : PayoutCaps) (hLink : cap.allocableCap ≤ 0) :
    cap.payment = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact le_trans cap.hAllocable hLink

/-! ## Yield-like formula certificates -/

structure FeeRebateCert where
  feesPaid : Nat
  rebate : Nat
  hRebate : rebate ≤ feesPaid

theorem fee_rebate_bounded_by_own_fees (r : FeeRebateCert) :
    r.rebate ≤ r.feesPaid :=
  r.hRebate

structure FeePoolDistribution where
  totalFees : Nat
  payouts : List Nat
  hDistributed : payouts.sum ≤ totalFees

theorem fee_pool_distribution_source_bounded (d : FeePoolDistribution) :
    d.payouts.sum ≤ d.totalFees :=
  d.hDistributed

structure ServiceRewardCert where
  baseReward : Nat
  feeShare : Nat
  penalties : Nat
  reward : Nat
  hReward : reward + penalties ≤ baseReward + feeShare

theorem service_reward_source_bounded (c : ServiceRewardCert) :
    c.reward ≤ c.baseReward + c.feeShare := by
  have h := c.hReward
  omega

structure PassThroughReceiptCert where
  underlyingAssets : Nat
  accruedProtocolRewards : Nat
  providerFees : Nat
  slashingLosses : Nat
  receiptClaim : Nat
  hPassThrough :
    receiptClaim + providerFees + slashingLosses ≤
      underlyingAssets + accruedProtocolRewards

theorem pass_through_receipt_source_bounded (c : PassThroughReceiptCert) :
    c.receiptClaim ≤ c.underlyingAssets + c.accruedProtocolRewards := by
  have h := c.hPassThrough
  omega

structure DeflationaryBurnCert where
  allocableBudget : Nat
  burnAmount : Nat
  hBurn : burnAmount ≤ allocableBudget

theorem burn_amount_source_bounded (c : DeflationaryBurnCert) :
    c.burnAmount ≤ c.allocableBudget :=
  c.hBurn

end ZenoDEXYieldLikeFundingSafety
end Proofs
