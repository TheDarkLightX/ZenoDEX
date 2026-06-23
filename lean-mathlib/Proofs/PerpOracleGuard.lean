/-!
Boolean shell for the isolated perps settlement-oracle guard.

This file models the fail-closed shape of `guard_settle_epoch`: settlement
admission implies that a usable oracle snapshot is present. It deliberately
does not model PnL, liquidation, or fixed-point price arithmetic; those remain
separate arithmetic proof surfaces.
-/

set_option autoImplicit false

namespace Proofs
namespace PerpOracleGuard

inductive EpochPhase where
  | open
  | pricePublished
  | settled
  deriving DecidableEq, Repr

structure PerpGuardState where
  epochPhase : EpochPhase
  clearingPriceSeen : Bool
  clearingPriceEpoch : Nat
  nowEpoch : Nat
  oracleLastUpdateEpoch : Nat
  maxOracleStalenessEpochs : Nat
  oracleSeen : Bool
  indexPriceE8 : Nat
  deriving Repr

def isOracleFresh (s : PerpGuardState) : Bool :=
  s.oracleSeen
    && decide (s.oracleLastUpdateEpoch <= s.nowEpoch)
    && decide (s.nowEpoch - s.oracleLastUpdateEpoch <= s.maxOracleStalenessEpochs)

def isSettleOracleUsable (s : PerpGuardState) : Bool :=
  decide (0 < s.indexPriceE8) && isOracleFresh s

def guardSettleEpoch (s : PerpGuardState) : Bool :=
  decide (s.epochPhase = EpochPhase.pricePublished)
    && s.clearingPriceSeen
    && decide (s.clearingPriceEpoch = s.nowEpoch)
    && decide (s.oracleLastUpdateEpoch < s.nowEpoch)
    && isSettleOracleUsable s

theorem guard_true_implies_oracle_usable
    (s : PerpGuardState)
    (h : guardSettleEpoch s = true) :
    isSettleOracleUsable s = true := by
  unfold guardSettleEpoch at h
  rw [Bool.and_eq_true] at h
  exact h.2

theorem guard_true_implies_oracle_seen
    (s : PerpGuardState)
    (h : guardSettleEpoch s = true) :
    s.oracleSeen = true := by
  have h1 := guard_true_implies_oracle_usable s h
  unfold isSettleOracleUsable isOracleFresh at h1
  rw [Bool.and_eq_true] at h1
  rw [Bool.and_eq_true] at h1
  rw [Bool.and_eq_true] at h1
  exact h1.2.1.1

theorem guard_true_implies_index_positive
    (s : PerpGuardState)
    (h : guardSettleEpoch s = true) :
    0 < s.indexPriceE8 := by
  have h1 := guard_true_implies_oracle_usable s h
  unfold isSettleOracleUsable at h1
  rw [Bool.and_eq_true] at h1
  exact of_decide_eq_true h1.1

theorem guard_true_implies_oracle_not_future
    (s : PerpGuardState)
    (h : guardSettleEpoch s = true) :
    s.oracleLastUpdateEpoch <= s.nowEpoch := by
  have h1 := guard_true_implies_oracle_usable s h
  unfold isSettleOracleUsable isOracleFresh at h1
  rw [Bool.and_eq_true] at h1
  rw [Bool.and_eq_true] at h1
  rw [Bool.and_eq_true] at h1
  exact of_decide_eq_true h1.2.1.2

theorem guard_true_implies_oracle_within_staleness
    (s : PerpGuardState)
    (h : guardSettleEpoch s = true) :
    s.nowEpoch - s.oracleLastUpdateEpoch <= s.maxOracleStalenessEpochs := by
  have h1 := guard_true_implies_oracle_usable s h
  unfold isSettleOracleUsable isOracleFresh at h1
  rw [Bool.and_eq_true] at h1
  rw [Bool.and_eq_true] at h1
  rw [Bool.and_eq_true] at h1
  exact of_decide_eq_true h1.2.2

end PerpOracleGuard
end Proofs
