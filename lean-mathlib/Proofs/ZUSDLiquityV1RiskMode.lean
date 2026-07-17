import Mathlib

/-!
# Liquity V1 Exact System Risk Mode

The risk-bearing system state contains only the Active Pool and Default Pool.
Stability Pool, Gas Pool, borrower surplus, wallets, and fee custody do not occur
in the type or the aggregate.
-/

namespace ZenoDEX.ZUSDLiquityV1RiskMode

inductive RiskMode where
  | normal
  | recovery
  deriving DecidableEq, Repr

structure SystemPools where
  activeCollateral : Nat
  activeDebt : Nat
  defaultCollateral : Nat
  defaultDebt : Nat


def decimalPrecision : Nat := 1_000_000_000_000_000_000

def bpsToE18 : Nat := 100_000_000_000_000

def ccrE18 : Nat := 15_000 * bpsToE18

def maxU256 : Nat := 2 ^ 256 - 1


def totalCollateral (p : SystemPools) : Nat :=
  p.activeCollateral + p.defaultCollateral


def totalDebt (p : SystemPools) : Nat :=
  p.activeDebt + p.defaultDebt


def tcrE18 (p : SystemPools) (priceE18 : Nat) : Nat :=
  if totalDebt p = 0 then maxU256
  else totalCollateral p * priceE18 / totalDebt p


def riskMode (p : SystemPools) (priceE18 : Nat) : RiskMode :=
  if totalDebt p = 0 then .normal
  else if tcrE18 p priceE18 < ccrE18 then .recovery else .normal


theorem riskMode_total (p : SystemPools) (priceE18 : Nat) :
    riskMode p priceE18 = .normal ∨ riskMode p priceE18 = .recovery := by
  unfold riskMode
  split <;> split <;> simp_all


theorem zero_debt_is_normal (p : SystemPools) (priceE18 : Nat)
    (hDebt : totalDebt p = 0) :
    riskMode p priceE18 = .normal := by
  simp [riskMode, hDebt]


theorem below_ccr_is_recovery
    (p : SystemPools)
    (priceE18 : Nat)
    (hDebt : totalDebt p ≠ 0)
    (hBelow : tcrE18 p priceE18 < ccrE18) :
    riskMode p priceE18 = .recovery := by
  simp [riskMode, hDebt, hBelow]


theorem at_or_above_ccr_is_normal
    (p : SystemPools)
    (priceE18 : Nat)
    (hDebt : totalDebt p ≠ 0)
    (hSafe : ccrE18 ≤ tcrE18 p priceE18) :
    riskMode p priceE18 = .normal := by
  simp [riskMode, hDebt, Nat.not_lt.mpr hSafe]


theorem active_and_default_aggregate_exact :
    let p : SystemPools := {
      activeCollateral := 100
      activeDebt := 100
      defaultCollateral := 50
      defaultDebt := 0
    }
    totalCollateral p = 150 ∧
      totalDebt p = 100 ∧
      tcrE18 p decimalPrecision = ccrE18 ∧
      riskMode p decimalPrecision = .normal := by
  norm_num [totalCollateral, totalDebt, tcrE18, riskMode,
    decimalPrecision, ccrE18, bpsToE18]


theorem exact_source_ratio_preserved :
    let p : SystemPools := {
      activeCollateral := 1_000_000_010_000_000_000
      activeDebt := 1_000_000_000_000_000_000
      defaultCollateral := 0
      defaultDebt := 0
    }
    tcrE18 p decimalPrecision = 1_000_000_010_000_000_000 := by
  norm_num [tcrE18, totalCollateral, totalDebt, decimalPrecision]


theorem boundary_partition_examples :
    let below : SystemPools := {
      activeCollateral := 14_999
      activeDebt := 10_000
      defaultCollateral := 0
      defaultDebt := 0
    }
    let exact : SystemPools := {
      activeCollateral := 15_000
      activeDebt := 10_000
      defaultCollateral := 0
      defaultDebt := 0
    }
    let above : SystemPools := {
      activeCollateral := 15_001
      activeDebt := 10_000
      defaultCollateral := 0
      defaultDebt := 0
    }
    riskMode below decimalPrecision = .recovery ∧
      riskMode exact decimalPrecision = .normal ∧
      riskMode above decimalPrecision = .normal := by
  norm_num [riskMode, tcrE18, totalCollateral, totalDebt,
    decimalPrecision, ccrE18, bpsToE18]

end ZenoDEX.ZUSDLiquityV1RiskMode
