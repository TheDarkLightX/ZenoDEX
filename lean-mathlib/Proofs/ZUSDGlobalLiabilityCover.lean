import Mathlib

namespace ZenoDEX.ZUSDGlobalLiabilityCover

/-- The abstract free-zUSD custody domains enumerated by the runtime checker. -/
structure Breakdown where
  wallet : Nat
  dexPool : Nat
  perps : Nat
  protocolFeeReserve : Nat
  stakingFeePool : Nat
  hostFeePool : Nat
  gasPoolReserve : Nat


def total (b : Breakdown) : Nat :=
  b.wallet
    + b.dexPool
    + b.perps
    + b.protocolFeeReserve
    + b.stakingFeePool
    + b.hostFeePool
    + b.gasPoolReserve


def walletToDexPool (b : Breakdown) (amount : Nat) : Breakdown :=
  { b with
    wallet := b.wallet - amount
    dexPool := b.dexPool + amount }

/-- Moving existing zUSD from a wallet into a DEX pool preserves free cover. -/
theorem walletToDexPool_preserves_total
    (b : Breakdown)
    (amount : Nat)
    (hAmount : amount ≤ b.wallet) :
    total (walletToDexPool b amount) = total b := by
  simp [total, walletToDexPool]
  omega


def gasPoolToKeeperWallet (b : Breakdown) (amount : Nat) : Breakdown :=
  { b with
    wallet := b.wallet + amount
    gasPoolReserve := b.gasPoolReserve - amount }

/-- Paying a fixed liquidation reserve moves existing zUSD without mint or burn. -/
theorem gasPoolToKeeperWallet_preserves_total
    (b : Breakdown)
    (amount : Nat)
    (hAmount : amount ≤ b.gasPoolReserve) :
    total (gasPoolToKeeperWallet b amount) = total b := by
  simp [total, gasPoolToKeeperWallet]
  omega

/-- Exact equality decides the abstract free-debt cover relation. -/
theorem cover_iff_total_eq (b : Breakdown) (freeDebt : Nat) :
    (total b = freeDebt) ↔ (freeDebt = total b) := by
  constructor <;> intro h <;> omega

end ZenoDEX.ZUSDGlobalLiabilityCover
