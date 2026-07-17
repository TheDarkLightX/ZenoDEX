import Mathlib
import Proofs.ZUSDGlobalLiabilityCover

namespace ZenoDEX.ZUSDGlobalDebtCover

open ZenoDEX.ZUSDGlobalLiabilityCover

/-- The complete scoped debt/custody relation checked at composition boundaries. -/
structure CoverState where
  freeLiabilities : Breakdown
  stabilityPoolEscrow : Nat
  coreFreeDebt : Nat
  coreStabilityPoolDebt : Nat
  coreTotalDebt : Nat


def exactCover (s : CoverState) : Prop :=
  total s.freeLiabilities = s.coreFreeDebt
    ∧ s.stabilityPoolEscrow = s.coreStabilityPoolDebt
    ∧ s.coreFreeDebt + s.coreStabilityPoolDebt = s.coreTotalDebt

/-- Component equality implies equality of all externally owned zUSD and total debt. -/
theorem exactCover_implies_global_liability_equality
    (s : CoverState)
    (h : exactCover s) :
    total s.freeLiabilities + s.stabilityPoolEscrow = s.coreTotalDebt := by
  rcases h with ⟨hFree, hSp, hSplit⟩
  omega

/-- External total equality alone is insufficient; component ownership stays explicit. -/
theorem exactCover_of_component_equalities
    (s : CoverState)
    (hFree : total s.freeLiabilities = s.coreFreeDebt)
    (hSp : s.stabilityPoolEscrow = s.coreStabilityPoolDebt)
    (hSplit : s.coreFreeDebt + s.coreStabilityPoolDebt = s.coreTotalDebt) :
    exactCover s := by
  exact ⟨hFree, hSp, hSplit⟩

/-- Wallet-to-pool movement preserves global cover when the other components stay fixed. -/
theorem walletToDexPool_preserves_exactCover
    (s : CoverState)
    (amount : Nat)
    (hAmount : amount ≤ s.freeLiabilities.wallet)
    (hCover : exactCover s) :
    exactCover
      { s with
        freeLiabilities := walletToDexPool s.freeLiabilities amount } := by
  rcases hCover with ⟨hFree, hSp, hSplit⟩
  refine ⟨?_, hSp, hSplit⟩
  rw [walletToDexPool_preserves_total s.freeLiabilities amount hAmount]
  exact hFree

/-- Gas-Pool-to-keeper payment preserves global cover without mint or burn. -/
theorem gasPoolToKeeper_preserves_exactCover
    (s : CoverState)
    (amount : Nat)
    (hAmount : amount ≤ s.freeLiabilities.gasPoolReserve)
    (hCover : exactCover s) :
    exactCover
      { s with
        freeLiabilities := gasPoolToKeeperWallet s.freeLiabilities amount } := by
  rcases hCover with ⟨hFree, hSp, hSplit⟩
  refine ⟨?_, hSp, hSplit⟩
  rw [gasPoolToKeeperWallet_preserves_total s.freeLiabilities amount hAmount]
  exact hFree

end ZenoDEX.ZUSDGlobalDebtCover
