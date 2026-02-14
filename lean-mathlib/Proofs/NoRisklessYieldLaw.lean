import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# No-Riskless-Yield Law

Manual Lean formalization of the IL-futures safety identity used in analysis:

`profit = -(protocol_fee + stranded_premium)`

With non-negative fee and stranded premium, attacker profit is always
non-positive, and strictly negative when either component is strictly positive.
-/

namespace Proofs
namespace NoRisklessYieldLaw

/-- Attacker profit model from conservation analysis. -/
def attackerProfit (protocolFee strandedPremium : Int) : Int :=
  -(protocolFee + strandedPremium)

/-- Profit is always non-positive when fee and stranded premium are non-negative. -/
theorem attacker_profit_nonpos
    (protocolFee strandedPremium : Int)
    (hFee : 0 ≤ protocolFee)
    (hStranded : 0 ≤ strandedPremium) :
    attackerProfit protocolFee strandedPremium ≤ 0 := by
  unfold attackerProfit
  linarith

/-- Profit is strictly negative if either fee or stranded premium is strictly positive. -/
theorem attacker_profit_strict_neg
    (protocolFee strandedPremium : Int)
    (hFee : 0 ≤ protocolFee)
    (hStranded : 0 ≤ strandedPremium)
    (hPos : 0 < protocolFee ∨ 0 < strandedPremium) :
    attackerProfit protocolFee strandedPremium < 0 := by
  unfold attackerProfit
  rcases hPos with hFeePos | hStrandedPos
  · linarith
  · linarith

/-- Profit is exactly zero iff both fee and stranded premium are zero. -/
theorem attacker_profit_zero_iff
    (protocolFee strandedPremium : Int)
    (hFee : 0 ≤ protocolFee)
    (hStranded : 0 ≤ strandedPremium) :
    attackerProfit protocolFee strandedPremium = 0 ↔
      protocolFee = 0 ∧ strandedPremium = 0 := by
  constructor
  · intro hZero
    unfold attackerProfit at hZero
    have hSumZero : protocolFee + strandedPremium = 0 := by linarith
    have hFeeZero : protocolFee = 0 := by linarith
    have hStrandedZero : strandedPremium = 0 := by linarith
    exact ⟨hFeeZero, hStrandedZero⟩
  · intro hBothZero
    rcases hBothZero with ⟨hFeeZero, hStrandedZero⟩
    subst hFeeZero
    subst hStrandedZero
    simp [attackerProfit]

/-- Non-vacuity witness with concrete positive fee and stranded premium. -/
theorem witness_attacker_loss :
    attackerProfit 17 3 = -20 ∧ attackerProfit 17 3 < 0 := by
  constructor
  · decide
  · norm_num [attackerProfit]

end NoRisklessYieldLaw
end Proofs
