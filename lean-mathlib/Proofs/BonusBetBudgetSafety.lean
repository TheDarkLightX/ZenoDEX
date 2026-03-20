import Mathlib.Tactic

/-!
# Bonus Bet Budget Safety

This file formalizes core arithmetic safety properties for winner-only bonus-bet
issuance under clipping/cap controls.

Model summary:
- Winner bonus is computed from usage and clipped by a per-winner cap.
- Aggregate paid bonus is clipped by available epoch budget.
- Realized value of bonus credits is further haircutted by `evBps`.

Theorems prove that payouts are bounded by budget and cannot exceed paid credits.
-/

namespace Proofs
namespace BonusBetBudgetSafety

def BPS : Nat := 10000

def expectedWinnersFloor (eligible winProbBps : Nat) : Nat :=
  (eligible * winProbBps) / BPS

def rawBonusPerWinner (usage bonusRateBps : Nat) : Nat :=
  (usage * bonusRateBps) / BPS

def cappedBonusPerWinner (usage bonusRateBps capPerWinner : Nat) : Nat :=
  min (rawBonusPerWinner usage bonusRateBps) capPerWinner

def budgetAvailable (budget honestDemand : Nat) : Nat :=
  budget - honestDemand

def paidBonus
    (eligible winProbBps usage bonusRateBps capPerWinner budget honestDemand : Nat) : Nat :=
  min
    (expectedWinnersFloor eligible winProbBps * cappedBonusPerWinner usage bonusRateBps capPerWinner)
    (budgetAvailable budget honestDemand)

def realizedBonus (paid evBps : Nat) : Nat :=
  (paid * evBps) / BPS

theorem paidBonus_le_budgetAvailable
    (eligible winProbBps usage bonusRateBps capPerWinner budget honestDemand : Nat) :
    paidBonus eligible winProbBps usage bonusRateBps capPerWinner budget honestDemand
      ≤ budgetAvailable budget honestDemand := by
  unfold paidBonus
  exact min_le_right _ _

theorem paidBonus_le_preclip
    (eligible winProbBps usage bonusRateBps capPerWinner budget honestDemand : Nat) :
    paidBonus eligible winProbBps usage bonusRateBps capPerWinner budget honestDemand
      ≤ expectedWinnersFloor eligible winProbBps * cappedBonusPerWinner usage bonusRateBps capPerWinner := by
  unfold paidBonus
  exact min_le_left _ _

theorem realizedBonus_le_paid
    (paid evBps : Nat) (hev : evBps ≤ BPS) :
    realizedBonus paid evBps ≤ paid := by
  unfold realizedBonus
  have hmul : paid * evBps ≤ paid * BPS := Nat.mul_le_mul_left paid hev
  have hdiv : (paid * evBps) / BPS ≤ (paid * BPS) / BPS := Nat.div_le_div_right hmul
  simpa [BPS] using hdiv

theorem realizedBonus_le_budgetAvailable
    (eligible winProbBps usage bonusRateBps capPerWinner budget honestDemand evBps : Nat)
    (hev : evBps ≤ BPS) :
    realizedBonus
        (paidBonus eligible winProbBps usage bonusRateBps capPerWinner budget honestDemand)
        evBps
      ≤ budgetAvailable budget honestDemand := by
  have h1 :
      realizedBonus
          (paidBonus eligible winProbBps usage bonusRateBps capPerWinner budget honestDemand)
          evBps
        ≤ paidBonus eligible winProbBps usage bonusRateBps capPerWinner budget honestDemand := by
    exact realizedBonus_le_paid _ _ hev
  have h2 :
      paidBonus eligible winProbBps usage bonusRateBps capPerWinner budget honestDemand
        ≤ budgetAvailable budget honestDemand := by
    exact paidBonus_le_budgetAvailable _ _ _ _ _ _ _
  exact le_trans h1 h2

theorem budgetAvailable_zero_when_honest_demand_exhausts
    {budget honestDemand : Nat} (h : budget ≤ honestDemand) :
    budgetAvailable budget honestDemand = 0 := by
  unfold budgetAvailable
  exact Nat.sub_eq_zero_of_le h

theorem paidBonus_zero_when_no_available_budget
    {eligible winProbBps usage bonusRateBps capPerWinner budget honestDemand : Nat}
    (h : budget ≤ honestDemand) :
    paidBonus eligible winProbBps usage bonusRateBps capPerWinner budget honestDemand = 0 := by
  unfold paidBonus
  have hAvail : budgetAvailable budget honestDemand = 0 := by
    exact budgetAvailable_zero_when_honest_demand_exhausts h
  simp [hAvail]

end BonusBetBudgetSafety
end Proofs
