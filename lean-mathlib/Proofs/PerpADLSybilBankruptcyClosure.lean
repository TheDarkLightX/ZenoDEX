import Mathlib

/-!
# Perp ADL Sybil Bankruptcy Closure

Internal proof note for Campaign 5's offsetting-account bankruptcy drain.

The witness shape is:

* two Sybil accounts each post `margin`;
* one side loses `shockPnl`;
* the opposing side gains `shockPnl`;
* when `margin < shockPnl`, paying the winner in full and charging the deficit
  to insurance gives the attacker profit equal to the bankrupt leg's deficit.

The CBC rule is ADL before treasury: the bankrupt-leg deficit is first haircutted
from opposing winner PnL. In the two-leg offsetting witness, that removes the
risk-free treasury siphon exactly.
-/

namespace Internal
namespace PerpADLSybilBankruptcyClosure

/-- Deficit left by the bankrupt losing account. -/
def BankruptcyDeficit (margin shockPnl : Nat) : Nat :=
  shockPnl - margin

/-- Standard payout shape: losing leg is zeroed, winning leg is paid in full. -/
def StandardSybilFinalCapital (margin shockPnl : Nat) : Nat :=
  margin + shockPnl

/-- Standard insurance draw equals the bankrupt-account deficit. -/
def StandardInsuranceDraw (margin shockPnl : Nat) : Nat :=
  BankruptcyDeficit margin shockPnl

/-- ADL payout shape: the winning leg is haircutted by the losing leg's deficit
before any treasury or insurance draw is admitted. -/
def ADLSybilFinalCapital (margin shockPnl : Nat) : Nat :=
  margin + shockPnl - BankruptcyDeficit margin shockPnl

/-- The ADL haircut is always covered by the winning leg's positive PnL. -/
theorem adl_deficit_haircut_is_covered
    (margin shockPnl : Nat) :
    BankruptcyDeficit margin shockPnl ≤ shockPnl := by
  unfold BankruptcyDeficit
  omega

/-- Without ADL, the offsetting-account attacker's profit equals the insurance
deficit whenever the losing account jumps past bankruptcy. -/
theorem standard_sybil_profit_equals_insurance_draw
    {margin shockPnl : Nat}
    (hBankrupt : margin < shockPnl) :
    StandardSybilFinalCapital margin shockPnl - 2 * margin =
      StandardInsuranceDraw margin shockPnl := by
  unfold StandardSybilFinalCapital StandardInsuranceDraw BankruptcyDeficit
  omega

/-- With ADL, the same offsetting witness returns exactly the attacker's initial
two-leg margin when the shock reaches or passes bankruptcy. -/
theorem adl_blocks_sybil_bankruptcy_profit
    {margin shockPnl : Nat}
    (hBankruptOrAtBoundary : margin ≤ shockPnl) :
    ADLSybilFinalCapital margin shockPnl = 2 * margin := by
  unfold ADLSybilFinalCapital BankruptcyDeficit
  omega

/-- ADL admits zero insurance draw for the two-leg offsetting witness because the
winner PnL covers the loser deficit before treasury participation. -/
theorem adl_treasury_draw_zero_for_offsetting_sybil
    {margin shockPnl : Nat}
    (hBankruptOrAtBoundary : margin ≤ shockPnl) :
    StandardInsuranceDraw margin shockPnl ≤ shockPnl ∧
      ADLSybilFinalCapital margin shockPnl - 2 * margin = 0 := by
  constructor
  · exact adl_deficit_haircut_is_covered margin shockPnl
  · rw [adl_blocks_sybil_bankruptcy_profit hBankruptOrAtBoundary]
    omega

/-- Campaign 5 witness: margin 1000, PnL shock 2000. Standard insurance pays
1000; ADL removes the attacker's profit. -/
theorem campaign5_sybil_bankruptcy_witness :
    StandardInsuranceDraw 1000 2000 = 1000 ∧
      StandardSybilFinalCapital 1000 2000 - 2 * 1000 = 1000 ∧
      ADLSybilFinalCapital 1000 2000 = 2 * 1000 := by
  norm_num [StandardInsuranceDraw, StandardSybilFinalCapital,
    ADLSybilFinalCapital, BankruptcyDeficit]

end PerpADLSybilBankruptcyClosure
end Internal
