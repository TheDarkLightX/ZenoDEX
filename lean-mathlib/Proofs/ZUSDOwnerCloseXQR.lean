import Mathlib

/-!
# zUSD Owner-Close E18/E8 Quotient And Residue

This file proves the pure F25 arithmetic candidate only. It does not authorize a
physical transfer, F15 composition, or F16 commit.
-/

namespace ZenoDEX.ZUSDOwnerCloseXQR


def conversionFactor : Nat := 10_000_000_000


def quotientE8 (closedCollateralE18 : Nat) : Nat :=
  closedCollateralE18 / conversionFactor


def residueE18 (closedCollateralE18 : Nat) : Nat :=
  closedCollateralE18 % conversionFactor


def activePoolShadowAfter (before closedCollateralE18 : Nat) : Nat :=
  before - closedCollateralE18


def custodyAfter (before closedCollateralE18 : Nat) : Nat :=
  before - quotientE8 closedCollateralE18


def ownerExternalAfter (before closedCollateralE18 : Nat) : Nat :=
  before + quotientE8 closedCollateralE18


def ownerClaimAfter (before closedCollateralE18 : Nat) : Nat :=
  before + residueE18 closedCollateralE18


theorem conversionFactor_positive : 0 < conversionFactor := by
  norm_num [conversionFactor]


theorem xqr_decomposition (closedCollateralE18 : Nat) :
    conversionFactor * quotientE8 closedCollateralE18
      + residueE18 closedCollateralE18 = closedCollateralE18 := by
  rw [Nat.mul_comm]
  exact Nat.div_add_mod closedCollateralE18 conversionFactor


theorem residue_lt_factor (closedCollateralE18 : Nat) :
    residueE18 closedCollateralE18 < conversionFactor := by
  exact Nat.mod_lt closedCollateralE18 conversionFactor_positive


theorem sub_e8_has_zero_quotient
    (closedCollateralE18 : Nat)
    (hSmall : closedCollateralE18 < conversionFactor) :
    quotientE8 closedCollateralE18 = 0 := by
  exact Nat.div_eq_of_lt hSmall


theorem sub_e8_is_all_residue
    (closedCollateralE18 : Nat)
    (hSmall : closedCollateralE18 < conversionFactor) :
    residueE18 closedCollateralE18 = closedCollateralE18 := by
  exact Nat.mod_eq_of_lt hSmall


theorem exact_multiple_has_zero_residue (physicalQuotientE8 : Nat) :
    residueE18 (conversionFactor * physicalQuotientE8) = 0 := by
  simp [residueE18]


theorem exact_multiple_recovers_quotient (physicalQuotientE8 : Nat) :
    quotientE8 (conversionFactor * physicalQuotientE8) = physicalQuotientE8 := by
  simp [quotientE8, conversionFactor]


theorem credits_recompose_exactly
    (ownerExternalBeforeE8 ownerClaimBeforeE18 closedCollateralE18 : Nat) :
    conversionFactor
        * (ownerExternalAfter ownerExternalBeforeE8 closedCollateralE18
          - ownerExternalBeforeE8)
      + (ownerClaimAfter ownerClaimBeforeE18 closedCollateralE18
          - ownerClaimBeforeE18)
      = closedCollateralE18 := by
  simp [ownerExternalAfter, ownerClaimAfter]
  exact xqr_decomposition closedCollateralE18


theorem active_shadow_debit_preserves_amount
    (before closedCollateralE18 : Nat)
    (hBound : closedCollateralE18 ≤ before) :
    activePoolShadowAfter before closedCollateralE18 + closedCollateralE18 = before := by
  exact Nat.sub_add_cancel hBound


theorem accounted_custody_debit_preserves_quotient
    (before closedCollateralE18 : Nat)
    (hBound : quotientE8 closedCollateralE18 ≤ before) :
    custodyAfter before closedCollateralE18 + quotientE8 closedCollateralE18 = before := by
  exact Nat.sub_add_cancel hBound


theorem no_physical_transfer_for_sub_e8
    (closedCollateralE18 : Nat)
    (hSmall : closedCollateralE18 < conversionFactor) :
    ownerExternalAfter 0 closedCollateralE18 = 0 := by
  simp [ownerExternalAfter, sub_e8_has_zero_quotient closedCollateralE18 hSmall]


theorem adopted_examples :
    quotientE8 (3 * conversionFactor) = 3
      ∧ residueE18 (3 * conversionFactor) = 0
      ∧ quotientE8 (3 * conversionFactor + 7) = 3
      ∧ residueE18 (3 * conversionFactor + 7) = 7
      ∧ quotientE8 (conversionFactor - 1) = 0
      ∧ residueE18 (conversionFactor - 1) = conversionFactor - 1 := by
  norm_num [quotientE8, residueE18, conversionFactor]

end ZenoDEX.ZUSDOwnerCloseXQR
