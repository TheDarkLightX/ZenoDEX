import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Fee Revenue Boundedness Obligations

Arithmetic lemmas used by fee accumulator / optimizer kernels:

1. Fee component `(amount * fee_bps) / 10000` is bounded by `amount` when `fee_bps ≤ 10000`.
2. Therefore the component is bounded by known amount caps.
3. A guard of the form `total ≤ cap - delta` implies `total + delta ≤ cap`.
-/

namespace Proofs
namespace FeeRevenueBoundedness

def feeComponent (amount feeBps : Nat) : Nat :=
  (amount * feeBps) / 10000

theorem fee_component_nonneg (amount feeBps : Nat) :
    0 ≤ feeComponent amount feeBps := by
  exact Nat.zero_le _

theorem fee_component_le_amount {amount feeBps : Nat}
    (hBps : feeBps ≤ 10000) :
    feeComponent amount feeBps ≤ amount := by
  unfold feeComponent
  have hMul : amount * feeBps ≤ amount * 10000 := Nat.mul_le_mul_left amount hBps
  have hDiv : (amount * feeBps) / 10000 ≤ (amount * 10000) / 10000 := Nat.div_le_div_right hMul
  calc
    (amount * feeBps) / 10000 ≤ (amount * 10000) / 10000 := hDiv
    _ = amount := by
      simp at *

theorem fee_component_le_1m {amount feeBps : Nat}
    (hAmount : amount ≤ 1000000)
    (hBps : feeBps ≤ 10000) :
    feeComponent amount feeBps ≤ 1000000 := by
  exact le_trans (fee_component_le_amount hBps) hAmount

theorem fee_component_le_10m {amount feeBps : Nat}
    (hAmount : amount ≤ 10000000)
    (hBps : feeBps ≤ 10000) :
    feeComponent amount feeBps ≤ 10000000 := by
  exact le_trans (fee_component_le_amount hBps) hAmount

theorem bounded_add_from_sub_guard {total delta cap : Nat}
    (hDelta : delta ≤ cap)
    (hGuard : total ≤ cap - delta) :
    total + delta ≤ cap := by
  omega

theorem fee_calculator_step_preserves_cap
    {total amount feeBps : Nat}
    (hAmount : amount ≤ 1000000)
    (hBps : feeBps ≤ 10000)
    (hGuard : total ≤ 10000000 - feeComponent amount feeBps) :
    total + feeComponent amount feeBps ≤ 10000000 := by
  have hDelta : feeComponent amount feeBps ≤ 10000000 := by
    exact le_trans (fee_component_le_amount hBps) (le_trans hAmount (by norm_num))
  exact bounded_add_from_sub_guard hDelta hGuard

theorem fee_optimizer_step_preserves_cap
    {total amount feeBps : Nat}
    (hAmount : amount ≤ 10000000)
    (hBps : feeBps ≤ 1000)
    (hGuard : total ≤ 1000000000 - feeComponent amount feeBps) :
    total + feeComponent amount feeBps ≤ 1000000000 := by
  have hBpsWide : feeBps ≤ 10000 := le_trans hBps (by norm_num)
  have hDelta : feeComponent amount feeBps ≤ 1000000000 := by
    exact le_trans (fee_component_le_amount hBpsWide) (le_trans hAmount (by norm_num))
  exact bounded_add_from_sub_guard hDelta hGuard

end FeeRevenueBoundedness
end Proofs
