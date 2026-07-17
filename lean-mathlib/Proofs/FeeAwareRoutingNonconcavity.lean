import Mathlib.Tactic
import Proofs.CPMMInvariants

/-!
# Fee-aware gross-input routing is not uniformly nearly concave

The zero-fee CPMM output has a reserve-independent second-difference defect bound.
That fact does not extend to the production v8 gross-input semantics, because the
ceiling fee can hold net input flat for one gross unit and then release an
arbitrarily large first output jump.

For every proposed natural defect grade `k`, choose input reserve `1`, output
reserve `2 * (k + 1)`, fee `1` bp, and inspect gross inputs `0, 1, 2`:

* gross `0` produces output `0`;
* gross `1` pays a one-unit ceiling fee, so net input and output are `0`;
* gross `2` still pays one unit, so net input is `1` and output is `k + 1`.

Hence the positive second difference is `k + 1`, exceeding `k`. Any exact
fee-aware optimizer therefore needs a staircase, exhaustive, or independently
checkable global certificate; it cannot inherit a reserve-independent local
concavity certificate from the zero-fee model.
-/

namespace Proofs
namespace FeeAwareRoutingNonconcavity

open CPMMInvariants

/-- Production-style v8 output specialized to input reserve `1` and fee `1` bp. -/
def feeAwareOut (reserveOut grossIn : ℕ) : ℕ :=
  swapOutput 1 reserveOut (netAmount grossIn 1)

@[simp] theorem feeAwareOut_zero (reserveOut : ℕ) :
    feeAwareOut reserveOut 0 = 0 := by
  norm_num [feeAwareOut, swapOutput, netAmount, computeFee, ceilDiv]

@[simp] theorem feeAwareOut_one (reserveOut : ℕ) :
    feeAwareOut reserveOut 1 = 0 := by
  norm_num [feeAwareOut, swapOutput, netAmount, computeFee, ceilDiv]

@[simp] theorem feeAwareOut_two (k : ℕ) :
    feeAwareOut ((k + 1) * 2) 2 = k + 1 := by
  norm_num [feeAwareOut, swapOutput, netAmount, computeFee, ceilDiv]

/-- Natural-number cross-multiplied form of a bounded positive second difference. -/
def NatNearlyDiscreteConcave (grade : ℕ) (f : ℕ → ℕ) (domain : ℕ) : Prop :=
  ∀ i, i + 2 ≤ domain → f (i + 2) + f i ≤ 2 * f (i + 1) + grade

/-- The v8 gross-input output has a positive second difference larger than any
fixed reserve-independent grade. -/
theorem fee_aware_gross_second_difference_unbounded (grade : ℕ) :
    2 * feeAwareOut ((grade + 1) * 2) 1 + grade <
      feeAwareOut ((grade + 1) * 2) 2 +
        feeAwareOut ((grade + 1) * 2) 0 := by
  rw [feeAwareOut_one, feeAwareOut_two, feeAwareOut_zero]
  omega

/-- No natural grade chosen independently of reserves can certify even the
three-point domain `{0,1,2}` for the v8 fee-aware output family. -/
theorem no_reserve_independent_concavity_grade (grade : ℕ) :
    ¬ NatNearlyDiscreteConcave grade
      (feeAwareOut ((grade + 1) * 2)) 2 := by
  intro h
  have hAtZero := h 0 (by omega)
  have hBad := fee_aware_gross_second_difference_unbounded grade
  omega

/-- Concrete threshold witness: for `(x,y,fee) = (1,3,1 bp)`, the minimal gross
costs of output levels one and two are two and three. The threshold increments
are therefore `2` and `1`, so gross-space marginal jump costs can decrease. -/
theorem decreasing_threshold_increment_witness :
    feeAwareOut 3 0 = 0 ∧
    feeAwareOut 3 1 = 0 ∧
    feeAwareOut 3 2 = 1 ∧
    feeAwareOut 3 3 = 2 ∧
    (3 - 2 : ℕ) < (2 - 0 : ℕ) := by
  norm_num [feeAwareOut, swapOutput, netAmount, computeFee, ceilDiv]

end FeeAwareRoutingNonconcavity
end Proofs
