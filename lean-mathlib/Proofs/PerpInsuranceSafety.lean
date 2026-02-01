import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Insurance fund safety for epoch-based perpetuals

## Main results

* `insurance_accounting`: Balance identity: balance + claims = initial + fees.
* `insurance_solvency_from_surplus`: Fund solvent when fees ≥ claims.
* `insurance_multi_epoch_solvent`: Multi-epoch solvency with non-negative net income.
* `insurance_depletion_bounded`: Per-epoch depletion bounded by max_claim.
* `insurance_survives_epochs`: Fund survives N epochs if initial ≥ N × max_drain.

## Key insight

The insurance fund balance satisfies `balance = initial + Σ fees - Σ claims`.
Solvency holds iff `balance ≥ 0`. When each epoch has `fees ≥ claims`, the
fund is monotonically non-decreasing.
-/

namespace Proofs

namespace PerpInsuranceSafety

/-- Insurance accounting identity: rearranging the balance equation. -/
theorem insurance_accounting
    (initial fee_income claims balance : ℚ)
    (h : balance = initial + fee_income - claims) :
    balance + claims = initial + fee_income := by
  linarith

/-- Fund solvent when cumulative fees ≥ cumulative claims. -/
theorem insurance_solvency_from_surplus
    (initial fee_income claims : ℚ)
    (h_init : 0 ≤ initial)
    (h_surplus : claims ≤ fee_income) :
    0 ≤ initial + fee_income - claims := by
  linarith

/-- Multi-epoch solvency: non-negative initial balance plus non-negative
    net income at each epoch guarantees the fund stays non-negative. -/
theorem insurance_multi_epoch_solvent
    (initial : ℚ)
    (net_incomes : List ℚ)
    (h_init : 0 ≤ initial)
    (h_pos : ∀ x ∈ net_incomes, 0 ≤ x) :
    0 ≤ initial + net_incomes.sum := by
  suffices h : 0 ≤ net_incomes.sum by linarith
  induction net_incomes with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.sum_cons]
    have hhd := h_pos hd (.head _)
    have htl : ∀ x ∈ tl, 0 ≤ x := fun x hx =>
      h_pos x (List.mem_cons_of_mem hd hx)
    linarith [ih htl]

/-- Per-epoch depletion bounded: balance decrease is at most max_claim
    (achieved when fee = 0 and claim = max_claim). -/
theorem insurance_depletion_bounded
    (balance fee claim max_claim : ℚ)
    (h_claim : claim ≤ max_claim)
    (h_fee : 0 ≤ fee) :
    balance - max_claim ≤ balance + fee - claim := by
  linarith

/-- Fund survives N epochs: if initial ≥ N × max_drain_per_epoch,
    the balance remains non-negative even under worst-case drain. -/
theorem insurance_survives_epochs
    (initial max_drain : ℚ)
    (n : ℕ)
    (h_bound : (n : ℚ) * max_drain ≤ initial) :
    0 ≤ initial - (n : ℚ) * max_drain := by
  linarith

/-! ## Non-vacuity witnesses -/

/-- Witness: insurance accounting identity — init=10000, fees=500, claims=300,
    balance=10200 → balance + claims = 10500 = init + fees. -/
theorem witness_accounting :
    let init : ℚ := 10000
    let fees : ℚ := 500
    let claims : ℚ := 300
    let balance : ℚ := 10200
    balance = init + fees - claims ∧ balance + claims = init + fees := by
  norm_num

/-- Witness: fund solvent with concrete values (init=10000, fees=500, claims=300). -/
theorem witness_solvent :
    let init : ℚ := 10000
    let fees : ℚ := 500
    let claims : ℚ := 300
    0 ≤ init + fees - claims := by
  norm_num

/-- Witness: multi-epoch solvency with 4 epochs of net income [100,50,200,75]. -/
theorem witness_multi_epoch :
    let init : ℚ := 1000
    let net : ℚ := 100 + 50 + 200 + 75
    0 ≤ init + net := by
  norm_num

/-- Witness: per-epoch depletion bounded — balance=1000, fee=50, claim=80,
    max_claim=100. balance-max_claim=900 ≤ balance+fee-claim=970. -/
theorem witness_depletion :
    let balance : ℚ := 1000
    let fee : ℚ := 50
    let claim : ℚ := 80
    let max_claim : ℚ := 100
    claim ≤ max_claim ∧ 0 ≤ fee ∧ balance - max_claim ≤ balance + fee - claim := by
  norm_num

/-- Witness: fund survives 5 epochs of max drain 100 from initial 1000. -/
theorem witness_survives :
    0 ≤ (1000 : ℚ) - (5 : ℚ) * 100 := by
  norm_num

end PerpInsuranceSafety

end Proofs
