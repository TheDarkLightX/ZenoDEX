import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Perp Funding — Zero-Sum Bounded-Sink Conservation (N accounts)

Formalizes the funding-auto settlement rule (replacing the counterparty-residual
design). Each of N open accounts receives EXACTLY its formula-derived funding
payment `fpᵢ`, so its collateral delta is `-fpᵢ`. The net of all payments,
`Σ fpᵢ` (structural OI imbalance + floor rounding, either sign), is routed into
the protocol sink. This is zero-sum by construction:

  Σ (collateral deltaᵢ) + sink delta = 0.

Bumping the three linked sink mirrors (fee_pool_quote / fee_income /
insurance_balance) by the SAME net preserves the persistent state identities,
and the gate's fail-closed bound keeps every post-sink value in domain.
-/

namespace Proofs
namespace PerpFundingSinkConservation

/-- Sum of negated funding payments equals the negation of the sum. -/
theorem map_neg_sum (fps : List ℤ) :
    (fps.map (fun p => -p)).sum = -fps.sum := by
  induction fps with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Account `i`'s collateral delta is exactly minus its own funding payment. -/
def collateral_delta (funding_payment : ℤ) : ℤ := -funding_payment

/-- The sink absorbs the net of all per-account funding payments. -/
def sink_delta (fps : List ℤ) : ℤ := fps.sum

/-- ZERO-SUM CONSERVATION: total collateral change plus the sink delta is zero,
    for any number of accounts and any signed funding payments. -/
theorem conservation (fps : List ℤ) :
    (fps.map collateral_delta).sum + sink_delta fps = 0 := by
  unfold collateral_delta sink_delta
  rw [map_neg_sum]
  ring

/-- Equivalent form: the sink delta is exactly minus the total collateral change. -/
theorem sink_eq_neg_collateral (fps : List ℤ) :
    sink_delta fps = -(fps.map collateral_delta).sum := by
  unfold collateral_delta sink_delta
  rw [map_neg_sum]; ring

/-- NO ARTIFICIAL TRANSFER: an account's collateral delta depends only on its
    OWN funding payment (= -fpᵢ); it is never adjusted to absorb a global
    accounting residual (the flaw of the removed counterparty design). -/
theorem per_account_delta_is_raw (funding_payment : ℤ) :
    collateral_delta funding_payment = -funding_payment := rfl

/-- IDENTITY 1 preserved: `fee_pool_quote == fee_income` survives the joint bump
    (both increase by the same net). -/
theorem fee_pool_identity_preserved (fee_pool fee_income net : ℤ)
    (h : fee_pool = fee_income) :
    fee_pool + net = fee_income + net := by rw [h]

/-- IDENTITY 2 preserved: `insurance == initial + fee_income - claims` survives
    the joint bump, because insurance and fee_income move together by the same
    net. This is WHY all three mirrors must be bumped, not just fee_pool. -/
theorem insurance_identity_preserved
    (insurance initial fee_income claims net : ℤ)
    (h : insurance = initial + fee_income - claims) :
    insurance + net = initial + (fee_income + net) - claims := by
  rw [h]; ring

/-- FAIL-CLOSED domain bound: when the gate admits the net (it requires
    `0 ≤ s + net ≤ MAX` for each sink `s` BEFORE any mutation), every
    post-settlement sink value is in domain. -/
theorem post_sink_in_domain (s net maxv : ℤ)
    (h0 : 0 ≤ s + net) (h1 : s + net ≤ maxv) :
    0 ≤ s + net ∧ s + net ≤ maxv := ⟨h0, h1⟩

-- ============================================================================
-- Non-vacuity witnesses (concrete books)
-- ============================================================================

/-- Balanced book (+20, -10, -10): sink delta 0, collateral conserved. -/
theorem witness_balanced :
    let fps : List ℤ := [20, -10, -10]
    (fps.map collateral_delta).sum + sink_delta fps = 0 ∧ sink_delta fps = 0 := by
  native_decide

/-- Net-LONG book (+20, -10): sink +10, total collateral -10, sum 0. -/
theorem witness_net_long :
    let fps : List ℤ := [20, -10]
    sink_delta fps = 10
      ∧ (fps.map collateral_delta).sum = -10
      ∧ (fps.map collateral_delta).sum + sink_delta fps = 0 := by
  native_decide

/-- Net-SHORT book (+10, -20): sink -10 (requires a prefunded sink), sum 0. -/
theorem witness_net_short :
    let fps : List ℤ := [10, -20]
    sink_delta fps = -10
      ∧ (fps.map collateral_delta).sum = 10
      ∧ (fps.map collateral_delta).sum + sink_delta fps = 0 := by
  native_decide

end PerpFundingSinkConservation
end Proofs
