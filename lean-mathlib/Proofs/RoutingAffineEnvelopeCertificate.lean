import Mathlib

/-!
# Affine-envelope certificates for globally optimal integer routing

This file gives a solver-independent weak-duality certificate for exact-in
routing across finitely many pools. A proposer may use continuous KKT methods,
a mixed-integer active-set solver, dynamic programming, or any heuristic to
produce a candidate. The verifier only checks finite per-pool affine envelopes
and one aggregate strict-gap inequality.

For nonnegative integers `slopeNum`, `slopeDen`, and per-pool intercepts
`intercept i`, suppose every pool output obeys

`  slopeDen * out_i(a) ≤ slopeNum * a + intercept_i`

for every allocation `a` up to the total budget. Summing the inequalities gives

`  slopeDen * totalOut ≤ slopeNum * budget + Σ intercept_i`.

If that upper bound is strictly below

`  slopeDen * (winnerOut + 1)`,

then integer output forces every feasible competitor to have output at most
`winnerOut`. This certificate does not assume concavity, monotone marginal
jumps, or completeness of the optimizer's candidate enumeration.
-/

open scoped BigOperators

namespace Proofs
namespace RoutingAffineEnvelopeCertificate

variable {ι : Type _} [Fintype ι] [DecidableEq ι]

/-- Total gross input allocated across all pools. -/
def totalSpent (allocation : ι → ℕ) : ℕ :=
  ∑ i, allocation i

/-- Total output from independently quoted parallel pools. -/
def totalOutput (poolOut : ι → ℕ → ℕ) (allocation : ι → ℕ) : ℕ :=
  ∑ i, poolOut i (allocation i)

/-- A routing allocation is feasible when its total gross input is within budget. -/
def Feasible (budget : ℕ) (allocation : ι → ℕ) : Prop :=
  totalSpent allocation ≤ budget

/-- A common rational slope `slopeNum / slopeDen` plus one nonnegative
intercept per pool upper-bounds every exact integer quote in the audited domain. -/
def EnvelopeValid
    (slopeNum slopeDen budget : ℕ)
    (poolOut : ι → ℕ → ℕ)
    (intercept : ι → ℕ) : Prop :=
  ∀ i amount, amount ≤ budget →
    slopeDen * poolOut i amount ≤ slopeNum * amount + intercept i

/-- Any component of a nonnegative allocation is at most the total budget. -/
theorem component_le_budget
    {budget : ℕ} {allocation : ι → ℕ}
    (hFeasible : Feasible budget allocation)
    (i : ι) :
    allocation i ≤ budget := by
  have hLeSum : allocation i ≤ ∑ j, allocation j := by
    have hAdd := Finset.sum_erase_add
      (s := Finset.univ)
      (f := allocation)
      (by simp : i ∈ (Finset.univ : Finset ι))
    calc
      allocation i ≤ Finset.sum (Finset.univ.erase i) allocation + allocation i := by
        exact Nat.le_add_left _ _
      _ = ∑ j, allocation j := by
        simpa using hAdd
  exact hLeSum.trans hFeasible

/-- Weak duality: valid per-pool affine envelopes sum to a global output upper
bound for every budget-feasible allocation. -/
theorem affine_envelope_global_upper_bound
    {slopeNum slopeDen budget : ℕ}
    {poolOut : ι → ℕ → ℕ}
    {intercept : ι → ℕ}
    {allocation : ι → ℕ}
    (hEnvelope : EnvelopeValid slopeNum slopeDen budget poolOut intercept)
    (hFeasible : Feasible budget allocation) :
    slopeDen * totalOutput poolOut allocation ≤
      slopeNum * budget + ∑ i, intercept i := by
  have hPointwise :
      ∀ i ∈ (Finset.univ : Finset ι),
        slopeDen * poolOut i (allocation i) ≤
          slopeNum * allocation i + intercept i := by
    intro i _hi
    exact hEnvelope i (allocation i) (component_le_budget hFeasible i)
  calc
    slopeDen * totalOutput poolOut allocation =
        ∑ i, slopeDen * poolOut i (allocation i) := by
          simp [totalOutput, Finset.mul_sum]
    _ ≤ ∑ i, (slopeNum * allocation i + intercept i) := by
          exact Finset.sum_le_sum hPointwise
    _ = slopeNum * totalSpent allocation + ∑ i, intercept i := by
          simp [totalSpent, Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ slopeNum * budget + ∑ i, intercept i := by
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_left slopeNum hFeasible) _

/-- Global optimality under the primary economic objective. Canonical tie-break
selection remains a separate, already-mechanized concern. -/
def GloballyOutputOptimal
    (poolOut : ι → ℕ → ℕ)
    (budget : ℕ)
    (winner : ι → ℕ) : Prop :=
  Feasible budget winner ∧
    ∀ competitor, Feasible budget competitor →
      totalOutput poolOut competitor ≤ totalOutput poolOut winner

/-- A strict one-integer-unit gap between the dual upper bound and the next
possible winner output certifies exact global optimality. -/
theorem strict_unit_gap_certifies_global_optimality
    {slopeNum slopeDen budget : ℕ}
    {poolOut : ι → ℕ → ℕ}
    {intercept : ι → ℕ}
    {winner : ι → ℕ}
    (hDenPositive : 0 < slopeDen)
    (hEnvelope : EnvelopeValid slopeNum slopeDen budget poolOut intercept)
    (hWinnerFeasible : Feasible budget winner)
    (hStrictGap :
      slopeNum * budget + ∑ i, intercept i <
        slopeDen * (totalOutput poolOut winner + 1)) :
    GloballyOutputOptimal poolOut budget winner := by
  refine ⟨hWinnerFeasible, ?_⟩
  intro competitor hCompetitorFeasible
  have hUpper := affine_envelope_global_upper_bound
    (hEnvelope := hEnvelope)
    (hFeasible := hCompetitorFeasible)
  have hScaled :
      slopeDen * totalOutput poolOut competitor <
        slopeDen * (totalOutput poolOut winner + 1) :=
    lt_of_le_of_lt hUpper hStrictGap
  have hOutputLt :
      totalOutput poolOut competitor < totalOutput poolOut winner + 1 :=
    (Nat.mul_lt_mul_left hDenPositive).mp hScaled
  omega

/-- Exact tightness is a convenient sufficient condition for the strict unit
gap: a positive denominator leaves at least one scaled unit before the next
integer output level. -/
theorem tight_envelope_certifies_global_optimality
    {slopeNum slopeDen budget : ℕ}
    {poolOut : ι → ℕ → ℕ}
    {intercept : ι → ℕ}
    {winner : ι → ℕ}
    (hDenPositive : 0 < slopeDen)
    (hEnvelope : EnvelopeValid slopeNum slopeDen budget poolOut intercept)
    (hWinnerFeasible : Feasible budget winner)
    (hTight :
      slopeNum * budget + ∑ i, intercept i =
        slopeDen * totalOutput poolOut winner) :
    GloballyOutputOptimal poolOut budget winner := by
  apply strict_unit_gap_certifies_global_optimality
    (hDenPositive := hDenPositive)
    (hEnvelope := hEnvelope)
    (hWinnerFeasible := hWinnerFeasible)
  rw [hTight]
  exact (Nat.mul_lt_mul_left hDenPositive).mpr (by omega)

end RoutingAffineEnvelopeCertificate
end Proofs
