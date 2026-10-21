import Mathlib.Tactic
import Proofs.CpmmSwapV8ExactOutMinimality

open scoped BigOperators

/-!
# ZenoDEX Exact-Out Primal-Dual Routing Certificate

The runtime exact-out many-pool router currently proves optimality by rebuilding
and comparing a bounded candidate stream.  This file formalizes a complementary
certificate surface that does not require enumerating every feasible allocation.

The certificate has three layers:

1. an abstract affine dual lower bound for any separable fixed-total allocation;
2. an exact continuous CPMM tangent identity, which supplies per-pool affine
   lower bounds;
3. an integer bridge showing the v8 nested-ceiling exact-out quote is never below
   its continuous CPMM relaxation.

The important boundary is explicit.  Integer exact-out quotes are not generally
discretely convex after nested ceiling operations.  A concrete witness below
therefore rejects the tempting but false rule that two neighboring marginal
checks always certify exact integer optimality.

A proposed route is globally optimal when its executable integer input equals
the certified dual lower bound.  When they differ, the same certificate gives
an explicit additive suboptimality gap.
-/

namespace TauSwap
namespace Routing
namespace ExactOutDualCertificate

/-- A fixed-total allocation with a per-coordinate feasibility predicate. -/
def FeasibleAllocation {n : ℕ}
    (feasible : Fin n → ℚ → Prop)
    (total : ℚ)
    (allocation : Fin n → ℚ) : Prop :=
  (∀ i, feasible i (allocation i)) ∧
    (∑ i, allocation i) = total

/-- `intercept + slope * q` is a valid lower bound on one pool's cost. -/
def AffineLowerBound
    (cost : ℚ → ℚ)
    (feasible : ℚ → Prop)
    (slope intercept : ℚ) : Prop :=
  ∀ q, feasible q → intercept + slope * q ≤ cost q

/-- The aggregate dual value for a common slope and fixed total. -/
def dualLowerBound {n : ℕ}
    (intercept : Fin n → ℚ)
    (slope total : ℚ) : ℚ :=
  (∑ i, intercept i) + slope * total

/-- Weak duality for separable fixed-total routing.

Any collection of per-pool affine lower bounds sharing one slope yields a lower
bound on every feasible allocation.  The proof is the fixed-total cancellation
at the heart of KKT/Lagrange multiplier certificates. -/
theorem affine_dual_lower_bound
    {n : ℕ}
    (cost : Fin n → ℚ → ℚ)
    (feasible : Fin n → ℚ → Prop)
    (intercept : Fin n → ℚ)
    (slope total : ℚ)
    (allocation : Fin n → ℚ)
    (hLower :
      ∀ i, AffineLowerBound (cost i) (feasible i) slope (intercept i))
    (hFeasible : FeasibleAllocation feasible total allocation) :
    dualLowerBound intercept slope total ≤
      ∑ i, cost i (allocation i) := by
  calc
    dualLowerBound intercept slope total
        = ∑ i, (intercept i + slope * allocation i) := by
            simp only [dualLowerBound]
            rw [← hFeasible.2, Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ ∑ i, cost i (allocation i) := by
      exact Finset.sum_le_sum fun i _hi =>
        hLower i (allocation i) (hFeasible.1 i)

/-- Convert an arbitrary tangent slope into a common dual slope over a bounded
interval.  If the common slope is no larger, nonnegative outputs preserve the
tangent intercept.  If it is larger, shifting the intercept at the upper bound
keeps the new line below the tangent throughout `[0, cap]`. -/
def normalizedIntercept
    (tangentIntercept tangentSlope commonSlope cap : ℚ) : ℚ :=
  if commonSlope ≤ tangentSlope then
    tangentIntercept
  else
    tangentIntercept + (tangentSlope - commonSlope) * cap

theorem normalized_affine_below_tangent
    (tangentIntercept tangentSlope commonSlope cap q : ℚ)
    (hQNonneg : 0 ≤ q)
    (hQCap : q ≤ cap) :
    normalizedIntercept tangentIntercept tangentSlope commonSlope cap +
        commonSlope * q ≤
      tangentIntercept + tangentSlope * q := by
  unfold normalizedIntercept
  by_cases hSlope : commonSlope ≤ tangentSlope
  · simp only [hSlope, if_pos]
    have hScaled : commonSlope * q ≤ tangentSlope * q :=
      mul_le_mul_of_nonneg_right hSlope hQNonneg
    linarith
  · simp only [hSlope, if_neg]
    have hSlope' : tangentSlope < commonSlope := lt_of_not_ge hSlope
    have hScaled :
        (commonSlope - tangentSlope) * q ≤
          (commonSlope - tangentSlope) * cap :=
      mul_le_mul_of_nonneg_left hQCap (sub_nonneg.mpr (le_of_lt hSlope'))
    linarith

/-- A feasible candidate whose cost is within `gap` of the dual lower bound is
within the same additive gap of every feasible allocation. -/
theorem affine_dual_additive_gap
    {n : ℕ}
    (cost : Fin n → ℚ → ℚ)
    (feasible : Fin n → ℚ → Prop)
    (intercept : Fin n → ℚ)
    (slope total gap : ℚ)
    (candidate : Fin n → ℚ)
    (hGap : 0 ≤ gap)
    (hLower :
      ∀ i, AffineLowerBound (cost i) (feasible i) slope (intercept i))
    (hCandidateFeasible : FeasibleAllocation feasible total candidate)
    (hCandidateCost :
      (∑ i, cost i (candidate i)) ≤
        dualLowerBound intercept slope total + gap) :
    ∀ alternative,
      FeasibleAllocation feasible total alternative →
        (∑ i, cost i (candidate i)) ≤
          (∑ i, cost i (alternative i)) + gap := by
  intro alternative hAlternative
  have hDual :=
    affine_dual_lower_bound
      cost feasible intercept slope total alternative hLower hAlternative
  linarith

/-- Zero primal-dual gap certifies exact global optimality. -/
theorem affine_dual_zero_gap_global_optimal
    {n : ℕ}
    (cost : Fin n → ℚ → ℚ)
    (feasible : Fin n → ℚ → Prop)
    (intercept : Fin n → ℚ)
    (slope total : ℚ)
    (candidate : Fin n → ℚ)
    (hLower :
      ∀ i, AffineLowerBound (cost i) (feasible i) slope (intercept i))
    (hCandidateFeasible : FeasibleAllocation feasible total candidate)
    (hCandidateCost :
      (∑ i, cost i (candidate i)) =
        dualLowerBound intercept slope total) :
    ∀ alternative,
      FeasibleAllocation feasible total alternative →
        (∑ i, cost i (candidate i)) ≤
          ∑ i, cost i (alternative i) := by
  intro alternative hAlternative
  have hDual :=
    affine_dual_lower_bound
      cost feasible intercept slope total alternative hLower hAlternative
  linarith

/-- Integer objectives turn a strict sub-unit rational gap into exact order.

If two integer costs differ, they differ by at least one atom. -/
theorem int_le_of_cast_lt_add_one
    {candidate alternative : ℤ}
    (hGap :
      (candidate : ℚ) < (alternative : ℚ) + 1) :
    candidate ≤ alternative := by
  by_contra hNot
  have hStep : alternative + 1 ≤ candidate := by
    omega
  have hCast :
      (alternative : ℚ) + 1 ≤ (candidate : ℚ) := by
    exact_mod_cast hStep
  linarith

/-- A dual lower bound less than one atom below an executable integer candidate
already certifies exact global optimality against every integer alternative. -/
theorem integer_objective_exact_of_dual_gap_lt_one
    (dualValue : ℚ)
    (candidateCost alternativeCost : ℤ)
    (hCandidateGap :
      (candidateCost : ℚ) < dualValue + 1)
    (hAlternativeLower :
      dualValue ≤ (alternativeCost : ℚ)) :
    candidateCost ≤ alternativeCost := by
  apply int_le_of_cast_lt_add_one
  linarith

/-! ## Continuous CPMM exact-out tangent certificate -/

/-- Continuous gross input for exact output `q` under reserve pair `(x, y)` and
fee denominator `feeDen = 10000 - feeBps`.

This is the relaxation of the v8 nested-ceiling quote:
`x * q * 10000 / (feeDen * (y - q))`. -/
def continuousExactOutCost
    (x y feeDen q : ℚ) : ℚ :=
  x * q * 10000 / (feeDen * (y - q))

/-- Marginal continuous gross-input cost at anchor `a`. -/
def continuousExactOutSlope
    (x y feeDen a : ℚ) : ℚ :=
  x * y * 10000 / (feeDen * (y - a) ^ 2)

/-- Exact tangent-gap identity for continuous CPMM exact-out cost.

The right side is a nonnegative square on the valid domain, so every tangent is
a global affine lower bound. -/
theorem continuous_exact_out_tangent_gap_identity
    (x y feeDen a q : ℚ)
    (hFeeDen : feeDen ≠ 0)
    (hAnchorDen : y - a ≠ 0)
    (hQuoteDen : y - q ≠ 0) :
    continuousExactOutCost x y feeDen q -
        (continuousExactOutCost x y feeDen a +
          continuousExactOutSlope x y feeDen a * (q - a)) =
      x * y * 10000 * (q - a) ^ 2 /
        (feeDen * (y - a) ^ 2 * (y - q)) := by
  field_simp [continuousExactOutCost, continuousExactOutSlope,
    hFeeDen, hAnchorDen, hQuoteDen]
  ring

/-- Every valid continuous CPMM tangent is a global lower bound. -/
theorem continuous_exact_out_tangent_lower_bound
    (x y feeDen a q : ℚ)
    (hX : 0 ≤ x)
    (hY : 0 < y)
    (hFeeDen : 0 < feeDen)
    (hAnchor : a < y)
    (hQuote : q < y) :
    continuousExactOutCost x y feeDen a +
        continuousExactOutSlope x y feeDen a * (q - a) ≤
      continuousExactOutCost x y feeDen q := by
  have hAnchorPos : 0 < y - a := sub_pos.mpr hAnchor
  have hQuotePos : 0 < y - q := sub_pos.mpr hQuote
  have hIdentity :=
    continuous_exact_out_tangent_gap_identity
      x y feeDen a q
      (ne_of_gt hFeeDen)
      (ne_of_gt hAnchorPos)
      (ne_of_gt hQuotePos)
  have hNumerator :
      0 ≤ x * y * 10000 * (q - a) ^ 2 := by
    positivity
  have hDenominator :
      0 < feeDen * (y - a) ^ 2 * (y - q) := by
    positivity
  have hGap :
      0 ≤ x * y * 10000 * (q - a) ^ 2 /
        (feeDen * (y - a) ^ 2 * (y - q)) :=
    div_nonneg hNumerator (le_of_lt hDenominator)
  linarith

/-! ## Integer v8 quote bridge -/

/-- The exact nested-ceiling gross-input formula used by CPMM v8 exact-out. -/
def grossInRequiredV8
    (reserveIn reserveOut amountOut feeBps : ℕ) : ℕ :=
  let netRequired :=
    (reserveIn * amountOut) ⌈/⌉ (reserveOut - amountOut)
  (netRequired * 10000) ⌈/⌉ (10000 - feeBps)

/-- The integer quote dominates the continuous relaxation after clearing the
positive denominators.

Equivalently:
`gross >= reserveIn * amountOut * 10000 /
          ((10000 - feeBps) * (reserveOut - amountOut))`.
The cross-multiplied form avoids any lossy cast or division. -/
theorem grossInRequiredV8_scaled_continuous_lower_bound
    {reserveIn reserveOut amountOut feeBps : ℕ}
    (hAmountOut : amountOut < reserveOut)
    (hFee : feeBps < 10000) :
    reserveIn * amountOut * 10000 ≤
      grossInRequiredV8 reserveIn reserveOut amountOut feeBps *
        (10000 - feeBps) * (reserveOut - amountOut) := by
  let outDen : ℕ := reserveOut - amountOut
  let feeDen : ℕ := 10000 - feeBps
  let netRequired : ℕ := (reserveIn * amountOut) ⌈/⌉ outDen
  let gross : ℕ := (netRequired * 10000) ⌈/⌉ feeDen
  have hOutDen : 0 < outDen := by
    dsimp [outDen]
    omega
  have hFeeDen : 0 < feeDen := by
    dsimp [feeDen]
    omega
  have hNet :
      reserveIn * amountOut ≤ outDen * netRequired := by
    exact le_smul_ceilDiv
      (a := outDen) (b := reserveIn * amountOut) hOutDen
  have hGross :
      netRequired * 10000 ≤ feeDen * gross := by
    exact le_smul_ceilDiv
      (a := feeDen) (b := netRequired * 10000) hFeeDen
  have hScaled :
      reserveIn * amountOut * 10000 ≤ gross * feeDen * outDen := by
    calc
      reserveIn * amountOut * 10000
          ≤ (outDen * netRequired) * 10000 :=
            Nat.mul_le_mul_right 10000 hNet
      _ = outDen * (netRequired * 10000) := by ring
      _ ≤ outDen * (feeDen * gross) :=
        Nat.mul_le_mul_left outDen hGross
      _ = gross * feeDen * outDen := by ring
  simpa [grossInRequiredV8, outDen, feeDen, netRequired, gross] using hScaled

/-- Nested ceiling destroys exact discrete convexity in general.

For `(reserveIn, reserveOut, feeBps) = (1, 4, 0)`, costs at outputs
`0, 1, 2` are `0, 1, 1`.  The first forward difference is `1`, while the next
is `0`.  Therefore an exact integer routing proof must not assume monotone
forward differences without an instance-specific certificate. -/
theorem witness_integer_exact_out_not_discrete_convex :
    grossInRequiredV8 1 4 0 0 = 0 ∧
    grossInRequiredV8 1 4 1 0 = 1 ∧
    grossInRequiredV8 1 4 2 0 = 1 ∧
    ¬ (grossInRequiredV8 1 4 1 0 - grossInRequiredV8 1 4 0 0 ≤
       grossInRequiredV8 1 4 2 0 - grossInRequiredV8 1 4 1 0) := by
  decide

end ExactOutDualCertificate
end Routing
end TauSwap
