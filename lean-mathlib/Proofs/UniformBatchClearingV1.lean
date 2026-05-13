/-!
# Uniform Batch Clearing V1

This file formalizes the small algebraic shape used by the UPBA v1 runtime
certificate verifier:

* fills are reduced to aggregate reserve deltas;
* execution applies the aggregate deltas once;
* any permutation of the fill list yields the same final state.
* the v1 canonical price objective depends only on aggregate net flow, so it is
  invariant under order-list permutation for a fixed admission set.

The theorem is intentionally scoped. It does not prove price optimality,
admission fairness, oracle safety, or multi-hop clearing.
-/

namespace UniformBatchClearingV1

/-- Abstract reserve state for a single two-asset pool. -/
structure PoolState where
  reserve0 : Int
  reserve1 : Int
deriving DecidableEq, Repr

/-- Abstract per-fill reserve delta. -/
structure FillDelta where
  delta0 : Int
  delta1 : Int
deriving DecidableEq, Repr

/-- Aggregate the first asset reserve deltas. -/
def sumDelta0 : List FillDelta → Int
  | [] => 0
  | fill :: fills => fill.delta0 + sumDelta0 fills

/-- Aggregate the second asset reserve deltas. -/
def sumDelta1 : List FillDelta → Int
  | [] => 0
  | fill :: fills => fill.delta1 + sumDelta1 fills

/-- Uniform execution applies aggregate deltas once. -/
def executeUniform (state : PoolState) (fills : List FillDelta) : PoolState :=
  {
    reserve0 := state.reserve0 + sumDelta0 fills
    reserve1 := state.reserve1 + sumDelta1 fills
  }

theorem sumDelta0_perm {fillsA fillsB : List FillDelta}
    (h : fillsA.Perm fillsB) :
    sumDelta0 fillsA = sumDelta0 fillsB := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [sumDelta0, ih]
  | swap _ _ _ => simp [sumDelta0, Int.add_left_comm]
  | trans _ _ ihAB ihBC => exact Eq.trans ihAB ihBC

theorem sumDelta1_perm {fillsA fillsB : List FillDelta}
    (h : fillsA.Perm fillsB) :
    sumDelta1 fillsA = sumDelta1 fillsB := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [sumDelta1, ih]
  | swap _ _ _ => simp [sumDelta1, Int.add_left_comm]
  | trans _ _ ihAB ihBC => exact Eq.trans ihAB ihBC

/--
UPBA v1 permutation invariance.

If two certificate fill lists are permutations of each other, uniform execution
returns the same aggregate state transition.
-/
theorem uniform_execution_permutation_invariant
    (state : PoolState)
    {fillsA fillsB : List FillDelta}
    (h : fillsA.Perm fillsB) :
    executeUniform state fillsA = executeUniform state fillsB := by
  cases state
  simp [executeUniform, sumDelta0_perm h, sumDelta1_perm h]

/--
Uniform execution is exactly linear aggregation followed by one state update.

This theorem pins the runtime design choice: the batch is not interpreted as a
sequential fold over intermediate pool states.
-/
theorem uniform_execution_is_linear_aggregation
    (state : PoolState)
    (fills : List FillDelta) :
    executeUniform state fills =
      {
        reserve0 := state.reserve0 + sumDelta0 fills
        reserve1 := state.reserve1 + sumDelta1 fills
      } := by
  rfl

/-! ## Canonical price-objective model -/

/--
Abstract admitted exact-in order, reduced to the net input it contributes on
each side of the single v1 pool.

The Python runtime computes these values after the deterministic fee rule and
before checking the submitted certificate price.
-/
structure NetOrder where
  baseToQuoteNet : Nat
  quoteToBaseNet : Nat
deriving DecidableEq, Repr

/-- Aggregate net base input from base-to-quote orders. -/
def sumBaseToQuoteNet : List NetOrder → Nat
  | [] => 0
  | order :: orders => order.baseToQuoteNet + sumBaseToQuoteNet orders

/-- Aggregate net quote input from quote-to-base orders. -/
def sumQuoteToBaseNet : List NetOrder → Nat
  | [] => 0
  | order :: orders => order.quoteToBaseNet + sumQuoteToBaseNet orders

/-- A rational price ratio represented by numerator and denominator. -/
structure PriceRatio where
  numerator : Nat
  denominator : Nat
deriving DecidableEq, Repr

/-- Reduce a positive rational ratio to a canonical representative. -/
def reducePriceRatio (ratio : PriceRatio) : PriceRatio :=
  let divisor := Nat.gcd ratio.numerator ratio.denominator
  {
    numerator := ratio.numerator / divisor
    denominator := ratio.denominator / divisor
  }

/--
Raw v1 price objective before ratio reduction.

When both directions are present, the objective is the aggregate quote flow over
aggregate base flow. When the batch is one-sided, the objective falls back to
the pre-pool spot ratio `reserveQuote / reserveBase`.
-/
def canonicalPriceObjectiveRaw
    (reserveQuote reserveBase : Nat)
    (orders : List NetOrder) : PriceRatio :=
  if 0 < sumBaseToQuoteNet orders ∧ 0 < sumQuoteToBaseNet orders then
    {
      numerator := sumQuoteToBaseNet orders
      denominator := sumBaseToQuoteNet orders
    }
  else
    {
      numerator := reserveQuote
      denominator := reserveBase
    }

/-- Canonical v1 price objective after ratio reduction. -/
def canonicalPriceObjective
    (reserveQuote reserveBase : Nat)
    (orders : List NetOrder) : PriceRatio :=
  reducePriceRatio (canonicalPriceObjectiveRaw reserveQuote reserveBase orders)

theorem sumBaseToQuoteNet_perm {ordersA ordersB : List NetOrder}
    (h : ordersA.Perm ordersB) :
    sumBaseToQuoteNet ordersA = sumBaseToQuoteNet ordersB := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [sumBaseToQuoteNet, ih]
  | swap _ _ _ => simp [sumBaseToQuoteNet, Nat.add_left_comm]
  | trans _ _ ihAB ihBC => exact Eq.trans ihAB ihBC

theorem sumQuoteToBaseNet_perm {ordersA ordersB : List NetOrder}
    (h : ordersA.Perm ordersB) :
    sumQuoteToBaseNet ordersA = sumQuoteToBaseNet ordersB := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [sumQuoteToBaseNet, ih]
  | swap _ _ _ => simp [sumQuoteToBaseNet, Nat.add_left_comm]
  | trans _ _ ihAB ihBC => exact Eq.trans ihAB ihBC

/--
The raw v1 price objective is invariant under permutation of the admitted order
list.

This matches the runtime certificate check before `_reduce_ratio`.
-/
theorem canonical_price_objective_raw_permutation_invariant
    (reserveQuote reserveBase : Nat)
    {ordersA ordersB : List NetOrder}
    (h : ordersA.Perm ordersB) :
    canonicalPriceObjectiveRaw reserveQuote reserveBase ordersA =
      canonicalPriceObjectiveRaw reserveQuote reserveBase ordersB := by
  simp [
    canonicalPriceObjectiveRaw,
    sumBaseToQuoteNet_perm h,
    sumQuoteToBaseNet_perm h,
  ]

/--
The reduced v1 price objective is invariant under permutation of the admitted
order list.

This is the abstract model of the Python verifier's
`price_objective_id = zenodex/upba_v1/net_flow_ratio_or_pool_spot_price`
certificate obligation.
-/
theorem canonical_price_objective_permutation_invariant
    (reserveQuote reserveBase : Nat)
    {ordersA ordersB : List NetOrder}
    (h : ordersA.Perm ordersB) :
    canonicalPriceObjective reserveQuote reserveBase ordersA =
      canonicalPriceObjective reserveQuote reserveBase ordersB := by
  simp [
    canonicalPriceObjective,
    canonical_price_objective_raw_permutation_invariant reserveQuote reserveBase h,
  ]

end UniformBatchClearingV1
