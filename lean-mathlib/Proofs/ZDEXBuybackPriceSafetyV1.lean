import Init.Omega

/-!
Natural-number proof obligations for the governed ZDEX buyback price envelope.

The executable Python and Rust cores derive a reserve-spend limit and an
Oracle-relative minimum output, then check freshness, depth, pool/Oracle
deviation, realized execution impact, and realized Oracle deviation with
cross multiplication. `Accepted` is the corresponding proof object: every
field is one obligation which a runtime acceptance must establish.

Nonclaims: this file does not authenticate Oracle or reserve observations,
prove Python/Rust/RISC0 refinement, prove machine-width overflow rejection,
select production policy parameters, prevent pre-trade MEV, verify a receipt,
or grant route, settlement, publication, or value-moving authority.
-/

namespace Proofs
namespace ZDEXBuybackPriceSafetyV1

def basisPoints : Nat := 10_000

structure Policy where
  maximumOracleAgeBlocks : Nat
  minimumQuoteReserve : Nat
  minimumZdexReserve : Nat
  maximumPoolOracleDeviationBps : Nat
  maximumExecutionImpactBps : Nat
  maximumOracleExecutionDeviationBps : Nat
  maximumQuoteReserveSpendBps : Nat
  deriving DecidableEq, Repr

structure Observation where
  currentHeight : Nat
  oracleObservedHeight : Nat
  oracleQuoteNumerator : Nat
  oracleZdexDenominator : Nat
  quoteReserve : Nat
  zdexReserve : Nat
  quoteAmountIn : Nat
  purchasedZdex : Nat
  claimedRouteSafeQuoteLimit : Nat
  claimedMinimumOutput : Nat
  deriving DecidableEq, Repr

def routeSafeQuoteLimit (p : Policy) (o : Observation) : Nat :=
  o.quoteReserve * p.maximumQuoteReserveSpendBps / basisPoints

def ceilDiv (numerator denominator : Nat) : Nat :=
  numerator / denominator + if numerator % denominator = 0 then 0 else 1

def oracleMinimumOutput (p : Policy) (o : Observation) : Nat :=
  ceilDiv
    (o.quoteAmountIn * o.oracleZdexDenominator * basisPoints)
    (o.oracleQuoteNumerator *
      (basisPoints + p.maximumOracleExecutionDeviationBps))

def absoluteDifference (left right : Nat) : Nat :=
  if left ≤ right then right - left else left - right

/-- Exact obligations carried by an accepted price-safety observation. -/
structure Accepted (p : Policy) (o : Observation) : Prop where
  policyDeviationBounds :
    p.maximumPoolOracleDeviationBps < basisPoints ∧
    p.maximumExecutionImpactBps < basisPoints ∧
    p.maximumOracleExecutionDeviationBps < basisPoints
  policySpendBounds :
    0 < p.maximumQuoteReserveSpendBps ∧
    p.maximumQuoteReserveSpendBps ≤ basisPoints
  positiveRatios :
    0 < o.oracleQuoteNumerator ∧ 0 < o.oracleZdexDenominator
  heightMonotone : o.oracleObservedHeight ≤ o.currentHeight
  oracleFresh :
    o.currentHeight - o.oracleObservedHeight ≤ p.maximumOracleAgeBlocks
  sufficientDepth :
    p.minimumQuoteReserve ≤ o.quoteReserve ∧
    p.minimumZdexReserve ≤ o.zdexReserve
  outputWithinReserve : o.purchasedZdex ≤ o.zdexReserve
  exactRouteLimit :
    o.claimedRouteSafeQuoteLimit = routeSafeQuoteLimit p o
  positiveRouteLimit : 0 < o.claimedRouteSafeQuoteLimit
  spendWithinRouteLimit : o.quoteAmountIn ≤ o.claimedRouteSafeQuoteLimit
  exactMinimumOutput :
    o.claimedMinimumOutput = oracleMinimumOutput p o
  realizedMinimumOutput : o.claimedMinimumOutput ≤ o.purchasedZdex
  poolOracleEnvelope :
    absoluteDifference
        (o.quoteReserve * o.oracleZdexDenominator)
        (o.zdexReserve * o.oracleQuoteNumerator) * basisPoints ≤
      o.zdexReserve * o.oracleQuoteNumerator *
        p.maximumPoolOracleDeviationBps
  executionImpactEnvelope :
    o.quoteAmountIn * o.zdexReserve * basisPoints ≤
      o.purchasedZdex * o.quoteReserve *
        (basisPoints + p.maximumExecutionImpactBps)
  oracleExecutionEnvelope :
    o.quoteAmountIn * o.oracleZdexDenominator * basisPoints ≤
      o.purchasedZdex * o.oracleQuoteNumerator *
        (basisPoints + p.maximumOracleExecutionDeviationBps)

/-- Acceptance exposes the exact freshness and depth obligations. -/
theorem accepted_implies_fresh_deep_observation
    (p : Policy) (o : Observation) (h : Accepted p o) :
    o.oracleObservedHeight ≤ o.currentHeight ∧
      o.currentHeight - o.oracleObservedHeight ≤ p.maximumOracleAgeBlocks ∧
      p.minimumQuoteReserve ≤ o.quoteReserve ∧
      p.minimumZdexReserve ≤ o.zdexReserve := by
  exact ⟨h.heightMonotone, h.oracleFresh,
    h.sufficientDepth.1, h.sufficientDepth.2⟩

/-- The selected spend is bounded by the uniquely derived reserve limit. -/
theorem accepted_spend_within_derived_limit
    (p : Policy) (o : Observation) (h : Accepted p o) :
    o.quoteAmountIn ≤ routeSafeQuoteLimit p o := by
  rw [← h.exactRouteLimit]
  exact h.spendWithinRouteLimit

/-- The claimed minimum is uniquely derived and met by realized output. -/
theorem accepted_meets_derived_minimum_output
    (p : Policy) (o : Observation) (h : Accepted p o) :
    oracleMinimumOutput p o ≤ o.purchasedZdex := by
  rw [← h.exactMinimumOutput]
  exact h.realizedMinimumOutput

/-- Acceptance carries both independent realized-price inequalities. -/
theorem accepted_implies_execution_envelopes
    (p : Policy) (o : Observation) (h : Accepted p o) :
    o.quoteAmountIn * o.zdexReserve * basisPoints ≤
        o.purchasedZdex * o.quoteReserve *
          (basisPoints + p.maximumExecutionImpactBps) ∧
      o.quoteAmountIn * o.oracleZdexDenominator * basisPoints ≤
        o.purchasedZdex * o.oracleQuoteNumerator *
          (basisPoints + p.maximumOracleExecutionDeviationBps) := by
  exact ⟨h.executionImpactEnvelope, h.oracleExecutionEnvelope⟩

def witnessPolicy : Policy where
  maximumOracleAgeBlocks := 3
  minimumQuoteReserve := 500
  minimumZdexReserve := 200
  maximumPoolOracleDeviationBps := 500
  maximumExecutionImpactBps := 500
  maximumOracleExecutionDeviationBps := 1_000
  maximumQuoteReserveSpendBps := 2_000

def witnessObservation : Observation where
  currentHeight := 77
  oracleObservedHeight := 76
  oracleQuoteNumerator := 4
  oracleZdexDenominator := 1
  quoteReserve := 1_000
  zdexReserve := 250
  quoteAmountIn := 100
  purchasedZdex := 24
  claimedRouteSafeQuoteLimit := 200
  claimedMinimumOutput := 23

/-- A positive fixture shared with Python and Rust makes the obligations live. -/
theorem nonvacuity_witness_is_accepted :
    Accepted witnessPolicy witnessObservation := by
  set_option maxRecDepth 100_000 in
  constructor <;> decide

end ZDEXBuybackPriceSafetyV1
end Proofs
