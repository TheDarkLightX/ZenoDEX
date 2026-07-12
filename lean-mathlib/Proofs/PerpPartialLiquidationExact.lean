import Mathlib.Tactic

/-!
# Exact bounded selector for partial liquidation

The runtime partial-liquidation selector searches the fixed basis-point domain
`{1, ..., 10000}` for the first fraction that restores maintenance margin.
This file proves the generic bounded-search contract and instantiates the same
integer arithmetic on the bounty-threshold counterexample that invalidates
binary search.

The proof deliberately does not assume that sufficiency is monotone. Activating
the liquidation bounty and integer floors can make the predicate alternate
between false and true several times.

This theorem verifies the selector and arithmetic model. A separate parity test
is still required to bind the Lean definitions to the Python runtime.
-/

namespace Proofs
namespace PerpPartialLiquidationExact

def priceScale : ℕ := 100_000_000
def bpsScale : ℕ := 10_000

/-- Scan `fuel` consecutive values beginning at `start`; if none succeeds,
return the first value after the scanned interval. -/
def firstSufficientFrom (sufficient : ℕ → Bool) (start : ℕ) : ℕ → ℕ
  | 0 => start
  | fuel + 1 =>
      if sufficient start then start
      else firstSufficientFrom sufficient (start + 1) fuel

theorem firstSufficientFrom_lower
    (sufficient : ℕ → Bool) (start fuel : ℕ) :
    start ≤ firstSufficientFrom sufficient start fuel := by
  induction fuel generalizing start with
  | zero => simp [firstSufficientFrom]
  | succ fuel ih =>
      cases h : sufficient start with
      | false =>
          simp only [firstSufficientFrom, h, Bool.false_eq_true, ↓reduceIte]
          exact le_trans (Nat.le_add_right start 1) (ih (start + 1))
      | true => simp [firstSufficientFrom, h]

theorem firstSufficientFrom_upper
    (sufficient : ℕ → Bool) (start fuel : ℕ) :
    firstSufficientFrom sufficient start fuel ≤ start + fuel := by
  induction fuel generalizing start with
  | zero => simp [firstSufficientFrom]
  | succ fuel ih =>
      cases h : sufficient start with
      | false =>
          simp only [firstSufficientFrom, h, Bool.false_eq_true, ↓reduceIte]
          have htail := ih (start + 1)
          omega
      | true => simp [firstSufficientFrom, h]

theorem firstSufficientFrom_success_or_fallback
    (sufficient : ℕ → Bool) (start fuel : ℕ) :
    firstSufficientFrom sufficient start fuel = start + fuel ∨
      sufficient (firstSufficientFrom sufficient start fuel) = true := by
  induction fuel generalizing start with
  | zero => simp [firstSufficientFrom]
  | succ fuel ih =>
      cases h : sufficient start with
      | false =>
          simp only [firstSufficientFrom, h, Bool.false_eq_true, ↓reduceIte]
          rcases ih (start + 1) with hfallback | hsuccess
          · left
            omega
          · exact Or.inr hsuccess
      | true => simp [firstSufficientFrom, h]

theorem firstSufficientFrom_minimal
    (sufficient : ℕ → Bool) (start fuel x : ℕ)
    (hstart : start ≤ x)
    (hx : x < firstSufficientFrom sufficient start fuel) :
    sufficient x = false := by
  induction fuel generalizing start x with
  | zero =>
      simp [firstSufficientFrom] at hx
      omega
  | succ fuel ih =>
      cases h : sufficient start with
      | false =>
          have hxTail : x < firstSufficientFrom sufficient (start + 1) fuel := by
            simpa [firstSufficientFrom, h] using hx
          rcases eq_or_lt_of_le hstart with rfl | hlt
          · exact h
          · exact ih (start + 1) x (by omega) hxTail
      | true =>
          simp [firstSufficientFrom, h] at hx
          omega

/-- Runtime-shaped selector: scan fractions `1` through `9999`, then use full
close (`10000`) as the fail-closed fallback. -/
def firstSufficientFraction (sufficient : ℕ → Bool) : ℕ :=
  firstSufficientFrom sufficient 1 (bpsScale - 1)

theorem firstSufficientFraction_bounds (sufficient : ℕ → Bool) :
    1 ≤ firstSufficientFraction sufficient ∧
      firstSufficientFraction sufficient ≤ bpsScale := by
  constructor
  · exact firstSufficientFrom_lower sufficient 1 (bpsScale - 1)
  · simpa [firstSufficientFraction, bpsScale] using
      firstSufficientFrom_upper sufficient 1 (bpsScale - 1)

theorem firstSufficientFraction_succeeds
    (sufficient : ℕ → Bool)
    (hfull : sufficient bpsScale = true) :
    sufficient (firstSufficientFraction sufficient) = true := by
  rcases firstSufficientFrom_success_or_fallback sufficient 1 (bpsScale - 1) with
    hfallback | hsuccess
  · rw [firstSufficientFraction, hfallback]
    simpa [bpsScale] using hfull
  · exact hsuccess

theorem firstSufficientFraction_is_minimal
    (sufficient : ℕ → Bool) (x : ℕ)
    (hxOne : 1 ≤ x)
    (hxBefore : x < firstSufficientFraction sufficient) :
    sufficient x = false :=
  firstSufficientFrom_minimal sufficient 1 (bpsScale - 1) x hxOne hxBefore

def notionalQuote (positionAbs priceE8 : ℕ) : ℕ :=
  positionAbs * priceE8 / priceScale

def marginRequirement (notional rateBps : ℕ) : ℕ :=
  notional * rateBps / bpsScale

def partialCloseBase (positionAbs fractionBps : ℕ) : ℕ :=
  positionAbs * fractionBps / bpsScale

def remainingPosition (positionAbs fractionBps : ℕ) : ℕ :=
  positionAbs - partialCloseBase positionAbs fractionBps

def partialPenalty
    (collateral positionAbs fractionBps priceE8 penaltyBps minNotional : ℕ) : ℕ :=
  let closed := partialCloseBase positionAbs fractionBps
  let notional := notionalQuote closed priceE8
  if notional < minNotional then 0
  else min collateral (marginRequirement notional penaltyBps)

def sufficientAfterPartialClose
    (positionAbs collateral fractionBps priceE8 maintBps depegBps
      penaltyBps minNotional : ℕ) : Bool :=
  let remaining := remainingPosition positionAbs fractionBps
  let penalty := partialPenalty collateral positionAbs fractionBps priceE8 penaltyBps minNotional
  let collateralAfter := collateral - penalty
  let requirement := marginRequirement (notionalQuote remaining priceE8) (maintBps + depegBps)
  decide (remaining = 0 ∨ requirement ≤ collateralAfter)

/-- Runtime predicate specialized to a fixed account and market parameter tuple. -/
def runtimeSufficient
    (positionAbs collateral priceE8 maintBps depegBps penaltyBps minNotional : ℕ) :
    ℕ → Bool :=
  fun fractionBps =>
    sufficientAfterPartialClose positionAbs collateral fractionBps priceE8
      maintBps depegBps penaltyBps minNotional

/-- The precondition used by the Python selector, expressed over the unsigned
position magnitude and nonnegative collateral fragment modeled in this file. -/
def isLiquidatable
    (positionAbs collateral priceE8 maintBps depegBps : ℕ) : Bool :=
  decide (
    positionAbs ≠ 0 ∧
      collateral < marginRequirement (notionalQuote positionAbs priceE8)
        (maintBps + depegBps))

/-- Runtime-shaped entry point: return zero for a flat or healthy account;
otherwise return the first sufficient basis-point fraction. -/
def runtimeFraction
    (positionAbs collateral priceE8 maintBps depegBps penaltyBps minNotional : ℕ) : ℕ :=
  if isLiquidatable positionAbs collateral priceE8 maintBps depegBps then
    firstSufficientFraction
      (runtimeSufficient positionAbs collateral priceE8 maintBps depegBps
        penaltyBps minNotional)
  else
    0

theorem runtimeSufficient_full_close
    (positionAbs collateral priceE8 maintBps depegBps penaltyBps minNotional : ℕ) :
    runtimeSufficient positionAbs collateral priceE8 maintBps depegBps
      penaltyBps minNotional bpsScale = true := by
  simp [runtimeSufficient, sufficientAfterPartialClose, remainingPosition,
    partialCloseBase, bpsScale]

theorem runtimeFraction_eq_zero_of_not_liquidatable
    (positionAbs collateral priceE8 maintBps depegBps penaltyBps minNotional : ℕ)
    (hNotLiquidatable :
      isLiquidatable positionAbs collateral priceE8 maintBps depegBps = false) :
    runtimeFraction positionAbs collateral priceE8 maintBps depegBps
      penaltyBps minNotional = 0 := by
  simp [runtimeFraction, hNotLiquidatable]

/-- On liquidatable inputs, the runtime-shaped selector returns a sufficient
fraction in range and every earlier admissible fraction is insufficient. -/
theorem runtimeFraction_contract_of_liquidatable
    (positionAbs collateral priceE8 maintBps depegBps penaltyBps minNotional : ℕ)
    (hLiquidatable :
      isLiquidatable positionAbs collateral priceE8 maintBps depegBps = true) :
    let sufficient := runtimeSufficient positionAbs collateral priceE8 maintBps
      depegBps penaltyBps minNotional
    let selected := runtimeFraction positionAbs collateral priceE8 maintBps
      depegBps penaltyBps minNotional
    1 ≤ selected ∧ selected ≤ bpsScale ∧ sufficient selected = true ∧
      ∀ x, 1 ≤ x → x < selected → sufficient x = false := by
  dsimp only
  have hBounds := firstSufficientFraction_bounds
    (runtimeSufficient positionAbs collateral priceE8 maintBps depegBps
      penaltyBps minNotional)
  have hSucceeds := firstSufficientFraction_succeeds
    (runtimeSufficient positionAbs collateral priceE8 maintBps depegBps
      penaltyBps minNotional)
    (runtimeSufficient_full_close positionAbs collateral priceE8 maintBps
      depegBps penaltyBps minNotional)
  constructor
  · simpa [runtimeFraction, hLiquidatable] using hBounds.1
  constructor
  · simpa [runtimeFraction, hLiquidatable] using hBounds.2
  constructor
  · simpa [runtimeFraction, hLiquidatable] using hSucceeds
  · intro x hxOne hxBefore
    apply firstSufficientFraction_is_minimal
      (runtimeSufficient positionAbs collateral priceE8 maintBps depegBps
        penaltyBps minNotional) x hxOne
    simpa [runtimeFraction, hLiquidatable] using hxBefore

def witnessSufficient : ℕ → Bool :=
  fun fractionBps =>
    sufficientAfterPartialClose 1_000 60 fractionBps 100_000_000 1_000 0 500 500

/-- The bounty threshold makes the liquidation-health predicate nonmonotone. -/
theorem witness_nonmonotone :
    witnessSufficient 4_999 = true ∧ witnessSufficient 5_000 = false := by
  decide

/-- Exact replay of the Python counterexample: the first sufficient close is
`3910` bps. The former binary search returned `7710`. -/
theorem witness_exact_fraction :
    firstSufficientFraction witnessSufficient = 3_910 := by
  set_option maxRecDepth 20000 in
    decide

/-- The runtime precondition admits the witness, and the complete runtime-shaped
selector returns the same exact minimum. -/
theorem witness_runtime_fraction :
    runtimeFraction 1_000 60 100_000_000 1_000 0 500 500 = 3_910 := by
  set_option maxRecDepth 20000 in
    decide

theorem witness_full_close_succeeds : witnessSufficient bpsScale = true := by
  decide

/-- The selected witness fraction is sufficient and every earlier admissible
fraction is insufficient. -/
theorem witness_exact_fraction_is_minimal :
    witnessSufficient (firstSufficientFraction witnessSufficient) = true ∧
      ∀ x, 1 ≤ x → x < firstSufficientFraction witnessSufficient →
        witnessSufficient x = false := by
  constructor
  · exact firstSufficientFraction_succeeds witnessSufficient witness_full_close_succeeds
  · intro x hxOne hxBefore
    exact firstSufficientFraction_is_minimal witnessSufficient x hxOne hxBefore

end PerpPartialLiquidationExact
end Proofs
