import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# ZenoDEX Settlement Compact Bundle

This file formalizes the current `settlement_v5_aligned_compact_bundle` shape:

- strict canonical ordering on four replay ids,
- monotone 3-point price trace,
- only the final price step is bounded by `< 50`,
- all module / proof flags are accepted.

It also records the exact refinement boundary against the stronger
`settlement_price_rails_aligned_v1` shape:

- full price rails imply the compact bundle price gate,
- the converse is false, with an explicit witness.
-/

namespace TauSwap
namespace ZenoDEX
namespace SettlementCompactBundle

def CanonicalIds (a b c d : Nat) : Prop :=
  a < b ∧ b < c ∧ c < d

def MonotonePriceTrace (pricePP pricePrev priceCurr : Nat) : Prop :=
  (pricePP ≤ pricePrev ∧ pricePrev ≤ priceCurr) ∨
    (pricePP ≥ pricePrev ∧ pricePrev ≥ priceCurr)

def CompactPriceGate (a b c d pricePP pricePrev priceCurr : Nat) : Prop :=
  CanonicalIds a b c d ∧
    MonotonePriceTrace pricePP pricePrev priceCurr ∧
    Nat.dist pricePrev priceCurr < 50

/-- Stronger than the compact price gate: both adjacent price steps are bounded. -/
def FullPriceRails (a b c d pricePP pricePrev priceCurr : Nat) : Prop :=
  CanonicalIds a b c d ∧
    MonotonePriceTrace pricePP pricePrev priceCurr ∧
    Nat.dist pricePP pricePrev < 50 ∧
    Nat.dist pricePrev priceCurr < 50

def FlagsAllOn
    (cpmmOk balanceOk tokenOk buybackFloorOk buybackFloorFixedpointOk
      rebateOk lockWeightOk proofOk bindingOk : Bool) : Prop :=
  cpmmOk = true ∧
    balanceOk = true ∧
    tokenOk = true ∧
    buybackFloorOk = true ∧
    buybackFloorFixedpointOk = true ∧
    rebateOk = true ∧
    lockWeightOk = true ∧
    proofOk = true ∧
    bindingOk = true

def CompactBundleOk
    (a b c d pricePP pricePrev priceCurr : Nat)
    (cpmmOk balanceOk tokenOk buybackFloorOk buybackFloorFixedpointOk
      rebateOk lockWeightOk proofOk bindingOk : Bool) : Prop :=
  CompactPriceGate a b c d pricePP pricePrev priceCurr ∧
    FlagsAllOn cpmmOk balanceOk tokenOk buybackFloorOk buybackFloorFixedpointOk
      rebateOk lockWeightOk proofOk bindingOk

theorem fullPriceRails_implies_compactPriceGate
    {a b c d pricePP pricePrev priceCurr : Nat}
    (h : FullPriceRails a b c d pricePP pricePrev priceCurr) :
    CompactPriceGate a b c d pricePP pricePrev priceCurr := by
  rcases h with ⟨hcanon, hmono, _hPrevPrev, hPrevCurr⟩
  exact ⟨hcanon, hmono, hPrevCurr⟩

theorem compactBundleOk_of_fullPriceRails_of_flags
    {a b c d pricePP pricePrev priceCurr : Nat}
    {cpmmOk balanceOk tokenOk buybackFloorOk buybackFloorFixedpointOk
      rebateOk lockWeightOk proofOk bindingOk : Bool}
    (hRails : FullPriceRails a b c d pricePP pricePrev priceCurr)
    (hFlags : FlagsAllOn cpmmOk balanceOk tokenOk buybackFloorOk buybackFloorFixedpointOk
      rebateOk lockWeightOk proofOk bindingOk) :
    CompactBundleOk a b c d pricePP pricePrev priceCurr
      cpmmOk balanceOk tokenOk buybackFloorOk buybackFloorFixedpointOk
      rebateOk lockWeightOk proofOk bindingOk := by
  exact ⟨fullPriceRails_implies_compactPriceGate hRails, hFlags⟩

theorem flagsAllOn_all_true :
    FlagsAllOn true true true true true true true true true := by
  simp [FlagsAllOn]

theorem compactBundleOk_of_fullPriceRails_all_true
    {a b c d pricePP pricePrev priceCurr : Nat}
    (hRails : FullPriceRails a b c d pricePP pricePrev priceCurr) :
    CompactBundleOk a b c d pricePP pricePrev priceCurr
      true true true true true true true true true := by
  exact compactBundleOk_of_fullPriceRails_of_flags hRails flagsAllOn_all_true

theorem compactBundleOk_implies_lastStepBound
    {a b c d pricePP pricePrev priceCurr : Nat}
    {cpmmOk balanceOk tokenOk buybackFloorOk buybackFloorFixedpointOk
      rebateOk lockWeightOk proofOk bindingOk : Bool}
    (h : CompactBundleOk a b c d pricePP pricePrev priceCurr
      cpmmOk balanceOk tokenOk buybackFloorOk buybackFloorFixedpointOk
      rebateOk lockWeightOk proofOk bindingOk) :
    Nat.dist pricePrev priceCurr < 50 := by
  exact h.1.2.2

theorem compactBundleOk_implies_canonicalIds
    {a b c d pricePP pricePrev priceCurr : Nat}
    {cpmmOk balanceOk tokenOk buybackFloorOk buybackFloorFixedpointOk
      rebateOk lockWeightOk proofOk bindingOk : Bool}
    (h : CompactBundleOk a b c d pricePP pricePrev priceCurr
      cpmmOk balanceOk tokenOk buybackFloorOk buybackFloorFixedpointOk
      rebateOk lockWeightOk proofOk bindingOk) :
    CanonicalIds a b c d := by
  exact h.1.1

theorem compactPriceGate_counterexample :
    CompactPriceGate 1 2 3 4 0 60 70 := by
  unfold CompactPriceGate CanonicalIds MonotonePriceTrace
  native_decide

theorem not_fullPriceRails_counterexample :
    ¬ FullPriceRails 1 2 3 4 0 60 70 := by
  unfold FullPriceRails CanonicalIds MonotonePriceTrace
  native_decide

theorem compactBundleOk_counterexample :
    CompactBundleOk 1 2 3 4 0 60 70
      true true true true true true true true true := by
  unfold CompactBundleOk CompactPriceGate FlagsAllOn CanonicalIds MonotonePriceTrace
  native_decide

theorem compactBundle_not_equivalent_to_fullPriceRails :
    ¬ ∀ a b c d pricePP pricePrev priceCurr,
      CompactBundleOk a b c d pricePP pricePrev priceCurr
        true true true true true true true true true →
      FullPriceRails a b c d pricePP pricePrev priceCurr := by
  intro h
  exact not_fullPriceRails_counterexample
    (h 1 2 3 4 0 60 70 compactBundleOk_counterexample)

end SettlementCompactBundle
end ZenoDEX
end TauSwap
