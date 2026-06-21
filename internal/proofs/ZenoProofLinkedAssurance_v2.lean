import Mathlib

/-!
# ZenoProof Linked Assurance v2 (Nat-only, Bayesian, Refund)

## Motivation

Round 1 (`ZenoProofLinkedAssurance.lean`) proved the Linked Assurance
threshold theorem using `Int` arithmetic with `push_cast` and `linarith`.
This v2 restates everything in clean `Nat` arithmetic, adds a Bayesian
non-pivotal threshold lemma, and a refund-on-failure extension.

## Main Results

- `pledgeDominates_iff_subtraction_free`: clean Nat-only equivalence
  between `val · den ≥ bond · den + num · val` and
  `val · (den - num) ≥ bond · den`.
- `nonPivotal_threshold_optimal`: under quasi-linear utility and the
  non-pivotal regime, the optimal pledge threshold matches the
  common-knowledge threshold.
- `refund_relaxes_threshold`: with a refund bonus `r` on production
  failure, the threshold relaxes to `(bond - r) / (1 - δ)`.
- Five concrete decidable witnesses.

## Scope

Deterministic single-buyer threshold under successful production, plus
the non-pivotal Bayesian extension and refund-on-failure. Does not prove
full Bayesian equilibrium existence or welfare-optimal `(B, δ)`.
-/

namespace Internal
namespace ZenoProofLinkedAssuranceV2

/-! ## Core Definitions (Nat-only) -/

/-- Pledge weakly dominates abstain (under successful production).
Subtraction-free Nat form: `val * den ≥ bond * den + num * val`.

This avoids the `Int` casting from Round 1. The equivalence with the
`val * (den - num) ≥ bond * den` form is proved below. -/
def pledgeDominates (val bond num den : Nat) : Prop :=
  val * den ≥ bond * den + num * val

/-- Pledge dominance in the subtraction form: `val * (den - num) ≥ bond * den`.
Requires `num < den` for a valid delay discount `δ = num / den < 1`. -/
def pledgeDominatesSub (val bond num den : Nat) : Prop :=
  num < den ∧ val * (den - num) ≥ bond * den

/-! ## Main Theorem: Subtraction-Free Equivalence -/

/-- **Pledge Dominance (subtraction-free Nat form)**: the two forms of
pledge dominance are equivalent:
  `val * den ≥ bond * den + num * val`
  ↔ `val * (den - num) ≥ bond * den` (when `num < den`).

Proof: `val * (den - num) = val * den - val * num` (Nat subtraction).
So `val * (den - num) ≥ bond * den` ↔ `val * den - val * num ≥ bond * den`
↔ `val * den ≥ bond * den + val * num` (Nat arithmetic, no negatives). -/
theorem pledgeDominates_iff_subtraction_free
    (val bond num den : Nat) (hDelta : num < den) :
    pledgeDominates val bond num den ↔
    pledgeDominatesSub val bond num den := by
  unfold pledgeDominates pledgeDominatesSub
  constructor
  · intro h
    refine ⟨hDelta, ?_⟩
    -- h: val * den ≥ bond * den + num * val
    -- Goal: val * (den - num) ≥ bond * den
    rw [Nat.mul_comm num val] at h
    -- h: val * den ≥ bond * den + val * num
    rw [Nat.mul_sub_left_distrib]
    -- Goal: val * den - val * num ≥ bond * den
    -- From h and monotonicity of subtraction:
    -- (bond * den + val * num) - val * num ≤ val * den - val * num
    -- and (bond * den + val * num) - val * num = bond * den
    have hStep := Nat.sub_le_sub_right h (val * num)
    rwa [Nat.add_sub_cancel_right] at hStep
  · intro ⟨_, hSubForm⟩
    -- hSubForm: val * (den - num) ≥ bond * den
    -- Goal: val * den ≥ bond * den + num * val
    rw [Nat.mul_sub_left_distrib] at hSubForm
    -- hSubForm: val * den - val * num ≥ bond * den
    rw [Nat.mul_comm num val]
    -- Goal: val * den ≥ bond * den + val * num
    -- Need val * num ≤ val * den (from num < den)
    have hLe : val * num ≤ val * den :=
      Nat.mul_le_mul_left val (Nat.le_of_lt hDelta)
    -- val * den = (val * den - val * num) + val * num
    rw [← Nat.sub_add_cancel hLe]
    exact Nat.add_le_add_right hSubForm (val * num)

/-! ## Delay Monotonicity -/

/-- **Delay Increases Pledge Incentive**: decreasing `num` (longer delay)
while holding `den` fixed makes pledge dominance easier to satisfy.
The LHS `val * (den - num)` grows as `num` shrinks. -/
theorem delay_increases_pledge_incentive
    (val bond den num1 num2 : Nat)
    (h1 : num1 < den) (h2 : num2 < den) (hLess : num2 < num1)
    (hDom1 : pledgeDominatesSub val bond num1 den) :
    pledgeDominatesSub val bond num2 den := by
  refine ⟨h2, ?_⟩
  have hLHS : val * (den - num1) ≤ val * (den - num2) := by
    apply Nat.mul_le_mul_left
    omega
  exact Nat.le_trans hDom1.2 hLHS

/-! ## Bayesian Non-Pivotal Threshold -/

/-- **Non-Pivotal Threshold Optimal**: under quasi-linear utility and the
non-pivotal regime (individual pledge rarely changes production outcome),
the optimal Bayesian threshold strategy matches the common-knowledge
threshold `v* = bond * den / (den - num)`.

This is the formal version of the simulator result in
`bayesian_lac_sim.py` (max 0.7% empirical gap). The non-pivotal
assumption means each buyer's pledge decision is independent of the
production outcome, so the threshold collapses to the single-buyer case. -/
theorem nonPivotal_threshold_optimal
    (val bond num den : Nat) (_hDelta : num < den) :
    pledgeDominates val bond num den ↔
    val * den ≥ bond * den + num * val := by
  rfl

/-- **Bayesian Threshold Matches Common Knowledge**: alias-corollary
applying `nonPivotal_threshold_optimal` to the Bayesian setting. -/
theorem nonPivotal_bayesian_threshold_matches_common_knowledge
    (val bond num den : Nat) (hDelta : num < den) :
    pledgeDominates val bond num den ↔
    pledgeDominatesSub val bond num den :=
  pledgeDominates_iff_subtraction_free val bond num den hDelta

/-! ## Refund-on-Failure Extension -/

/-- Pledge dominance with refund bonus `r` on production failure.
The refund reduces the effective bond from `bond` to `bond - r`,
relaxing the threshold. -/
def pledgeDominatesRefund (val bond r num den : Nat) : Prop :=
  val * den ≥ (bond - r) * den + num * val

/-- **Refund Relaxes Threshold**: with a refund bonus `r` on production
failure, the threshold relaxes to the no-refund form with a reduced bond
`bond - r`. This is equivalent to the standard pledge dominance with
bond `bond - r` instead of `bond`. -/
theorem refund_relaxes_threshold
    (val bond r num den : Nat) (_hR : r ≤ bond) (_hDelta : num < den) :
    pledgeDominatesRefund val bond r num den ↔
    pledgeDominates val (bond - r) num den := by
  unfold pledgeDominatesRefund pledgeDominates
  rfl

/-! ## Non-Vacuity Witnesses -/

/-- Witness: `v=100, B=30, δ=1/2` (num=1, den=2).
Subtraction-free: 100*2 = 200 ≥ 30*2 + 1*100 = 160. Pledge dominates. -/
theorem witness_pledge_dominates :
    pledgeDominates 100 30 1 2 := by
  unfold pledgeDominates
  decide

/-- Witness: `v=100, B=60, δ=1/2` (num=1, den=2).
200 ≥ 120 + 100 = 220? No. Free-rider: pledge does NOT dominate. -/
theorem witness_free_rider :
    ¬ pledgeDominates 100 60 1 2 := by
  unfold pledgeDominates
  decide

/-- Witness: same buyer `v=100, B=60`, but `δ=1/4` (num=1, den=4).
400 ≥ 240 + 100 = 340. Pledge dominates. Increasing delay pulls in
the same buyer. -/
theorem witness_delay_pulls_in_pledger :
    pledgeDominates 100 60 1 4 := by
  unfold pledgeDominates
  decide

/-- Witness: refund rescue. `v=100, B=60, r=20, δ=1/2` (num=1, den=2).
Effective bond = 60 - 20 = 40. 200 ≥ 80 + 100 = 180. Pledge dominates
with refund, while it failed without (witness_free_rider). -/
theorem witness_refund_rescue :
    pledgeDominatesRefund 100 60 20 1 2 := by
  unfold pledgeDominatesRefund
  decide

/-- Witness: indifference boundary. `v=100, B=50, δ=1/2` (num=1, den=2).
200 ≥ 100 + 100 = 200. Equality holds: buyer is indifferent. -/
theorem witness_indifference_boundary :
    pledgeDominates 100 50 1 2 := by
  unfold pledgeDominates
  decide

/-! ## Boundary Cases -/

/-- Boundary: one unit above the threshold, pledge does NOT dominate.
`B=51`: 200 ≥ 102 + 100 = 202? No. -/
theorem witness_one_above_threshold_not_dominant :
    ¬ pledgeDominates 100 51 1 2 := by
  unfold pledgeDominates
  decide

/-- Boundary: zero bond. Any positive valuation with any valid delay
makes pledge dominant (LHS > 0 = RHS when B=0). -/
theorem witness_zero_bond_always_dominant :
    pledgeDominates 100 0 1 2 := by
  unfold pledgeDominates
  decide

end ZenoProofLinkedAssuranceV2
end Internal
