import Mathlib

/-!
# ZenoProof Mechanism Composition (Parallel and Series)

## Motivation

Without composition theorems, every multi-bounty round required re-proving
safety from scratch. This file proves that parallel and series composition
of `BountyMechanism` instances preserves safety, with explicit budget-
conservation theorems. The series case formalizes `counterexample beats
proof` from the ZenoProof spec.

## Main Results

- `parallelPayout_le_sum_cap`: parallel composite is bounded by the sum cap.
- `parallelPayout_zero_when_ineligible`: parallel ineligibility gives zero.
- `parallel_positive_implies_eligible`: generic safety theorem inherits.
- `seriesPayout_le_cap`: series composite is bounded by the shared cap
  (not the sum, because only one branch fires).
- `seriesPayout_zero_when_ineligible`: series ineligibility gives zero.
- `series_positive_implies_eligible`: generic safety inherits.
- `counterexample_wins_when_proof_not_eligible`: the spec's
  `counterexample beats proof` reward mode formalized (equality).
- `counterexample_payout_positive`: positivity under cap > 0.
- `proof_wins_when_eligible`: dual case.
- Four concrete decidable witnesses.

## Scope

Parallel (both fire) and series (first eligible fires, else second)
composition. Does not address temporal ordering of series submissions.
-/

namespace Internal
namespace ZenoProofMechanismComposition

/-! ## Core Definitions -/

/-- A bounty mechanism is a typeclass capturing the common safety structure. -/
class BountyMechanism (S : Type) where
  eligible : S → Bool
  payout : Nat → S → Nat
  payout_zero_when_ineligible : ∀ cap s, eligible s = false → payout cap s = 0
  payout_le_cap : ∀ cap s, payout cap s ≤ cap

open BountyMechanism

/-- Parallel composition: two mechanisms `M₁` and `M₂` over submission
types `S₁` and `S₂`. Both fire independently. The total payout is the
sum of individual payouts, bounded by the sum of caps. -/
structure ParallelComposite (S₁ S₂ : Type) [BountyMechanism S₁] [BountyMechanism S₂] where
  sub1 : S₁
  sub2 : S₂

/-- Series composition: two mechanisms `M₁` and `M₂`. `M₁` runs first;
if `M₁` is ineligible, `M₂` runs. Only one branch fires. The payout is
bounded by the shared cap (not the sum). -/
structure SeriesComposite (S₁ S₂ : Type) [BountyMechanism S₁] [BountyMechanism S₂] where
  sub1 : S₁
  sub2 : S₂

/-- Parallel eligibility: both submissions must be eligible. -/
def parallelEligible {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (p : ParallelComposite S₁ S₂) : Bool :=
  eligible p.sub1 ∧ eligible p.sub2

/-- Parallel payout: sum of individual payouts. -/
def parallelPayout {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (cap1 cap2 : Nat) (p : ParallelComposite S₁ S₂) : Nat :=
  payout cap1 p.sub1 + payout cap2 p.sub2

/-- Series eligibility: `M₁` is eligible, OR `M₁` is ineligible and `M₂`
is eligible. -/
def seriesEligible {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (p : SeriesComposite S₁ S₂) : Bool :=
  if eligible p.sub1 then true else eligible p.sub2

/-- Series payout: if `M₁` is eligible, pay `M₁`; else pay `M₂`. -/
def seriesPayout {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (cap : Nat) (p : SeriesComposite S₁ S₂) : Nat :=
  if eligible p.sub1 then payout cap p.sub1 else payout cap p.sub2

/-! ## Parallel Composition Theorems -/

/-- **Parallel Payout Bounded by Sum Cap**: the total payout of a parallel
composite is bounded by the sum of the two caps. -/
theorem parallelPayout_le_sum_cap
    {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (cap1 cap2 : Nat) (p : ParallelComposite S₁ S₂) :
    parallelPayout cap1 cap2 p ≤ cap1 + cap2 := by
  unfold parallelPayout
  have h1 : payout cap1 p.sub1 ≤ cap1 := payout_le_cap cap1 p.sub1
  have h2 : payout cap2 p.sub2 ≤ cap2 := payout_le_cap cap2 p.sub2
  omega

/-- **Parallel Payout Zero When Ineligible**: if both submissions are
ineligible, the parallel payout is zero. -/
theorem parallelPayout_zero_when_ineligible
    {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (cap1 cap2 : Nat) (p : ParallelComposite S₁ S₂)
    (h1 : eligible p.sub1 = false) (h2 : eligible p.sub2 = false) :
    parallelPayout cap1 cap2 p = 0 := by
  unfold parallelPayout
  have hp1 : payout cap1 p.sub1 = 0 := payout_zero_when_ineligible cap1 p.sub1 h1
  have hp2 : payout cap2 p.sub2 = 0 := payout_zero_when_ineligible cap2 p.sub2 h2
  rw [hp1, hp2]

/-- **Parallel Positive Payout Implies Eligible**: if the parallel payout
is positive, at least one submission is eligible. -/
theorem parallel_positive_implies_eligible
    {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (cap1 cap2 : Nat) (p : ParallelComposite S₁ S₂)
    (hPos : 0 < parallelPayout cap1 cap2 p) :
    eligible p.sub1 = true ∨ eligible p.sub2 = true := by
  by_contra h
  push_neg at h
  have hf1 : eligible p.sub1 = false := by
    cases hElig : eligible p.sub1 with
    | false => rfl
    | true => exact (h.1 hElig).elim
  have hf2 : eligible p.sub2 = false := by
    cases hElig : eligible p.sub2 with
    | false => rfl
    | true => exact (h.2 hElig).elim
  have hZero := parallelPayout_zero_when_ineligible cap1 cap2 p hf1 hf2
  omega

/-! ## Series Composition Theorems -/

/-- **Series Payout Bounded by Cap**: the series payout is bounded by the
shared cap (not the sum), because only one branch fires. -/
theorem seriesPayout_le_cap
    {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (cap : Nat) (p : SeriesComposite S₁ S₂) :
    seriesPayout cap p ≤ cap := by
  unfold seriesPayout
  by_cases h1 : eligible p.sub1
  · simp [h1]
    exact payout_le_cap cap p.sub1
  · simp [h1]
    exact payout_le_cap cap p.sub2

/-- **Series Payout Zero When Ineligible**: if both submissions are
ineligible, the series payout is zero. -/
theorem seriesPayout_zero_when_ineligible
    {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (cap : Nat) (p : SeriesComposite S₁ S₂)
    (h1 : eligible p.sub1 = false) (h2 : eligible p.sub2 = false) :
    seriesPayout cap p = 0 := by
  unfold seriesPayout
  simp [h1]
  exact payout_zero_when_ineligible cap p.sub2 h2

/-- **Series Positive Payout Implies Eligible**: if the series payout is
positive, at least one submission is eligible. -/
theorem series_positive_implies_eligible
    {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (cap : Nat) (p : SeriesComposite S₁ S₂)
    (hPos : 0 < seriesPayout cap p) :
    eligible p.sub1 = true ∨ eligible p.sub2 = true := by
  by_contra h
  push_neg at h
  have hf1 : eligible p.sub1 = false := by
    cases hElig : eligible p.sub1 with
    | false => rfl
    | true => exact (h.1 hElig).elim
  have hf2 : eligible p.sub2 = false := by
    cases hElig : eligible p.sub2 with
    | false => rfl
    | true => exact (h.2 hElig).elim
  have hZero := seriesPayout_zero_when_ineligible cap p hf1 hf2
  omega

/-! ## Counterexample Beats Proof -/

/-- **Counterexample Wins When Proof Not Eligible**: in the series
composition where `M₁` is the proof mechanism and `M₂` is the
counterexample mechanism, if the proof is ineligible, the counterexample
fires. This formalizes the spec's `counterexample beats proof` reward
mode.

The equality `seriesPayout cap p = payout cap p.sub2` holds unconditionally
given the eligibility assumptions. Positivity of the counterexample payout
requires `cap > 0` and is stated as a separate theorem below. -/
theorem counterexample_wins_when_proof_not_eligible
    {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (cap : Nat) (p : SeriesComposite S₁ S₂)
    (_hProofIneligible : eligible p.sub1 = false)
    (_hCounterEligible : eligible p.sub2 = true) :
    seriesPayout cap p = payout cap p.sub2 := by
  unfold seriesPayout
  simp [_hProofIneligible]

/-- **Counterexample Payout Positive When Cap Positive**: if the
counterexample is eligible and the cap is positive, the payout is positive.
This requires the additional `BountyMechanism` axiom that eligible
submissions with positive cap receive positive payout.

`_hCapPos` is a semantic precondition for the `hPositiveEligible` axiom:
the axiom is only meaningful when `cap > 0` (otherwise `payout 0 s = 0`
for all `s`). The proof itself derives positivity from `hPositiveEligible`. -/
theorem counterexample_payout_positive
    {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (cap : Nat) (p : SeriesComposite S₁ S₂)
    (_hCapPos : 0 < cap)
    (hProofIneligible : eligible p.sub1 = false)
    (hCounterEligible : eligible p.sub2 = true)
    (hPositiveEligible : ∀ s : S₂, eligible s = true → 0 < payout cap s) :
    0 < seriesPayout cap p := by
  rw [counterexample_wins_when_proof_not_eligible cap p hProofIneligible hCounterEligible]
  exact hPositiveEligible p.sub2 hCounterEligible

/-- **Proof Wins When Eligible**: dual case. If the proof is eligible,
the proof fires and the counterexample does not. -/
theorem proof_wins_when_eligible
    {S₁ S₂ : Type} [BountyMechanism S₁] [BountyMechanism S₂]
    (cap : Nat) (p : SeriesComposite S₁ S₂)
    (hProofEligible : eligible p.sub1 = true) :
    seriesPayout cap p = payout cap p.sub1 := by
  unfold seriesPayout
  simp [hProofEligible]

/-! ## Concrete Instances and Witnesses -/

/-- Simple submission type for witnesses. -/
structure SimpleSubmission where
  valid : Bool
  claimed : Nat

instance : BountyMechanism SimpleSubmission where
  eligible s := s.valid
  payout cap s := if s.valid then min s.claimed cap else 0
  payout_zero_when_ineligible := by
    intro cap s hElig
    simp [hElig]
  payout_le_cap := by
    intro cap s
    by_cases hValid : s.valid
    · simp [hValid]
    · simp [hValid]

/-- Witness: parallel composition with two valid submissions.
cap1=100, cap2=200, sub1 claims 50, sub2 claims 150.
Payout = 50 + 150 = 200 ≤ 100 + 200 = 300. -/
theorem witness_parallel_both_valid :
    parallelPayout 100 200
      (ParallelComposite.mk ({ valid := true, claimed := 50 : SimpleSubmission })
        ({ valid := true, claimed := 150 : SimpleSubmission })) = 200 ∧
    parallelPayout 100 200
      (ParallelComposite.mk ({ valid := true, claimed := 50 : SimpleSubmission })
        ({ valid := true, claimed := 150 : SimpleSubmission })) ≤ 300 := by
  refine ⟨?_, ?_⟩
  · unfold parallelPayout payout
    simp
    decide
  · exact parallelPayout_le_sum_cap 100 200
      (ParallelComposite.mk ({ valid := true, claimed := 50 : SimpleSubmission })
        ({ valid := true, claimed := 150 : SimpleSubmission }))

/-- Witness: parallel composition with one invalid submission.
sub1 invalid (payout 0), sub2 valid (payout 150).
Payout = 0 + 150 = 150 ≤ 300. -/
theorem witness_parallel_one_invalid :
    parallelPayout 100 200
      (ParallelComposite.mk ({ valid := false, claimed := 50 : SimpleSubmission })
        ({ valid := true, claimed := 150 : SimpleSubmission })) = 150 := by
  unfold parallelPayout payout
  simp
  decide

/-- Witness: series composition, proof eligible.
sub1 valid (proof), sub2 valid (counterexample).
Series pays sub1: payout = min 50 100 = 50. -/
theorem witness_series_proof_eligible :
    seriesPayout 100
      (SeriesComposite.mk ({ valid := true, claimed := 50 : SimpleSubmission })
        ({ valid := true, claimed := 150 : SimpleSubmission })) = 50 := by
  unfold seriesPayout payout
  simp
  decide

/-- Witness: series composition, proof ineligible, counterexample eligible.
sub1 invalid (proof), sub2 valid (counterexample).
Series pays sub2: payout = min 150 100 = 100. -/
theorem witness_series_counterexample_wins :
    seriesPayout 100
      (SeriesComposite.mk ({ valid := false, claimed := 50 : SimpleSubmission })
        ({ valid := true, claimed := 150 : SimpleSubmission })) = 100 := by
  unfold seriesPayout payout
  simp
  decide

end ZenoProofMechanismComposition
end Internal
