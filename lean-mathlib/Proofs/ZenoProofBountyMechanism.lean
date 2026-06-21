import Mathlib

/-!
# ZenoProof Bounty Mechanism Typeclass

## Motivation

`lean-mathlib/Proofs/BountyAuctionMechanisms.lean` defines six bounty types
(fixed, best-artifact, counterexample, retroactive, challenge-priority,
two-award) and proves the same shape of safety lemma per type:
`positive_payout_implies_eligible`, `payout_le_cap`. Each new bounty mechanism
repeats the same boilerplate. The proof debt is linear in mechanism count.

## Proposal

A `class BountyMechanism (S : Type)` with three required fields:
- `eligible : S → Bool`
- `payout : Nat → S → Nat`
- `payout_zero_when_ineligible : ∀ cap s, eligible s = false → payout cap s = 0`
- `payout_le_cap : ∀ cap s, payout cap s ≤ cap`

Two generic theorems are proved once:
- `positive_payout_implies_eligible` (subsumes four concrete safety lemmas)
- `two_task_budget_bound` (subsumes the multi-award composition lemmas)

Plus a list-shaped budget bound `list_budget_bound : sum of payouts ≤ cap × n`.

## Scope

Typeclass-based generic safety. Does not address Sybil resistance (see
`ZenoProofSybilBondBound.lean`), composition (see
`ZenoProofMechanismComposition.lean`), or Bayesian equilibrium.
-/

namespace Internal
namespace ZenoProofBountyMechanism

/-- A bounty mechanism is a typeclass capturing the common safety structure:
eligibility, payout, and two axioms (zero payout when ineligible, payout
bounded by cap). -/
class BountyMechanism (S : Type) where
  /-- Eligibility predicate: is this submission eligible for a payout? -/
  eligible : S → Bool
  /-- Payout amount: how much does this submission receive, given a cap? -/
  payout : Nat → S → Nat
  /-- Axiom 1: ineligible submissions receive zero payout. -/
  payout_zero_when_ineligible : ∀ cap s, eligible s = false → payout cap s = 0
  /-- Axiom 2: payout never exceeds the cap. -/
  payout_le_cap : ∀ cap s, payout cap s ≤ cap

open BountyMechanism

/-- **Positive Payout Implies Eligible**: if `payout cap s > 0`, then
`eligible s = true`. This is the contrapositive of
`payout_zero_when_ineligible` and subsumes the per-type safety lemmas
in `BountyAuctionMechanisms.lean`. -/
theorem positive_payout_implies_eligible
    {S : Type} [BountyMechanism S] (cap : Nat) (s : S)
    (hPos : 0 < payout cap s) :
    eligible s = true := by
  cases hElig : eligible s with
  | true => exact rfl
  | false =>
    have hZero : payout cap s = 0 :=
      payout_zero_when_ineligible cap s hElig
    omega

/-- **Payout Bounded by Cap**: `payout cap s ≤ cap` for any submission.
This is the second axiom, restated as a theorem for the public API. -/
theorem payout_bounded_by_cap
    {S : Type} [BountyMechanism S] (cap : Nat) (s : S) :
    payout cap s ≤ cap :=
  payout_le_cap cap s

/-- **Two-Task Budget Bound**: for two submissions `s₁` and `s₂` with a
shared cap, the total payout is bounded by `2 * cap`. -/
theorem two_task_budget_bound
    {S : Type} [BountyMechanism S] (cap : Nat) (s₁ s₂ : S) :
    payout cap s₁ + payout cap s₂ ≤ 2 * cap := by
  have h1 : payout cap s₁ ≤ cap := payout_le_cap cap s₁
  have h2 : payout cap s₂ ≤ cap := payout_le_cap cap s₂
  omega

/-- **List Budget Bound**: for a list of `n` submissions with a shared cap,
the total payout is bounded by `n * cap`. -/
theorem list_budget_bound
    {S : Type} [BountyMechanism S] (cap : Nat) (submissions : List S) :
    (submissions.map (payout cap)).sum ≤ submissions.length * cap := by
  induction submissions with
  | nil => simp
  | cons s rest ih =>
    simp [List.map_cons, List.sum_cons]
    have hPayout : payout cap s ≤ cap := payout_le_cap cap s
    have hRest : (rest.map (payout cap)).sum ≤ rest.length * cap := ih
    have : payout cap s + (rest.map (payout cap)).sum ≤
           cap + rest.length * cap := by
      omega
    have : cap + rest.length * cap = (rest.length + 1) * cap := by ring
    omega

/-! ## Concrete Instance: Fixed Bounty

A simple `Submission` type where eligible submissions receive a fixed
payout (capped), and ineligible submissions receive zero. -/
structure Submission where
  /-- Is this submission valid? -/
  valid : Bool
  /-- Claimed payout amount (before cap). -/
  claimed : Nat

instance : BountyMechanism Submission where
  eligible s := s.valid
  payout cap s := if s.valid then min s.claimed cap else 0
  payout_zero_when_ineligible := by
    intro cap s hElig
    simp [hElig]
  payout_le_cap := by
    intro cap s
    by_cases hValid : s.valid
    · rw [if_pos hValid]; exact Nat.min_le_right _ _
    · rw [if_neg hValid]; exact Nat.zero_le _

/-- **Fixed Bounty Safety**: for a valid submission, payout is bounded
by the cap. For an invalid submission, payout is zero. -/
theorem fixed_bounty_safety (cap : Nat) (s : Submission) :
    payout cap s ≤ cap :=
  payout_le_cap cap s

/-- **Fixed Bounty Eligibility**: a positive payout implies the submission
is valid. -/
theorem fixed_bounty_positive_implies_valid (cap : Nat) (s : Submission)
    (hPos : 0 < payout cap s) :
    s.valid = true :=
  positive_payout_implies_eligible cap s hPos

/-! ## Non-Vacuity Witnesses -/

/-- Witness: a valid submission with claimed=50, cap=100 receives payout=50. -/
theorem witness_valid_submission_payout :
    payout 100 (Submission.mk true 50) = 50 := by
  show (if (Submission.mk true 50).valid then min (Submission.mk true 50).claimed 100 else 0) = 50
  rfl

/-- Witness: an invalid submission receives payout=0. -/
theorem witness_invalid_submission_zero :
    payout 100 (Submission.mk false 50) = 0 := by
  show (if (Submission.mk false 50).valid then min (Submission.mk false 50).claimed 100 else 0) = 0
  rfl

/-- Witness: a valid submission with claimed=150, cap=100 receives payout=100
(capped). -/
theorem witness_capped_payout :
    payout 100 (Submission.mk true 150) = 100 := by
  show (if (Submission.mk true 150).valid then min (Submission.mk true 150).claimed 100 else 0) = 100
  rfl

/-- Witness: two valid submissions with cap=100 have total payout ≤ 200. -/
theorem witness_two_task_bound :
    payout 100 (Submission.mk true 50) + payout 100 (Submission.mk true 60) ≤ 200 :=
  two_task_budget_bound 100 (Submission.mk true 50) (Submission.mk true 60)

end ZenoProofBountyMechanism
end Internal
