import Mathlib.Tactic

/-!
# k-Pool Multiset DP Identity Quotient

This file formalizes the proof skeleton behind the k-pool multiset DP research
oracle. The modeled router transition may depend on:

- the current abstract state;
- the exact-in amount;
- the chosen k-way allocation.

It may not depend on the identity of the intent. Under that interface, replacing
duplicate equal-amount intent identities with per-amount counts preserves the
reachable state/value trace for any fixed `(amount, allocation)` sequence.

This is a proof component for the research oracle only. It does not formalize
CPMM reserves, feasibility, per-user balances, heterogeneous `min_out`, exact-out
requests, or production settlement authority.
-/

namespace Proofs
namespace KPoolMultisetQuotient

/-- A routed step includes identity metadata plus the data that the modeled
transition is allowed to inspect. -/
structure RoutedStep (Alloc : Type) where
  intentId : Nat
  amount : Nat
  allocation : Alloc
  deriving Repr, DecidableEq

/-- The identity-free key used by the quotient proof. -/
def stepKey {Alloc : Type} (step : RoutedStep Alloc) : Nat × Alloc :=
  (step.amount, step.allocation)

/-- Position-wise equality of the identity-free routed trace. -/
def SameStepKeys {Alloc : Type} : List (RoutedStep Alloc) → List (RoutedStep Alloc) → Prop
  | [], [] => True
  | x :: xs, y :: ys => stepKey x = stepKey y ∧ SameStepKeys xs ys
  | _, _ => False

/-- Run an abstract amount/allocation-only transition and accumulate an abstract
reward. The step identity is deliberately ignored. -/
def runTrace {State Alloc : Type}
    (next : State → Nat → Alloc → State)
    (reward : State → Nat → Alloc → Nat) :
    State → List (RoutedStep Alloc) → State × Nat
  | state, [] => (state, 0)
  | state, step :: rest =>
      let gained := reward state step.amount step.allocation
      let nextState := next state step.amount step.allocation
      let tail := runTrace next reward nextState rest
      (tail.1, gained + tail.2)

/-- If two traces have the same `(amount, allocation)` sequence, the abstract
router run returns the same final state and accumulated reward. -/
theorem runTrace_congr_sameStepKeys
    {State Alloc : Type}
    (next : State → Nat → Alloc → State)
    (reward : State → Nat → Alloc → Nat)
    {xs ys : List (RoutedStep Alloc)}
    (h : SameStepKeys xs ys)
    (state : State) :
    runTrace next reward state xs = runTrace next reward state ys := by
  induction xs generalizing ys state with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => simp [SameStepKeys] at h
  | cons x xs ih =>
      cases ys with
      | nil => simp [SameStepKeys] at h
      | cons y ys =>
          rcases h with ⟨hxy, htail⟩
          have hAmount : x.amount = y.amount := congrArg Prod.fst hxy
          have hAllocation : x.allocation = y.allocation := congrArg Prod.snd hxy
          simp [runTrace, hAmount, hAllocation, ih htail]

/-- Swapping only the identities of two equal-amount adjacent routed steps
preserves the abstract run. The allocation positions are unchanged. -/
theorem equalAmount_identity_swap
    {State Alloc : Type}
    (next : State → Nat → Alloc → State)
    (reward : State → Nat → Alloc → Nat)
    (state : State)
    (idA idB amount : Nat)
    (allocA allocB : Alloc) :
    runTrace next reward state
        [⟨idA, amount, allocA⟩, ⟨idB, amount, allocB⟩] =
      runTrace next reward state
        [⟨idB, amount, allocA⟩, ⟨idA, amount, allocB⟩] := by
  apply runTrace_congr_sameStepKeys
  simp [SameStepKeys, stepKey]

/-- Identity changes over an entire trace preserve the abstract run when the
amount/allocation trace is unchanged. -/
theorem identityErasure_preserves_trace
    {State Alloc : Type}
    (next : State → Nat → Alloc → State)
    (reward : State → Nat → Alloc → Nat)
    (state : State)
    {xs ys : List (RoutedStep Alloc)}
    (h : SameStepKeys xs ys) :
    (runTrace next reward state xs).1 = (runTrace next reward state ys).1 ∧
      (runTrace next reward state xs).2 = (runTrace next reward state ys).2 := by
  have hrun := runTrace_congr_sameStepKeys next reward h state
  constructor
  · exact congrArg Prod.fst hrun
  · exact congrArg Prod.snd hrun

/-! ## Non-vacuity witnesses -/

def witnessNext (state amount allocation : Nat) : Nat :=
  state + amount + allocation

def witnessReward (state amount allocation : Nat) : Nat :=
  state + amount * 2 + allocation

/-- Concrete witness: equal-amount identity swap leaves the amount/allocation
run unchanged. -/
theorem witness_equalAmount_identity_swap :
    runTrace witnessNext witnessReward 7 [⟨1, 4, 2⟩, ⟨2, 4, 3⟩] =
      runTrace witnessNext witnessReward 7 [⟨2, 4, 2⟩, ⟨1, 4, 3⟩] ∧
    runTrace witnessNext witnessReward 7 [⟨1, 4, 2⟩, ⟨2, 4, 3⟩] = (20, 41) := by
  native_decide

/-- Boundary witness: allocation position is load-bearing. The quotient erases
intent identity, not the chosen allocation sequence. -/
theorem witness_allocation_position_matters :
    runTrace witnessNext witnessReward 7 [⟨1, 4, 2⟩, ⟨2, 4, 3⟩] ≠
      runTrace witnessNext witnessReward 7 [⟨2, 4, 3⟩, ⟨1, 4, 2⟩] := by
  native_decide

end KPoolMultisetQuotient
end Proofs
