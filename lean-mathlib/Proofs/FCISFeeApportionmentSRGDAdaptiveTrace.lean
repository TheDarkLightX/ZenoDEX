import Proofs.FCISFeeApportionmentSRGDTrace

namespace FCISFeeApportionmentSRGDAdaptiveTrace

open FCISFeeApportionmentSRGD
open FCISFeeApportionmentSRGDTrace

/-- A typed policy witness bound to the denominator used by an occurrence. -/
structure AuthenticatedPolicy (D : Int) where
  policyRoot : Int
  denominator : Int
  denominator_eq : denominator = D
  denominator_positive : 0 < denominator

/-- One ordered SRGD occurrence, carrying its policy witness. -/
structure AuthenticatedOccurrence (D : Int) where
  policy : AuthenticatedPolicy D
  fraction0 : Int
  fraction1 : Int
  fraction2 : Int
  bonus0 : Int
  bonus1 : Int
  bonus2 : Int

/-- The three-coordinate signed-deficit state. -/
structure DeficitState where
  d0 : Int
  d1 : Int
  d2 : Int

/-- The invariant required at every prefix of an ordered occurrence word. -/
def stateValid (D : Int) (state : DeficitState) : Prop :=
  0 < D ∧
    state.d0 + state.d1 + state.d2 = 0 ∧
    -D < state.d0 ∧ state.d0 < D ∧
    -D < state.d1 ∧ state.d1 < D ∧
    -D < state.d2 ∧ state.d2 < D

/-- A policy and its occurrence data satisfy the exact SRGD one-step relation. -/
def occurrenceValid
    (D : Int)
    (state : DeficitState)
    (occurrence : AuthenticatedOccurrence D) : Prop :=
  occurrence.policy.denominator = D ∧
    0 ≤ occurrence.fraction0 ∧ occurrence.fraction0 < D ∧
    0 ≤ occurrence.fraction1 ∧ occurrence.fraction1 < D ∧
    0 ≤ occurrence.fraction2 ∧ occurrence.fraction2 < D ∧
    SRGDBonusRel D state.d0 state.d1 state.d2
      occurrence.fraction0 occurrence.fraction1 occurrence.fraction2
      occurrence.bonus0 occurrence.bonus1 occurrence.bonus2

/-- Apply one occurrence to a state without flattening any segment boundary. -/
def applyOccurrence
    (D : Int)
    (state : DeficitState)
    (occurrence : AuthenticatedOccurrence D) : DeficitState :=
  { d0 := updateDeficit D state.d0 occurrence.fraction0 occurrence.bonus0
    d1 := updateDeficit D state.d1 occurrence.fraction1 occurrence.bonus1
    d2 := updateDeficit D state.d2 occurrence.fraction2 occurrence.bonus2 }

/-- Fold one ordered SLNF segment. -/
def foldSegment
    (D : Int)
    (segment : List (AuthenticatedOccurrence D))
    (state : DeficitState) : DeficitState :=
  segment.foldl (fun current occurrence => applyOccurrence D current occurrence) state

/-- Fold the ordered SLNF word as a list of segments. -/
def foldWord
    (D : Int)
    (word : List (List (AuthenticatedOccurrence D)))
    (state : DeficitState) : DeficitState :=
  word.foldl (fun current segment => foldSegment D segment current) state

/-- Typed validity for every occurrence in one ordered segment. -/
inductive ValidSegment
    (D : Int) : DeficitState → List (AuthenticatedOccurrence D) → Prop
  | nil (state : DeficitState) : ValidSegment D state []
  | cons
      (state : DeficitState)
      (occurrence : AuthenticatedOccurrence D)
      (rest : List (AuthenticatedOccurrence D))
      (headValid : occurrenceValid D state occurrence)
      (tailValid : ValidSegment D (applyOccurrence D state occurrence) rest) :
      ValidSegment D state (occurrence :: rest)

/-- Typed validity for an ordered word of segments. -/
inductive ValidWord
    (D : Int) : DeficitState → List (List (AuthenticatedOccurrence D)) → Prop
  | nil (state : DeficitState) : ValidWord D state []
  | cons
      (state : DeficitState)
      (segment : List (AuthenticatedOccurrence D))
      (rest : List (List (AuthenticatedOccurrence D)))
      (segmentValid : ValidSegment D state segment)
      (restValid : ValidWord D (foldSegment D segment state) rest) :
      ValidWord D state (segment :: rest)

/-- One authenticated SRGD occurrence preserves the prefix invariant. -/
theorem one_occurrence_preserves_state
    (D : Int)
    (state : DeficitState)
    (occurrence : AuthenticatedOccurrence D)
    (hState : stateValid D state)
    (hOccurrence : occurrenceValid D state occurrence) :
    stateValid D (applyOccurrence D state occurrence) := by
  unfold stateValid at hState ⊢
  unfold occurrenceValid at hOccurrence
  unfold applyOccurrence
  rcases hState with ⟨hD, hSum, h0Lo, h0Hi, h1Lo, h1Hi, h2Lo, h2Hi⟩
  rcases hOccurrence with
    ⟨hPolicyEq, hf0Lo, hf0Hi, hf1Lo, hf1Hi, hf2Lo, hf2Hi, hBonus⟩
  have hPolicyD : 0 < D := by
    exact hPolicyEq ▸ occurrence.policy.denominator_positive
  have hStep := step_preserves_strict_deficit
    D state.d0 state.d1 state.d2
    occurrence.fraction0 occurrence.fraction1 occurrence.fraction2
    occurrence.bonus0 occurrence.bonus1 occurrence.bonus2
    hPolicyD hSum h0Lo h0Hi h1Lo h1Hi h2Lo h2Hi
    hf0Lo hf0Hi hf1Lo hf1Hi hf2Lo hf2Hi hBonus
  rcases hStep with ⟨hSum', h0Lo', h0Hi', h1Lo', h1Hi', h2Lo', h2Hi'⟩
  exact ⟨hPolicyD, hSum', h0Lo', h0Hi', h1Lo', h1Hi', h2Lo', h2Hi'⟩

/-- Every valid occurrence in a segment preserves the state invariant. -/
theorem valid_segment_preserves_state
    (D : Int)
    (state : DeficitState)
    (segment : List (AuthenticatedOccurrence D))
    (hState : stateValid D state)
    (hSegment : ValidSegment D state segment) :
    stateValid D (foldSegment D segment state) := by
  induction hSegment with
  | nil state =>
      exact hState
  | @cons state occurrence rest headValid tailValid ih =>
      have hNext := one_occurrence_preserves_state D state occurrence hState headValid
      exact ih hNext

/-- Every finite ordered SLNF word preserves every prefix invariant. -/
theorem valid_word_preserves_state
    (D : Int)
    (state : DeficitState)
    (word : List (List (AuthenticatedOccurrence D)))
    (hState : stateValid D state)
    (hWord : ValidWord D state word) :
    stateValid D (foldWord D word state) := by
  induction hWord with
  | nil state =>
      exact hState
  | @cons state segment rest segmentValid restValid ih =>
      have hAfterSegment :=
        valid_segment_preserves_state D state segment hState segmentValid
      exact ih hAfterSegment

end FCISFeeApportionmentSRGDAdaptiveTrace
