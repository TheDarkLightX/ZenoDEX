import Proofs.FCISFeeApportionmentSRGDAdaptiveTrace
import Proofs.FCISFeeApportionmentAGQESRGDRefinement

namespace FCISFeeApportionmentAGQESRGDTraceConjugacy

open FCISFeeApportionmentSRGD
open FCISFeeApportionmentAGQESRGDRefinement
open FCISFeeApportionmentSRGDAdaptiveTrace

/- The shared carrier makes the sign dual a genuine involution. -/
structure SignedState where
  c0 : Int
  c1 : Int
  c2 : Int

def phiState (state : SignedState) : SignedState :=
  { c0 := -state.c0, c1 := -state.c1, c2 := -state.c2 }

theorem phi_state_involution (state : SignedState) :
    phiState (phiState state) = state := by
  cases state
  simp [phiState]

/- A key is carried through the representation change unchanged. -/
structure TraceKey where
  feeDomain : Int
  asset : Int
  semanticProfile : Int
  fixedRoleOrder : Int

structure KeyedState where
  key : TraceKey
  state : SignedState

def phiKeyedState (value : KeyedState) : KeyedState :=
  { key := value.key, state := phiState value.state }

theorem phi_keyed_state_key_preserved (value : KeyedState) :
    (phiKeyedState value).key = value.key := by
  rfl

theorem phi_keyed_state_involution (value : KeyedState) :
    phiKeyedState (phiKeyedState value) = value := by
  cases value with
  | mk key state =>
      simp [phiKeyedState, phiState]

def applySRGD
    (D : Int)
    (state : SignedState)
    (occurrence : AuthenticatedOccurrence D) : SignedState :=
  { c0 := updateDeficit D state.c0 occurrence.fraction0 occurrence.bonus0
    c1 := updateDeficit D state.c1 occurrence.fraction1 occurrence.bonus1
    c2 := updateDeficit D state.c2 occurrence.fraction2 occurrence.bonus2 }

def applyAGQE
    (D : Int)
    (state : SignedState)
    (occurrence : AuthenticatedOccurrence D) : SignedState :=
  { c0 := updateSurplus D state.c0 occurrence.fraction0 occurrence.bonus0
    c1 := updateSurplus D state.c1 occurrence.fraction1 occurrence.bonus1
    c2 := updateSurplus D state.c2 occurrence.fraction2 occurrence.bonus2 }

def foldSRGD
    (D : Int)
    (segment : List (AuthenticatedOccurrence D))
    (state : SignedState) : SignedState :=
  segment.foldl (fun current occurrence => applySRGD D current occurrence) state

def foldAGQE
    (D : Int)
    (segment : List (AuthenticatedOccurrence D))
    (state : SignedState) : SignedState :=
  segment.foldl (fun current occurrence => applyAGQE D current occurrence) state

def foldSRGDWord
    (D : Int)
    (word : List (List (AuthenticatedOccurrence D)))
    (state : SignedState) : SignedState :=
  word.foldl (fun current segment => foldSRGD D segment current) state

def foldAGQEWord
    (D : Int)
    (word : List (List (AuthenticatedOccurrence D)))
    (state : SignedState) : SignedState :=
  word.foldl (fun current segment => foldAGQE D segment current) state

def srgdOccurrenceValid
    (D : Int)
    (state : SignedState)
    (occurrence : AuthenticatedOccurrence D) : Prop :=
  occurrence.policy.denominator = D ∧
    0 ≤ occurrence.fraction0 ∧ occurrence.fraction0 < D ∧
    0 ≤ occurrence.fraction1 ∧ occurrence.fraction1 < D ∧
    0 ≤ occurrence.fraction2 ∧ occurrence.fraction2 < D ∧
    SRGDBonusRel D state.c0 state.c1 state.c2
      occurrence.fraction0 occurrence.fraction1 occurrence.fraction2
      occurrence.bonus0 occurrence.bonus1 occurrence.bonus2

def agqeOccurrenceValid
    (D : Int)
    (state : SignedState)
    (occurrence : AuthenticatedOccurrence D) : Prop :=
  occurrence.policy.denominator = D ∧
    0 ≤ occurrence.fraction0 ∧ occurrence.fraction0 < D ∧
    0 ≤ occurrence.fraction1 ∧ occurrence.fraction1 < D ∧
    0 ≤ occurrence.fraction2 ∧ occurrence.fraction2 < D ∧
    AGQEBonusRel D state.c0 state.c1 state.c2
      occurrence.fraction0 occurrence.fraction1 occurrence.fraction2
      occurrence.bonus0 occurrence.bonus1 occurrence.bonus2

def stateValid
    (D : Int)
    (state : SignedState) : Prop :=
  0 < D ∧
    state.c0 + state.c1 + state.c2 = 0 ∧
    -D < state.c0 ∧ state.c0 < D ∧
    -D < state.c1 ∧ state.c1 < D ∧
    -D < state.c2 ∧ state.c2 < D

inductive ValidSRGDSegment
    (D : Int) : SignedState → List (AuthenticatedOccurrence D) → Prop
  | nil (state : SignedState) : ValidSRGDSegment D state []
  | cons
      (state : SignedState)
      (occurrence : AuthenticatedOccurrence D)
      (rest : List (AuthenticatedOccurrence D))
      (headValid : srgdOccurrenceValid D state occurrence)
      (tailValid : ValidSRGDSegment D (applySRGD D state occurrence) rest) :
      ValidSRGDSegment D state (occurrence :: rest)

inductive ValidAGQESegment
    (D : Int) : SignedState → List (AuthenticatedOccurrence D) → Prop
  | nil (state : SignedState) : ValidAGQESegment D state []
  | cons
      (state : SignedState)
      (occurrence : AuthenticatedOccurrence D)
      (rest : List (AuthenticatedOccurrence D))
      (headValid : agqeOccurrenceValid D state occurrence)
      (tailValid : ValidAGQESegment D (applyAGQE D state occurrence) rest) :
      ValidAGQESegment D state (occurrence :: rest)

inductive ValidSRGDWord
    (D : Int) : SignedState → List (List (AuthenticatedOccurrence D)) → Prop
  | nil (state : SignedState) : ValidSRGDWord D state []
  | cons
      (state : SignedState)
      (segment : List (AuthenticatedOccurrence D))
      (rest : List (List (AuthenticatedOccurrence D)))
      (segmentValid : ValidSRGDSegment D state segment)
      (restValid : ValidSRGDWord D (foldSRGD D segment state) rest) :
      ValidSRGDWord D state (segment :: rest)

inductive ValidAGQEWord
    (D : Int) : SignedState → List (List (AuthenticatedOccurrence D)) → Prop
  | nil (state : SignedState) : ValidAGQEWord D state []
  | cons
      (state : SignedState)
      (segment : List (AuthenticatedOccurrence D))
      (rest : List (List (AuthenticatedOccurrence D)))
      (segmentValid : ValidAGQESegment D state segment)
      (restValid : ValidAGQEWord D (foldAGQE D segment state) rest) :
      ValidAGQEWord D state (segment :: rest)

theorem state_valid_sign_dual
    (D : Int)
    (state : SignedState)
    (hState : stateValid D state) :
    stateValid D (phiState state) := by
  unfold stateValid at hState ⊢
  rcases hState with ⟨hD, hSum, h0Lo, h0Hi, h1Lo, h1Hi, h2Lo, h2Hi⟩
  simp [phiState]
  omega

theorem occurrence_valid_sign_dual
    (D : Int)
    (state : SignedState)
    (occurrence : AuthenticatedOccurrence D) :
    srgdOccurrenceValid D state occurrence ↔
      agqeOccurrenceValid D (phiState state) occurrence := by
  constructor
  · intro h
    rcases h with ⟨hPolicy, hf0Lo, hf0Hi, hf1Lo, hf1Hi, hf2Lo, hf2Hi, hBonus⟩
    refine ⟨hPolicy, hf0Lo, hf0Hi, hf1Lo, hf1Hi, hf2Lo, hf2Hi, ?_⟩
    exact (bonus_relation_sign_dual D state.c0 state.c1 state.c2
      occurrence.fraction0 occurrence.fraction1 occurrence.fraction2
      occurrence.bonus0 occurrence.bonus1 occurrence.bonus2).2 hBonus
  · intro h
    rcases h with ⟨hPolicy, hf0Lo, hf0Hi, hf1Lo, hf1Hi, hf2Lo, hf2Hi, hBonus⟩
    refine ⟨hPolicy, hf0Lo, hf0Hi, hf1Lo, hf1Hi, hf2Lo, hf2Hi, ?_⟩
    exact (bonus_relation_sign_dual D state.c0 state.c1 state.c2
      occurrence.fraction0 occurrence.fraction1 occurrence.fraction2
      occurrence.bonus0 occurrence.bonus1 occurrence.bonus2).1 hBonus

theorem one_step_sign_dual
    (D : Int)
    (state : SignedState)
    (occurrence : AuthenticatedOccurrence D) :
    phiState (applySRGD D state occurrence) =
      applyAGQE D (phiState state) occurrence := by
  cases state with
  | mk c0 c1 c2 =>
      simp only [phiState, applySRGD, applyAGQE]
      congr 1
      · exact (update_sign_dual D c0 occurrence.fraction0 occurrence.bonus0).symm
      · exact (update_sign_dual D c1 occurrence.fraction1 occurrence.bonus1).symm
      · exact (update_sign_dual D c2 occurrence.fraction2 occurrence.bonus2).symm

theorem fold_segment_sign_dual
    (D : Int)
    (segment : List (AuthenticatedOccurrence D))
    (state : SignedState) :
    phiState (foldSRGD D segment state) =
      foldAGQE D segment (phiState state) := by
  induction segment generalizing state with
  | nil =>
      rfl
  | cons occurrence rest ih =>
      change phiState (foldSRGD D rest (applySRGD D state occurrence)) =
        foldAGQE D rest (applyAGQE D (phiState state) occurrence)
      rw [← one_step_sign_dual D state occurrence]
      exact ih (applySRGD D state occurrence)

theorem fold_word_sign_dual
    (D : Int)
    (word : List (List (AuthenticatedOccurrence D)))
    (state : SignedState) :
    phiState (foldSRGDWord D word state) =
      foldAGQEWord D word (phiState state) := by
  induction word generalizing state with
  | nil =>
      rfl
  | cons segment rest ih =>
      change phiState (foldSRGDWord D rest (foldSRGD D segment state)) =
        foldAGQEWord D rest (foldAGQE D segment (phiState state))
      rw [← fold_segment_sign_dual D segment state]
      exact ih (foldSRGD D segment state)

theorem valid_srgd_segment_sign_dual
    (D : Int)
    (state : SignedState)
    (segment : List (AuthenticatedOccurrence D))
    (hSegment : ValidSRGDSegment D state segment) :
    ValidAGQESegment D (phiState state) segment := by
  induction hSegment with
  | nil state =>
      exact ValidAGQESegment.nil (phiState state)
  | @cons state occurrence rest headValid tailValid ih =>
      have hHead := (occurrence_valid_sign_dual D state occurrence).1 headValid
      have hTail := ih
      rw [one_step_sign_dual D state occurrence] at hTail
      exact ValidAGQESegment.cons (phiState state) occurrence rest hHead hTail

theorem valid_srgd_word_sign_dual
    (D : Int)
    (state : SignedState)
    (word : List (List (AuthenticatedOccurrence D)))
    (hWord : ValidSRGDWord D state word) :
    ValidAGQEWord D (phiState state) word := by
  induction hWord with
  | nil state =>
      exact ValidAGQEWord.nil (phiState state)
  | @cons state segment rest segmentValid restValid ih =>
      have hSegment := valid_srgd_segment_sign_dual D state segment segmentValid
      have hRest := ih
      rw [fold_segment_sign_dual D segment state] at hRest
      exact ValidAGQEWord.cons (phiState state) segment rest hSegment hRest

theorem trace_conjugacy
    (D : Int)
    (word : List (List (AuthenticatedOccurrence D)))
    (state : SignedState) :
    phiState (foldSRGDWord D word state) =
      foldAGQEWord D word (phiState state) := by
  exact fold_word_sign_dual D word state

end FCISFeeApportionmentAGQESRGDTraceConjugacy
