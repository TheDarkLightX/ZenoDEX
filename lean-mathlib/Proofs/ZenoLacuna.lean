import Mathlib.Data.Finset.Basic

/-!
# Finite question identifiability and exact sequential filtering

`C` denotes semantic classes supplied by a fixed, correct quotient. Questions
have total deterministic answers. The operational filter consumes an explicit
finite transcript; it keeps exactly the original classes compatible with every
answer. Pair separation is equivalent both to injective complete answer
signatures and to singleton recovery after a complete faithful transcript.

An indistinguishable pair survives every finite sequence drawn from its question
language, including repeated or reordered questions. Concrete three-class
examples distinguish the two-question language from its inadequate first question.

These statements do not verify the Python quotient, its encodings, owner
authentication, runtime correspondence, Bellman optimality, or closure checker.
-/

namespace ZenoLacuna

universe u v w

variable {C : Type u} {Q : Type v} {A : Type w}
variable [DecidableEq A]

/-- Execute the finite transcript by filtering after each individual answer. -/
def filterAnswers (answer : Q → C → A) : Finset C → List (Q × A) → Finset C
  | candidates, [] => candidates
  | candidates, (q, a) :: rest =>
      filterAnswers answer (candidates.filter (fun h => answer q h = a)) rest

/-- Sequential filtering retains exactly the original transcript-compatible classes. -/
theorem mem_filterAnswers (answer : Q → C → A) (candidates : Finset C)
    (transcript : List (Q × A)) (h : C) :
    h ∈ filterAnswers answer candidates transcript ↔
      h ∈ candidates ∧ ∀ entry ∈ transcript, answer entry.1 h = entry.2 := by
  induction transcript generalizing candidates with
  | nil => simp [filterAnswers]
  | cons entry rest ih =>
      rcases entry with ⟨q, a⟩
      simp [filterAnswers, ih, and_assoc]

/-- The complete signature includes every question in its stated order. -/
def signature (answer : Q → C → A) (questions : List Q) (h : C) : List A :=
  questions.map (fun q => answer q h)

/-- Every distinct candidate pair has a question with differing answers. -/
def Separates (answer : Q → C → A) (questions : List Q) (candidates : Finset C) : Prop :=
  ∀ x ∈ candidates, ∀ y ∈ candidates, x ≠ y →
    ∃ q ∈ questions, answer q x ≠ answer q y

/-- Pair separation is precisely injectivity of complete signatures on the candidate set. -/
theorem separates_iff_signature_unique (answer : Q → C → A)
    (questions : List Q) (candidates : Finset C) :
    Separates answer questions candidates ↔
      ∀ x ∈ candidates, ∀ y ∈ candidates,
        signature answer questions x = signature answer questions y → x = y := by
  classical
  constructor
  · intro separated x hx y hy same
    by_contra different
    obtain ⟨q, hq, unequal⟩ := separated x hx y hy different
    exact unequal ((List.map_inj_left.mp same) q hq)
  · intro unique x hx y hy different
    by_contra noSeparator
    apply different
    apply unique x hx y hy
    apply List.map_congr_left
    intro q hq
    by_contra unequal
    exact noSeparator ⟨q, hq, unequal⟩

/-- The owner answers each question according to a fixed intended class. -/
def filterQuestions (answer : Q → C → A) (truth : C)
    (candidates : Finset C) (questions : List Q) : Finset C :=
  filterAnswers answer candidates (questions.map (fun q => (q, answer q truth)))

/-- Faithful sequential execution has the complete-signature fiber as its exact result. -/
theorem mem_filterQuestions (answer : Q → C → A) (truth : C)
    (candidates : Finset C) (questions : List Q) (h : C) :
    h ∈ filterQuestions answer truth candidates questions ↔
      h ∈ candidates ∧ signature answer questions h = signature answer questions truth := by
  simp [filterQuestions, mem_filterAnswers, signature, List.map_inj_left]

/-- A faithful transcript never removes an intended class present initially. -/
theorem faithful_truth_survives (answer : Q → C → A) (truth : C)
    (candidates : Finset C) (questions : List Q) (included : truth ∈ candidates) :
    truth ∈ filterQuestions answer truth candidates questions := by
  exact (mem_filterQuestions answer truth candidates questions truth).mpr ⟨included, rfl⟩

/-- Asking every question of a separating language faithfully recovers exactly the truth. -/
theorem complete_faithful_filter_singleton (answer : Q → C → A) (truth : C)
    (candidates : Finset C) (questions : List Q)
    (included : truth ∈ candidates) (separated : Separates answer questions candidates) :
    filterQuestions answer truth candidates questions = {truth} := by
  ext h
  rw [mem_filterQuestions, Finset.mem_singleton]
  constructor
  · intro compatible
    exact (separates_iff_signature_unique answer questions candidates).mp separated
      h compatible.1 truth included compatible.2
  · intro equal
    subst h
    exact ⟨included, rfl⟩

/-- Universal singleton recovery after all questions is also necessary for separation. -/
theorem separates_iff_complete_filter_singleton (answer : Q → C → A)
    (candidates : Finset C) (questions : List Q) :
    Separates answer questions candidates ↔
      ∀ truth ∈ candidates, filterQuestions answer truth candidates questions = {truth} := by
  constructor
  · intro separated truth included
    exact complete_faithful_filter_singleton answer truth candidates questions included separated
  · intro singletons
    apply (separates_iff_signature_unique answer questions candidates).mpr
    intro x hx y hy same
    have survives := (mem_filterQuestions answer y candidates questions x).mpr ⟨hx, same⟩
    rw [singletons y hy, Finset.mem_singleton] at survives
    exact survives

/-- Indistinguishability on a language persists along any finite sequence from it. -/
theorem indistinguishable_pair_survives (answer : Q → C → A)
    (candidates : Finset C) (language asked : List Q) (x y : C)
    (hx : x ∈ candidates) (hy : y ∈ candidates)
    (same : signature answer language x = signature answer language y)
    (withinLanguage : ∀ q ∈ asked, q ∈ language) :
    x ∈ filterQuestions answer x candidates asked ∧
      y ∈ filterQuestions answer x candidates asked := by
  constructor
  · exact faithful_truth_survives answer x candidates asked hx
  · apply (mem_filterQuestions answer x candidates asked y).mpr
    constructor
    · exact hy
    · apply List.map_congr_left
      intro q hq
      exact ((List.map_inj_left.mp same) q (withinLanguage q hq)).symm

/-- An indistinguishable distinct pair rules out singleton identification on every such sequence. -/
theorem indistinguishable_pair_prevents_singleton (answer : Q → C → A)
    (candidates : Finset C) (language asked : List Q) (x y : C)
    (hx : x ∈ candidates) (hy : y ∈ candidates) (different : x ≠ y)
    (same : signature answer language x = signature answer language y)
    (withinLanguage : ∀ q ∈ asked, q ∈ language) :
    ∀ only, filterQuestions answer x candidates asked ≠ {only} := by
  obtain ⟨xSurvives, ySurvives⟩ :=
    indistinguishable_pair_survives answer candidates language asked x y hx hy same withinLanguage
  intro only singleton
  rw [singleton, Finset.mem_singleton] at xSurvives ySurvives
  exact different (xSurvives.trans ySurvives.symm)

/-- false is qA=(0,1,1); true is qB=(0,0,1), using Boolean answer tokens. -/
def demoAnswer (q : Bool) (h : Fin 3) : Bool :=
  if q then decide (2 ≤ h.val) else decide (1 ≤ h.val)

theorem demo_two_questions_separate :
    Separates demoAnswer [false, true] ({0, 1, 2} : Finset (Fin 3)) := by
  unfold Separates
  decide

theorem demo_complete_filter_recovers_each_class (truth : Fin 3) :
    filterQuestions demoAnswer truth {0, 1, 2} [false, true] = {truth} := by
  apply complete_faithful_filter_singleton
  · exact (by decide : ∀ t : Fin 3, t ∈ ({0, 1, 2} : Finset (Fin 3))) truth
  · exact demo_two_questions_separate

theorem demo_sole_question_does_not_separate :
    ¬Separates demoAnswer [false] ({0, 1, 2} : Finset (Fin 3)) := by
  unfold Separates
  decide

/-- Repeating the useful first split cannot distinguish classes 1 and 2. -/
theorem demo_sole_question_never_identifies (asked : List Bool)
    (onlyFirst : ∀ q ∈ asked, q = false) :
    ∀ only, filterQuestions demoAnswer 1 ({0, 1, 2} : Finset (Fin 3)) asked ≠ {only} := by
  apply indistinguishable_pair_prevents_singleton demoAnswer {0, 1, 2} [false] asked 1 2
  · decide
  · decide
  · decide
  · rfl
  · intro q hq
    simp [onlyFirst q hq]

#print axioms mem_filterAnswers
#print axioms separates_iff_signature_unique
#print axioms mem_filterQuestions
#print axioms faithful_truth_survives
#print axioms complete_faithful_filter_singleton
#print axioms separates_iff_complete_filter_singleton
#print axioms indistinguishable_pair_survives
#print axioms indistinguishable_pair_prevents_singleton
#print axioms demo_two_questions_separate
#print axioms demo_complete_filter_recovers_each_class
#print axioms demo_sole_question_does_not_separate
#print axioms demo_sole_question_never_identifies

end ZenoLacuna
