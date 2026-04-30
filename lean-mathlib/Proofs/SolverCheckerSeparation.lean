import Mathlib.Tactic

/-!
# Solver-Checker Separation Soundness

This file formalizes the small proof principle behind a runtime
solver/checker boundary.

If a checker accepts only spec-valid decisions, and a solver only emits
checker-accepted decisions, then every emitted solver decision is spec-valid.
The checker can be either an executable `Bool` checker or a semantic `Prop`
checker used while proving the executable checker correct.
-/

namespace Proofs
namespace SolverCheckerSeparation

variable {Input State Decision Witness : Type}

/-- A specification relates inputs and states to valid decisions. -/
abbrev Spec (Input State Decision : Type) :=
  Input → State → Decision → Prop

/-- A solver maps `(input, state)` to an optional `(decision, witness)` pair. -/
abbrev Solver (Input State Decision Witness : Type) :=
  Input → State → Option (Decision × Witness)

/-- An executable checker validates a `(decision, witness)` pair. -/
abbrev Checker (Input State Decision Witness : Type) :=
  Input → State → Decision → Witness → Bool

/-- A semantic checker validates a `(decision, witness)` pair in `Prop`. -/
abbrev PropChecker (Input State Decision Witness : Type) :=
  Input → State → Decision → Witness → Prop

/-- A Boolean checker is sound if every accepted decision satisfies the spec. -/
def CheckerSound
    (checker : Checker Input State Decision Witness)
    (spec : Spec Input State Decision) : Prop :=
  ∀ (i : Input) (s : State) (d : Decision) (w : Witness),
    checker i s d w = true → spec i s d

/-- A semantic checker is sound if every accepted decision satisfies the spec. -/
def PropCheckerSound
    (checker : PropChecker Input State Decision Witness)
    (spec : Spec Input State Decision) : Prop :=
  ∀ (i : Input) (s : State) (d : Decision) (w : Witness),
    checker i s d w → spec i s d

/-- A solver is accepted by a Boolean checker if every solver output is accepted. -/
def SolverAccepted
    (solver : Solver Input State Decision Witness)
    (checker : Checker Input State Decision Witness) : Prop :=
  ∀ (i : Input) (s : State) (d : Decision) (w : Witness),
    solver i s = some (d, w) → checker i s d w = true

/-- A solver is accepted by a semantic checker if every solver output is accepted. -/
def PropSolverAccepted
    (solver : Solver Input State Decision Witness)
    (checker : PropChecker Input State Decision Witness) : Prop :=
  ∀ (i : Input) (s : State) (d : Decision) (w : Witness),
    solver i s = some (d, w) → checker i s d w

/-- A solver is sound if every output satisfies the specification. -/
def SolverSound
    (solver : Solver Input State Decision Witness)
    (spec : Spec Input State Decision) : Prop :=
  ∀ (i : Input) (s : State) (d : Decision) (w : Witness),
    solver i s = some (d, w) → spec i s d

/-- Boolean solver-checker separation. -/
theorem solver_sound_of_checker_sound_and_solver_accepted
    (solver : Solver Input State Decision Witness)
    (checker : Checker Input State Decision Witness)
    (spec : Spec Input State Decision)
    (hCheckerSound : CheckerSound checker spec)
    (hSolverAccepted : SolverAccepted solver checker) :
    SolverSound solver spec := by
  intro i s d w hOut
  exact hCheckerSound i s d w (hSolverAccepted i s d w hOut)

/-- Semantic solver-checker separation. -/
theorem prop_solver_sound_of_checker_sound_and_solver_accepted
    (solver : Solver Input State Decision Witness)
    (checker : PropChecker Input State Decision Witness)
    (spec : Spec Input State Decision)
    (hCheckerSound : PropCheckerSound checker spec)
    (hSolverAccepted : PropSolverAccepted solver checker) :
    SolverSound solver spec := by
  intro i s d w hOut
  exact hCheckerSound i s d w (hSolverAccepted i s d w hOut)

/-- A solver is total if it produces an output for every `(input, state)`. -/
def SolverTotal
    (solver : Solver Input State Decision Witness) : Prop :=
  ∀ (i : Input) (s : State), ∃ d w, solver i s = some (d, w)

/-- A checker is complete when each spec-valid decision has an accepting witness. -/
def CheckerComplete
    (checker : Checker Input State Decision Witness)
    (spec : Spec Input State Decision) : Prop :=
  ∀ (i : Input) (s : State) (d : Decision),
    spec i s d → ∃ w, checker i s d w = true

/-- Total accepted Boolean solvers produce a spec-valid decision everywhere. -/
theorem solver_valid_output_exists_of_checker_sound_and_solver_total_accepted
    (solver : Solver Input State Decision Witness)
    (checker : Checker Input State Decision Witness)
    (spec : Spec Input State Decision)
    (hCheckerSound : CheckerSound checker spec)
    (hSolverAccepted : SolverAccepted solver checker)
    (hSolverTotal : SolverTotal solver) :
    ∀ (i : Input) (s : State), ∃ d, spec i s d := by
  intro i s
  obtain ⟨d, w, hOut⟩ := hSolverTotal i s
  exact ⟨d, hCheckerSound i s d w (hSolverAccepted i s d w hOut)⟩

/-- Two Boolean checkers are equivalent if they accept the same tuples. -/
def CheckerEquiv
    (c1 c2 : Checker Input State Decision Witness) : Prop :=
  ∀ (i : Input) (s : State) (d : Decision) (w : Witness),
    c1 i s d w = c2 i s d w

/-- Equivalent Boolean checkers preserve solver soundness. -/
theorem equivalent_checkers_preserve_solver_soundness
    (solver : Solver Input State Decision Witness)
    (checker1 checker2 : Checker Input State Decision Witness)
    (spec : Spec Input State Decision)
    (hEquiv : CheckerEquiv checker1 checker2)
    (hSolverAccepted : SolverAccepted solver checker1)
    (hChecker2Sound : CheckerSound checker2 spec) :
    SolverSound solver spec := by
  intro i s d w hOut
  exact hChecker2Sound i s d w ((hEquiv i s d w).symm ▸ hSolverAccepted i s d w hOut)

variable {Decision2 Witness2 : Type}

/-- Sequential composition of two solver stages. -/
def ComposedSolver
    (solver1 : Solver Input State Decision Witness)
    (solver2 : Solver Input Decision Decision2 Witness2)
    (stateOfDecision : Decision → Decision) :
    Solver Input State Decision2 (Witness × Witness2) :=
  fun i s =>
    match solver1 i s with
    | none => none
    | some (d1, w1) =>
      match solver2 i (stateOfDecision d1) with
      | none => none
      | some (d2, w2) => some (d2, (w1, w2))

/-- Sound solver stages compose if the intermediate specs imply the end spec. -/
theorem composed_solver_sound
    (solver1 : Solver Input State Decision Witness)
    (solver2 : Solver Input Decision Decision2 Witness2)
    (stateOfDecision : Decision → Decision)
    (spec1 : Spec Input State Decision)
    (spec2 : Spec Input Decision Decision2)
    (specEnd : Spec Input State Decision2)
    (hSolver1Sound : SolverSound solver1 spec1)
    (hSolver2Sound : SolverSound solver2 spec2)
    (hCompose : ∀ (i : Input) (s : State) (d1 : Decision) (d2 : Decision2),
      spec1 i s d1 → spec2 i (stateOfDecision d1) d2 → specEnd i s d2) :
    SolverSound (ComposedSolver solver1 solver2 stateOfDecision) specEnd := by
  intro i s d2 ⟨w1, w2⟩ hOut
  unfold ComposedSolver at hOut
  match heq1 : solver1 i s with
  | none => simp [heq1] at hOut
  | some (d1, w1') =>
    simp [heq1] at hOut
    match heq2 : solver2 i (stateOfDecision d1) with
    | none => simp [heq2] at hOut
    | some (d2', w2') =>
      simp [heq2] at hOut
      obtain ⟨rfl, rfl, rfl⟩ := hOut
      exact
        hCompose i s d1 d2'
          (hSolver1Sound i s d1 w1' heq1)
          (hSolver2Sound i (stateOfDecision d1) d2' w2' heq2)

/-- A sound solver's decision is spec-valid regardless of the witness payload. -/
theorem witness_irrelevance
    (solver : Solver Input State Decision Witness)
    (spec : Spec Input State Decision)
    (hSound : SolverSound solver spec)
    {i : Input} {s : State} {d : Decision} {w : Witness}
    (hOut : solver i s = some (d, w)) :
    spec i s d := by
  exact hSound i s d w hOut

end SolverCheckerSeparation
end Proofs
