import Mathlib.Tactic

/-!
# Deterministic parallel execution

This file isolates the theorem needed before ZenoDEX may parallelize functional
core work.  Workers evaluate pure tasks against one immutable pre-state and
return patches.  Patches with disjoint write domains commute.  Consequently,
any two schedules that are permutations of the same independent task list
produce the same state.

This is deliberately narrower than a claim about arbitrary concurrent code.  A
runtime must separately prove that its task partition is fixed, each worker is
pure, the emitted patch is complete, write domains are disjoint, and the final
commit is an expected-root compare-and-swap.
-/

namespace ZenoDEX.DeterministicParallelExecution

/-- A committed state is observed extensionally by key. -/
abbrev State (Key Value : Type*) := Key → Value

/-- A pure task patch writes zero or one value at each key. -/
abbrev Patch (Key Value : Type*) := Key → Option Value

/-- Apply one immutable patch to a state. -/
def applyPatch {Key Value : Type*}
    (patch : Patch Key Value)
    (state : State Key Value) : State Key Value :=
  fun key =>
    match patch key with
    | some value => value
    | none => state key

/-- Two patches never both write the same key. -/
def Disjoint {Key Value : Type*}
    (left right : Patch Key Value) : Prop :=
  ∀ key, left key = none ∨ right key = none

/-- Patch disjointness is symmetric. -/
theorem disjoint_symm
    {Key Value : Type*}
    {left right : Patch Key Value}
    (h : Disjoint left right) :
    Disjoint right left := by
  intro key
  rcases h key with hleft | hright
  · exact Or.inr hleft
  · exact Or.inl hright

/-- Disjoint patches commute as state transformers. -/
theorem applyPatch_commute_of_disjoint
    {Key Value : Type*}
    {left right : Patch Key Value}
    (h : Disjoint left right) :
    Function.Commute (applyPatch left) (applyPatch right) := by
  intro state
  funext key
  rcases h key with hleft | hright
  · simp [applyPatch, hleft]
  · simp [applyPatch, hright]

/-- Execute a task list in the listed order. -/
def runTasks {Task StateType : Type*}
    (step : Task → StateType → StateType) :
    List Task → StateType → StateType
  | [], state => state
  | task :: tasks, state => runTasks step tasks (step task state)

/--
If every pair of task transformers commutes, execution depends only on the
multiset of tasks, not on their schedule order.
-/
theorem runTasks_eq_of_perm
    {Task StateType : Type*}
    (step : Task → StateType → StateType)
    (hcommute : ∀ left right, Function.Commute (step left) (step right))
    {first second : List Task}
    (hperm : first.Perm second) :
    ∀ state, runTasks step first state = runTasks step second state := by
  induction hperm with
  | nil =>
      intro state
      rfl
  | cons task hperm ih =>
      intro state
      simp only [runTasks]
      exact ih (step task state)
  | swap left right rest =>
      intro state
      simp only [runTasks]
      rw [hcommute left right state]
  | trans hfirst hsecond ihfirst ihsecond =>
      intro state
      exact (ihfirst state).trans (ihsecond state)

/--
A family of patches indexed by task identifiers commutes when distinct task
identifiers have disjoint write domains.  Equal identifiers commute trivially.
-/
theorem patchFamily_commutes
    {Task Key Value : Type*}
    [DecidableEq Task]
    (patchOf : Task → Patch Key Value)
    (hindependent : ∀ left right, left ≠ right → Disjoint (patchOf left) (patchOf right)) :
    ∀ left right,
      Function.Commute (applyPatch (patchOf left)) (applyPatch (patchOf right)) := by
  intro left right
  by_cases heq : left = right
  · subst right
    intro state
    rfl
  · exact applyPatch_commute_of_disjoint (hindependent left right heq)

/--
The central deterministic-parallel theorem: permutations of the same independent
pure task list produce extensionally equal post-states.
-/
theorem independent_schedule_equivalence
    {Task Key Value : Type*}
    [DecidableEq Task]
    (patchOf : Task → Patch Key Value)
    (hindependent : ∀ left right, left ≠ right → Disjoint (patchOf left) (patchOf right))
    {first second : List Task}
    (hperm : first.Perm second)
    (preState : State Key Value) :
    runTasks (fun task => applyPatch (patchOf task)) first preState =
      runTasks (fun task => applyPatch (patchOf task)) second preState := by
  exact runTasks_eq_of_perm
    (fun task => applyPatch (patchOf task))
    (patchFamily_commutes patchOf hindependent)
    hperm
    preState

/-- A typed compare-and-swap result carries a candidate only on root equality. -/
def commitIfRootMatches
    {Root Candidate : Type*}
    [DecidableEq Root]
    (expected observed : Root)
    (candidate : Candidate) : Option Candidate :=
  if expected = observed then some candidate else none

/-- Root mismatch cannot publish any candidate state or effects. -/
theorem commit_rejects_root_mismatch
    {Root Candidate : Type*}
    [DecidableEq Root]
    {expected observed : Root}
    (candidate : Candidate)
    (hmismatch : expected ≠ observed) :
    commitIfRootMatches expected observed candidate = none := by
  simp [commitIfRootMatches, hmismatch]

/-- Root equality publishes exactly the supplied atomic candidate. -/
theorem commit_accepts_root_match
    {Root Candidate : Type*}
    [DecidableEq Root]
    {expected observed : Root}
    (candidate : Candidate)
    (hmatch : expected = observed) :
    commitIfRootMatches expected observed candidate = some candidate := by
  simp [commitIfRootMatches, hmatch]

end ZenoDEX.DeterministicParallelExecution
