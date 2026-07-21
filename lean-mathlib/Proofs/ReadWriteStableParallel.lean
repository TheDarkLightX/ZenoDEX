import Mathlib.Tactic
import Proofs.DeterministicParallelExecution

/-!
# Read/write-stable deterministic parallel execution

`DeterministicParallelExecution` proves that already-computed disjoint immutable
patches commute.  This file closes the missing semantic step for state-dependent
tasks.  Disjoint writes alone are not sufficient: one task may read a cell that
another task writes, changing the patch it computes.

We model a task as a pure function from one immutable pre-state to a patch.  A
static footprint is sound when:

* `ReadsOnly`: agreeing on the declared read set gives the same patch; and
* `WritesWithin`: every emitted patch cell belongs to the declared write set.

If two sound footprints have no write/write or read/write conflicts, each task's
patch is stable under execution of the other task.  Their full state
transformers therefore commute.

The theorem is still an abstract refinement obligation.  A runtime must prove
that its concrete footprint extractor satisfies `SoundFootprint` and that all
workers evaluate against the same immutable snapshot.
-/

namespace ZenoDEX.ReadWriteStableParallel

open ZenoDEX.DeterministicParallelExecution

/-- A pure state-dependent task computes one immutable patch. -/
abbrev Task (Key Value : Type*) := State Key Value → Patch Key Value

/-- Evaluate one pure task and apply its complete patch to the same pre-state. -/
def execute {Key Value : Type*}
    (task : Task Key Value)
    (state : State Key Value) : State Key Value :=
  applyPatch (task state) state

/-- Two states agree on every key in a declared read set. -/
def AgreesOn {Key Value : Type*}
    (keys : Set Key)
    (left right : State Key Value) : Prop :=
  ∀ key, key ∈ keys → left key = right key

/-- A task's output depends only on its declared read set. -/
def ReadsOnly {Key Value : Type*}
    (reads : Set Key)
    (task : Task Key Value) : Prop :=
  ∀ left right, AgreesOn reads left right → task left = task right

/-- Every cell emitted by a task belongs to its declared write set. -/
def WritesWithin {Key Value : Type*}
    (writes : Set Key)
    (task : Task Key Value) : Prop :=
  ∀ state key value, task state key = some value → key ∈ writes

/-- Static read/write metadata for one task profile. -/
structure Footprint (Key : Type*) where
  reads : Set Key
  writes : Set Key

/-- The semantic contract that a runtime footprint extractor must refine. -/
def SoundFootprint {Key Value : Type*}
    (footprint : Footprint Key)
    (task : Task Key Value) : Prop :=
  ReadsOnly footprint.reads task ∧ WritesWithin footprint.writes task

/-- No write/write or either-direction read/write conflict exists. -/
def Noninterfering {Key : Type*}
    (left right : Footprint Key) : Prop :=
  Set.Disjoint left.writes right.writes ∧
    Set.Disjoint left.reads right.writes ∧
    Set.Disjoint right.reads left.writes

/-- Applying a patch outside `reads` preserves the values observed on `reads`. -/
theorem execute_agrees_on_of_disjoint_read_write
    {Key Value : Type*}
    {reads writes : Set Key}
    {task : Task Key Value}
    (hwrites : WritesWithin writes task)
    (hdisjoint : Set.Disjoint reads writes)
    (state : State Key Value) :
    AgreesOn reads (execute task state) state := by
  intro key hread
  unfold execute applyPatch
  cases hpatch : task state key with
  | none => simp [hpatch]
  | some value =>
      have hwrite : key ∈ writes := hwrites state key value hpatch
      exact False.elim (Set.disjoint_left.1 hdisjoint hread hwrite)

/-- A read-only dependency contract makes a task stable under noninterfering writes. -/
theorem stable_under_of_reads_only_writes_within
    {Key Value : Type*}
    {reads writes : Set Key}
    {observer mutator : Task Key Value}
    (hreads : ReadsOnly reads observer)
    (hwrites : WritesWithin writes mutator)
    (hdisjoint : Set.Disjoint reads writes) :
    ∀ state, observer (execute mutator state) = observer state := by
  intro state
  exact hreads
    (execute mutator state)
    state
    (execute_agrees_on_of_disjoint_read_write hwrites hdisjoint state)

/-- Sound tasks with disjoint declared write sets emit disjoint patches. -/
theorem patches_disjoint_of_sound_writes
    {Key Value : Type*}
    {leftWrites rightWrites : Set Key}
    {left right : Task Key Value}
    (hleft : WritesWithin leftWrites left)
    (hright : WritesWithin rightWrites right)
    (hdisjoint : Set.Disjoint leftWrites rightWrites) :
    ∀ state, Disjoint (left state) (right state) := by
  intro state key
  cases hleftPatch : left state key with
  | none => exact Or.inl rfl
  | some leftValue =>
      cases hrightPatch : right state key with
      | none => exact Or.inr rfl
      | some rightValue =>
          have hleftKey : key ∈ leftWrites :=
            hleft state key leftValue hleftPatch
          have hrightKey : key ∈ rightWrites :=
            hright state key rightValue hrightPatch
          exact False.elim (Set.disjoint_left.1 hdisjoint hleftKey hrightKey)

/--
The sufficient footprint theorem: sound tasks with no write/write or read/write
conflicts commute as complete state transformers.
-/
theorem execute_commutes_of_sound_noninterference
    {Key Value : Type*}
    {leftFootprint rightFootprint : Footprint Key}
    {left right : Task Key Value}
    (hleft : SoundFootprint leftFootprint left)
    (hright : SoundFootprint rightFootprint right)
    (hindependent : Noninterfering leftFootprint rightFootprint) :
    Function.Commute (execute left) (execute right) := by
  intro state
  have hpatchDisjoint : Disjoint (left state) (right state) :=
    patches_disjoint_of_sound_writes
      hleft.2
      hright.2
      hindependent.1
      state
  have hleftStable : left (execute right state) = left state :=
    stable_under_of_reads_only_writes_within
      hleft.1
      hright.2
      hindependent.2.1
      state
  have hrightStable : right (execute left state) = right state :=
    stable_under_of_reads_only_writes_within
      hright.1
      hleft.2
      hindependent.2.2
      state
  simp only [execute, hleftStable, hrightStable]
  exact applyPatch_commute_of_disjoint hpatchDisjoint state

/-! ## Why disjoint writes alone are insufficient -/

inductive Cell where
  | x
  | y
  deriving DecidableEq, Repr

/-- Task A reads `x` and writes the observed value into `y`. -/
def readXWriteY : Task Cell Nat :=
  fun state key =>
    if key = Cell.y then some (state Cell.x) else none

/-- Task B writes `1` into `x`. -/
def writeXOne : Task Cell Nat :=
  fun _ key =>
    if key = Cell.x then some 1 else none

/-- The all-zero witness state. -/
def zeroState : State Cell Nat :=
  fun _ => 0

/-- The two tasks always have disjoint write domains. -/
theorem counterexample_write_domains_disjoint :
    ∀ state, Disjoint (readXWriteY state) (writeXOne state) := by
  intro state key
  cases key <;> simp [Disjoint, readXWriteY, writeXOne]

/--
Despite disjoint writes, the schedules differ because Task A's read set intersects
Task B's write set.
-/
theorem disjoint_writes_alone_not_sufficient :
    execute readXWriteY (execute writeXOne zeroState) ≠
      execute writeXOne (execute readXWriteY zeroState) := by
  intro hequal
  have hy := congrFun hequal Cell.y
  norm_num [execute, applyPatch, readXWriteY, writeXOne, zeroState] at hy

end ZenoDEX.ReadWriteStableParallel
