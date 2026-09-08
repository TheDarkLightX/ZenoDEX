import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic

/-!
# Reproductive composition and guarded covers

A reproductive map sends every seed to a solution and fixes every solution.
These are standard retraction facts over arbitrary environment and seed types.
They require no finiteness, Boolean algebra, commutation, or convergence premise.

An ordered composition always retains common fixed points. Its exact soundness
guard is `Good`; feasibility alone need not imply this guard. A finite list of
environment-only Boolean guards selects the first enabled map, and rejects when
every guard is false. Completeness of that selector requires the separate
premise that the guard union equals feasibility.

A later retraction that preserves the earlier constraint safely extends a
composition to their conjunction. This standard extension lemma can support an
inductive schedule proof; it does not verify a candidate interference graph or
graph scheduling algorithm.

This file gives mathematical evidence only. It does not establish a Tau parser,
an executable compiler binding, novelty, or settlement authority.
-/

namespace TauReproductiveComposition

universe u v w

variable {Env : Type u} {Seed : Type v}

/-- The map fixes every solution in this environment. -/
def Fixes (P : Env → Seed → Prop) (r : Env → Seed → Seed) (e : Env) : Prop :=
  ∀ x, P e x → r e x = x

/-- The exact environment-only guard for soundness on every seed. -/
def Good (P : Env → Seed → Prop) (r : Env → Seed → Seed) (e : Env) : Prop :=
  ∀ x, P e (r e x)

/-- Soundness and reproduction of all solutions, with both obligations explicit. -/
def Reproductive (P : Env → Seed → Prop) (r : Env → Seed → Seed) (e : Env) : Prop :=
  Good P r e ∧ Fixes P r e

/-- Feasibility asserts that at least one solution exists. -/
def Feasible (P : Env → Seed → Prop) (e : Env) : Prop :=
  ∃ x, P e x

/-- The common solution predicate for an arbitrary family of local constraints. -/
def Common {ι : Type w} (Q : ι → Env → Seed → Prop) (e : Env) (x : Seed) : Prop :=
  ∀ i, Q i e x

/-- Apply maps in list order: the head runs first and the empty list is identity. -/
def compose : List (Env → Seed → Seed) → Env → Seed → Seed
  | [], _, x => x
  | r :: rs, e, x => compose rs e (r e x)

/-- Ordered composition retains all shared fixed points, without commutation. -/
theorem compose_fixes (P : Env → Seed → Prop)
    (rs : List (Env → Seed → Seed)) (e : Env) :
    (∀ r ∈ rs, Fixes P r e) → Fixes P (compose rs) e := by
  induction rs with
  | nil => intro _ x _; rfl
  | cons r rs ih =>
    intro h x hx
    change compose rs e (r e x) = x
    rw [h r (by simp) x hx]
    exact ih (fun s hs => h s (by simp only [List.mem_cons]; exact Or.inr hs)) x hx

/-- Each local fixed-point law suffices to preserve the intersection of constraints. -/
theorem compose_fixes_common {ι : Type w} (Q : ι → Env → Seed → Prop)
    (r : ι → Env → Seed → Seed) (order : List ι) (e : Env)
    (hfix : ∀ i ∈ order, Fixes (Q i) (r i) e) :
    Fixes (Common Q) (compose (order.map r)) e := by
  apply compose_fixes
  intro f hf x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
  exact hfix i hi x (hx i)

/-- A later retraction preserving the earlier constraint safely solves their conjunction. -/
theorem compose_reproductive_of_preserves (A B : Env → Seed → Prop)
    (p q : Env → Seed → Seed) (e : Env)
    (hp : Reproductive A p e) (hq : Reproductive B q e)
    (hpreserve : ∀ x, A e x → A e (q e x)) :
    Reproductive (fun e x => A e x ∧ B e x) (compose [p, q]) e := by
  constructor
  · intro x
    exact ⟨hpreserve (p e x) (hp.1 x), hq.1 (p e x)⟩
  · intro x hx
    change q e (p e x) = x
    rw [hp.2 x hx.1]
    exact hq.2 x hx.2

/-- On a guard proving composite soundness, local fixed-point laws give reproduction. -/
theorem compose_reproductive_on_guard (P : Env → Seed → Prop)
    (rs : List (Env → Seed → Seed)) (G : Env → Prop) (e : Env)
    (hfix : ∀ r ∈ rs, Fixes P r e)
    (hsound : G e → Good P (compose rs) e) (hg : G e) :
    Reproductive P (compose rs) e :=
  ⟨hsound hg, compose_fixes P rs e hfix⟩

/-- Reapplying a reproductive map does not change its output. -/
theorem Reproductive.idempotent {P : Env → Seed → Prop}
    {r : Env → Seed → Seed} {e : Env} (h : Reproductive P r e) (x : Seed) :
    r e (r e x) = r e x :=
  h.2 (r e x) (h.1 x)

/-- A value is an output exactly when it is a solution. -/
theorem Reproductive.image_iff {P : Env → Seed → Prop}
    {r : Env → Seed → Seed} {e : Env} (h : Reproductive P r e) (y : Seed) :
    (∃ x, r e x = y) ↔ P e y := by
  constructor
  · rintro ⟨x, rfl⟩
    exact h.1 x
  · intro hy
    exact ⟨y, h.2 y hy⟩

/-- The range of a reproductive map is precisely the solution set. -/
theorem Reproductive.range_eq {P : Env → Seed → Prop}
    {r : Env → Seed → Seed} {e : Env} (h : Reproductive P r e) :
    Set.range (r e) = {y | P e y} :=
  Set.ext h.image_iff

/-- Definitional inclusion: a sound environment-only guard implies `Good`. -/
example (P : Env → Seed → Prop)
    (r : Env → Seed → Seed) (G : Env → Prop)
    (hsound : ∀ e, G e → ∀ x, P e (r e x)) :
    ∀ e, G e → Good P r e :=
  hsound

/-- `Good` is the largest permitted environment set when the map fixes solutions. -/
theorem guard_reproductive_iff_implies_good (P : Env → Seed → Prop)
    (r : Env → Seed → Seed) (G : Env → Prop)
    (hfix : ∀ e, Fixes P r e) :
    (∀ e, G e → Reproductive P r e) ↔ (∀ e, G e → Good P r e) := by
  constructor
  · intro h e hg
    exact (h e hg).1
  · intro h e hg
    exact ⟨h e hg, hfix e⟩

/-- A seed witness is needed to infer feasibility, since the seed type can be empty. -/
theorem good_implies_feasible {P : Env → Seed → Prop}
    {r : Env → Seed → Seed} {e : Env} (seed : Seed) (h : Good P r e) :
    Feasible P e :=
  ⟨r e seed, h seed⟩

/-- Feasibility and fixed-point preservation can both hold while `Good` fails. -/
theorem feasibility_does_not_imply_good :
    Feasible (fun (_ : Unit) (x : Bool) => x = true) () ∧
    Fixes (fun (_ : Unit) (x : Bool) => x = true) (fun _ x => x) () ∧
    ¬Good (fun (_ : Unit) (x : Bool) => x = true) (fun _ x => x) () := by
  constructor
  · exact ⟨true, rfl⟩
  · constructor
    · intro _ _
      rfl
    · intro h
      cases h false

/-- An environment-only decidable guard paired with its proposed map. -/
structure GuardedMap (Env : Type u) (Seed : Type v) where
  guard : Env → Bool
  run : Env → Seed → Seed

/-- The finite guard union, retaining the given list order for selection. -/
def Covered : List (GuardedMap Env Seed) → Env → Prop
  | [], _ => False
  | b :: bs, e => b.guard e = true ∨ Covered bs e

/-- Select the first enabled map; absence of a true guard produces rejection. -/
def firstTrue : List (GuardedMap Env Seed) → Env → Seed → Option Seed
  | [], _, _ => none
  | b :: bs, e, x =>
      if b.guard e = true then some (b.run e x) else firstTrue bs e x

/-- Selection produces an output exactly on the finite guard union. -/
theorem first_true_has_value_iff (bs : List (GuardedMap Env Seed)) (e : Env)
    (x : Seed) : (∃ y, firstTrue bs e x = some y) ↔ Covered bs e := by
  induction bs with
  | nil => simp [firstTrue, Covered]
  | cons b bs ih =>
    by_cases hb : b.guard e = true
    · simp [firstTrue, Covered, hb]
    · simp [firstTrue, Covered, hb, ih]

/-- Rejection is exactly failure of every guard, independently of the seed. -/
theorem first_true_none_iff (bs : List (GuardedMap Env Seed)) (e : Env)
    (x : Seed) : firstTrue bs e x = none ↔ ¬Covered bs e := by
  induction bs with
  | nil => simp [firstTrue, Covered]
  | cons b bs ih =>
    by_cases hb : b.guard e = true
    · simp [firstTrue, Covered, hb]
    · simp [firstTrue, Covered, hb, ih]

/-- Every accepted output satisfies the constraint if enabled branches are reproductive. -/
theorem first_true_sound (P : Env → Seed → Prop)
    (bs : List (GuardedMap Env Seed)) (e : Env) :
    (∀ b ∈ bs, b.guard e = true → Reproductive P b.run e) →
    ∀ x y, firstTrue bs e x = some y → P e y := by
  induction bs with
  | nil => intro _ x y hy; cases hy
  | cons b bs ih =>
    intro h x y hy
    by_cases hb : b.guard e = true
    · have heq : b.run e x = y := by simpa [firstTrue, hb] using hy
      rw [←heq]
      exact (h b (by simp) hb).1 x
    · apply ih (fun c hc => h c (by simp only [List.mem_cons]; exact Or.inr hc)) x y
      simpa [firstTrue, hb] using hy

/-- On the guard union, first-true selection fixes every solution. -/
theorem first_true_fixes (P : Env → Seed → Prop)
    (bs : List (GuardedMap Env Seed)) (e : Env) :
    (∀ b ∈ bs, b.guard e = true → Reproductive P b.run e) →
    Covered bs e → ∀ x, P e x → firstTrue bs e x = some x := by
  induction bs with
  | nil => intro _ hc; cases hc
  | cons b bs ih =>
    intro h hc x hx
    by_cases hb : b.guard e = true
    · simp [firstTrue, hb, (h b (by simp) hb).2 x hx]
    · have htail : Covered bs e := hc.resolve_left hb
      simpa [firstTrue, hb] using
        ih (fun c hc => h c (by simp only [List.mem_cons]; exact Or.inr hc)) htail x hx

/-- On the covered environments, the selector is total, sound, and reproduces solutions. -/
theorem first_true_reproductive_on_cover (P : Env → Seed → Prop)
    (bs : List (GuardedMap Env Seed)) (e : Env)
    (h : ∀ b ∈ bs, b.guard e = true → Reproductive P b.run e)
    (hc : Covered bs e) :
    (∀ x, ∃ y, firstTrue bs e x = some y ∧ P e y) ∧
    (∀ x, P e x → firstTrue bs e x = some x) := by
  constructor
  · intro x
    obtain ⟨y, hy⟩ := (first_true_has_value_iff bs e x).mpr hc
    exact ⟨y, hy, first_true_sound P bs e h x y hy⟩
  · exact first_true_fixes P bs e h hc

/-- Exact guard coverage yields a valid output for every seed in a feasible environment. -/
theorem first_true_domain_complete (P : Env → Seed → Prop)
    (bs : List (GuardedMap Env Seed)) (e : Env) (x : Seed)
    (h : ∀ b ∈ bs, b.guard e = true → Reproductive P b.run e)
    (hcover : Covered bs e ↔ Feasible P e) :
    (∃ y, firstTrue bs e x = some y ∧ P e y) ↔ Feasible P e := by
  constructor
  · rintro ⟨y, _, hy⟩
    exact ⟨y, hy⟩
  · intro hf
    exact (first_true_reproductive_on_cover P bs e h (hcover.mpr hf)).1 x

/-- Under exact coverage, the rejecting fallback runs exactly on infeasible environments. -/
theorem first_true_rejects_iff_infeasible (P : Env → Seed → Prop)
    (bs : List (GuardedMap Env Seed)) (e : Env) (x : Seed)
    (hcover : Covered bs e ↔ Feasible P e) :
    firstTrue bs e x = none ↔ ¬Feasible P e := by
  rw [first_true_none_iff, hcover]

/-- A constant map onto a designated solution supplies a non-vacuous reproductive instance. -/
theorem constant_is_reproductive (chosen : Env → Seed) (e : Env) :
    Reproductive (fun e x => x = chosen e) (fun e _ => chosen e) e := by
  constructor
  · intro _
    rfl
  · intro x hx
    exact hx.symm

/-- Independent Boolean coordinate repairs supply a non-vacuous safe composition. -/
example :
    Reproductive (fun (_ : Unit) (x : Bool × Bool) => x.1 = true ∧ x.2 = true)
      (compose [(fun _ x => (true, x.2)), (fun _ x => (x.1, true))]) () := by
  constructor
  · intro x
    exact ⟨rfl, rfl⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    cases ha
    cases hb
    rfl

/-- Finite behavior is an instance: this composition reproduces the designated Boolean. -/
example : ∀ e : Bool,
    Reproductive (fun e x => x = e)
      (compose [(fun _ x => x), (fun e _ => e)]) e := by
  unfold Reproductive Good Fixes compose
  decide

/-- Complementary guards cover every Boolean environment, with the stated first-true result. -/
example :
    let bs : List (GuardedMap Bool Bool) :=
      [⟨(fun e => e), (fun e _ => e)⟩, ⟨(fun e => !e), (fun e _ => e)⟩]
    (∀ e, Covered bs e ↔ Feasible (fun e x => x = e) e) ∧
    (∀ e x, firstTrue bs e x = some e) := by
  dsimp only
  constructor
  · intro e
    cases e <;> simp [Covered, Feasible]
  · intro e x
    cases e <;> rfl

/-- An empty cover rejects every Boolean seed. -/
example : ∀ e x : Bool, firstTrue [] e x = none := by
  decide

end TauReproductiveComposition
