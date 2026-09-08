import Mathlib.Data.Set.Basic

/-!
# Exact expansion of safe products of local choices

A fixed global relation constrains assignments of local choices. An exact
coordinate expansion admits every own choice compatible with all combinations
of the current other factors. The `ExactExpansion` record requires those other
factors to remain unchanged across that step.

Each expansion preserves safety and grows a previously safe product. Once a
coordinate is exact, every later safe, larger snapshot retains that same exact
factor. A finite sweep covering every coordinate therefore produces a safe
factorwise inclusion-maximal product. An explicit initial anchor is retained
and witnesses nonempty factors and a nonempty safe product.

This is a standard relational closure argument, with no novelty claim. The
relation and choice universes remain fixed throughout a run; agent-specific
universe restrictions can be included in the relation. Environment parameters
may instantiate the relation pointwise. The theorem does not establish maximum
product size, fairness, an order-independent result, quantifier elimination,
Python bindings, concurrency control, or runtime authority. A final example
shows why merging full expansions computed from a stale common snapshot fails.
-/

namespace TauSwarmAutonomy

universe u v

variable {I : Type u} {V : Type v}

/-- One set of permitted local choices for each coordinate. -/
abbrev Domains (I : Type u) (V : Type v) := I → Set V

/-- A complete assignment belongs to every corresponding factor. -/
def InProduct (A : Domains I V) (x : I → V) : Prop :=
  ∀ i, x i ∈ A i

/-- Every independently combined local assignment satisfies the fixed relation. -/
def Safe (C : (I → V) → Prop) (A : Domains I V) : Prop :=
  ∀ x, InProduct A x → C x

/-- Compatibility quantifies over every combination of the other current factors.
The factor at `i` is deliberately absent from this definition. -/
def Compatible (C : (I → V) → Prop) (A : Domains I V) (i : I) : Set V :=
  {v | ∀ x, x i = v → (∀ j, j ≠ i → x j ∈ A j) → C x}

/-- A safe product admitting no strict factorwise enlargement to another safe product. -/
def MaximalSafe (C : (I → V) → Prop) (A : Domains I V) : Prop :=
  Safe C A ∧ ∀ B, A ≤ B → Safe C B → B = A

/-- A single exact update against the current, unchanged other factors. -/
structure ExactExpansion (C : (I → V) → Prop) (i : I)
    (before after : Domains I V) : Prop where
  current_others : ∀ j, j ≠ i → after j = before j
  expanded : after i = Compatible C before i

/-- Larger other factors can only reduce the compatible own-choice set. -/
theorem compatible_antitone (C : (I → V) → Prop) (i : I)
    {A B : Domains I V} (hAB : A ≤ B) :
    Compatible C B i ⊆ Compatible C A i := by
  intro v hv x hxi hother
  exact hv x hxi (fun j hji => hAB j (hother j hji))

private theorem compatible_eq_of_other_eq (C : (I → V) → Prop) (i : I)
    {A B : Domains I V} (h : ∀ j, j ≠ i → A j = B j) :
    Compatible C A i = Compatible C B i := by
  apply Set.Subset.antisymm
  · intro v hv x hxi hother
    apply hv x hxi
    intro j hji
    rw [h j hji]
    exact hother j hji
  · intro v hv x hxi hother
    apply hv x hxi
    intro j hji
    rw [← h j hji]
    exact hother j hji

/-- Safety makes every currently admitted own choice compatible with all other factors. -/
theorem safe_self_inclusion (C : (I → V) → Prop) (A : Domains I V) (i : I)
    (hsafe : Safe C A) : A i ⊆ Compatible C A i := by
  classical
  intro v hv x hxi hother
  apply hsafe x
  intro j
  by_cases hji : j = i
  · subst j
    rw [hxi]
    exact hv
  · exact hother j hji

/-- An exact step produces a safe product because its other factors are current. -/
theorem ExactExpansion.safe_after {C : (I → V) → Prop} {i : I}
    {before after : Domains I V} (h : ExactExpansion C i before after) :
    Safe C after := by
  intro x hx
  have hxi : x i ∈ Compatible C before i := by
    rw [← h.expanded]
    exact hx i
  apply hxi x rfl
  intro j hji
  rw [← h.current_others j hji]
  exact hx j

/-- An exact step grows every factor when its input product is safe. -/
theorem ExactExpansion.grows {C : (I → V) → Prop} {i : I}
    {before after : Domains I V} (h : ExactExpansion C i before after)
    (hsafe : Safe C before) : before ≤ after := by
  classical
  intro j v hv
  by_cases hji : j = i
  · subst j
    rw [h.expanded]
    exact safe_self_inclusion C before i hsafe hv
  · rw [h.current_others j hji]
    exact hv

/-- The expanded coordinate is exact against the resulting snapshot as well. -/
theorem ExactExpansion.exact_after {C : (I → V) → Prop} {i : I}
    {before after : Domains I V} (h : ExactExpansion C i before after) :
    after i = Compatible C after i :=
  h.expanded.trans (compatible_eq_of_other_eq C i h.current_others).symm

/-- An exact factor stays unchanged and exact under every safe factorwise enlargement. -/
theorem exact_persists (C : (I → V) → Prop) (i : I) {A B : Domains I V}
    (hAB : A ≤ B) (hsafe : Safe C B) (hexact : A i = Compatible C A i) :
    B i = A i ∧ B i = Compatible C B i := by
  have hBA : B i ⊆ A i := by
    intro v hv
    rw [hexact]
    exact compatible_antitone C i hAB (safe_self_inclusion C B i hsafe hv)
  have hback : Compatible C B i ⊆ B i := by
    intro v hv
    apply hAB i
    rw [hexact]
    exact compatible_antitone C i hAB hv
  exact ⟨Set.Subset.antisymm hBA (hAB i),
    Set.Subset.antisymm (safe_self_inclusion C B i hsafe) hback⟩

/-- Exactness in every coordinate excludes simultaneous safe enlargements too. -/
theorem all_exact_implies_maximal (C : (I → V) → Prop) (A : Domains I V)
    (hsafe : Safe C A) (hexact : ∀ i, A i = Compatible C A i) :
    MaximalSafe C A := by
  constructor
  · exact hsafe
  · intro B hAB hB
    funext i
    exact (exact_persists C i hAB hB (hexact i)).1

private theorem sweep_snapshot_safe (C : (I → V) → Prop) (n : Nat)
    (states : Nat → Domains I V) (order : Fin n → I)
    (steps : ∀ t, ExactExpansion C (order t) (states t.val) (states (t.val + 1)))
    (hstart : Safe C (states 0)) (k : Nat) (hk : k ≤ n) :
    Safe C (states k) := by
  cases k with
  | zero => exact hstart
  | succ k => exact (steps ⟨k, Nat.lt_of_succ_le hk⟩).safe_after

private theorem sweep_snapshots_grow (C : (I → V) → Prop) (n : Nat)
    (states : Nat → Domains I V) (order : Fin n → I)
    (steps : ∀ t, ExactExpansion C (order t) (states t.val) (states (t.val + 1)))
    (hstart : Safe C (states 0)) (s t : Nat) (hst : s ≤ t) :
    t ≤ n → states s ≤ states t := by
  induction t, hst using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ t hst ih =>
    intro ht
    have hprev := Nat.le_of_succ_le ht
    have hsafe := sweep_snapshot_safe C n states order steps hstart t hprev
    exact le_trans (ih hprev) ((steps ⟨t, Nat.lt_of_succ_le ht⟩).grows hsafe)

/-- A finite covering sweep is safe and factorwise maximal, retaining its anchor.
The anchor explicitly witnesses nonempty factors and an actual safe assignment. -/
theorem finite_covering_sweep (C : (I → V) → Prop) (n : Nat)
    (states : Nat → Domains I V) (order : Fin n → I)
    (steps : ∀ t, ExactExpansion C (order t) (states t.val) (states (t.val + 1)))
    (hstart : Safe C (states 0)) (covers : ∀ i, ∃ t, order t = i)
    (anchor : I → V) (hanchor : InProduct (states 0) anchor) :
    MaximalSafe C (states n) ∧ InProduct (states n) anchor ∧ C anchor ∧
    (∀ i, (states n i).Nonempty) ∧ (∀ i, states n i = Compatible C (states n) i) := by
  have hfinal : Safe C (states n) := sweep_snapshot_safe C n states order steps hstart n le_rfl
  have hexact : ∀ i, states n i = Compatible C (states n) i := by
    intro i
    obtain ⟨t, hti⟩ := covers i
    have hgrow := sweep_snapshots_grow C n states order steps hstart (t.val + 1) n
      (Nat.succ_le_of_lt t.isLt) le_rfl
    have hex := (exact_persists C (order t) hgrow hfinal (steps t).exact_after).2
    simpa only [hti] using hex
  have hgrow := sweep_snapshots_grow C n states order steps hstart 0 n (Nat.zero_le n) le_rfl
  have hretained : InProduct (states n) anchor := fun i => hgrow i (hanchor i)
  exact ⟨all_exact_implies_maximal C (states n) hfinal hexact, hretained,
    hfinal anchor hretained, (fun i => ⟨anchor i, hretained i⟩), hexact⟩

/-- Both Boolean agents can propose their full old-snapshot cofactor, yet the merge is unsafe. -/
theorem stale_parallel_expansion_can_be_unsafe :
    let C : (Bool → Bool) → Prop := fun x => ¬(x false = true ∧ x true = true)
    let initial : Domains Bool Bool := fun _ => {false}
    let stale : Domains Bool Bool := fun _ => Set.univ
    Safe C initial ∧ InProduct initial (fun _ => false) ∧
      (∀ i, stale i = Compatible C initial i) ∧ ¬Safe C stale := by
  let C : (Bool → Bool) → Prop := fun x => ¬(x false = true ∧ x true = true)
  let initial : Domains Bool Bool := fun _ => {false}
  let stale : Domains Bool Bool := fun _ => Set.univ
  change Safe C initial ∧ InProduct initial (fun _ => false) ∧
    (∀ i, stale i = Compatible C initial i) ∧ ¬Safe C stale
  have hsafe : Safe C initial := by
    intro x hx hbad
    have hz : x false = false := hx false
    have hf : true = false := hbad.1.symm.trans hz
    cases hf
  have hanchor : InProduct initial (fun _ => false) := fun _ => rfl
  have hfull : ∀ i, stale i = Compatible C initial i := by
    intro i
    apply Set.Subset.antisymm
    · intro v _ x _ hother
      cases i with
      | false =>
        intro hbad
        have hz : x true = false := hother true (by decide)
        have hf : true = false := hbad.2.symm.trans hz
        cases hf
      | true =>
        intro hbad
        have hz : x false = false := hother false (by decide)
        have hf : true = false := hbad.1.symm.trans hz
        cases hf
    · intro v _
      trivial
  have hunsafe : ¬Safe C stale := by
    intro h
    exact h (fun _ => true) (fun _ => Set.mem_univ _) ⟨rfl, rfl⟩
  exact ⟨hsafe, hanchor, hfull, hunsafe⟩

end TauSwarmAutonomy
