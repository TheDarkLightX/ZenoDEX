import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic

/-!
# Closed pipeline behavior and artifact-class products

Total component functions `State → State` keep every intermediate value in the
same complete domain. Pointwise equality is required at every value of this
type. A finite integer domain can instantiate `State`; agreement merely on
allowed initial inputs is insufficient, as the Boolean counterexample shows.

Stage-specific class maps lift a safe abstract product to all matching concrete
artifacts under an explicit exact relation correspondence. If every abstract
class has a concrete representative, factorwise inclusion maximality also
transfers. An abstract anchor provides a concrete non-vacuity witness.

These are standard substitution and inverse-image arguments, with no novelty
claim. Artifact and class types denote the admitted stage-specific universes.
The source does not prove table enumeration, evaluator/CPython refinement,
termination of submitted code, source-byte binding, selector parsing, or Tau
execution. The class and relation correspondence premises must be established
for the actual admitted artifacts and the complete closed component domain.
-/

namespace TauArtifactQuotient

universe u v w z

variable {State : Type z}

/-- Run total stages in list order; each output is a valid input to the next stage. -/
def runPipeline : List (State → State) → State → State
  | [], x => x
  | f :: fs, x => runPipeline fs (f x)

/-- Equality on the complete closed component domain is preserved by sequential composition. -/
theorem run_pipeline_eq {fs gs : List (State → State)}
    (h : List.Forall₂ (fun f g => ∀ x, f x = g x) fs gs) (x : State) :
    runPipeline fs x = runPipeline gs x := by
  induction h generalizing x with
  | nil => rfl
  | cons hfg _ ih =>
    simp only [runPipeline]
    rw [hfg x]
    exact ih _

/-- Stages can agree on the initial input while differing on a reachable intermediate value. -/
theorem initial_input_agreement_is_insufficient :
    let fs : List (Bool → Bool) := [fun _ => true, fun x => x]
    let gs : List (Bool → Bool) := [fun _ => true, fun _ => false]
    List.Forall₂ (fun f g => f false = g false) fs gs ∧
      runPipeline fs false ≠ runPipeline gs false := by
  constructor
  · exact List.Forall₂.cons rfl (List.Forall₂.cons rfl List.Forall₂.nil)
  · decide

variable {I : Type u} {Artifact : I → Type v} {Class : I → Type w}

/-- Local admitted sets, with stage-specific element types. -/
abbrev Factors (Obj : I → Type v) := ∀ i, Set (Obj i)

def InProduct {Obj : I → Type v} (A : Factors Obj) (x : ∀ i, Obj i) : Prop :=
  ∀ i, x i ∈ A i

def Safe {Obj : I → Type v} (C : (∀ i, Obj i) → Prop) (A : Factors Obj) : Prop :=
  ∀ x, InProduct A x → C x

/-- Maximality concerns factor inclusion, independently of cardinality or volume. -/
def MaximalSafe {Obj : I → Type v} (C : (∀ i, Obj i) → Prop) (A : Factors Obj) : Prop :=
  Safe C A ∧ ∀ B, A ≤ B → Safe C B → B = A

def classify (classOf : (i : I) → Artifact i → Class i) (x : ∀ i, Artifact i) :
    ∀ i, Class i :=
  fun i => classOf i (x i)

/-- Lift each class factor to every admitted artifact mapping into it. -/
def pullback (classOf : (i : I) → Artifact i → Class i) (A : Factors Class) :
    Factors Artifact :=
  fun i => classOf i ⁻¹' A i

private def pushforward (classOf : (i : I) → Artifact i → Class i) (B : Factors Artifact) :
    Factors Class :=
  fun i => classOf i '' B i

/-- A supplied concrete representative for every stage-specific abstract class. -/
structure Representatives (classOf : (i : I) → Artifact i → Class i) where
  artifact : (i : I) → Class i → Artifact i
  class_eq : ∀ i c, classOf i (artifact i c) = c

/-- Class-preserving artifact replacement preserves pipeline output when classes imply
pointwise equality on the whole closed state type. -/
theorem pipeline_eq_of_equal_classes
    (classOf : (i : I) → Artifact i → Class i)
    (meaning : (i : I) → Artifact i → State → State)
    (class_behavior : ∀ i a b, classOf i a = classOf i b → ∀ x, meaning i a x = meaning i b x)
    (stages : List I) (a b : ∀ i, Artifact i)
    (same_class : ∀ i, classOf i (a i) = classOf i (b i)) (x : State) :
    runPipeline (stages.map (fun i => meaning i (a i))) x =
      runPipeline (stages.map (fun i => meaning i (b i))) x := by
  apply run_pipeline_eq
  induction stages with
  | nil => exact List.Forall₂.nil
  | cons i stages ih =>
    exact List.Forall₂.cons (class_behavior i (a i) (b i) (same_class i)) ih

/-- Exact relation correspondence lifts abstract product safety to all matching artifacts. -/
theorem safe_pullback (classOf : (i : I) → Artifact i → Class i)
    (concrete : (∀ i, Artifact i) → Prop) (abstract : (∀ i, Class i) → Prop)
    (relation_exact : ∀ x, concrete x ↔ abstract (classify classOf x))
    (A : Factors Class) (hsafe : Safe abstract A) :
    Safe concrete (pullback classOf A) := by
  intro x hx
  apply (relation_exact x).mpr
  exact hsafe (classify classOf x) hx

private theorem safe_pushforward (classOf : (i : I) → Artifact i → Class i)
    (concrete : (∀ i, Artifact i) → Prop) (abstract : (∀ i, Class i) → Prop)
    (relation_exact : ∀ x, concrete x ↔ abstract (classify classOf x))
    (B : Factors Artifact) (hsafe : Safe concrete B) :
    Safe abstract (pushforward classOf B) := by
  classical
  intro y hy
  have witnesses : ∀ i, ∃ a, a ∈ B i ∧ classOf i a = y i := fun i => hy i
  let x : ∀ i, Artifact i := fun i => Classical.choose (witnesses i)
  have hx : InProduct B x := fun i => (Classical.choose_spec (witnesses i)).1
  have hclass : classify classOf x = y := by
    funext i
    exact (Classical.choose_spec (witnesses i)).2
  have h := (relation_exact x).mp (hsafe x hx)
  simpa only [hclass] using h

/-- Representatives transfer factorwise maximality to the full inverse-image artifact product. -/
theorem maximal_safe_pullback (classOf : (i : I) → Artifact i → Class i)
    (reps : Representatives classOf)
    (concrete : (∀ i, Artifact i) → Prop) (abstract : (∀ i, Class i) → Prop)
    (relation_exact : ∀ x, concrete x ↔ abstract (classify classOf x))
    (A : Factors Class) (hmax : MaximalSafe abstract A) :
    MaximalSafe concrete (pullback classOf A) := by
  constructor
  · exact safe_pullback classOf concrete abstract relation_exact A hmax.1
  · intro B hAB hsafe
    have habstract := safe_pushforward classOf concrete abstract relation_exact B hsafe
    have hinclusion : A ≤ pushforward classOf B := by
      intro i c hc
      have hr : reps.artifact i c ∈ pullback classOf A i := by
        change classOf i (reps.artifact i c) ∈ A i
        rw [reps.class_eq]
        exact hc
      exact ⟨reps.artifact i c, hAB i hr, reps.class_eq i c⟩
    have heq : pushforward classOf B = A := hmax.2 _ hinclusion habstract
    funext i
    apply Set.Subset.antisymm
    · intro a ha
      change classOf i a ∈ A i
      rw [← heq]
      exact ⟨a, ha, rfl⟩
    · exact hAB i

/-- An admitted abstract anchor supplies an actual safe concrete bundle through its representatives. -/
theorem pullback_with_anchor (classOf : (i : I) → Artifact i → Class i)
    (reps : Representatives classOf)
    (concrete : (∀ i, Artifact i) → Prop) (abstract : (∀ i, Class i) → Prop)
    (relation_exact : ∀ x, concrete x ↔ abstract (classify classOf x))
    (A : Factors Class) (hsafe : Safe abstract A)
    (anchor : ∀ i, Class i) (hanchor : InProduct A anchor) :
    ∃ x, InProduct (pullback classOf A) x ∧ concrete x := by
  let x : ∀ i, Artifact i := fun i => reps.artifact i (anchor i)
  have hx : InProduct (pullback classOf A) x := by
    intro i
    change classOf i (reps.artifact i (anchor i)) ∈ A i
    rw [reps.class_eq]
    exact hanchor i
  exact ⟨x, hx, safe_pullback classOf concrete abstract relation_exact A hsafe x hx⟩

end TauArtifactQuotient
