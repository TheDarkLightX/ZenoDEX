import Proofs.FiniteTraceBarriers
import Mathlib.Data.Set.Basic

/-!
# Abstract Interpretation Disaster Safety

This packet turns the order-theory / abstract-interpretation source shelf into
a reusable ZenoDEX theorem shape.

The core contract is a forward simulation:

- every concrete step is over-approximated by at least one abstract step,
- the abstract invariant is preserved by abstract steps,
- the abstract invariant concretizes to concrete safety.

Then every concrete reachable state is safe. Equivalently, any concrete
disaster predicate excluded by the abstract invariant is unreachable.
-/

namespace Proofs
namespace AbstractInterpretationDisasterSafety

open FiniteTraceBarriers

abbrev TransitionSystem := FiniteTraceBarriers.TransitionSystem

namespace TransitionSystem

variable {σ α τ β : Type*}

/--
`R c a` means abstract state `a` soundly represents concrete state `c`.
Forward simulation says every represented concrete step can be matched by an
abstract step that represents the new concrete state.
-/
def ForwardSimulation
    (C : TransitionSystem σ) (A : TransitionSystem α)
    (R : σ → α → Prop) : Prop :=
  ∀ {c d : σ} {a : α},
    R c a → C.Step c d → ∃ b : α, A.Step a b ∧ R d b

/-- An abstract invariant is preserved by every abstract step. -/
def AbstractInvariant
    (A : TransitionSystem α) (Inv : α → Prop) : Prop :=
  ∀ {a b : α}, Inv a → A.Step a b → Inv b

/--
The abstract invariant is strong enough to imply the concrete safety predicate
for every concrete state represented by the abstract state.
-/
def ConcretizesSafety
    (R : σ → α → Prop) (Inv : α → Prop) (safe : σ → Prop) : Prop :=
  ∀ {c : σ} {a : α}, R c a → Inv a → safe c

/--
The abstract invariant excludes the named concrete disaster predicate.
-/
def ExcludesDisaster
    (R : σ → α → Prop) (Inv : α → Prop) (disaster : σ → Prop) : Prop :=
  ∀ {c : σ} {a : α}, R c a → Inv a → ¬ disaster c

theorem abstractInvariant_of_reachable
    {A : TransitionSystem α} {Inv : α → Prop}
    (hInv : AbstractInvariant A Inv)
    {a0 a : α} (hReach : A.Reachable a0 a)
    (hInit : Inv a0) :
    Inv a := by
  induction hReach with
  | refl =>
      exact hInit
  | tail _ hStep ih =>
      exact hInv ih hStep

theorem abstractInvariant_of_traceN
    {A : TransitionSystem α} {Inv : α → Prop}
    (hInv : AbstractInvariant A Inv)
    {n : Nat} {a0 a : α} (hTrace : A.TraceN n a0 a)
    (hInit : Inv a0) :
    Inv a :=
  abstractInvariant_of_reachable hInv
    (FiniteTraceBarriers.TransitionSystem.reachable_of_traceN hTrace)
    hInit

theorem reachable_lift_exists
    {C : TransitionSystem σ} {A : TransitionSystem α}
    {R : σ → α → Prop}
    (hSim : ForwardSimulation C A R)
    {c0 c : σ} {a0 : α}
    (hInitial : R c0 a0)
    (hReach : C.Reachable c0 c) :
    ∃ a : α, A.Reachable a0 a ∧ R c a := by
  induction hReach with
  | refl =>
      exact ⟨a0, FiniteTraceBarriers.TransitionSystem.Reachable.refl a0, hInitial⟩
  | tail _ hStep ih =>
      rcases ih with ⟨a, hAbsReach, hRep⟩
      rcases hSim hRep hStep with ⟨b, hAbsStep, hRepNext⟩
      exact ⟨b,
        FiniteTraceBarriers.TransitionSystem.Reachable.tail hAbsReach hAbsStep,
        hRepNext⟩

theorem traceN_lift_exists
    {C : TransitionSystem σ} {A : TransitionSystem α}
    {R : σ → α → Prop}
    (hSim : ForwardSimulation C A R)
    {n : Nat} {c0 c : σ} {a0 : α}
    (hInitial : R c0 a0)
    (hTrace : C.TraceN n c0 c) :
    ∃ a : α, A.TraceN n a0 a ∧ R c a := by
  revert a0
  induction hTrace with
  | nil =>
      intro a0 hInitial
      exact ⟨a0, FiniteTraceBarriers.TransitionSystem.TraceN.nil a0, hInitial⟩
  | snoc _ hStep ih =>
      intro a0 hInitial
      rcases ih hInitial with ⟨a, hAbsTrace, hRep⟩
      rcases hSim hRep hStep with ⟨b, hAbsStep, hRepNext⟩
      exact ⟨b,
        FiniteTraceBarriers.TransitionSystem.TraceN.snoc hAbsTrace hAbsStep,
        hRepNext⟩

theorem safe_of_concrete_reachable_simulation
    {C : TransitionSystem σ} {A : TransitionSystem α}
    {R : σ → α → Prop} {Inv : α → Prop} {safe : σ → Prop}
    (hSim : ForwardSimulation C A R)
    (hInv : AbstractInvariant A Inv)
    (hSound : ConcretizesSafety R Inv safe)
    {c0 c : σ} {a0 : α}
    (hInitialRep : R c0 a0)
    (hInitialInv : Inv a0)
    (hReach : C.Reachable c0 c) :
    safe c := by
  rcases reachable_lift_exists hSim hInitialRep hReach with
    ⟨a, hAbsReach, hRep⟩
  exact hSound hRep
    (abstractInvariant_of_reachable hInv hAbsReach hInitialInv)

theorem safe_of_concrete_traceN_simulation
    {C : TransitionSystem σ} {A : TransitionSystem α}
    {R : σ → α → Prop} {Inv : α → Prop} {safe : σ → Prop}
    (hSim : ForwardSimulation C A R)
    (hInv : AbstractInvariant A Inv)
    (hSound : ConcretizesSafety R Inv safe)
    {n : Nat} {c0 c : σ} {a0 : α}
    (hInitialRep : R c0 a0)
    (hInitialInv : Inv a0)
    (hTrace : C.TraceN n c0 c) :
    safe c := by
  rcases traceN_lift_exists hSim hInitialRep hTrace with
    ⟨a, hAbsTrace, hRep⟩
  exact hSound hRep
    (abstractInvariant_of_traceN hInv hAbsTrace hInitialInv)

theorem no_disaster_of_concrete_reachable_simulation
    {C : TransitionSystem σ} {A : TransitionSystem α}
    {R : σ → α → Prop} {Inv : α → Prop} {disaster : σ → Prop}
    (hSim : ForwardSimulation C A R)
    (hInv : AbstractInvariant A Inv)
    (hExcludes : ExcludesDisaster R Inv disaster)
    {c0 c : σ} {a0 : α}
    (hInitialRep : R c0 a0)
    (hInitialInv : Inv a0)
    (hReach : C.Reachable c0 c) :
    ¬ disaster c :=
  safe_of_concrete_reachable_simulation
    hSim hInv hExcludes hInitialRep hInitialInv hReach

theorem no_disaster_of_concrete_traceN_simulation
    {C : TransitionSystem σ} {A : TransitionSystem α}
    {R : σ → α → Prop} {Inv : α → Prop} {disaster : σ → Prop}
    (hSim : ForwardSimulation C A R)
    (hInv : AbstractInvariant A Inv)
    (hExcludes : ExcludesDisaster R Inv disaster)
    {n : Nat} {c0 c : σ} {a0 : α}
    (hInitialRep : R c0 a0)
    (hInitialInv : Inv a0)
    (hTrace : C.TraceN n c0 c) :
    ¬ disaster c :=
  safe_of_concrete_traceN_simulation
    hSim hInv hExcludes hInitialRep hInitialInv hTrace

/-- Deterministic abstraction is the common case: `abs c` is the abstract state. -/
def FunctionSound
    (C : TransitionSystem σ) (A : TransitionSystem α)
    (abs : σ → α) : Prop :=
  ∀ {c d : σ}, C.Step c d → A.Step (abs c) (abs d)

theorem reachable_map_of_functionSound
    {C : TransitionSystem σ} {A : TransitionSystem α}
    {abs : σ → α}
    (hStep : FunctionSound C A abs)
    {c0 c : σ} (hReach : C.Reachable c0 c) :
    A.Reachable (abs c0) (abs c) := by
  induction hReach with
  | refl =>
      exact FiniteTraceBarriers.TransitionSystem.Reachable.refl _
  | tail _ hConcreteStep ih =>
      exact FiniteTraceBarriers.TransitionSystem.Reachable.tail ih
        (hStep hConcreteStep)

theorem traceN_map_of_functionSound
    {C : TransitionSystem σ} {A : TransitionSystem α}
    {abs : σ → α}
    (hStep : FunctionSound C A abs)
    {n : Nat} {c0 c : σ} (hTrace : C.TraceN n c0 c) :
    A.TraceN n (abs c0) (abs c) := by
  induction hTrace with
  | nil =>
      exact FiniteTraceBarriers.TransitionSystem.TraceN.nil _
  | snoc _ hConcreteStep ih =>
      exact FiniteTraceBarriers.TransitionSystem.TraceN.snoc ih
        (hStep hConcreteStep)

theorem safe_of_function_abstraction_reachable
    {C : TransitionSystem σ} {A : TransitionSystem α}
    {abs : σ → α} {Inv : α → Prop} {safe : σ → Prop}
    (hStep : FunctionSound C A abs)
    (hInv : AbstractInvariant A Inv)
    (hSound : ∀ {c : σ}, Inv (abs c) → safe c)
    {c0 c : σ}
    (hInitialInv : Inv (abs c0))
    (hReach : C.Reachable c0 c) :
    safe c :=
  hSound
    (abstractInvariant_of_reachable hInv
      (reachable_map_of_functionSound hStep hReach)
      hInitialInv)

theorem no_disaster_of_function_abstraction_reachable
    {C : TransitionSystem σ} {A : TransitionSystem α}
    {abs : σ → α} {Inv : α → Prop} {disaster : σ → Prop}
    (hStep : FunctionSound C A abs)
    (hInv : AbstractInvariant A Inv)
    (hExcludes : ∀ {c : σ}, Inv (abs c) → ¬ disaster c)
    {c0 c : σ}
    (hInitialInv : Inv (abs c0))
    (hReach : C.Reachable c0 c) :
    ¬ disaster c :=
  safe_of_function_abstraction_reachable
    hStep hInv hExcludes hInitialInv hReach

/-- Set concretization form: abstract state `a` denotes concrete set `γ a`. -/
def SetForwardSimulation
    (C : TransitionSystem σ) (A : TransitionSystem α)
    (γ : α → Set σ) : Prop :=
  ForwardSimulation C A (fun c a => c ∈ γ a)

theorem safe_of_set_concretization_reachable
    {C : TransitionSystem σ} {A : TransitionSystem α}
    {γ : α → Set σ} {Inv : α → Prop} {safe : σ → Prop}
    (hSim : SetForwardSimulation C A γ)
    (hInv : AbstractInvariant A Inv)
    (hSound : ∀ {c : σ} {a : α}, c ∈ γ a → Inv a → safe c)
    {c0 c : σ} {a0 : α}
    (hInitialRep : c0 ∈ γ a0)
    (hInitialInv : Inv a0)
    (hReach : C.Reachable c0 c) :
    safe c :=
  safe_of_concrete_reachable_simulation
    hSim hInv hSound hInitialRep hInitialInv hReach

theorem syncProduct_forwardSimulation
    {C₁ : TransitionSystem σ} {A₁ : TransitionSystem α}
    {C₂ : TransitionSystem τ} {A₂ : TransitionSystem β}
    {R₁ : σ → α → Prop} {R₂ : τ → β → Prop}
    (h₁ : ForwardSimulation C₁ A₁ R₁)
    (h₂ : ForwardSimulation C₂ A₂ R₂) :
    ForwardSimulation
      (FiniteTraceBarriers.TransitionSystem.SyncProduct C₁ C₂)
      (FiniteTraceBarriers.TransitionSystem.SyncProduct A₁ A₂)
      (fun c a => R₁ c.1 a.1 ∧ R₂ c.2 a.2) := by
  intro c d a hRep hStep
  rcases hRep with ⟨hRep₁, hRep₂⟩
  rcases hStep with ⟨hStep₁, hStep₂⟩
  rcases h₁ hRep₁ hStep₁ with ⟨b₁, hAbsStep₁, hRepNext₁⟩
  rcases h₂ hRep₂ hStep₂ with ⟨b₂, hAbsStep₂, hRepNext₂⟩
  exact ⟨(b₁, b₂), ⟨hAbsStep₁, hAbsStep₂⟩,
    ⟨hRepNext₁, hRepNext₂⟩⟩

theorem asyncProduct_forwardSimulation
    {C₁ : TransitionSystem σ} {A₁ : TransitionSystem α}
    {C₂ : TransitionSystem τ} {A₂ : TransitionSystem β}
    {R₁ : σ → α → Prop} {R₂ : τ → β → Prop}
    (h₁ : ForwardSimulation C₁ A₁ R₁)
    (h₂ : ForwardSimulation C₂ A₂ R₂) :
    ForwardSimulation
      (FiniteTraceBarriers.TransitionSystem.AsyncProduct C₁ C₂)
      (FiniteTraceBarriers.TransitionSystem.AsyncProduct A₁ A₂)
      (fun c a => R₁ c.1 a.1 ∧ R₂ c.2 a.2) := by
  intro c d a hRep hStep
  rcases hRep with ⟨hRep₁, hRep₂⟩
  rcases hStep with hLeft | hRight
  · rcases hLeft with ⟨hStep₁, hSame₂⟩
    rcases h₁ hRep₁ hStep₁ with ⟨b₁, hAbsStep₁, hRepNext₁⟩
    exact ⟨(b₁, a.2), Or.inl ⟨hAbsStep₁, rfl⟩,
      ⟨hRepNext₁, by simpa [hSame₂] using hRep₂⟩⟩
  · rcases hRight with ⟨hSame₁, hStep₂⟩
    rcases h₂ hRep₂ hStep₂ with ⟨b₂, hAbsStep₂, hRepNext₂⟩
    exact ⟨(a.1, b₂), Or.inr ⟨rfl, hAbsStep₂⟩,
      ⟨by simpa [hSame₁] using hRep₁, hRepNext₂⟩⟩

theorem syncProduct_abstractInvariant
    {A₁ : TransitionSystem α} {A₂ : TransitionSystem β}
    {Inv₁ : α → Prop} {Inv₂ : β → Prop}
    (h₁ : AbstractInvariant A₁ Inv₁)
    (h₂ : AbstractInvariant A₂ Inv₂) :
    AbstractInvariant
      (FiniteTraceBarriers.TransitionSystem.SyncProduct A₁ A₂)
      (fun a : α × β => Inv₁ a.1 ∧ Inv₂ a.2) := by
  intro a b hInv hStep
  exact ⟨h₁ hInv.1 hStep.1, h₂ hInv.2 hStep.2⟩

theorem asyncProduct_abstractInvariant
    {A₁ : TransitionSystem α} {A₂ : TransitionSystem β}
    {Inv₁ : α → Prop} {Inv₂ : β → Prop}
    (h₁ : AbstractInvariant A₁ Inv₁)
    (h₂ : AbstractInvariant A₂ Inv₂) :
    AbstractInvariant
      (FiniteTraceBarriers.TransitionSystem.AsyncProduct A₁ A₂)
      (fun a : α × β => Inv₁ a.1 ∧ Inv₂ a.2) := by
  intro a b hInv hStep
  rcases hStep with hLeft | hRight
  · exact ⟨h₁ hInv.1 hLeft.1, by simpa [hLeft.2] using hInv.2⟩
  · exact ⟨by simpa [hRight.1] using hInv.1, h₂ hInv.2 hRight.2⟩

end TransitionSystem

end AbstractInterpretationDisasterSafety
end Proofs
