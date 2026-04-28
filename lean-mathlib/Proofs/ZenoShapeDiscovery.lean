import Mathlib

/-!
# ZenoDEX Shape Discovery

This module records abstract theorem shapes used by the disaster-state and
tokenomics work:

* canonical winners are unique under antisymmetric dominance;
* local accepted-step preservation lifts to accepted traces;
* guard coverage transfers across equivalent disaster axes;
* representative coverage lifts to whole axis families; and
* natural-number burn steps that are capped by surplus cannot cross a protected
  floor.

The module is intentionally abstract. It does not claim global DEX safety,
runtime enumeration completeness, or automatic guard synthesis.
-/

namespace Proofs
namespace ZenoShapeDiscovery

section CanonicalWinner

variable {α : Type} (R : α → α → Prop)

def IsReflexive : Prop := ∀ x, R x x
def IsTransitive : Prop := ∀ x y z, R x y → R y z → R x z
def IsAntisymmetric : Prop := ∀ x y, R x y → R y x → x = y

def Winner (C : α → Prop) (w : α) : Prop :=
  C w ∧ ∀ x, C x → R w x

theorem canonical_winner_unique
    (C : α → Prop)
    (hanti : IsAntisymmetric R)
    {w₁ w₂ : α}
    (hw₁ : Winner R C w₁)
    (hw₂ : Winner R C w₂) :
    w₁ = w₂ := by
  exact hanti _ _ (hw₁.2 _ hw₂.1) (hw₂.2 _ hw₁.1)

theorem winner_mem {C : α → Prop} {w : α} (hw : Winner R C w) : C w :=
  hw.1

theorem winner_le {C : α → Prop} {w : α} (hw : Winner R C w) {x : α} (hx : C x) :
    R w x :=
  hw.2 x hx

theorem winner_of_singleton
    (hrefl : IsReflexive R) (a : α) :
    Winner R (· = a) a :=
  ⟨rfl, fun _ hx => hx ▸ hrefl a⟩

theorem winner_of_subset {C D : α → Prop} {w : α}
    (hw : Winner R C w) (hD : ∀ x, D x → C x) (hwD : D w) :
    Winner R D w :=
  ⟨hwD, fun x hx => hw.2 x (hD x hx)⟩

end CanonicalWinner

section TraceLifting

variable {State Action : Type}

def AcceptedStep
    (Safe : State → Prop)
    (Accept : State → Action → State → Prop) : Prop :=
  ∀ s a s', Safe s → Accept s a s' → Safe s'

inductive AcceptedTrace
    (Accept : State → Action → State → Prop) :
    State → List Action → State → Prop
  | nil (s : State) : AcceptedTrace Accept s [] s
  | cons {s₀ s₁ s₂ : State} {a : Action} {rest : List Action} :
      Accept s₀ a s₁ →
      AcceptedTrace Accept s₁ rest s₂ →
      AcceptedTrace Accept s₀ (a :: rest) s₂

theorem accepted_trace_preserves_safe
    (Safe : State → Prop)
    (Accept : State → Action → State → Prop)
    (hstep : AcceptedStep Safe Accept)
    {s₀ s : State} {tr : List Action}
    (hs₀ : Safe s₀)
    (htr : AcceptedTrace Accept s₀ tr s) :
    Safe s := by
  induction htr with
  | nil => exact hs₀
  | cons ha _ ih => exact ih (hstep _ _ _ hs₀ ha)

theorem accepted_trace_excludes_disaster
    (Safe Disaster : State → Prop)
    (Accept : State → Action → State → Prop)
    (hstep : AcceptedStep Safe Accept)
    (hexcl : ∀ s, Safe s → ¬ Disaster s)
    {s₀ s : State} {tr : List Action}
    (hs₀ : Safe s₀)
    (htr : AcceptedTrace Accept s₀ tr s) :
    ¬ Disaster s := by
  exact hexcl s (accepted_trace_preserves_safe _ _ hstep hs₀ htr)

theorem accepted_trace_append
    (Accept : State → Action → State → Prop)
    {s₀ s₁ s₂ : State} {tr₁ tr₂ : List Action}
    (h₁ : AcceptedTrace Accept s₀ tr₁ s₁)
    (h₂ : AcceptedTrace Accept s₁ tr₂ s₂) :
    AcceptedTrace Accept s₀ (tr₁ ++ tr₂) s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons ha _ ih => exact AcceptedTrace.cons ha (ih h₂)

theorem accepted_trace_all_safe
    (Safe : State → Prop)
    (Accept : State → Action → State → Prop)
    (hstep : AcceptedStep Safe Accept)
    {s₀ s : State} {tr : List Action}
    (hs₀ : Safe s₀)
    (htr : AcceptedTrace Accept s₀ tr s) :
    Safe s₀ ∧ Safe s :=
  ⟨hs₀, accepted_trace_preserves_safe _ _ hstep hs₀ htr⟩

theorem accepted_trace_preserves_invariant
    (P : State → Prop)
    (Accept : State → Action → State → Prop)
    (hstep : ∀ s a s', P s → Accept s a s' → P s')
    {s₀ s : State} {tr : List Action}
    (hp₀ : P s₀)
    (htr : AcceptedTrace Accept s₀ tr s) :
    P s := by
  induction htr with
  | nil => exact hp₀
  | cons ha _ ih => exact ih (hstep _ _ _ hp₀ ha)

theorem accepted_trace_preserves_pair
    (P Q : State → Prop)
    (Accept : State → Action → State → Prop)
    (hP : AcceptedStep P Accept) (hQ : AcceptedStep Q Accept)
    {s₀ s : State} {tr : List Action}
    (hp₀ : P s₀) (hq₀ : Q s₀)
    (htr : AcceptedTrace Accept s₀ tr s) :
    P s ∧ Q s :=
  ⟨accepted_trace_preserves_safe P Accept hP hp₀ htr,
   accepted_trace_preserves_safe Q Accept hQ hq₀ htr⟩

end TraceLifting

section GuardCoverage

variable {Guard Axis Obligation : Type}

def AxisCovered
    (Requires : Axis → Obligation → Prop)
    (Covers : Guard → Obligation → Prop)
    (Selected : Guard → Prop)
    (a : Axis) : Prop :=
  ∀ o, Requires a o → ∃ g, Selected g ∧ Covers g o

def FamilyCovered
    (Requires : Axis → Obligation → Prop)
    (Covers : Guard → Obligation → Prop)
    (Selected : Guard → Prop)
    (Family : Axis → Prop) : Prop :=
  ∀ a, Family a → AxisCovered Requires Covers Selected a

def AxisObligationEquivalent
    (Requires : Axis → Obligation → Prop)
    (a b : Axis) : Prop :=
  ∀ o, Requires a o ↔ Requires b o

theorem coverage_transfers_across_equivalent_axes
    (Requires : Axis → Obligation → Prop)
    (Covers : Guard → Obligation → Prop)
    (Selected : Guard → Prop)
    {a b : Axis}
    (heq : AxisObligationEquivalent Requires a b)
    (ha : AxisCovered Requires Covers Selected a) :
    AxisCovered Requires Covers Selected b := by
  exact fun o ho => ha o (heq o |>.2 ho)

theorem representative_cover_lifts_to_family
    (Requires : Axis → Obligation → Prop)
    (Covers : Guard → Obligation → Prop)
    (Selected : Guard → Prop)
    (Family Rep : Axis → Prop)
    (hrep : ∀ a, Family a → ∃ r, Rep r ∧ AxisObligationEquivalent Requires r a)
    (hcov : FamilyCovered Requires Covers Selected Rep) :
    FamilyCovered Requires Covers Selected Family := by
  intro a ha
  obtain ⟨r, hr₁, hr₂⟩ := hrep a ha
  exact coverage_transfers_across_equivalent_axes Requires Covers Selected hr₂ (hcov r hr₁)

theorem axisCovered_mono
    (Requires : Axis → Obligation → Prop)
    (Covers : Guard → Obligation → Prop)
    (S₁ S₂ : Guard → Prop)
    (hmono : ∀ g, S₁ g → S₂ g)
    {a : Axis}
    (hcov : AxisCovered Requires Covers S₁ a) :
    AxisCovered Requires Covers S₂ a := by
  intro o ho
  obtain ⟨g, hg₁, hg₂⟩ := hcov o ho
  exact ⟨g, hmono g hg₁, hg₂⟩

theorem familyCovered_mono
    (Requires : Axis → Obligation → Prop)
    (Covers : Guard → Obligation → Prop)
    (S₁ S₂ : Guard → Prop)
    (hmono : ∀ g, S₁ g → S₂ g)
    {F : Axis → Prop}
    (hcov : FamilyCovered Requires Covers S₁ F) :
    FamilyCovered Requires Covers S₂ F := by
  intro a ha
  exact axisCovered_mono Requires Covers S₁ S₂ hmono (hcov a ha)

theorem axisObligationEquivalent_refl
    (Requires : Axis → Obligation → Prop) (a : Axis) :
    AxisObligationEquivalent Requires a a :=
  fun _ => Iff.rfl

theorem axisObligationEquivalent_symm
    (Requires : Axis → Obligation → Prop) {a b : Axis}
    (h : AxisObligationEquivalent Requires a b) :
    AxisObligationEquivalent Requires b a :=
  fun o => (h o).symm

theorem axisObligationEquivalent_trans
    (Requires : Axis → Obligation → Prop) {a b c : Axis}
    (hab : AxisObligationEquivalent Requires a b)
    (hbc : AxisObligationEquivalent Requires b c) :
    AxisObligationEquivalent Requires a c :=
  fun o => (hab o).trans (hbc o)

theorem familyCovered_union
    (Requires : Axis → Obligation → Prop)
    (Covers : Guard → Obligation → Prop)
    (Selected : Guard → Prop)
    {F₁ F₂ : Axis → Prop}
    (h₁ : FamilyCovered Requires Covers Selected F₁)
    (h₂ : FamilyCovered Requires Covers Selected F₂) :
    FamilyCovered Requires Covers Selected (fun a => F₁ a ∨ F₂ a) := by
  intro a ha
  rcases ha with hf₁ | hf₂
  · exact h₁ a hf₁
  · exact h₂ a hf₂

end GuardCoverage

section ZenoFloor

def FloorSafe (floor supply : Nat) : Prop := floor ≤ supply

def BurnStep (floor supply burn next : Nat) : Prop :=
  burn ≤ supply - floor ∧ next = supply - burn

theorem burn_step_preserves_floor
    {floor supply burn next : Nat}
    (hsafe : FloorSafe floor supply)
    (hstep : BurnStep floor supply burn next) :
    FloorSafe floor next := by
  unfold FloorSafe BurnStep at *
  omega

theorem burn_step_surplus_nonincreasing
    {floor supply burn next : Nat}
    (hsafe : FloorSafe floor supply)
    (hstep : BurnStep floor supply burn next) :
    next - floor ≤ supply - floor := by
  unfold FloorSafe BurnStep at *
  omega

theorem burn_step_zero_noop
    {floor supply next : Nat}
    (_hsafe : FloorSafe floor supply)
    (hstep : BurnStep floor supply 0 next) :
    next = supply := by
  unfold BurnStep at hstep
  omega

theorem max_burn_is_surplus
    {floor supply : Nat}
    (hsafe : FloorSafe floor supply) :
    BurnStep floor supply (supply - floor) floor := by
  unfold BurnStep FloorSafe at *
  omega

theorem max_burn_reaches_floor
    {floor supply : Nat}
    (hsafe : FloorSafe floor supply) :
    supply - (supply - floor) = floor := by
  unfold FloorSafe at *
  omega

end ZenoFloor

section CombinedShape

variable {State Action : Type}

theorem pipeline_safety_and_floor
    (Safe : State → Prop)
    (Disaster : State → Prop)
    (Accept : State → Action → State → Prop)
    (Floor : State → Prop)
    (hstepS : AcceptedStep Safe Accept)
    (hstepF : AcceptedStep Floor Accept)
    (hexcl : ∀ s, Safe s → ¬ Disaster s)
    {s₀ s : State} {tr : List Action}
    (hs₀ : Safe s₀) (hf₀ : Floor s₀)
    (htr : AcceptedTrace Accept s₀ tr s) :
    ¬ Disaster s ∧ Floor s :=
  ⟨accepted_trace_excludes_disaster Safe Disaster Accept hstepS hexcl hs₀ htr,
   accepted_trace_preserves_safe Floor Accept hstepF hf₀ htr⟩

theorem trace_winner_unique_at_each_step
    {β : Type} (R : β → β → Prop)
    (hanti : IsAntisymmetric R)
    (C : State → β → Prop)
    (Accept : State → Action → State → Prop)
    {s₀ s : State} {tr : List Action}
    (_htr : AcceptedTrace Accept s₀ tr s)
    {w₁ w₂ : β}
    (hw₁ : Winner R (C s) w₁)
    (hw₂ : Winner R (C s) w₂) :
    w₁ = w₂ :=
  canonical_winner_unique R (C s) hanti hw₁ hw₂

end CombinedShape

end ZenoShapeDiscovery
end Proofs
