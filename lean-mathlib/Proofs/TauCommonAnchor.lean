import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Boolean repairs with a common solution anchor

For a scalar value in an arbitrary Boolean algebra, `mix x a p` keeps `x` under
the complement of the mask `p` and uses the anchor `a` under `p`. A residual
`f` is assumed to preserve every such Boolean mixture. This locality premise
is explicit; the results do not apply to an arbitrary nonlocal function.

With a common zero-residual anchor, two local residual repairs commute and
their composition equals the repair using the pointwise join of residuals.
Both constraints hold after composition, and every common solution is fixed.

These are standard Boolean-algebra identities, with no novelty claim. The
formalized value and residual both lie in the same Boolean algebra. This file
does not formalize vector syntax, a polynomial compiler, anchor synthesis,
causal witnesses, Tau execution, or performance and settlement claims.
-/

namespace TauCommonAnchor

universe u

variable {B : Type u} [BooleanAlgebra B]

/-- Select the anchor on the mask and the original value on its complement. -/
def mix (x a p : B) : B :=
  (x ⊓ pᶜ) ⊔ (a ⊓ p)

/-- Residual locality under every Boolean mask, stated independently of syntax. -/
def MixingLocal (f : B → B) : Prop :=
  ∀ x a p, f (mix x a p) = mix (f x) (f a) p

/-- Repair the part of the value selected by its residual using a fixed anchor. -/
def repair (f : B → B) (a x : B) : B :=
  mix x a (f x)

/-- Two successive mixtures with the same anchor combine their masks by join. -/
theorem mix_mix_common_anchor (x a p q : B) :
    mix (mix x a p) a q = mix x a (p ⊔ q) := by
  have hmask : (p ⊓ qᶜ) ⊔ q = p ⊔ q := by
    simp [sup_inf_right]
  simp only [mix, inf_sup_right, compl_sup, inf_assoc, sup_assoc]
  rw [← inf_sup_left, hmask]

/-- Pointwise joins retain the required residual locality. -/
theorem mixing_local_sup {f g : B → B} (hf : MixingLocal f) (hg : MixingLocal g) :
    MixingLocal (fun x => f x ⊔ g x) := by
  intro x a p
  change f (mix x a p) ⊔ g (mix x a p) = mix (f x ⊔ g x) (f a ⊔ g a) p
  rw [hf x a p, hg x a p]
  simp only [mix, inf_sup_right, sup_assoc, sup_left_comm]

/-- A local residual is zero after repair to one of its zero-residual anchors. -/
theorem repair_sound (f : B → B) (a x : B)
    (hf : MixingLocal f) (ha : f a = ⊥) :
    f (repair f a x) = ⊥ := by
  unfold repair
  rw [hf x a (f x), ha]
  simp [mix]

/-- Every zero-residual value is fixed, without needing the locality premise. -/
theorem repair_fixes (f : B → B) (a x : B) (hx : f x = ⊥) :
    repair f a x = x := by
  simp [repair, hx, mix]

/-- Soundness and reproduction imply idempotence of the repair. -/
theorem repair_idempotent (f : B → B) (a x : B)
    (hf : MixingLocal f) (ha : f a = ⊥) :
    repair f a (repair f a x) = repair f a x :=
  repair_fixes f a (repair f a x) (repair_sound f a x hf ha)

/-- The image of the repair is exactly the zero set of the residual. -/
theorem repair_image_iff (f : B → B) (a y : B)
    (hf : MixingLocal f) (ha : f a = ⊥) :
    (∃ x, repair f a x = y) ↔ f y = ⊥ := by
  constructor
  · rintro ⟨x, rfl⟩
    exact repair_sound f a x hf ha
  · intro hy
    exact ⟨y, repair_fixes f a y hy⟩

/-- Another repair removes its mask from any local residual vanishing at the anchor. -/
theorem residual_after_repair (f g : B → B) (a x : B)
    (hf : MixingLocal f) (ha : f a = ⊥) :
    f (repair g a x) = f x ⊓ (g x)ᶜ := by
  unfold repair
  rw [hf x a (g x), ha]
  simp [mix]

/-- Shared-anchor composition equals one repair with the join of the original residuals.
Only the outer residual requires locality and a zero anchor for this equality. -/
theorem repair_compose_eq_join (f g : B → B) (a x : B)
    (hf : MixingLocal f) (ha : f a = ⊥) :
    repair f a (repair g a x) = repair (fun y => f y ⊔ g y) a x := by
  change mix (repair g a x) a (f (repair g a x)) = mix x a (f x ⊔ g x)
  rw [residual_after_repair f g a x hf ha]
  change mix (mix x a (g x)) a (f x ⊓ (g x)ᶜ) = mix x a (f x ⊔ g x)
  rw [mix_mix_common_anchor]
  have hmask : g x ⊔ (f x ⊓ (g x)ᶜ) = f x ⊔ g x := by
    rw [sup_inf_left, sup_compl_eq_top, inf_top_eq, sup_comm]
  rw [hmask]

/-- Local residual repairs commute when the same anchor solves both residual equations. -/
theorem common_anchor_commutes (f g : B → B) (a x : B)
    (hf : MixingLocal f) (hg : MixingLocal g) (hfa : f a = ⊥) (hga : g a = ⊥) :
    repair f a (repair g a x) = repair g a (repair f a x) := by
  rw [repair_compose_eq_join f g a x hf hfa, repair_compose_eq_join g f a x hg hga]
  change mix x a (f x ⊔ g x) = mix x a (g x ⊔ f x)
  rw [sup_comm (f x) (g x)]

/-- The composite solves both residual equations and fixes every common solution. -/
theorem common_anchor_sound_and_fixes (f g : B → B) (a : B)
    (hf : MixingLocal f) (hg : MixingLocal g) (hfa : f a = ⊥) (hga : g a = ⊥) :
    (∀ x, f (repair f a (repair g a x)) = ⊥ ∧ g (repair f a (repair g a x)) = ⊥) ∧
    (∀ x, f x = ⊥ → g x = ⊥ → repair f a (repair g a x) = x) := by
  constructor
  · intro x
    constructor
    · exact repair_sound f a (repair g a x) hf hfa
    · rw [residual_after_repair g f a (repair g a x) hg hga, repair_sound g a x hg hga]
      simp
  · intro x hfx hgx
    rw [repair_fixes g a x hgx, repair_fixes f a x hfx]

/-- Meeting a value with a constant is an explicit family of local residuals. -/
theorem mixing_local_inf_const (c : B) : MixingLocal (fun x => x ⊓ c) := by
  intro x a p
  simp only [mix, inf_sup_right, inf_right_comm]

/-- At the bottom anchor, a masked residual repairs by removing that constant mask. -/
theorem repair_inf_const (c x : B) :
    repair (fun y => y ⊓ c) ⊥ x = x ⊓ cᶜ := by
  simp [repair, mix, compl_inf, inf_sup_left]

/-- A nonlocal coordinate swap has a zero anchor but its repair can remain invalid. -/
theorem zero_anchor_without_locality_can_fail :
    let f : Bool × Bool → Bool × Bool := fun x => (x.2, x.1)
    f ⊥ = ⊥ ∧ ¬MixingLocal f ∧ f (repair f ⊥ (true, false)) ≠ ⊥ := by
  let f : Bool × Bool → Bool × Bool := fun x => (x.2, x.1)
  change f ⊥ = ⊥ ∧ ¬MixingLocal f ∧ f (repair f ⊥ (true, false)) ≠ ⊥
  have hbad : f (repair f ⊥ (true, false)) ≠ ⊥ := by decide
  exact ⟨rfl, (fun hf => hbad (repair_sound f ⊥ (true, false) hf rfl)), hbad⟩

/-- A concrete Boolean instance changes an invalid value and preserves a valid one. -/
example :
    repair (fun x : Bool => x ⊓ true) false true = false ∧
    repair (fun x : Bool => x ⊓ true) false false = false := by
  decide

end TauCommonAnchor
