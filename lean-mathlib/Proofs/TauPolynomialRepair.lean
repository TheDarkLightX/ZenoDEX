import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Polynomial residual repair of Boolean vectors

`Polynomial B I` is an original minimal syntax with fixed coefficients in an
arbitrary Boolean algebra `B` and variables indexed by an arbitrary type `I`.
Its complement, meet, and join operations evaluate in `B`. Structural induction
proves evaluation preserves uniform mixing of every vector coordinate by the
same scalar mask. No finiteness of `B` or `I` is assumed.

A zero-residual anchor then gives sound repair, fixed solutions, and exact
image. Shared-anchor composition equals repair by the joined residual. The
joint polynomial contract states these properties for the conjunction of two
zero-residual requirements.

These are standard Boolean polynomial identities, with no novelty claim. This
syntax has no established binding to a parser, BaTerm, a control compiler,
engine, bitvector comparison, or temporal/causal semantics. Coefficients and
the anchor are explicit fixed values; anchor synthesis is outside the theorem.
-/

namespace TauPolynomialRepair

universe u v

variable {B : Type u} {I : Type v} [BooleanAlgebra B]

/-- Scalar mixture, duplicated locally to keep this source independently checkable. -/
def mix (x a p : B) : B := (x ⊓ pᶜ) ⊔ (a ⊓ p)

private theorem mix_same (x p : B) : mix x x p = x := by
  unfold mix
  rw [← inf_sup_left]
  simp

private theorem mix_sup (x a y b p : B) :
    mix x a p ⊔ mix y b p = mix (x ⊔ y) (a ⊔ b) p := by
  simp only [mix, inf_sup_right, sup_assoc, sup_left_comm]

private theorem mix_inf (x a y b p : B) :
    mix x a p ⊓ mix y b p = mix (x ⊓ y) (a ⊓ b) p := by
  simp only [mix, inf_sup_left, inf_sup_right]
  rw [inf_inf_inf_comm x pᶜ y pᶜ, inf_inf_inf_comm a p y pᶜ,
    inf_inf_inf_comm x pᶜ b p, inf_inf_inf_comm a p b p]
  simp

private theorem mix_compl (x a p : B) :
    (mix x a p)ᶜ = mix xᶜ aᶜ p := by
  apply compl_unique
  · rw [mix_inf]
    simp [mix]
  · rw [mix_sup]
    simp [mix]

private theorem mix_nested (x a p q : B) :
    mix (mix x a p) a q = mix x a (p ⊔ q) := by
  have hmask : (p ⊓ qᶜ) ⊔ q = p ⊔ q := by simp [sup_inf_right]
  simp only [mix, inf_sup_right, compl_sup, inf_assoc, sup_assoc]
  rw [← inf_sup_left, hmask]

/-- Every coordinate uses the same scalar mask, with coordinatewise anchor values. -/
def vectorMix (x a : I → B) (p : B) : I → B :=
  fun j => mix (x j) (a j) p

/-- Locality of a scalar residual on vectors under uniform Boolean mixing. -/
def MixingLocal (f : (I → B) → B) : Prop :=
  ∀ x a p, f (vectorMix x a p) = mix (f x) (f a) p

/-- A minimal Boolean polynomial syntax; coefficients are fixed independently of variables. -/
inductive Polynomial (B : Type u) (I : Type v) where
  | coeff : B → Polynomial B I
  | var : I → Polynomial B I
  | compl : Polynomial B I → Polynomial B I
  | inf : Polynomial B I → Polynomial B I → Polynomial B I
  | sup : Polynomial B I → Polynomial B I → Polynomial B I

/-- Evaluate the syntax using the Boolean-algebra operations. -/
def Polynomial.eval : Polynomial B I → (I → B) → B
  | .coeff c, _ => c
  | .var j, x => x j
  | .compl t, x => (t.eval x)ᶜ
  | .inf s t, x => s.eval x ⊓ t.eval x
  | .sup s t, x => s.eval x ⊔ t.eval x

/-- Every polynomial in this syntax preserves uniform Boolean mixing of vectors. -/
theorem Polynomial.eval_mixing (t : Polynomial B I) : MixingLocal t.eval := by
  induction t with
  | coeff c =>
    intro x a p
    exact (mix_same c p).symm
  | var j => intro x a p; rfl
  | compl t ih =>
    intro x a p
    change (t.eval (vectorMix x a p))ᶜ = mix (t.eval x)ᶜ (t.eval a)ᶜ p
    rw [ih x a p]
    exact mix_compl _ _ _
  | inf s t ihs iht =>
    intro x a p
    change s.eval (vectorMix x a p) ⊓ t.eval (vectorMix x a p) =
      mix (s.eval x ⊓ t.eval x) (s.eval a ⊓ t.eval a) p
    rw [ihs x a p, iht x a p]
    exact mix_inf _ _ _ _ _
  | sup s t ihs iht =>
    intro x a p
    change s.eval (vectorMix x a p) ⊔ t.eval (vectorMix x a p) =
      mix (s.eval x ⊔ t.eval x) (s.eval a ⊔ t.eval a) p
    rw [ihs x a p, iht x a p]
    exact mix_sup _ _ _ _ _

/-- Repair every coordinate using the same scalar residual mask. -/
def repair (f : (I → B) → B) (a x : I → B) : I → B :=
  vectorMix x a (f x)

/-- Vector repair is sound under explicit locality and a zero-residual anchor. -/
theorem repair_sound (f : (I → B) → B) (a x : I → B)
    (hf : MixingLocal f) (ha : f a = ⊥) : f (repair f a x) = ⊥ := by
  unfold repair
  rw [hf x a (f x), ha]
  simp [mix]

/-- A zero-residual vector is fixed in every coordinate. -/
theorem repair_fixes (f : (I → B) → B) (a x : I → B) (hx : f x = ⊥) :
    repair f a x = x := by
  funext j
  simp [repair, vectorMix, mix, hx]

/-- The image of vector repair is precisely the residual's zero set. -/
theorem repair_image_iff (f : (I → B) → B) (a y : I → B)
    (hf : MixingLocal f) (ha : f a = ⊥) :
    (∃ x, repair f a x = y) ↔ f y = ⊥ := by
  constructor
  · rintro ⟨x, rfl⟩
    exact repair_sound f a x hf ha
  · intro hy
    exact ⟨y, repair_fixes f a y hy⟩

/-- Uniform repair removes its mask from a local residual vanishing at the anchor. -/
theorem residual_after_repair (f g : (I → B) → B) (a x : I → B)
    (hf : MixingLocal f) (ha : f a = ⊥) :
    f (repair g a x) = f x ⊓ (g x)ᶜ := by
  unfold repair
  rw [hf x a (g x), ha]
  simp [mix]

/-- Shared-anchor vector composition equals one repair using the joined residual.
Only the outer residual requires locality and a zero anchor for this equality. -/
theorem repair_compose_eq_join (f g : (I → B) → B) (a x : I → B)
    (hf : MixingLocal f) (ha : f a = ⊥) :
    repair f a (repair g a x) = repair (fun y => f y ⊔ g y) a x := by
  funext j
  change mix ((repair g a x) j) (a j) (f (repair g a x)) =
    mix (x j) (a j) (f x ⊔ g x)
  rw [residual_after_repair f g a x hf ha]
  change mix (mix (x j) (a j) (g x)) (a j) (f x ⊓ (g x)ᶜ) =
    mix (x j) (a j) (f x ⊔ g x)
  rw [mix_nested]
  have hmask : g x ⊔ (f x ⊓ (g x)ᶜ) = f x ⊔ g x := by
    rw [sup_inf_left, sup_compl_eq_top, inf_top_eq, sup_comm]
  rw [hmask]

/-- Two polynomial residual repairs commute around their shared solution anchor. -/
theorem Polynomial.repairs_commute (s t : Polynomial B I) (a x : I → B)
    (hs : s.eval a = ⊥) (ht : t.eval a = ⊥) :
    repair s.eval a (repair t.eval a x) = repair t.eval a (repair s.eval a x) := by
  rw [repair_compose_eq_join s.eval t.eval a x s.eval_mixing hs,
    repair_compose_eq_join t.eval s.eval a x t.eval_mixing ht]
  funext j
  change mix (x j) (a j) (s.eval x ⊔ t.eval x) =
    mix (x j) (a j) (t.eval x ⊔ s.eval x)
  rw [sup_comm (s.eval x) (t.eval x)]

/-- Joined polynomial repair solves both requirements, fixes common solutions,
and has exactly the common solution vectors as its image. -/
theorem Polynomial.joint_repair_contract (s t : Polynomial B I) (a : I → B)
    (hs : s.eval a = ⊥) (ht : t.eval a = ⊥) :
    (∀ x, s.eval (repair (s.sup t).eval a x) = ⊥ ∧
      t.eval (repair (s.sup t).eval a x) = ⊥) ∧
    (∀ x, s.eval x = ⊥ → t.eval x = ⊥ → repair (s.sup t).eval a x = x) ∧
    (∀ y, (∃ x, repair (s.sup t).eval a x = y) ↔ s.eval y = ⊥ ∧ t.eval y = ⊥) := by
  have ha : (s.sup t).eval a = ⊥ := by simp [eval, hs, ht]
  constructor
  · intro x
    exact sup_eq_bot_iff.mp (repair_sound (s.sup t).eval a x (s.sup t).eval_mixing ha)
  · constructor
    · intro x hsx htx
      apply repair_fixes
      simp [eval, hsx, htx]
    · intro y
      exact (repair_image_iff (s.sup t).eval a y (s.sup t).eval_mixing ha).trans
        sup_eq_bot_iff

/-- Two controls and a product Boolean algebra give a concrete uniform-mask instance. -/
example :
    let x : Bool → Bool × Bool := fun j => if j then (false, true) else (true, false)
    let a : Bool → Bool × Bool := fun _ => (false, false)
    let t : Polynomial (Bool × Bool) Bool := .sup (.var false) (.var true)
    ∀ j, repair t.eval a x j = (false, false) := by
  decide

end TauPolynomialRepair
