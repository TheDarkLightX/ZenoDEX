import Proofs.CertifiedFinancialMathObjects
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Zeno Payoff Language

This file formalizes a typed, bounded-payoff DSL in the style of ZPL v0.1.

The design split is:

- a typed AST (`Expr`)
- a partial compiler (`compile`) that rejects unsafe products
- a small compiled artifact (`CompiledExpr`) carrying value plus interval proof

The central theorem is compiler soundness:

`compile e = some c -> eval e ∈ [c.lower, c.upper]`

This is the Lean core of:

```text
safe DSL + compiler/prover + small verifier/runtime
```

## Proof architecture

Compiler soundness factors into two layers:

1. **Value preservation** (`compile_value_correct`): every successful compilation
   produces a `CompiledExpr` whose `.value` equals `Expr.eval e`.

2. **Interval soundness** (`compile_correct`): follows immediately because each
   `CompiledExpr` constructor already carries a proof that `lower ≤ value ∧ value ≤ upper`
   in its `sound` field.  Rewriting `value` to `eval e` via (1) gives the
   desired `lower ≤ eval e ∧ eval e ≤ upper`.
-/

namespace Proofs

namespace ZenoPayoffLanguage

open CertifiedFinancialMathObjects

variable {Asset : Type _}

/-- The small unit/type surface for ZPL v0.1. -/
inductive ValueType (Asset : Type _) where
  | index
  | amount (asset : Asset)
  | price (base quote : Asset)
  deriving DecidableEq, Repr

/-- Certified leaves: runtime value together with a declared interval. -/
structure Atom {Asset : Type _} (τ : ValueType Asset) where
  value : ℝ
  lower : ℝ
  upper : ℝ
  sound : lower ≤ value ∧ value ≤ upper

/-- ZPL v0.1 expressions. The type index is the unit discipline. -/
inductive Expr (Asset : Type _) : ValueType Asset → Type _ where
  | leaf {τ} : Atom τ → Expr Asset τ
  | const {τ} : ℝ → Expr Asset τ
  | add {τ} : Expr Asset τ → Expr Asset τ → Expr Asset τ
  | sub {τ} : Expr Asset τ → Expr Asset τ → Expr Asset τ
  | neg {τ} : Expr Asset τ → Expr Asset τ
  | minExpr {τ} : Expr Asset τ → Expr Asset τ → Expr Asset τ
  | maxExpr {τ} : Expr Asset τ → Expr Asset τ → Expr Asset τ
  | clamp {τ} : Expr Asset τ → (A B : ℝ) → A ≤ B → Expr Asset τ
  | scale {τ} : ℝ → Expr Asset τ → Expr Asset τ
  | indexMulNonneg :
      Expr Asset (ValueType.index) →
      Expr Asset (ValueType.index) →
      Expr Asset (ValueType.index)
  | amountMulIndexNonneg {a : Asset} :
      Expr Asset (ValueType.amount a) →
      Expr Asset (ValueType.index) →
      Expr Asset (ValueType.amount a)
  | priceMulAmountNonneg {base quote : Asset} :
      Expr Asset (ValueType.price base quote) →
      Expr Asset (ValueType.amount base) →
      Expr Asset (ValueType.amount quote)

namespace Expr

/-- Direct denotational semantics of a ZPL expression. -/
def eval : Expr Asset τ → ℝ
  | Expr.leaf src => src.value
  | const c => c
  | add e₁ e₂ => eval e₁ + eval e₂
  | sub e₁ e₂ => eval e₁ - eval e₂
  | neg e => - eval e
  | Expr.minExpr e₁ e₂ => min (eval e₁) (eval e₂)
  | Expr.maxExpr e₁ e₂ => max (eval e₁) (eval e₂)
  | clamp e A B _ => Proofs.CertifiedFinancialMathObjects.CertifiedPayoff.clampValue (eval e) A B
  | scale a e => a * eval e
  | indexMulNonneg e₁ e₂ => eval e₁ * eval e₂
  | amountMulIndexNonneg e₁ e₂ => eval e₁ * eval e₂
  | priceMulAmountNonneg e₁ e₂ => eval e₁ * eval e₂

end Expr

/-- The compiler output checked by a small runtime: one value, one interval,
and a proof that the value lies inside the interval. -/
structure CompiledExpr {Asset : Type _} (τ : ValueType Asset) where
  value : ℝ
  lower : ℝ
  upper : ℝ
  sound : lower ≤ value ∧ value ≤ upper

namespace CompiledExpr

@[simp] theorem lower_le (c : CompiledExpr (Asset := Asset) τ) : c.lower ≤ c.value :=
  c.sound.1

@[simp] theorem le_upper (c : CompiledExpr (Asset := Asset) τ) : c.value ≤ c.upper :=
  c.sound.2

def ofAtom (src : Atom τ) : CompiledExpr (Asset := Asset) τ where
  value := src.value
  lower := src.lower
  upper := src.upper
  sound := src.sound

def const (τ : ValueType Asset) (x : ℝ) : CompiledExpr (Asset := Asset) τ where
  value := x
  lower := x
  upper := x
  sound := by constructor <;> simp

def add (c₁ c₂ : CompiledExpr (Asset := Asset) τ) : CompiledExpr (Asset := Asset) τ where
  value := c₁.value + c₂.value
  lower := c₁.lower + c₂.lower
  upper := c₁.upper + c₂.upper
  sound := by
    constructor <;> linarith [c₁.lower_le, c₁.le_upper, c₂.lower_le, c₂.le_upper]

def sub (c₁ c₂ : CompiledExpr (Asset := Asset) τ) : CompiledExpr (Asset := Asset) τ where
  value := c₁.value - c₂.value
  lower := c₁.lower - c₂.upper
  upper := c₁.upper - c₂.lower
  sound := by
    constructor <;> linarith [c₁.lower_le, c₁.le_upper, c₂.lower_le, c₂.le_upper]

def neg (c : CompiledExpr (Asset := Asset) τ) : CompiledExpr (Asset := Asset) τ where
  value := -c.value
  lower := -c.upper
  upper := -c.lower
  sound := by
    constructor <;> linarith [c.lower_le, c.le_upper]

def pointwiseMin (c₁ c₂ : CompiledExpr (Asset := Asset) τ) : CompiledExpr (Asset := Asset) τ where
  value := min c₁.value c₂.value
  lower := min c₁.lower c₂.lower
  upper := min c₁.upper c₂.upper
  sound := by
    constructor
    · exact min_le_min c₁.lower_le c₂.lower_le
    · exact min_le_min c₁.le_upper c₂.le_upper

def pointwiseMax (c₁ c₂ : CompiledExpr (Asset := Asset) τ) : CompiledExpr (Asset := Asset) τ where
  value := max c₁.value c₂.value
  lower := max c₁.lower c₂.lower
  upper := max c₁.upper c₂.upper
  sound := by
    constructor
    · exact max_le_max c₁.lower_le c₂.lower_le
    · exact max_le_max c₁.le_upper c₂.le_upper

def clamp (c : CompiledExpr (Asset := Asset) τ) (A B : ℝ) (hAB : A ≤ B) :
    CompiledExpr (Asset := Asset) τ where
  value := Proofs.CertifiedFinancialMathObjects.CertifiedPayoff.clampValue c.value A B
  lower := A
  upper := B
  sound := by
    constructor
    · exact Proofs.CertifiedFinancialMathObjects.CertifiedPayoff.left_le_clampValue c.value A B
    · exact Proofs.CertifiedFinancialMathObjects.CertifiedPayoff.clampValue_le_right c.value A B hAB

noncomputable def scale (a : ℝ) (c : CompiledExpr (Asset := Asset) τ) : CompiledExpr (Asset := Asset) τ :=
  if ha : 0 ≤ a then
    { value := a * c.value
      lower := a * c.lower
      upper := a * c.upper
      sound := by
        constructor
        · exact mul_le_mul_of_nonneg_left c.lower_le ha
        · exact mul_le_mul_of_nonneg_left c.le_upper ha }
  else
    { value := a * c.value
      lower := a * c.upper
      upper := a * c.lower
      sound := by
        have hle : a ≤ 0 := le_of_not_ge ha
        constructor
        · exact mul_le_mul_of_nonpos_left c.le_upper hle
        · exact mul_le_mul_of_nonpos_left c.lower_le hle }

def zero (τ : ValueType Asset) : CompiledExpr (Asset := Asset) τ := const τ 0

def mulNonneg (c₁ : CompiledExpr (Asset := Asset) τ₁)
    (c₂ : CompiledExpr (Asset := Asset) τ₂)
    (h₁ : 0 ≤ c₁.lower) (h₂ : 0 ≤ c₂.lower) :
    CompiledExpr (Asset := Asset) τ₃ where
  value := c₁.value * c₂.value
  lower := c₁.lower * c₂.lower
  upper := c₁.upper * c₂.upper
  sound := by
    have h₁v : 0 ≤ c₁.value := le_trans h₁ c₁.lower_le
    have h₂v : 0 ≤ c₂.value := le_trans h₂ c₂.lower_le
    have h₁u : 0 ≤ c₁.upper := le_trans h₁ (le_trans c₁.lower_le c₁.le_upper)
    constructor
    · exact mul_le_mul c₁.lower_le c₂.lower_le h₂ h₁v
    · exact mul_le_mul c₁.le_upper c₂.le_upper h₂v h₁u

/-- `scale` preserves `value` regardless of the sign of the scalar. -/
private theorem scale_value (a : ℝ) (c : CompiledExpr (Asset := Asset) τ) :
    (CompiledExpr.scale a c).value = a * c.value := by
  unfold scale; split <;> rfl

def toCertifiedPayoff (c : CompiledExpr (Asset := Asset) τ) : CertifiedPayoff Unit where
  payoff := fun _ => c.value
  lower := c.lower
  upper := c.upper
  sound := by intro _; exact c.sound

end CompiledExpr

open Expr

/-- ZPL compiler. It is partial because live-admissible products require
domain proofs, especially nonnegative product factors. -/
noncomputable def compile : Expr Asset τ → Option (CompiledExpr (Asset := Asset) τ)
  | Expr.leaf src => some (CompiledExpr.ofAtom src)
  | const c => some (CompiledExpr.const τ c)
  | add e₁ e₂ => do
      let c₁ ← compile e₁
      let c₂ ← compile e₂
      pure (CompiledExpr.add c₁ c₂)
  | sub e₁ e₂ => do
      let c₁ ← compile e₁
      let c₂ ← compile e₂
      pure (CompiledExpr.sub c₁ c₂)
  | neg e => do
      let c ← compile e
      pure (CompiledExpr.neg c)
  | Expr.minExpr e₁ e₂ => do
      let c₁ ← compile e₁
      let c₂ ← compile e₂
      pure (CompiledExpr.pointwiseMin c₁ c₂)
  | Expr.maxExpr e₁ e₂ => do
      let c₁ ← compile e₁
      let c₂ ← compile e₂
      pure (CompiledExpr.pointwiseMax c₁ c₂)
  | clamp e A B hAB => do
      let c ← compile e
      pure (CompiledExpr.clamp c A B hAB)
  | scale a e => do
      let c ← compile e
      pure (CompiledExpr.scale a c)
  | indexMulNonneg e₁ e₂ => do
      let c₁ ← compile e₁
      let c₂ ← compile e₂
      if h : 0 ≤ c₁.lower ∧ 0 ≤ c₂.lower then
        pure (CompiledExpr.mulNonneg c₁ c₂ h.1 h.2)
      else
        none
  | amountMulIndexNonneg e₁ e₂ => do
      let c₁ ← compile e₁
      let c₂ ← compile e₂
      if h : 0 ≤ c₁.lower ∧ 0 ≤ c₂.lower then
        pure (CompiledExpr.mulNonneg c₁ c₂ h.1 h.2)
      else
        none
  | priceMulAmountNonneg e₁ e₂ => do
      let c₁ ← compile e₁
      let c₂ ← compile e₂
      if h : 0 ≤ c₁.lower ∧ 0 ≤ c₂.lower then
        pure (CompiledExpr.mulNonneg c₁ c₂ h.1 h.2)
      else
        none

/-! ## Compiler correctness

The compiler proof factors into two layers:

1. `compile_value_correct` — value preservation: every successful compilation
   produces `c.value = Expr.eval e`.

2. `compile_correct` — a short corollary: interval soundness follows because
   `CompiledExpr.sound` already proves `c.lower ≤ c.value ∧ c.value ≤ c.upper`,
   and substituting the value-preservation equality yields bounds on `Expr.eval e`.

Named helpers (`bind1_eq_some`, `bind2_eq_some`) factor out the `Option.bind`
unwrapping that recurs in every binary/unary constructor case. -/

/-- Unwrap a single `Option.bind` layer. -/
private theorem bind1_eq_some {α β : Type _} {a : Option α} {f : α → β}
    {c : β}
    (h : (a.bind fun x => some (f x)) = some c) :
    ∃ x, a = some x ∧ c = f x := by
  cases a with
  | none => simp at h
  | some x => exact ⟨x, rfl, by simpa using h.symm⟩

/-- Unwrap two successive `Option.bind` layers into existentials. -/
private theorem bind2_eq_some {α β γ : Type _} {a : Option α} {f : α → Option β}
    {g : α → β → γ} {c : γ}
    (h : (a.bind fun x => (f x).bind fun y => some (g x y)) = some c) :
    ∃ x y, a = some x ∧ f x = some y ∧ c = g x y := by
  cases a with
  | none => simp at h
  | some x =>
    simp at h
    cases hf : f x with
    | none => simp [hf] at h
    | some y => exact ⟨x, y, rfl, hf, by simp [hf] at h; exact h.symm⟩

/-- Unwrap the `Option.bind … dite` pattern shared by the three nonneg-product
constructors. Returns compiled sub-results, recursive compilation equalities,
the nonneg witnesses, and the output identity. -/
private theorem bind2_dite_nonneg_eq_some
    {τ₁ τ₂ τ₃ : ValueType Asset}
    {e₁ : Expr Asset τ₁} {e₂ : Expr Asset τ₂}
    {c : CompiledExpr (Asset := Asset) τ₃}
    (h : ((compile e₁).bind fun c₁ => (compile e₂).bind fun c₂ =>
          if hnn : 0 ≤ c₁.lower ∧ 0 ≤ c₂.lower then
            some (CompiledExpr.mulNonneg c₁ c₂ hnn.1 hnn.2)
          else none) = some c) :
    ∃ c₁ c₂, compile e₁ = some c₁ ∧ compile e₂ = some c₂ ∧
      ∃ hnn : 0 ≤ c₁.lower ∧ 0 ≤ c₂.lower,
        c = CompiledExpr.mulNonneg c₁ c₂ hnn.1 hnn.2 := by
  cases h₁ : compile e₁ with
  | none => simp [h₁] at h
  | some c₁ =>
    cases h₂ : compile e₂ with
    | none => simp [h₂] at h
    | some c₂ =>
      rw [h₁, h₂] at h; simp at h
      by_cases hnn : 0 ≤ c₁.lower ∧ 0 ≤ c₂.lower
      · exact ⟨c₁, c₂, rfl, rfl, hnn, by simp [hnn] at h; exact h.symm⟩
      · simp [hnn] at h

/-- Value preservation: a successfully compiled expression has `c.value = Expr.eval e`.

This is the main workhorse of compiler correctness.  Each constructor case
reduces to showing that the `CompiledExpr` builder preserves the value field,
which is typically definitional once the recursive results are substituted. -/
private theorem compile_value_correct :
    ∀ {τ} (e : Expr Asset τ) (c : CompiledExpr (Asset := Asset) τ),
      compile e = some c →
      c.value = Expr.eval e
  | _, Expr.leaf _, _, h => by simp [compile] at h; cases h; rfl
  | _, Expr.const _, _, h => by simp [compile] at h; cases h; rfl
  | _, add e₁ e₂, _, h => by
      simp only [compile] at h
      obtain ⟨c₁, c₂, h₁, h₂, rfl⟩ := bind2_eq_some h
      simp [CompiledExpr.add, Expr.eval,
        compile_value_correct e₁ c₁ h₁, compile_value_correct e₂ c₂ h₂]
  | _, sub e₁ e₂, _, h => by
      simp only [compile] at h
      obtain ⟨c₁, c₂, h₁, h₂, rfl⟩ := bind2_eq_some h
      simp [CompiledExpr.sub, Expr.eval,
        compile_value_correct e₁ c₁ h₁, compile_value_correct e₂ c₂ h₂]
  | _, neg e, _, h => by
      simp only [compile] at h
      obtain ⟨ce, hc, rfl⟩ := bind1_eq_some h
      simp [CompiledExpr.neg, Expr.eval, compile_value_correct e ce hc]
  | _, Expr.minExpr e₁ e₂, _, h => by
      simp only [compile] at h
      obtain ⟨c₁, c₂, h₁, h₂, rfl⟩ := bind2_eq_some h
      simp [CompiledExpr.pointwiseMin, Expr.eval,
        compile_value_correct e₁ c₁ h₁, compile_value_correct e₂ c₂ h₂]
  | _, Expr.maxExpr e₁ e₂, _, h => by
      simp only [compile] at h
      obtain ⟨c₁, c₂, h₁, h₂, rfl⟩ := bind2_eq_some h
      simp [CompiledExpr.pointwiseMax, Expr.eval,
        compile_value_correct e₁ c₁ h₁, compile_value_correct e₂ c₂ h₂]
  | _, clamp e A B _, _, h => by
      simp only [compile] at h
      obtain ⟨ce, hc, rfl⟩ := bind1_eq_some h
      simp [CompiledExpr.clamp, Expr.eval, compile_value_correct e ce hc]
  | _, scale a e, _, h => by
      simp only [compile] at h
      obtain ⟨ce, hc, rfl⟩ := bind1_eq_some h
      rw [CompiledExpr.scale_value, Expr.eval, compile_value_correct e ce hc]
  | _, indexMulNonneg e₁ e₂, _, h => by
      simp only [compile] at h
      obtain ⟨c₁, c₂, h₁, h₂, hnn, rfl⟩ := bind2_dite_nonneg_eq_some h
      simp [CompiledExpr.mulNonneg, Expr.eval,
        compile_value_correct e₁ c₁ h₁, compile_value_correct e₂ c₂ h₂]
  | _, amountMulIndexNonneg e₁ e₂, _, h => by
      simp only [compile] at h
      obtain ⟨c₁, c₂, h₁, h₂, hnn, rfl⟩ := bind2_dite_nonneg_eq_some h
      simp [CompiledExpr.mulNonneg, Expr.eval,
        compile_value_correct e₁ c₁ h₁, compile_value_correct e₂ c₂ h₂]
  | _, priceMulAmountNonneg e₁ e₂, _, h => by
      simp only [compile] at h
      obtain ⟨c₁, c₂, h₁, h₂, hnn, rfl⟩ := bind2_dite_nonneg_eq_some h
      simp [CompiledExpr.mulNonneg, Expr.eval,
        compile_value_correct e₁ c₁ h₁, compile_value_correct e₂ c₂ h₂]

/-- Compiler correctness: a compiled expression preserves denotation and its
reported interval really contains the denotation.

The proof is a short corollary of `compile_value_correct`: value preservation
lets us rewrite the `CompiledExpr`'s own `sound` invariant—which certifies
`c.lower ≤ c.value ∧ c.value ≤ c.upper`—into bounds on `Expr.eval e`. -/
theorem compile_correct :
    ∀ {τ} (e : Expr Asset τ) (c : CompiledExpr (Asset := Asset) τ),
      compile e = some c →
      c.value = Expr.eval e ∧ c.lower ≤ Expr.eval e ∧ Expr.eval e ≤ c.upper := by
  intro τ e c h
  have hv := compile_value_correct e c h
  exact ⟨hv, hv ▸ c.lower_le, hv ▸ c.le_upper⟩

/-- The compiler certificate implies bilateral collateral sufficiency for the
compiled denotation. -/
theorem compile_no_default
    {τ : ValueType Asset} {e : Expr Asset τ} {c : CompiledExpr (Asset := Asset) τ}
    (h : compile e = some c) :
    0 ≤ holderCollateral c.lower + Expr.eval e ∧
      0 ≤ writerCollateral c.upper - Expr.eval e := by
  rcases compile_correct e c h with ⟨hv, hl, hu⟩
  simpa [hv] using bilateral_no_default_of_bounds ⟨hl, hu⟩

/-- A small verifier artifact: the runtime does not re-run the compiler, it
checks a compiled interval certificate against the expression and posted
collateral. -/
structure VerifiedPayoff (a : Asset) where
  expr : Expr Asset (ValueType.amount a)
  compiled : CompiledExpr (Asset := Asset) (ValueType.amount a)
  compile_ok : compile expr = some compiled
  holderPosted : ℝ
  writerPosted : ℝ
  holderEnough : holderCollateral compiled.lower ≤ holderPosted
  writerEnough : writerCollateral compiled.upper ≤ writerPosted

/-- Small-verifier theorem: if the manifest matches a successful compile and the
posted collateral dominates the certified requirement, settlement is safe. -/
theorem VerifiedPayoff.settlement_safe
    {a : Asset} (V : VerifiedPayoff (Asset := Asset) a) :
    0 ≤ V.holderPosted + Expr.eval V.expr ∧
      0 ≤ V.writerPosted - Expr.eval V.expr := by
  rcases compile_no_default (e := V.expr) (c := V.compiled) V.compile_ok with ⟨hh, hw⟩
  constructor
  · linarith [V.holderEnough, hh]
  · linarith [V.writerEnough, hw]

/-- `FIRE-IR`: the compact interval-carrying object artifact produced by the
compiler for a payoff expression. -/
abbrev FIREIR (τ : ValueType Asset) := CompiledExpr (Asset := Asset) τ

/-- `FIRE-Cert`: compiler output for one settlement leg. The current formal
surface records the compiled interval certificate and the proof that it matches
the ZPL expression. -/
structure FIRECert (a : Asset) where
  expr : Expr Asset (ValueType.amount a)
  ir : FIREIR (Asset := Asset) (ValueType.amount a)
  compile_ok : compile expr = some ir

/-- Input to the small verifier `FIRE-V`: a certificate plus posted collateral. -/
structure FIREVInput (a : Asset) where
  cert : FIRECert (Asset := Asset) a
  holderPosted : ℝ
  writerPosted : ℝ

/-- `FIRE-V` acceptance condition for the current two-party payoff core. -/
def FIREVAccept {a : Asset} (I : FIREVInput (Asset := Asset) a) : Prop :=
  holderCollateral I.cert.ir.lower ≤ I.holderPosted ∧
    writerCollateral I.cert.ir.upper ≤ I.writerPosted

/-- Settlement safety for the two-party payoff core. -/
def SettlementSafe {a : Asset} (I : FIREVInput (Asset := Asset) a) : Prop :=
  0 ≤ I.holderPosted + Expr.eval I.cert.expr ∧
    0 ≤ I.writerPosted - Expr.eval I.cert.expr

/-- Main small-verifier theorem for the current FIRE core:

`FIREVAccept -> SettlementSafe`.

Reading: if the verifier accepts the compiler certificate and posted
collateral, the resulting settlement is mechanically solvent for both sides. -/
theorem firev_accept_settlement_safe
    {a : Asset} (I : FIREVInput (Asset := Asset) a) :
    FIREVAccept I -> SettlementSafe I := by
  intro hAccept
  rcases hAccept with ⟨hHolder, hWriter⟩
  let V : VerifiedPayoff (Asset := Asset) a :=
    { expr := I.cert.expr
      compiled := I.cert.ir
      compile_ok := I.cert.compile_ok
      holderPosted := I.holderPosted
      writerPosted := I.writerPosted
      holderEnough := hHolder
      writerEnough := hWriter }
  simpa [SettlementSafe] using V.settlement_safe

/-- A simple two-party object in settlement asset `a`. -/
structure TwoPartyObject (a : Asset) where
  holder : Expr Asset (ValueType.amount a)
  writer : Expr Asset (ValueType.amount a)
  writerIsNeg : writer = Expr.neg holder

/-- Zero-sum settlement for two-party objects whose writer leg is the negation
of the holder leg. -/
theorem twoPartyObject_conserves
    {a : Asset} (O : TwoPartyObject (Asset := Asset) a) :
    Expr.eval O.holder + Expr.eval O.writer = 0 := by
  rw [O.writerIsNeg]
  simp [Expr.eval]

end ZenoPayoffLanguage

end Proofs
