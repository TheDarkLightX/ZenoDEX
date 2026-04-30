import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic

/-!
# DEX Value Algebra: Price-Parameterized Functionals

## The Key Mathematical Object

For each market price p ∈ ℤ, define V_p : Settlement →+ ℤ by:
  V_p(s) = p · s.dx + s.dy

This family of homomorphisms captures how the VALUE of a settlement
depends on the market price of token X (measured in units of token Y).

## What This File Proves

### Structure
1. **V_at_unit_price**: V(1) = Δ (conservation = value at unit exchange rate)
2. **value_decomposition**: V_p(s) = (p-1)·dx + Δ(s)
3. **balanced_value**: Δ(s)=0 ⟹ V_p(s) = dx·(p-1)
4. **price_sensitivity**: V_{p+δ}(s) - V_p(s) = δ·dx

### Separation & Determination
5. **V_separates_points**: (∀p, V_p(s)=0) ⟹ s=0
6. **ker_Δ_inter_ker_V_trivial**: ker(Δ) ∩ ker(V_p) = {0} when p≠1 [NoZeroDivisors ℤ]
7. **two_prices_determine**: V at two distinct prices determines settlement uniquely

### Financial Interpretation
8. **balanced_positive_value**: balanced + dx>0 ⟹ (V_p>0 ↔ p>1) [arbitrage detection]
-/

namespace Proofs

namespace DEXValueAlgebra

/-! ## Part 1: Settlement Type -/

structure Settl where
  dx : ℤ
  dy : ℤ
  deriving Repr, DecidableEq

@[ext] theorem Settl.ext {s₁ s₂ : Settl}
    (hx : s₁.dx = s₂.dx) (hy : s₁.dy = s₂.dy) : s₁ = s₂ := by
  cases s₁; cases s₂; simp_all

instance : Zero Settl := ⟨⟨0, 0⟩⟩
instance : Add Settl := ⟨fun s₁ s₂ => ⟨s₁.dx + s₂.dx, s₁.dy + s₂.dy⟩⟩
instance : Neg Settl := ⟨fun s => ⟨-s.dx, -s.dy⟩⟩
instance : Sub Settl := ⟨fun s₁ s₂ => s₁ + (-s₂)⟩

@[simp] theorem Settl.zero_dx : (0 : Settl).dx = 0 := rfl
@[simp] theorem Settl.zero_dy : (0 : Settl).dy = 0 := rfl
@[simp] theorem Settl.add_dx (s₁ s₂ : Settl) :
    (s₁ + s₂).dx = s₁.dx + s₂.dx := rfl
@[simp] theorem Settl.add_dy (s₁ s₂ : Settl) :
    (s₁ + s₂).dy = s₁.dy + s₂.dy := rfl
@[simp] theorem Settl.neg_dx (s : Settl) : (-s).dx = -s.dx := rfl
@[simp] theorem Settl.neg_dy (s : Settl) : (-s).dy = -s.dy := rfl

instance : AddCommGroup Settl where
  add_assoc := fun a b c => by ext <;> simp <;> ring
  zero_add := fun a => by ext <;> simp
  add_zero := fun a => by ext <;> simp
  add_comm := fun a b => by ext <;> simp <;> ring
  neg_add_cancel := fun a => by ext <;> simp
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ## Part 2: Conservation Homomorphism -/

/-- Δ(s) = dx + dy. Zero iff the settlement is balanced (no net token creation). -/
def Δ : Settl →+ ℤ where
  toFun := fun s => s.dx + s.dy
  map_zero' := by rfl
  map_add' := fun a b => by
    show (a.dx + b.dx) + (a.dy + b.dy) = (a.dx + a.dy) + (b.dx + b.dy); ring

/-! ## Part 3: The Price-Parameterized Value Functional -/

/-- V_p(s) = p · dx + dy: the value of settlement s at market price p.
    This is an AddMonoidHom for each fixed price p. -/
def V (p : ℤ) : Settl →+ ℤ where
  toFun := fun s => p * s.dx + s.dy
  map_zero' := by simp
  map_add' := fun a b => by
    show p * (a.dx + b.dx) + (a.dy + b.dy) = (p * a.dx + a.dy) + (p * b.dx + b.dy)
    ring

/-! ## Part 4: Structural Theorems -/

/-- Conservation equals value at unit price: V₁ = Δ. -/
theorem V_at_unit_price : V 1 = Δ := by
  ext s; show 1 * s.dx + s.dy = s.dx + s.dy; ring

/-- Value decomposes as price deviation times dx, plus conservation measure.
    V_p(s) = (p-1)·dx + Δ(s). -/
theorem value_decomposition (p : ℤ) (s : Settl) :
    V p s = (p - 1) * s.dx + Δ s := by
  show p * s.dx + s.dy = (p - 1) * s.dx + (s.dx + s.dy); ring

/-- For balanced settlements (Δ=0), value is purely price deviation:
    V_p(s) = dx·(p-1). -/
theorem balanced_value (p : ℤ) (s : Settl) (h : Δ s = 0) :
    V p s = s.dx * (p - 1) := by
  have hd := value_decomposition p s
  simp only [Δ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  show p * s.dx + s.dy = s.dx * (p - 1)
  linarith

/-- Price sensitivity: changing price by δ changes value by δ·dx.
    This is the "delta" exposure of the settlement. -/
theorem price_sensitivity (p δ : ℤ) (s : Settl) :
    V (p + δ) s - V p s = δ * s.dx := by
  show (p + δ) * s.dx + s.dy - (p * s.dx + s.dy) = δ * s.dx; ring

/-! ## Part 5: Separation and Determination -/

/-- The family {V_p} SEPARATES POINTS: if V_p(s)=0 for all prices p, then s=0.
    Proof: evaluate at p=0 (gives dy=0) and p=1 (gives dx+dy=dx=0). -/
theorem V_separates_points (s : Settl) (h : ∀ p : ℤ, V p s = 0) :
    s = 0 := by
  have h0 : V 0 s = 0 := h 0
  have h1 : V 1 s = 0 := h 1
  simp only [V, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h0 h1
  simp only [zero_mul, one_mul, zero_add] at h0 h1
  have hdx : s.dx = 0 := by linarith
  have hdy : s.dy = 0 := h0
  ext
  · exact hdx
  · exact hdy

/-- ker(Δ) ∩ ker(V_p) = {0} when p ≠ 1.
    Uses the INTEGRAL DOMAIN property of ℤ (no zero divisors):
    balanced ∧ zero-value ⟹ dx·(p-1)=0 ⟹ dx=0 (since p≠1) ⟹ s=0.

    This is the deepest theorem in the file — it requires NoZeroDivisors ℤ. -/
theorem ker_Δ_inter_ker_V_trivial (p : ℤ) (hp : p ≠ 1)
    (s : Settl) (hbal : Δ s = 0) (hval : V p s = 0) :
    s = 0 := by
  simp only [Δ, V, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hbal hval
  have hdy : s.dy = -s.dx := by linarith
  have hmul : s.dx * (p - 1) = 0 := by linarith
  have hne : p - 1 ≠ 0 := by omega
  have hdx : s.dx = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact absurd h hne
  have hdy2 : s.dy = 0 := by linarith
  ext
  · exact hdx
  · exact hdy2

/-- Two distinct price evaluations determine the settlement uniquely.
    Proof: knowing V_{p₁} and V_{p₂} with p₁≠p₂ determines both dx and dy
    (2 linear equations in 2 unknowns, non-degenerate coefficient matrix).

    Uses NoZeroDivisors ℤ to solve the 2×2 system. -/
theorem two_prices_determine (p₁ p₂ : ℤ) (hp : p₁ ≠ p₂)
    (s₁ s₂ : Settl) (h₁ : V p₁ s₁ = V p₁ s₂) (h₂ : V p₂ s₁ = V p₂ s₂) :
    s₁ = s₂ := by
  simp only [V, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h₁ h₂
  -- Eliminate dy by subtraction: (p₁-p₂)·(dx₁-dx₂) = 0
  have hdiff : p₁ * s₁.dx - p₂ * s₁.dx = p₁ * s₂.dx - p₂ * s₂.dx := by linarith
  have hprod : (p₁ - p₂) * (s₁.dx - s₂.dx) = 0 := by
    have : (p₁ - p₂) * (s₁.dx - s₂.dx) =
           p₁ * s₁.dx - p₂ * s₁.dx - (p₁ * s₂.dx - p₂ * s₂.dx) := by ring
    linarith
  have hne : p₁ - p₂ ≠ 0 := by omega
  have hdx : s₁.dx = s₂.dx := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hne
    · linarith
  rw [hdx] at h₁
  have hdy : s₁.dy = s₂.dy := by linarith
  ext
  · exact hdx
  · exact hdy

/-! ## Part 6: Arbitrage Characterization -/

/-- ARBITRAGE THEOREM: For a balanced settlement with positive dx (buying X),
    the settlement has positive value precisely when market price > 1.

    Financially: buying X at the DEX rate (where dx+dy=0, implicit price 1)
    is profitable iff the external market values X above 1.

    Proof uses: V_p(s) = dx·(p-1), then dx>0 makes sign match (p-1). -/
theorem balanced_positive_value (s : Settl) (p : ℤ)
    (hbal : Δ s = 0) (hdx : 0 < s.dx) :
    0 < V p s ↔ 1 < p := by
  simp only [V, Δ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hbal ⊢
  have hdy : s.dy = -s.dx := by linarith
  rw [hdy]
  constructor
  · intro h
    by_contra hle; push_neg at hle
    have h1 : p - 1 ≤ 0 := by omega
    have h2 : (p - 1) * s.dx ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 (le_of_lt hdx)
    have h3 : (p - 1) * s.dx = p * s.dx + -s.dx := by ring
    linarith
  · intro hp
    have h1 : 0 < p - 1 := by omega
    have h2 : 0 < (p - 1) * s.dx := mul_pos h1 hdx
    have h3 : (p - 1) * s.dx = p * s.dx + -s.dx := by ring
    linarith

/-! ## Part 7: Non-Vacuity Witnesses -/

/-- Conservation = unit value: V_1(⟨100,-70⟩) = 30 = Δ(⟨100,-70⟩). -/
theorem witness_V_at_unit :
    V 1 (Settl.mk 100 (-70)) = 30 ∧
    Δ (Settl.mk 100 (-70)) = 30 := by native_decide

/-- Balanced settlement value at price 3:
    s = ⟨50,-50⟩ (balanced). V_3(s) = 3·50-50 = 100 = dx·(p-1) = 50·2. -/
theorem witness_balanced_value :
    let s : Settl := ⟨50, -50⟩
    Δ s = 0 ∧ V 3 s = 100 ∧ s.dx * (3 - 1) = 100 := by native_decide

/-- Nontrivial kernel intersection: s=⟨50,-50⟩ balanced, V_2(s)=50≠0. -/
theorem witness_nontrivial_kernel :
    let s : Settl := ⟨50, -50⟩
    Δ s = 0 ∧ V 2 s = 50 ∧ V 2 s ≠ 0 := by native_decide

/-- Two prices determine: V_0 and V_1 at ⟨100,-70⟩ give -70 and 30. -/
theorem witness_two_prices :
    V 0 (Settl.mk 100 (-70)) = -70 ∧
    V 1 (Settl.mk 100 (-70)) = 30 := by native_decide

/-- Arbitrage: s=⟨100,-100⟩ balanced, p=2>1, V_2(s)=100>0. Profitable. -/
theorem witness_arbitrage :
    let s : Settl := ⟨100, -100⟩
    Δ s = 0 ∧ 0 < V 2 s ∧ V 2 s = 100 := by native_decide

end DEXValueAlgebra

end Proofs
