import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic

/-!
# Perpetual Funding Rate Algebra

## The Key Mathematical Objects

A perpetual position has two components:
- `base`: contract quantity (positive=long, negative=short)
- `notional`: entry cost basis

Two families of homomorphisms capture the protocol's core mechanics:

1. **Mark-to-market**: M_p(pos) = p · base - notional
   Value of position at market price p.

2. **Funding**: F_r(pos) = r · base
   Funding payment at rate r.

The novel structure: the map r ↦ F_r is ITSELF a group homomorphism
from (ℤ,+) into the group of homomorphisms Hom(PerpPos, ℤ).
This makes funding a BILINEAR form on ℤ × PerpPos.

## What This File Proves

### Mark-to-Market (3 theorems)
1. **mtm_separates**: Two prices determine position uniquely [NoZeroDivisors]
2. **breakeven_char**: M_p(pos)=0 ↔ p·base = notional
3. **hedge_cancels**: M_p(pos + (-pos)) = 0 (perfect hedge)

### Funding Bilinearity (4 theorems)
4. **fundingHom**: r ↦ F_r is an AddMonoidHom ℤ →+ (PerpPos →+ ℤ)
5. **funding_bilinear**: F_{r₁+r₂}(pos) = F_{r₁}(pos) + F_{r₂}(pos)
6. **funding_zero_sum**: If base₁ + base₂ = 0, then F_r(pos₁) + F_r(pos₂) = 0
7. **funding_ker_is_zero_exposure**: ker(F_r) = {pos | base=0} when r≠0

### Combined Structure (2 theorems)
8. **pnl_after_funding**: Net PnL = M_p(pos) - F_r(pos) = (p-r)·base - notional
9. **effective_price_shift**: Funding shifts effective price: M_p - F_r = M_{p-r}
-/

namespace Proofs

namespace PerpFundingAlgebra

/-! ## Part 1: Position Type -/

structure PerpPos where
  base : ℤ
  notional : ℤ
  deriving Repr, DecidableEq

@[ext] theorem PerpPos.ext {p₁ p₂ : PerpPos}
    (hb : p₁.base = p₂.base) (hn : p₁.notional = p₂.notional) : p₁ = p₂ := by
  cases p₁; cases p₂; simp_all

instance : Zero PerpPos := ⟨⟨0, 0⟩⟩
instance : Add PerpPos := ⟨fun p₁ p₂ => ⟨p₁.base + p₂.base, p₁.notional + p₂.notional⟩⟩
instance : Neg PerpPos := ⟨fun p => ⟨-p.base, -p.notional⟩⟩
instance : Sub PerpPos := ⟨fun p₁ p₂ => p₁ + (-p₂)⟩

@[simp] theorem PerpPos.zero_base : (0 : PerpPos).base = 0 := rfl
@[simp] theorem PerpPos.zero_notional : (0 : PerpPos).notional = 0 := rfl
@[simp] theorem PerpPos.add_base (p₁ p₂ : PerpPos) :
    (p₁ + p₂).base = p₁.base + p₂.base := rfl
@[simp] theorem PerpPos.add_notional (p₁ p₂ : PerpPos) :
    (p₁ + p₂).notional = p₁.notional + p₂.notional := rfl
@[simp] theorem PerpPos.neg_base (p : PerpPos) : (-p).base = -p.base := rfl
@[simp] theorem PerpPos.neg_notional (p : PerpPos) : (-p).notional = -p.notional := rfl

instance : AddCommGroup PerpPos where
  add_assoc := fun a b c => by ext <;> simp <;> ring
  zero_add := fun a => by ext <;> simp
  add_zero := fun a => by ext <;> simp
  add_comm := fun a b => by ext <;> simp <;> ring
  neg_add_cancel := fun a => by ext <;> simp
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ## Part 2: Mark-to-Market Homomorphism -/

/-- M_p(pos) = p · base - notional: unrealized PnL at price p. -/
def mtm (p : ℤ) : PerpPos →+ ℤ where
  toFun := fun pos => p * pos.base - pos.notional
  map_zero' := by simp
  map_add' := fun a b => by
    show p * (a.base + b.base) - (a.notional + b.notional) =
         (p * a.base - a.notional) + (p * b.base - b.notional); ring

/-- Base projection: extracts contract quantity. -/
def baseProj : PerpPos →+ ℤ where
  toFun := fun pos => pos.base
  map_zero' := rfl
  map_add' := fun _ _ => rfl

/-- Notional projection: extracts cost basis. -/
def notionalProj : PerpPos →+ ℤ where
  toFun := fun pos => pos.notional
  map_zero' := rfl
  map_add' := fun _ _ => rfl

/-! ## Part 3: Mark-to-Market Theorems -/

/-- Break-even characterization: MTM is zero iff price × base = notional. -/
theorem breakeven_char (p : ℤ) (pos : PerpPos) :
    mtm p pos = 0 ↔ p * pos.base = pos.notional := by
  simp only [mtm, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  omega

/-- Two distinct prices determine position uniquely.
    Same algebra as settlements: 2×2 non-degenerate linear system.
    Uses NoZeroDivisors ℤ. -/
theorem mtm_separates (p₁ p₂ : ℤ) (hp : p₁ ≠ p₂)
    (pos₁ pos₂ : PerpPos) (h₁ : mtm p₁ pos₁ = mtm p₁ pos₂)
    (h₂ : mtm p₂ pos₁ = mtm p₂ pos₂) :
    pos₁ = pos₂ := by
  simp only [mtm, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h₁ h₂
  have hdiff : p₁ * pos₁.base - p₂ * pos₁.base =
               p₁ * pos₂.base - p₂ * pos₂.base := by linarith
  have hprod : (p₁ - p₂) * (pos₁.base - pos₂.base) = 0 := by
    have : (p₁ - p₂) * (pos₁.base - pos₂.base) =
           p₁ * pos₁.base - p₂ * pos₁.base -
           (p₁ * pos₂.base - p₂ * pos₂.base) := by ring
    linarith
  have hne : p₁ - p₂ ≠ 0 := by omega
  have hbase : pos₁.base = pos₂.base := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hne
    · linarith
  rw [hbase] at h₁
  have hnotional : pos₁.notional = pos₂.notional := by linarith
  ext
  · exact hbase
  · exact hnotional

/-- Perfect hedge: pos + (-pos) has zero MTM at all prices. -/
theorem hedge_cancels (p : ℤ) (pos : PerpPos) :
    mtm p (pos + (-pos)) = 0 := by
  simp [mtm, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-! ## Part 4: Funding Rate Homomorphism -/

/-- F_r(pos) = r · base: funding payment at rate r.
    Long positions (base>0) pay when r>0; short positions receive. -/
def funding (r : ℤ) : PerpPos →+ ℤ where
  toFun := fun pos => r * pos.base
  map_zero' := by simp
  map_add' := fun a b => by
    show r * (a.base + b.base) = r * a.base + r * b.base; ring

/-- THE HIGHER-ORDER HOMOMORPHISM: r ↦ F_r is a group homomorphism
    from (ℤ,+) into the group Hom(PerpPos, ℤ).

    This formalizes: composing funding rates (adding rates over epochs)
    composes funding payments (adding payment functions).
    This is the BILINEAR structure of funding. -/
def fundingHom : ℤ →+ (PerpPos →+ ℤ) where
  toFun := funding
  map_zero' := by ext pos; show 0 * pos.base = 0; ring
  map_add' := fun r₁ r₂ => by
    ext pos; show (r₁ + r₂) * pos.base = r₁ * pos.base + r₂ * pos.base; ring

/-! ## Part 5: Funding Theorems -/

/-- Funding is bilinear in rate: F_{r₁+r₂} = F_{r₁} + F_{r₂}. -/
theorem funding_bilinear (r₁ r₂ : ℤ) (pos : PerpPos) :
    funding (r₁ + r₂) pos = funding r₁ pos + funding r₂ pos := by
  show (r₁ + r₂) * pos.base = r₁ * pos.base + r₂ * pos.base; ring

/-- ZERO-SUM THEOREM: If two positions have opposite base (long/short balance),
    their funding payments cancel.
    This is the core protocol invariant: funding is redistributive, not extractive. -/
theorem funding_zero_sum (r : ℤ) (pos₁ pos₂ : PerpPos)
    (h : pos₁.base + pos₂.base = 0) :
    funding r pos₁ + funding r pos₂ = 0 := by
  show r * pos₁.base + r * pos₂.base = 0
  have : r * (pos₁.base + pos₂.base) = 0 := by rw [h]; ring
  linarith [mul_add r pos₁.base pos₂.base]

/-- Kernel of F_r when r ≠ 0: positions with zero base (zero exposure).
    Uses NoZeroDivisors ℤ: r·base=0 ∧ r≠0 ⟹ base=0. -/
theorem funding_ker_is_zero_exposure (r : ℤ) (hr : r ≠ 0) (pos : PerpPos) :
    funding r pos = 0 ↔ pos.base = 0 := by
  simp only [funding, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hr
    · exact h
  · intro h; rw [h]; ring

/-- The kernel of fundingHom is trivial: only rate 0 gives zero funding
    for ALL positions. -/
theorem fundingHom_ker_trivial (r : ℤ) (h : fundingHom r = 0) : r = 0 := by
  have : funding r (PerpPos.mk 1 0) = 0 := by
    have := congr_fun (congr_arg DFunLike.coe h) (PerpPos.mk 1 0)
    simp only [fundingHom, funding, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
               AddMonoidHom.zero_apply] at this
    exact this
  simp only [funding, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  linarith

/-! ## Part 6: Combined Structure -/

/-- Net PnL after funding: M_p(pos) - F_r(pos) = (p-r)·base - notional.
    Funding effectively shifts the price from p to p-r. -/
theorem pnl_after_funding (p r : ℤ) (pos : PerpPos) :
    mtm p pos - funding r pos = (p - r) * pos.base - pos.notional := by
  show (p * pos.base - pos.notional) - r * pos.base =
       (p - r) * pos.base - pos.notional; ring

/-- PRICE SHIFT THEOREM: Subtracting funding at rate r is equivalent to
    marking-to-market at shifted price p-r.
    M_p - F_r = M_{p-r}

    This is the fundamental insight: funding doesn't create or destroy value,
    it shifts the effective price. -/
theorem effective_price_shift (p r : ℤ) (pos : PerpPos) :
    mtm p pos - funding r pos = mtm (p - r) pos := by
  show (p * pos.base - pos.notional) - r * pos.base =
       (p - r) * pos.base - pos.notional; ring

/-! ## Part 7: Non-Vacuity Witnesses -/

/-- Long position: base=100, notional=5000. At price 60, MTM = 6000-5000 = 1000. -/
theorem witness_mtm_long :
    mtm 60 (PerpPos.mk 100 5000) = 1000 := by native_decide

/-- Hedge: long 100 + short 100 = zero MTM. -/
theorem witness_hedge :
    mtm 50 (PerpPos.mk 100 5000 + PerpPos.mk (-100) (-5000)) = 0 := by native_decide

/-- Zero-sum: long 100 base, short 100 base, rate=5. Payments: 500 + (-500) = 0. -/
theorem witness_zero_sum :
    let long := PerpPos.mk 100 5000
    let short := PerpPos.mk (-100) 4000
    funding 5 long + funding 5 short = 0 ∧
    long.base + short.base = 0 := by native_decide

/-- Bilinearity: F_{3+7} = F_3 + F_7 for position with base 100. -/
theorem witness_bilinear :
    let pos := PerpPos.mk 100 5000
    funding 10 pos = 1000 ∧
    funding 3 pos + funding 7 pos = 1000 := by native_decide

/-- Price shift: MTM at 60 minus funding at 5 = MTM at 55. -/
theorem witness_price_shift :
    let pos := PerpPos.mk 100 5000
    mtm 60 pos - funding 5 pos = mtm 55 pos ∧
    mtm 60 pos - funding 5 pos = 500 := by native_decide

end PerpFundingAlgebra

end Proofs
