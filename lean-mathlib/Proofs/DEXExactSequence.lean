import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic
import Proofs.SettlementAlgebra

/-!
# Conservation Exact Sequence: The Splitting Theorem for DeFi

## The Central Algebraic Object

For ANY conservation homomorphism φ : G →+ ℤ on an abelian group G,
if a right-inverse section σ : ℤ →+ G exists (φ ∘ σ = id), then:

```
              ι                φ
  0  →  ker(φ)  ────→  G  ────→  ℤ  →  0
                    ↑
                    σ  (section: φ(σ(n)) = n for all n)
```

### What This File Proves

#### Abstract Theory (for any ConservationSystem)
1. **surjective**: φ is surjective (from section existence)
2. **section_injective**: σ is injective
3. **kerProject_in_ker**: π(g) := g - σ(φ(g)) ∈ ker(φ)
4. **kerProject_idempotent**: π ∘ π = π (genuine projection)
5. **decomposition**: g = π(g) + σ(φ(g)) — FUNDAMENTAL SPLITTING
6. **decomposition_unique_n**: Violation number n = φ(g) is unique
7. **decomposition_unique_k**: Kernel part k = π(g) is unique
8. **kerProject_add**: π is additive (π is itself an AddMonoidHom)
9. **ker_inter_image_trivial**: ker(φ) ∩ im(σ) = {0} (direct sum)
10. **decomposition_injective**: Same (π,φ) ⟹ same element

#### Instantiations
11. **settlCS**: Settlement φ(s)=dx+dy, σ(n)=⟨n,0⟩
12. **debtCS**: zUSD debt φ(a)=Δfree+Δsp-Δtotal, σ(n)=⟨n,0,0⟩

### Mathematical Significance

The splitting says every DeFi action UNIQUELY decomposes into:
- A **conserving part** (in ker(φ)) — preserves the invariant
- A **violation part** (in im(σ)) — measured by a single integer

The violation number φ(g) is the unique obstruction to conservation.
The decomposition is FUNCTORIAL: π is an AddMonoidHom.
-/

namespace Proofs

namespace DEXExactSequence

/-! ## Part 1: The Conservation System -/

/-- A conservation system on an abelian group G:
    φ : G →+ ℤ (measure), σ : ℤ →+ G (section), with φ ∘ σ = id. -/
structure ConservationSystem (G : Type*) [AddCommGroup G] where
  φ : G →+ ℤ
  σ : ℤ →+ G
  right_inv : ∀ n : ℤ, φ (σ n) = n

variable {G : Type*} [AddCommGroup G]

/-! ## Part 2: Exactness -/

/-- φ is surjective: σ witnesses every integer. -/
theorem surjective (C : ConservationSystem G) :
    Function.Surjective C.φ :=
  fun n => ⟨C.σ n, C.right_inv n⟩

/-- σ is injective: σ(n)=σ(m) ⟹ n=m. Apply φ to both sides. -/
theorem section_injective (C : ConservationSystem G) :
    Function.Injective C.σ := by
  intro n m h
  have h₁ := C.right_inv n
  have h₂ := C.right_inv m
  rw [h] at h₁; linarith

/-! ## Part 3: The Kernel Projection -/

/-- Kernel projection: extracts the conserving part.
    π(g) := g - σ(φ(g)). -/
def kerProject (C : ConservationSystem G) (g : G) : G :=
  g - C.σ (C.φ g)

/-- π lands in ker(φ): φ(π(g)) = φ(g) - φ(σ(φ(g))) = φ(g) - φ(g) = 0. -/
theorem kerProject_in_ker (C : ConservationSystem G) (g : G) :
    C.φ (kerProject C g) = 0 := by
  unfold kerProject
  rw [C.φ.map_sub, C.right_inv, sub_self]

/-- π is idempotent: π(π(g)) = π(g).
    Key step: φ(π(g))=0, so σ(φ(π(g)))=σ(0)=0, so π(g)-0=π(g). -/
theorem kerProject_idempotent (C : ConservationSystem G) (g : G) :
    kerProject C (kerProject C g) = kerProject C g := by
  unfold kerProject
  rw [C.φ.map_sub, C.right_inv, sub_self, C.σ.map_zero, sub_zero]

/-! ## Part 4: The Fundamental Decomposition -/

/-- DECOMPOSITION: g = π(g) + σ(φ(g)). Every element splits. -/
theorem decomposition (C : ConservationSystem G) (g : G) :
    g = kerProject C g + C.σ (C.φ g) := by
  unfold kerProject; abel

/-- UNIQUENESS (violation): If g = k + σ(n) with φ(k)=0, then n = φ(g).
    The violation number is uniquely determined. -/
theorem decomposition_unique_n (C : ConservationSystem G) (g k : G) (n : ℤ)
    (hk : C.φ k = 0) (hdecomp : g = k + C.σ n) :
    n = C.φ g := by
  calc n = C.φ (C.σ n) := (C.right_inv n).symm
    _ = C.φ k + C.φ (C.σ n) := by rw [hk, zero_add]
    _ = C.φ (k + C.σ n) := (C.φ.map_add k (C.σ n)).symm
    _ = C.φ g := by rw [← hdecomp]

/-- UNIQUENESS (kernel): If g = k + σ(n) with φ(k)=0, then k = π(g). -/
theorem decomposition_unique_k (C : ConservationSystem G) (g k : G) (n : ℤ)
    (hk : C.φ k = 0) (hdecomp : g = k + C.σ n) :
    k = kerProject C g := by
  have hn : n = C.φ g := decomposition_unique_n C g k n hk hdecomp
  unfold kerProject; rw [← hn, hdecomp]; abel

/-! ## Part 5: π is an AddMonoidHom -/

/-- π is additive: π(g₁+g₂) = π(g₁) + π(g₂).
    Uses σ being a homomorphism:
    (g₁+g₂) - σ(φ(g₁)+φ(g₂)) = (g₁-σ(φg₁)) + (g₂-σ(φg₂)). -/
theorem kerProject_add (C : ConservationSystem G) (g₁ g₂ : G) :
    kerProject C (g₁ + g₂) = kerProject C g₁ + kerProject C g₂ := by
  unfold kerProject
  rw [C.φ.map_add, C.σ.map_add]; abel

/-- π(0) = 0. -/
theorem kerProject_zero (C : ConservationSystem G) :
    kerProject C 0 = 0 := by
  unfold kerProject
  rw [C.φ.map_zero, C.σ.map_zero, sub_zero]

/-- π as a formal AddMonoidHom G →+ G. -/
def kerProjectHom (C : ConservationSystem G) : G →+ G where
  toFun := kerProject C
  map_zero' := kerProject_zero C
  map_add' := kerProject_add C

/-! ## Part 6: Direct Sum Structure -/

/-- ker(φ) ∩ im(σ) = {0}: If φ(g)=0 and g=σ(n), then n=0 and g=0. -/
theorem ker_inter_image_trivial (C : ConservationSystem G)
    (g : G) (n : ℤ) (hk : C.φ g = 0) (him : g = C.σ n) :
    n = 0 ∧ g = 0 := by
  constructor
  · have := C.right_inv n; rw [← him] at this; linarith
  · have hn : n = 0 := by have := C.right_inv n; rw [← him] at this; linarith
    rw [him, hn, C.σ.map_zero]

/-- If two elements have the same π and φ, they are equal. -/
theorem decomposition_injective (C : ConservationSystem G) (g₁ g₂ : G)
    (hk : kerProject C g₁ = kerProject C g₂) (hv : C.φ g₁ = C.φ g₂) :
    g₁ = g₂ := by
  have h₁ := decomposition C g₁
  have h₂ := decomposition C g₂
  rw [h₁, h₂, hk, hv]

/-! ## Part 7: Violation Calculus -/

/-- Violations are additive. -/
theorem violation_additive (C : ConservationSystem G) (g₁ g₂ : G) :
    C.φ (g₁ + g₂) = C.φ g₁ + C.φ g₂ :=
  C.φ.map_add g₁ g₂

/-- Conserving actions preserve violation number. -/
theorem conserving_preserves_violation (C : ConservationSystem G) (k g : G)
    (hk : C.φ k = 0) :
    C.φ (k + g) = C.φ g := by
  rw [C.φ.map_add, hk, zero_add]

/-- σ(n) has violation exactly n. -/
theorem section_violation (C : ConservationSystem G) (n : ℤ) :
    C.φ (C.σ n) = n := C.right_inv n

/-- Subtracting the kernel projection recovers the section image. -/
theorem section_of_violation (C : ConservationSystem G) (g : G) :
    g - kerProject C g = C.σ (C.φ g) := by
  unfold kerProject; abel

/-- π fixes kernel elements: if φ(g)=0, then π(g)=g. -/
theorem kerProject_fixes_ker (C : ConservationSystem G) (g : G) (h : C.φ g = 0) :
    kerProject C g = g := by
  unfold kerProject; rw [h, C.σ.map_zero, sub_zero]

/-- π annihilates section images: π(σ(n)) = 0. -/
theorem kerProject_annihilates_section (C : ConservationSystem G) (n : ℤ) :
    kerProject C (C.σ n) = 0 := by
  unfold kerProject; rw [C.right_inv, sub_self]

/-! ## Part 8: Settlement Instantiation -/

abbrev Settl := SettlementAlgebra.Settlement

abbrev settlΔ : Settl →+ ℤ := SettlementAlgebra.Δ

def settlσ : ℤ →+ Settl where
  toFun := fun n => ⟨n, 0⟩
  map_zero' := by
    apply SettlementAlgebra.Settlement.ext <;> rfl
  map_add' := fun a b => by
    apply SettlementAlgebra.Settlement.ext
    · rfl
    · change 0 = (0 : ℤ) + 0
      simp

/-- The settlement conservation system: φ(s)=dx+dy, σ(n)=⟨n,0⟩. -/
def settlCS : ConservationSystem Settl where
  φ := settlΔ
  σ := settlσ
  right_inv := fun n => by
    simp only [settlΔ, SettlementAlgebra.Δ, SettlementAlgebra.netFlow, settlσ,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    ring

/-! ## Part 9: zUSD Debt Instantiation -/

structure DebtAction where
  Δfree : ℤ
  Δsp : ℤ
  Δtotal : ℤ
  deriving Repr, DecidableEq

@[ext] theorem DebtAction.ext {a₁ a₂ : DebtAction}
    (hf : a₁.Δfree = a₂.Δfree) (hs : a₁.Δsp = a₂.Δsp)
    (ht : a₁.Δtotal = a₂.Δtotal) : a₁ = a₂ := by
  cases a₁; cases a₂; simp_all

instance : Zero DebtAction := ⟨⟨0, 0, 0⟩⟩
instance : Add DebtAction :=
  ⟨fun a b => ⟨a.Δfree + b.Δfree, a.Δsp + b.Δsp, a.Δtotal + b.Δtotal⟩⟩
instance : Neg DebtAction := ⟨fun a => ⟨-a.Δfree, -a.Δsp, -a.Δtotal⟩⟩
instance : Sub DebtAction := ⟨fun a b => a + (-b)⟩

@[simp] theorem DebtAction.zero_f : (0 : DebtAction).Δfree = 0 := rfl
@[simp] theorem DebtAction.zero_s : (0 : DebtAction).Δsp = 0 := rfl
@[simp] theorem DebtAction.zero_t : (0 : DebtAction).Δtotal = 0 := rfl
@[simp] theorem DebtAction.add_f (a b : DebtAction) :
    (a + b).Δfree = a.Δfree + b.Δfree := rfl
@[simp] theorem DebtAction.add_s (a b : DebtAction) :
    (a + b).Δsp = a.Δsp + b.Δsp := rfl
@[simp] theorem DebtAction.add_t (a b : DebtAction) :
    (a + b).Δtotal = a.Δtotal + b.Δtotal := rfl
@[simp] theorem DebtAction.neg_f (a : DebtAction) :
    (-a).Δfree = -a.Δfree := rfl
@[simp] theorem DebtAction.neg_s (a : DebtAction) :
    (-a).Δsp = -a.Δsp := rfl
@[simp] theorem DebtAction.neg_t (a : DebtAction) :
    (-a).Δtotal = -a.Δtotal := rfl

instance : AddCommGroup DebtAction where
  add_assoc := fun a b c => by ext <;> simp <;> ring
  zero_add := fun a => by ext <;> simp
  add_zero := fun a => by ext <;> simp
  add_comm := fun a b => by ext <;> simp <;> ring
  neg_add_cancel := fun a => by ext <;> simp
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

def debtΔ : DebtAction →+ ℤ where
  toFun := fun a => a.Δfree + a.Δsp - a.Δtotal
  map_zero' := by rfl
  map_add' := fun a b => by
    show (a.Δfree + b.Δfree) + (a.Δsp + b.Δsp) - (a.Δtotal + b.Δtotal) =
         (a.Δfree + a.Δsp - a.Δtotal) + (b.Δfree + b.Δsp - b.Δtotal); ring

def debtσ : ℤ →+ DebtAction where
  toFun := fun n => ⟨n, 0, 0⟩
  map_zero' := by ext <;> simp
  map_add' := fun a b => by ext <;> simp

/-- The zUSD debt conservation system: φ(a)=Δfree+Δsp-Δtotal, σ(n)=⟨n,0,0⟩. -/
def debtCS : ConservationSystem DebtAction where
  φ := debtΔ
  σ := debtσ
  right_inv := fun n => by
    simp only [debtΔ, debtσ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    ring

/-! ## Part 10: Non-Vacuity Witnesses -/

/-- Settlement decomposition: ⟨100,-90⟩ = ⟨90,-90⟩ + ⟨10,0⟩.
    Balanced part ⟨90,-90⟩ (Δ=0) plus violation ⟨10,0⟩ (Δ=10). -/
theorem witness_settl_decomposition :
    let s : Settl := ⟨100, -90⟩
    settlΔ s = 10 ∧
    kerProject settlCS s = ({ dx := 90, dy := -90 } : Settl) ∧
    settlσ 10 = ({ dx := 10, dy := 0 } : Settl) ∧
    s = kerProject settlCS s + settlσ (settlΔ s) := by native_decide

/-- Debt decomposition: ⟨500,200,600⟩ = ⟨400,200,600⟩ + ⟨100,0,0⟩.
    Conserving part (Δ=400+200-600=0) plus violation (Δ=100). -/
theorem witness_debt_decomposition :
    let a : DebtAction := ⟨500, 200, 600⟩
    debtΔ a = 100 ∧
    kerProject debtCS a = DebtAction.mk 400 200 600 ∧
    debtσ 100 = DebtAction.mk 100 0 0 ∧
    a = kerProject debtCS a + debtσ (debtΔ a) := by native_decide

/-- Trivial intersection: σ(5) has Δ=5≠0, so it's NOT in the kernel. -/
theorem witness_trivial_intersection :
    let g : Settl := settlσ 5
    settlΔ g = 5 ∧ g = ({ dx := 5, dy := 0 } : Settl) ∧
    ¬(settlΔ g = 0 ∧ g ≠ 0) := by native_decide

/-- Uniqueness: the decomposition is determined by the element. -/
theorem witness_uniqueness :
    let s : Settl := ⟨100, -90⟩
    settlΔ (kerProject settlCS s) = 0 ∧
    settlΔ s = 10 ∧
    kerProject settlCS s + settlσ (settlΔ s) = s := by native_decide

/-- Section annihilation: π(σ(n)) = 0 for concrete n. -/
theorem witness_annihilation :
    kerProject settlCS (settlσ 42) = (0 : Settl) ∧
    kerProject debtCS (debtσ (-7)) = (0 : DebtAction) := by native_decide

/-- Idempotent projection: π(π(s)) = π(s) for concrete s. -/
theorem witness_idempotent :
    let s : Settl := ⟨100, -90⟩
    let πs := kerProject settlCS s
    kerProject settlCS πs = πs := by native_decide

end DEXExactSequence

end Proofs
