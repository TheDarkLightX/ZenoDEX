import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic

/-!
# Dual Conservation: The Product Homomorphism for zUSD

## Key Property

zUSD maintains TWO independent conservation laws simultaneously:
1. **Debt conservation**: `free_debt + sp_debt = total_debt`
2. **Collateral conservation**: `Δvault + Δsp + Δprotocol + Δexternal = 0`

A valid runtime protocol action must satisfy BOTH. This file formalizes
two independent AddMonoidHoms and proves:
- Both are genuinely independent (neither implies the other)
- Several concrete protocol actions are in both kernels simultaneously
- Additional abstract balance templates are in both kernels as algebraic objects
- Joint conservation composes and inverts

## What This File Proves (11 substantive theorems)

### Two Homomorphisms
1. **FullAction forms an AddCommGroup** over ℤ⁷
2. **debtHom : FullAction →+ ℤ** (debt conservation measure)
3. **collHom : FullAction →+ ℤ** (collateral conservation measure)

### Joint Conservation
4. **joint_conserves_iff**: a.conserves ↔ debtHom a = 0 ∧ collHom a = 0
5. **joint_conservation_compositional**: composition preserves joint conservation
6. **joint_conservation_inverse**: inverse preserves joint conservation

### Concrete protocol actions and abstract templates
7. **mint_joint_conserves**: mint satisfies both laws
8. **abstract_liquidation_template_conserves**: a liquidation-shaped transfer preserves both laws algebraically
9. **abstract_redemption_template_conserves**: a redemption-shaped fee split preserves both laws algebraically

### Independence (the deep result)
10. **debt_without_coll**: exists action satisfying debt but not coll
11. **coll_without_debt**: exists action satisfying coll but not debt

### Dimensionality
12. **total_determined**: Δtotal is forced by Δfree + Δsp_debt
13. **ext_coll_determined**: Δext_coll is forced by other 3 coll fields
-/

namespace Proofs

namespace ZUSDDualConservation

/-! ## Part 1: FullAction Definition -/

/-- A full zUSD action: changes to all 7 relevant state variables.
    3 debt fields + 4 collateral fields. -/
structure FullAction where
  Δfree : ℤ
  Δsp_debt : ℤ
  Δtotal : ℤ
  Δvault_coll : ℤ
  Δsp_coll : ℤ
  Δprot_coll : ℤ
  Δext_coll : ℤ
  deriving Repr, DecidableEq

@[ext]
theorem FullAction.ext {a₁ a₂ : FullAction}
    (hf : a₁.Δfree = a₂.Δfree) (hsd : a₁.Δsp_debt = a₂.Δsp_debt)
    (ht : a₁.Δtotal = a₂.Δtotal)
    (hvc : a₁.Δvault_coll = a₂.Δvault_coll) (hsc : a₁.Δsp_coll = a₂.Δsp_coll)
    (hpc : a₁.Δprot_coll = a₂.Δprot_coll) (hec : a₁.Δext_coll = a₂.Δext_coll) :
    a₁ = a₂ := by
  cases a₁; cases a₂; simp_all

/-! ## Part 2: AddCommGroup Instance -/

instance : Zero FullAction := ⟨⟨0, 0, 0, 0, 0, 0, 0⟩⟩
instance : Add FullAction := ⟨fun a₁ a₂ =>
  ⟨a₁.Δfree + a₂.Δfree, a₁.Δsp_debt + a₂.Δsp_debt, a₁.Δtotal + a₂.Δtotal,
   a₁.Δvault_coll + a₂.Δvault_coll, a₁.Δsp_coll + a₂.Δsp_coll,
   a₁.Δprot_coll + a₂.Δprot_coll, a₁.Δext_coll + a₂.Δext_coll⟩⟩
instance : Neg FullAction := ⟨fun a =>
  ⟨-a.Δfree, -a.Δsp_debt, -a.Δtotal,
   -a.Δvault_coll, -a.Δsp_coll, -a.Δprot_coll, -a.Δext_coll⟩⟩
instance : Sub FullAction := ⟨fun a₁ a₂ => a₁ + (-a₂)⟩

@[simp] theorem FullAction.zero_Δfree : (0 : FullAction).Δfree = 0 := rfl
@[simp] theorem FullAction.zero_Δsp_debt : (0 : FullAction).Δsp_debt = 0 := rfl
@[simp] theorem FullAction.zero_Δtotal : (0 : FullAction).Δtotal = 0 := rfl
@[simp] theorem FullAction.zero_Δvault_coll : (0 : FullAction).Δvault_coll = 0 := rfl
@[simp] theorem FullAction.zero_Δsp_coll : (0 : FullAction).Δsp_coll = 0 := rfl
@[simp] theorem FullAction.zero_Δprot_coll : (0 : FullAction).Δprot_coll = 0 := rfl
@[simp] theorem FullAction.zero_Δext_coll : (0 : FullAction).Δext_coll = 0 := rfl

@[simp] theorem FullAction.add_Δfree (a₁ a₂ : FullAction) :
    (a₁ + a₂).Δfree = a₁.Δfree + a₂.Δfree := rfl
@[simp] theorem FullAction.add_Δsp_debt (a₁ a₂ : FullAction) :
    (a₁ + a₂).Δsp_debt = a₁.Δsp_debt + a₂.Δsp_debt := rfl
@[simp] theorem FullAction.add_Δtotal (a₁ a₂ : FullAction) :
    (a₁ + a₂).Δtotal = a₁.Δtotal + a₂.Δtotal := rfl
@[simp] theorem FullAction.add_Δvault_coll (a₁ a₂ : FullAction) :
    (a₁ + a₂).Δvault_coll = a₁.Δvault_coll + a₂.Δvault_coll := rfl
@[simp] theorem FullAction.add_Δsp_coll (a₁ a₂ : FullAction) :
    (a₁ + a₂).Δsp_coll = a₁.Δsp_coll + a₂.Δsp_coll := rfl
@[simp] theorem FullAction.add_Δprot_coll (a₁ a₂ : FullAction) :
    (a₁ + a₂).Δprot_coll = a₁.Δprot_coll + a₂.Δprot_coll := rfl
@[simp] theorem FullAction.add_Δext_coll (a₁ a₂ : FullAction) :
    (a₁ + a₂).Δext_coll = a₁.Δext_coll + a₂.Δext_coll := rfl
@[simp] theorem FullAction.neg_Δfree (a : FullAction) :
    (-a).Δfree = -a.Δfree := rfl
@[simp] theorem FullAction.neg_Δsp_debt (a : FullAction) :
    (-a).Δsp_debt = -a.Δsp_debt := rfl
@[simp] theorem FullAction.neg_Δtotal (a : FullAction) :
    (-a).Δtotal = -a.Δtotal := rfl
@[simp] theorem FullAction.neg_Δvault_coll (a : FullAction) :
    (-a).Δvault_coll = -a.Δvault_coll := rfl
@[simp] theorem FullAction.neg_Δsp_coll (a : FullAction) :
    (-a).Δsp_coll = -a.Δsp_coll := rfl
@[simp] theorem FullAction.neg_Δprot_coll (a : FullAction) :
    (-a).Δprot_coll = -a.Δprot_coll := rfl
@[simp] theorem FullAction.neg_Δext_coll (a : FullAction) :
    (-a).Δext_coll = -a.Δext_coll := rfl

instance : AddCommGroup FullAction where
  add_assoc := fun a b c => by ext <;> simp [add_assoc]
  zero_add := fun a => by ext <;> simp
  add_zero := fun a => by ext <;> simp
  add_comm := fun a b => by ext <;> simp [add_comm]
  neg_add_cancel := fun a => by ext <;> simp
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ## Part 3: The Two Conservation Homomorphisms -/

/-- Debt conservation measure: Δfree + Δsp_debt - Δtotal.
    Zero iff free + sp = total is preserved. -/
def debtMeasure (a : FullAction) : ℤ :=
  a.Δfree + a.Δsp_debt - a.Δtotal

/-- Collateral conservation measure: sum of all 4 collateral deltas.
    Zero iff total collateral is preserved. -/
def collMeasure (a : FullAction) : ℤ :=
  a.Δvault_coll + a.Δsp_coll + a.Δprot_coll + a.Δext_coll

/-- Debt conservation as an AddMonoidHom. -/
def debtHom : FullAction →+ ℤ where
  toFun := debtMeasure
  map_zero' := by rfl
  map_add' := fun a₁ a₂ => by unfold debtMeasure; simp; ring

/-- Collateral conservation as an AddMonoidHom. -/
def collHom : FullAction →+ ℤ where
  toFun := collMeasure
  map_zero' := by rfl
  map_add' := fun a₁ a₂ => by unfold collMeasure; simp; ring

/-! ## Part 4: Joint Conservation -/

/-- Joint conservation: both debt and collateral are preserved. -/
def FullAction.conserves (a : FullAction) : Prop :=
  debtHom a = 0 ∧ collHom a = 0

/-- Joint conservation iff BOTH measures are zero. -/
theorem joint_conserves_iff (a : FullAction) :
    a.conserves ↔ debtMeasure a = 0 ∧ collMeasure a = 0 := by
  unfold FullAction.conserves debtHom collHom
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- Composition preserves joint conservation. -/
theorem joint_conservation_compositional {a₁ a₂ : FullAction}
    (h₁ : a₁.conserves) (h₂ : a₂.conserves) :
    (a₁ + a₂).conserves := by
  rw [joint_conserves_iff] at *
  obtain ⟨hd₁, hc₁⟩ := h₁; obtain ⟨hd₂, hc₂⟩ := h₂
  constructor
  · rw [show debtMeasure (a₁ + a₂) = debtMeasure a₁ + debtMeasure a₂
      from debtHom.map_add a₁ a₂, hd₁, hd₂, add_zero]
  · rw [show collMeasure (a₁ + a₂) = collMeasure a₁ + collMeasure a₂
      from collHom.map_add a₁ a₂, hc₁, hc₂, add_zero]

/-- Inverse preserves joint conservation. -/
theorem joint_conservation_inverse {a : FullAction}
    (h : a.conserves) : (-a).conserves := by
  rw [joint_conserves_iff] at *
  obtain ⟨hd, hc⟩ := h
  constructor
  · rw [show debtMeasure (-a) = -(debtMeasure a) from debtHom.map_neg a, hd, neg_zero]
  · rw [show collMeasure (-a) = -(collMeasure a) from collHom.map_neg a, hc, neg_zero]

/-! ## Part 5: Concrete protocol actions and abstract balance templates -/

def fullMint (amount : ℤ) : FullAction := ⟨amount, 0, amount, 0, 0, 0, 0⟩
def fullRepay (amount : ℤ) : FullAction := ⟨-amount, 0, -amount, 0, 0, 0, 0⟩
def fullDeposit (amount : ℤ) : FullAction := ⟨0, 0, 0, amount, 0, 0, -amount⟩
def fullWithdraw (amount : ℤ) : FullAction := ⟨0, 0, 0, -amount, 0, 0, amount⟩
def fullDepositSP (amount : ℤ) : FullAction := ⟨-amount, amount, 0, 0, 0, 0, 0⟩
/-- An abstract whole-vault liquidation-shaped transfer.
    This is an algebraic conservation template, not a claim about the
    exact runtime liquidation command surface. -/
def liquidationTemplate (debt_amt coll_amt : ℤ) : FullAction :=
  ⟨0, -debt_amt, -debt_amt, -coll_amt, coll_amt, 0, 0⟩
/-- An abstract redemption-shaped fee split.
    This is an algebraic conservation template, not a runtime pricing theorem. -/
def redemptionTemplate (debt_amt gross_coll fee_coll : ℤ) : FullAction :=
  ⟨-debt_amt, 0, -debt_amt, -gross_coll, 0, fee_coll, gross_coll - fee_coll⟩

theorem mint_joint_conserves (amt : ℤ) : (fullMint amt).conserves := by
  rw [joint_conserves_iff]; constructor <;> (simp [debtMeasure, collMeasure, fullMint])

theorem repay_joint_conserves (amt : ℤ) : (fullRepay amt).conserves := by
  rw [joint_conserves_iff]; constructor <;> (simp [debtMeasure, collMeasure, fullRepay])

theorem deposit_joint_conserves (amt : ℤ) : (fullDeposit amt).conserves := by
  rw [joint_conserves_iff]; constructor <;> (simp [debtMeasure, collMeasure, fullDeposit])

theorem withdraw_joint_conserves (amt : ℤ) : (fullWithdraw amt).conserves := by
  rw [joint_conserves_iff]; constructor <;> (simp [debtMeasure, collMeasure, fullWithdraw])

theorem deposit_sp_joint_conserves (amt : ℤ) : (fullDepositSP amt).conserves := by
  rw [joint_conserves_iff]; constructor <;> (simp [debtMeasure, collMeasure, fullDepositSP])

theorem abstract_liquidation_template_conserves (d c : ℤ) :
    (liquidationTemplate d c).conserves := by
  rw [joint_conserves_iff]
  constructor <;> (simp [debtMeasure, collMeasure, liquidationTemplate])

theorem abstract_redemption_template_conserves (d g f : ℤ) :
    (redemptionTemplate d g f).conserves := by
  rw [joint_conserves_iff]
  constructor <;> (simp [debtMeasure, collMeasure, redemptionTemplate])

/-! ## Part 6: Independence of the Two Conservation Laws

THE DEEP THEOREM: the two conservation laws are genuinely independent.
There exist actions satisfying one but violating the other. -/

/-- Witness: debt conserved (Δfree=1, Δsp=-1, Δtotal=0 → measure=0)
    but collateral NOT conserved (Δvault=1, rest=0 → measure=1). -/
theorem debt_without_coll :
    ∃ a : FullAction, debtMeasure a = 0 ∧ collMeasure a ≠ 0 :=
  ⟨⟨1, -1, 0, 1, 0, 0, 0⟩,
   by simp [debtMeasure],
   by simp [collMeasure]⟩

/-- Witness: collateral conserved (Δvault=1, Δext=-1 → measure=0)
    but debt NOT conserved (Δfree=1, Δsp=0, Δtotal=0 → measure=1). -/
theorem coll_without_debt :
    ∃ a : FullAction, collMeasure a = 0 ∧ debtMeasure a ≠ 0 :=
  ⟨⟨1, 0, 0, 1, 0, 0, -1⟩,
   by simp [collMeasure],
   by simp [debtMeasure]⟩

/-- THE INDEPENDENCE THEOREM: the two conservation laws are logically independent.
    Neither implies the other. `check_invariants()` in zusd.py must check BOTH. -/
theorem laws_independent :
    (∃ a : FullAction, debtMeasure a = 0 ∧ collMeasure a ≠ 0) ∧
    (∃ a : FullAction, collMeasure a = 0 ∧ debtMeasure a ≠ 0) :=
  ⟨debt_without_coll, coll_without_debt⟩

/-! ## Part 7: Dimensionality — 2 constraints on 7 variables = 5 degrees of freedom

Given joint conservation, 2 of the 7 fields are uniquely determined
by the other 5. This is the rank-nullity theorem for Φ : ℤ⁷ → ℤ². -/

/-- Δtotal is forced by Δfree + Δsp_debt (from debt conservation). -/
theorem total_determined (a : FullAction) (h : a.conserves) :
    a.Δtotal = a.Δfree + a.Δsp_debt := by
  rw [joint_conserves_iff] at h
  unfold debtMeasure at h; omega

/-- Δext_coll is forced by the other 3 coll fields (from coll conservation). -/
theorem ext_coll_determined (a : FullAction) (h : a.conserves) :
    a.Δext_coll = -(a.Δvault_coll + a.Δsp_coll + a.Δprot_coll) := by
  rw [joint_conserves_iff] at h
  unfold collMeasure at h; omega

/-- Uniqueness: two jointly-conserving actions agreeing on 5 free fields are equal. -/
theorem action_uniqueness {a₁ a₂ : FullAction}
    (h₁ : a₁.conserves) (h₂ : a₂.conserves)
    -- Agree on the 5 free fields
    (hf : a₁.Δfree = a₂.Δfree) (hsd : a₁.Δsp_debt = a₂.Δsp_debt)
    (hvc : a₁.Δvault_coll = a₂.Δvault_coll)
    (hsc : a₁.Δsp_coll = a₂.Δsp_coll) (hpc : a₁.Δprot_coll = a₂.Δprot_coll) :
    a₁ = a₂ := by
  ext
  · exact hf
  · exact hsd
  · rw [total_determined a₁ h₁, total_determined a₂ h₂, hf, hsd]
  · exact hvc
  · exact hsc
  · exact hpc
  · rw [ext_coll_determined a₁ h₁, ext_coll_determined a₂ h₂, hvc, hsc, hpc]

/-! ## Part 8: Non-Vacuity Witnesses -/

/-- Witness: mint 1000. -/
theorem witness_mint :
    (fullMint 1000).conserves := mint_joint_conserves 1000

/-- Witness: complex transaction satisfies both laws. -/
theorem witness_complex :
    let tx := fullDeposit 1000 + fullMint 500 + fullDepositSP 200 +
              liquidationTemplate 200 800
    tx.conserves :=
  joint_conservation_compositional
    (joint_conservation_compositional
      (joint_conservation_compositional
        (deposit_joint_conserves 1000) (mint_joint_conserves 500))
      (deposit_sp_joint_conserves 200))
    (abstract_liquidation_template_conserves 200 800)

/-- Witness: independence is real — same action gives different measures.
    a = ⟨1,-1,0,1,0,0,0⟩: debt_measure = 0, coll_measure = 1. -/
theorem witness_independence :
    let a : FullAction := ⟨1, -1, 0, 1, 0, 0, 0⟩
    debtMeasure a = 0 ∧ collMeasure a = 1 := by
  constructor <;> (simp [debtMeasure, collMeasure])

end ZUSDDualConservation

end Proofs
