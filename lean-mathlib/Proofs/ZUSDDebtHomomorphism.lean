import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic

/-!
# zUSD Debt Conservation Homomorphism

## Key Property

zUSD maintains three debt counters:
- `free_debt_e8`: debt NOT covered by the stability pool
- `sp_debt_e8`: debt covered by the stability pool
- `debt_e8`: total vault debt

The conservation invariant (zusd.py:266) is:
  `free_debt_e8 + sp_debt_e8 == debt_e8`

This file proves that debt conservation is COMPOSITIONAL:
  `Δ_zusd : ZUSDAction →+ ℤ` is an AddMonoidHom whose kernel
  is exactly the set of conservation-preserving actions.

## What This File Proves

### Algebraic Structure
1. **ZUSDAction forms an AddCommGroup** (over ℤ³)
2. **Δ_zusd is an AddMonoidHom** from ZUSDAction to ℤ
3. **Conservation = Kernel**: `Δ_zusd(a) = 0 ↔ a preserves free+sp=total`

### Compositional Verification
4. **conservation_compositional**: Composition of valid actions is valid
5. **conservation_rollback**: Inverse (rollback) of valid action is valid

### Protocol Actions in Kernel
6. **mint_conserves**: mint(amount) has Δ_zusd = 0
7. **repay_conserves**: repay(amount) has Δ_zusd = 0
8. **deposit_sp_conserves**: deposit_sp(amount) has Δ_zusd = 0
9. **withdraw_sp_conserves**: withdraw_sp(amount) has Δ_zusd = 0
10. **liquidate_conserves**: liquidate(debt) has Δ_zusd = 0
11. **any_sequence_conserves**: Any composition of the 5 actions conserves

### Algebraic Relationships
12. **repay_eq_neg_mint**: repay is the inverse of mint
13. **liquidate_decomposition**: liquidate = withdraw_sp + repay

## Mathematical Structure

```
                    Δ_zusd (AddMonoidHom)
  ZUSDAction    ─────────────────────────►  ℤ
  (AddCommGroup)                            (AddCommGroup)
       │                                         │
       │ addition                                 │ addition
       ▼                                          ▼
  a₁ + a₂ + a₃  ────────────────────────►  Δ a₁ + Δ a₂ + Δ a₃
```

Kernel(Δ_zusd) = { a : ZUSDAction | a.Δfree + a.Δsp = a.Δtotal }
             = Conservation-preserving actions (AddSubgroup)
-/

namespace Proofs

namespace ZUSDDebtHomomorphism

/-! ## Part 1: ZUSDAction Definition -/

/-- A zUSD action: signed changes to the three debt buckets.
    Δfree = change in free_debt_e8 (debt not covered by SP)
    Δsp = change in sp_debt_e8 (debt covered by SP)
    Δtotal = change in debt_e8 (total vault debt) -/
structure ZUSDAction where
  Δfree : ℤ
  Δsp : ℤ
  Δtotal : ℤ
  deriving Repr, DecidableEq

@[ext]
theorem ZUSDAction.ext {a₁ a₂ : ZUSDAction}
    (hf : a₁.Δfree = a₂.Δfree) (hs : a₁.Δsp = a₂.Δsp) (ht : a₁.Δtotal = a₂.Δtotal) :
    a₁ = a₂ := by
  cases a₁; cases a₂; simp_all

/-! ## Part 2: AddCommGroup Instance -/

instance : Zero ZUSDAction := ⟨⟨0, 0, 0⟩⟩
instance : Add ZUSDAction := ⟨fun a₁ a₂ => ⟨a₁.Δfree + a₂.Δfree, a₁.Δsp + a₂.Δsp, a₁.Δtotal + a₂.Δtotal⟩⟩
instance : Neg ZUSDAction := ⟨fun a => ⟨-a.Δfree, -a.Δsp, -a.Δtotal⟩⟩
instance : Sub ZUSDAction := ⟨fun a₁ a₂ => a₁ + (-a₂)⟩

-- Simp lemmas for field projection through Add/Neg (needed for ext proofs)
@[simp] theorem ZUSDAction.add_Δfree (a₁ a₂ : ZUSDAction) : (a₁ + a₂).Δfree = a₁.Δfree + a₂.Δfree := rfl
@[simp] theorem ZUSDAction.add_Δsp (a₁ a₂ : ZUSDAction) : (a₁ + a₂).Δsp = a₁.Δsp + a₂.Δsp := rfl
@[simp] theorem ZUSDAction.add_Δtotal (a₁ a₂ : ZUSDAction) : (a₁ + a₂).Δtotal = a₁.Δtotal + a₂.Δtotal := rfl
@[simp] theorem ZUSDAction.neg_Δfree (a : ZUSDAction) : (-a).Δfree = -a.Δfree := rfl
@[simp] theorem ZUSDAction.neg_Δsp (a : ZUSDAction) : (-a).Δsp = -a.Δsp := rfl
@[simp] theorem ZUSDAction.neg_Δtotal (a : ZUSDAction) : (-a).Δtotal = -a.Δtotal := rfl

/-- ZUSDAction forms an AddCommGroup (componentwise on ℤ³). -/
instance : AddCommGroup ZUSDAction where
  add_assoc := fun a₁ a₂ a₃ => by
    apply ZUSDAction.ext <;> show _ + _ + _ = _ + (_ + _) <;> ring
  zero_add := fun a => by apply ZUSDAction.ext <;> show 0 + _ = _ <;> ring
  add_zero := fun a => by apply ZUSDAction.ext <;> show _ + 0 = _ <;> ring
  add_comm := fun a₁ a₂ => by
    apply ZUSDAction.ext <;> show _ + _ = _ + _ <;> ring
  neg_add_cancel := fun a => by
    apply ZUSDAction.ext <;> show -_ + _ = 0 <;> ring
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ## Part 3: The Conservation Homomorphism Δ_zusd

Δ_zusd(a) = a.Δfree + a.Δsp - a.Δtotal

When Δ_zusd(a) = 0: a.Δfree + a.Δsp = a.Δtotal
This is exactly the conservation invariant: free + sp = total.
-/

/-- Conservation measure: Δfree + Δsp - Δtotal.
    Zero iff the action preserves free + sp = total. -/
def conservationMeasure (a : ZUSDAction) : ℤ := a.Δfree + a.Δsp - a.Δtotal

/-- Δ_zusd as an AddMonoidHom from ZUSDAction to ℤ.
    THE key algebraic structure: conservation is a homomorphism.

    Proof of additivity: (f₁+f₂) + (s₁+s₂) - (t₁+t₂)
    = (f₁+s₁-t₁) + (f₂+s₂-t₂). Verified by ring. -/
def Δ_zusd : ZUSDAction →+ ℤ where
  toFun := conservationMeasure
  map_zero' := by rfl
  map_add' := fun a₁ a₂ => by
    show (a₁.Δfree + a₂.Δfree) + (a₁.Δsp + a₂.Δsp) - (a₁.Δtotal + a₂.Δtotal) =
         (a₁.Δfree + a₁.Δsp - a₁.Δtotal) + (a₂.Δfree + a₂.Δsp - a₂.Δtotal)
    ring

/-- THE FUNDAMENTAL THEOREM: Δ_zusd is additive.
    Conservation composes: if each step preserves the invariant,
    so does their composition. -/
theorem conservation_homomorphism (a₁ a₂ : ZUSDAction) :
    Δ_zusd (a₁ + a₂) = Δ_zusd a₁ + Δ_zusd a₂ :=
  Δ_zusd.map_add a₁ a₂

theorem conservation_zero : Δ_zusd 0 = 0 := Δ_zusd.map_zero

theorem conservation_neg (a : ZUSDAction) : Δ_zusd (-a) = -(Δ_zusd a) :=
  Δ_zusd.map_neg a

/-! ## Part 4: Balanced Actions (Kernel of Δ_zusd) -/

/-- The AddSubgroup of conservation-preserving actions = kernel of Δ_zusd. -/
def ConservingActions : AddSubgroup ZUSDAction := Δ_zusd.ker

def ZUSDAction.conserves (a : ZUSDAction) : Prop := Δ_zusd a = 0

theorem conserves_iff_mem_ker (a : ZUSDAction) :
    a.conserves ↔ a ∈ ConservingActions := by
  simp [ZUSDAction.conserves, ConservingActions, AddMonoidHom.mem_ker]

/-- Conservation is equivalent to the balance equation Δfree + Δsp = Δtotal. -/
theorem conserves_iff_balance (a : ZUSDAction) :
    a.conserves ↔ a.Δfree + a.Δsp = a.Δtotal := by
  constructor
  · intro h; unfold ZUSDAction.conserves Δ_zusd conservationMeasure at h
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h; omega
  · intro h; unfold ZUSDAction.conserves Δ_zusd conservationMeasure
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]; omega

/-- COMPOSITIONAL VERIFICATION: composition of conserving actions conserves. -/
theorem conservation_compositional {a₁ a₂ : ZUSDAction}
    (h₁ : a₁.conserves) (h₂ : a₂.conserves) :
    (a₁ + a₂).conserves := by
  simp only [ZUSDAction.conserves] at *
  rw [Δ_zusd.map_add, h₁, h₂, add_zero]

/-- Rollback of a conserving action also conserves. -/
theorem conservation_rollback {a : ZUSDAction}
    (h : a.conserves) : (-a).conserves := by
  simp only [ZUSDAction.conserves] at *
  rw [Δ_zusd.map_neg, h, neg_zero]

/-! ## Part 5: Protocol Actions Are in the Kernel -/

def mint (amount : ℤ) : ZUSDAction := ⟨amount, 0, amount⟩
def repay (amount : ℤ) : ZUSDAction := ⟨-amount, 0, -amount⟩
def deposit_sp (amount : ℤ) : ZUSDAction := ⟨-amount, amount, 0⟩
def withdraw_sp (amount : ℤ) : ZUSDAction := ⟨amount, -amount, 0⟩
def liquidate (debt : ℤ) : ZUSDAction := ⟨0, -debt, -debt⟩

theorem mint_conserves (amount : ℤ) : (mint amount).conserves := by
  rw [conserves_iff_balance]; unfold mint; ring

theorem repay_conserves (amount : ℤ) : (repay amount).conserves := by
  rw [conserves_iff_balance]; unfold repay; ring

theorem deposit_sp_conserves (amount : ℤ) : (deposit_sp amount).conserves := by
  rw [conserves_iff_balance]; unfold deposit_sp; ring

theorem withdraw_sp_conserves (amount : ℤ) : (withdraw_sp amount).conserves := by
  rw [conserves_iff_balance]; unfold withdraw_sp; ring

theorem liquidate_conserves (debt : ℤ) : (liquidate debt).conserves := by
  rw [conserves_iff_balance]; unfold liquidate; ring

/-- ANY finite sequence of protocol actions conserves.
    Proof: induction on the list, using conservation_compositional. -/
theorem any_sequence_conserves (actions : List ZUSDAction)
    (h : ∀ a ∈ actions, a.conserves) :
    actions.sum.conserves := by
  induction actions with
  | nil =>
    simp only [List.sum_nil]
    rw [conserves_iff_balance]; rfl
  | cons hd tl ih =>
    simp only [List.sum_cons]
    have hhd := h hd (.head _)
    have htl : ∀ a ∈ tl, a.conserves := fun a ha =>
      h a (.tail hd ha)
    exact conservation_compositional hhd (ih htl)

/-! ## Part 6: Algebraic Relationships Between Operations -/

/-- Repay is the additive inverse of mint: repay undoes mint. -/
theorem repay_eq_neg_mint (amount : ℤ) : repay amount = -(mint amount) := by
  ext <;> simp [repay, mint]

/-- Withdraw_sp is the additive inverse of deposit_sp. -/
theorem withdraw_eq_neg_deposit (amount : ℤ) : withdraw_sp amount = -(deposit_sp amount) := by
  ext <;> simp [withdraw_sp, deposit_sp]

/-- Mint then repay is identity (nets to zero). -/
theorem mint_repay_cancel (amount : ℤ) : mint amount + repay amount = 0 := by
  rw [repay_eq_neg_mint, add_neg_cancel]

/-- Deposit_sp then withdraw_sp is identity. -/
theorem deposit_withdraw_cancel (amount : ℤ) : deposit_sp amount + withdraw_sp amount = 0 := by
  rw [withdraw_eq_neg_deposit, add_neg_cancel]

/-- Liquidate decomposes as withdraw_sp + repay.
    Algebraically: liquidate(d) = withdraw_sp(d) + repay(d).
    This captures the insight that liquidation = "move debt out of SP,
    then destroy it". -/
theorem liquidate_decomposition (d : ℤ) :
    liquidate d = withdraw_sp d + repay d := by
  ext <;> simp [liquidate, withdraw_sp, repay]

/-! ## Part 7: Non-Vacuity Witnesses -/

theorem witness_mint_repay :
    mint 100 + repay 100 = (0 : ZUSDAction) := by native_decide

/-- Witness: complex sequence mint 500 + deposit_sp 200 + liquidate 150.
    Δfree=300, Δsp=50, Δtotal=350. 300+50=350 ✓ -/
theorem witness_complex_sequence :
    let seq := mint 500 + deposit_sp 200 + liquidate 150
    seq.Δfree = 300 ∧ seq.Δsp = 50 ∧ seq.Δtotal = 350 ∧
    seq.conserves := by
  refine ⟨by native_decide, by native_decide, by native_decide, by
    rw [conserves_iff_balance]
    native_decide⟩

theorem witness_homomorphism :
    let a₁ := mint 1000
    let a₂ := deposit_sp 400
    Δ_zusd (a₁ + a₂) = Δ_zusd a₁ + Δ_zusd a₂ ∧
    Δ_zusd a₁ = 0 ∧ Δ_zusd a₂ = 0 ∧
    Δ_zusd (a₁ + a₂) = 0 := by native_decide

theorem witness_liquidate_decomp :
    liquidate 300 = withdraw_sp 300 + repay 300 := by native_decide

end ZUSDDebtHomomorphism

end Proofs
