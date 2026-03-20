import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic

/-!
# Collateral Flow Algebra: Kirchhoff Conservation for zUSD

## Key Property

In zUSD, collateral exists in exactly four buckets:
- **vault**: `collateral_e8` (user's vault collateral)
- **sp**: `sp_coll_e8` (stability pool collateral from absorbed liquidations)
- **protocol**: `protocol_collateral_e8` (protocol treasury from redemption fees)
- **external**: implicitly, all collateral not yet deposited or already withdrawn

Every action is a **flow** of collateral between buckets. The conservation law:
  `Δvault + Δsp + Δprotocol + Δexternal = 0`

This is Kirchhoff's current law applied to the collateral graph.

## What This File Proves (14 substantive theorems)

### Flow Conservation (the core algebraic structure)
1. **CollFlow forms an AddCommGroup** over ℤ⁴ (four buckets)
2. **totalFlowHom : CollFlow →+ ℤ** is an AddMonoidHom (total flow)
3. **conservation_iff_balanced**: totalFlowHom(f) = 0 ↔ f is conservative
4. **conservation_compositional**: composition of conservative flows is conservative
5. **conservation_inverse**: inverse (rollback) of conservative flow is conservative

### Protocol Actions in the Kernel
6. **deposit_conserves**: deposit moves external → vault, net zero
7. **withdraw_conserves**: withdraw moves vault → external, net zero
8. **liquidate_coll_conserves**: liquidation moves vault → sp, net zero
9. **redeem_conserves**: redemption = vault → external + vault → protocol, net zero
10. **fee_conserves**: fee split (vault → protocol) is conservative

### Compositional Properties
11. **withdraw_undoes_deposit**: deposit + withdraw = 0 (inverse)
12. **deposit_then_liquidate**: deposit + liquidate = external → sp (composition)
13. **redeem_accounting_identity**: fee + net = gross

### Sequence Conservation
14. **any_sequence_conserves**: any list of conservative flows sums to conservative

## Mathematical Structure

```
                    totalFlowHom (AddMonoidHom)
  CollFlow       ─────────────────────────►  ℤ
  (ℤ⁴, AddCommGroup)                       (AddCommGroup)
       │                                         │
       │ addition                                 │ addition
       ▼                                          ▼
  f₁ + f₂       ─────────────────────────►  Σf₁ + Σf₂
```

Kernel(totalFlowHom) = { f : CollFlow | Δvault + Δsp + Δprotocol + Δexternal = 0 }
-/

namespace Proofs

namespace ZUSDCollateralFlowAlgebra

/-! ## Part 1: CollFlow Definition -/

/-- A collateral flow: signed changes to the four collateral buckets. -/
structure CollFlow where
  Δvault : ℤ
  Δsp : ℤ
  Δprotocol : ℤ
  Δexternal : ℤ
  deriving Repr, DecidableEq

@[ext]
theorem CollFlow.ext {f₁ f₂ : CollFlow}
    (hv : f₁.Δvault = f₂.Δvault) (hs : f₁.Δsp = f₂.Δsp)
    (hp : f₁.Δprotocol = f₂.Δprotocol) (he : f₁.Δexternal = f₂.Δexternal) :
    f₁ = f₂ := by
  cases f₁; cases f₂; simp_all

/-! ## Part 2: AddCommGroup Instance -/

instance : Zero CollFlow := ⟨⟨0, 0, 0, 0⟩⟩
instance : Add CollFlow := ⟨fun f₁ f₂ =>
  ⟨f₁.Δvault + f₂.Δvault, f₁.Δsp + f₂.Δsp,
   f₁.Δprotocol + f₂.Δprotocol, f₁.Δexternal + f₂.Δexternal⟩⟩
instance : Neg CollFlow := ⟨fun f =>
  ⟨-f.Δvault, -f.Δsp, -f.Δprotocol, -f.Δexternal⟩⟩
instance : Sub CollFlow := ⟨fun f₁ f₂ => f₁ + (-f₂)⟩

@[simp] theorem CollFlow.zero_Δvault : (0 : CollFlow).Δvault = 0 := rfl
@[simp] theorem CollFlow.zero_Δsp : (0 : CollFlow).Δsp = 0 := rfl
@[simp] theorem CollFlow.zero_Δprotocol : (0 : CollFlow).Δprotocol = 0 := rfl
@[simp] theorem CollFlow.zero_Δexternal : (0 : CollFlow).Δexternal = 0 := rfl
@[simp] theorem CollFlow.add_Δvault (f₁ f₂ : CollFlow) :
    (f₁ + f₂).Δvault = f₁.Δvault + f₂.Δvault := rfl
@[simp] theorem CollFlow.add_Δsp (f₁ f₂ : CollFlow) :
    (f₁ + f₂).Δsp = f₁.Δsp + f₂.Δsp := rfl
@[simp] theorem CollFlow.add_Δprotocol (f₁ f₂ : CollFlow) :
    (f₁ + f₂).Δprotocol = f₁.Δprotocol + f₂.Δprotocol := rfl
@[simp] theorem CollFlow.add_Δexternal (f₁ f₂ : CollFlow) :
    (f₁ + f₂).Δexternal = f₁.Δexternal + f₂.Δexternal := rfl
@[simp] theorem CollFlow.neg_Δvault (f : CollFlow) :
    (-f).Δvault = -f.Δvault := rfl
@[simp] theorem CollFlow.neg_Δsp (f : CollFlow) :
    (-f).Δsp = -f.Δsp := rfl
@[simp] theorem CollFlow.neg_Δprotocol (f : CollFlow) :
    (-f).Δprotocol = -f.Δprotocol := rfl
@[simp] theorem CollFlow.neg_Δexternal (f : CollFlow) :
    (-f).Δexternal = -f.Δexternal := rfl

/-- CollFlow forms an AddCommGroup (componentwise on ℤ⁴). -/
instance : AddCommGroup CollFlow where
  add_assoc := fun a b c => by ext <;> simp [add_assoc]
  zero_add := fun a => by ext <;> simp
  add_zero := fun a => by ext <;> simp
  add_comm := fun a b => by ext <;> simp [add_comm]
  neg_add_cancel := fun a => by ext <;> simp
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ## Part 3: The Conservation Homomorphism

totalFlow(f) = Δvault + Δsp + Δprotocol + Δexternal

Conservation means totalFlow = 0: collateral is neither created nor destroyed. -/

/-- Total flow: sum of all bucket changes.
    Zero iff collateral is conserved (Kirchhoff's current law). -/
def totalFlow (f : CollFlow) : ℤ :=
  f.Δvault + f.Δsp + f.Δprotocol + f.Δexternal

/-- totalFlowHom as an AddMonoidHom from CollFlow to ℤ.
    THE key algebraic structure: conservation is a homomorphism. -/
def totalFlowHom : CollFlow →+ ℤ where
  toFun := totalFlow
  map_zero' := by rfl
  map_add' := fun f₁ f₂ => by
    show (f₁.Δvault + f₂.Δvault) + (f₁.Δsp + f₂.Δsp) +
         (f₁.Δprotocol + f₂.Δprotocol) + (f₁.Δexternal + f₂.Δexternal) =
         (f₁.Δvault + f₁.Δsp + f₁.Δprotocol + f₁.Δexternal) +
         (f₂.Δvault + f₂.Δsp + f₂.Δprotocol + f₂.Δexternal)
    ring

/-- Conservation predicate. -/
def CollFlow.conserves (f : CollFlow) : Prop := totalFlowHom f = 0

/-- Conservation ↔ the bucket changes sum to zero. -/
theorem conservation_iff_balanced (f : CollFlow) :
    f.conserves ↔ f.Δvault + f.Δsp + f.Δprotocol + f.Δexternal = 0 := by
  unfold CollFlow.conserves totalFlowHom totalFlow
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- Composition of conservative flows is conservative. -/
theorem conservation_compositional {f₁ f₂ : CollFlow}
    (h₁ : f₁.conserves) (h₂ : f₂.conserves) :
    (f₁ + f₂).conserves := by
  simp only [CollFlow.conserves] at *
  rw [totalFlowHom.map_add, h₁, h₂, add_zero]

/-- Inverse of a conservative flow is conservative. -/
theorem conservation_inverse {f : CollFlow}
    (h : f.conserves) : (-f).conserves := by
  simp only [CollFlow.conserves] at *
  rw [totalFlowHom.map_neg, h, neg_zero]

/-! ## Part 4: Protocol Actions as Concrete Flows

Each protocol action is defined as a specific CollFlow. Conservation
follows from the concrete values summing to zero. -/

/-- Deposit collateral: amount enters vault from external. -/
def deposit_coll (amount : ℤ) : CollFlow := ⟨amount, 0, 0, -amount⟩

/-- Withdraw collateral: amount leaves vault to external. -/
def withdraw_coll (amount : ℤ) : CollFlow := ⟨-amount, 0, 0, amount⟩

/-- Liquidation collateral transfer: vault → stability pool. -/
def liquidate_coll (amount : ℤ) : CollFlow := ⟨-amount, amount, 0, 0⟩

/-- Fee collection: vault → protocol treasury. -/
def fee_to_protocol (amount : ℤ) : CollFlow := ⟨-amount, 0, amount, 0⟩

/-- Redemption: vault → external (net) + vault → protocol (fee).
    Total vault outflow = gross = net + fee. -/
def redeem_coll (gross fee : ℤ) : CollFlow :=
  ⟨-gross, 0, fee, gross - fee⟩

-- Conservation proofs for each action

theorem deposit_conserves (amount : ℤ) : (deposit_coll amount).conserves := by
  rw [conservation_iff_balanced]; unfold deposit_coll; ring

theorem withdraw_conserves (amount : ℤ) : (withdraw_coll amount).conserves := by
  rw [conservation_iff_balanced]; unfold withdraw_coll; ring

theorem liquidate_coll_conserves (amount : ℤ) : (liquidate_coll amount).conserves := by
  rw [conservation_iff_balanced]; unfold liquidate_coll; ring

theorem fee_conserves (amount : ℤ) : (fee_to_protocol amount).conserves := by
  rw [conservation_iff_balanced]; unfold fee_to_protocol; ring

theorem redeem_conserves (gross fee : ℤ) : (redeem_coll gross fee).conserves := by
  rw [conservation_iff_balanced]; unfold redeem_coll; ring

/-! ## Part 5: Algebraic Relationships Between Actions -/

/-- Withdraw is the additive inverse of deposit. -/
theorem withdraw_eq_neg_deposit (amount : ℤ) :
    withdraw_coll amount = -(deposit_coll amount) := by
  ext <;> simp [withdraw_coll, deposit_coll]

/-- Deposit then withdraw = identity (nets to zero). -/
theorem withdraw_undoes_deposit (amount : ℤ) :
    deposit_coll amount + withdraw_coll amount = 0 := by
  rw [withdraw_eq_neg_deposit, add_neg_cancel]

/-- Deposit then liquidate = external → SP (bypasses vault).
    This is flow composition: external→vault + vault→SP = external→SP.
    The vault Δ cancels: (+amount) + (-amount) = 0. -/
theorem deposit_then_liquidate (amount : ℤ) :
    deposit_coll amount + liquidate_coll amount =
    (⟨0, amount, 0, -amount⟩ : CollFlow) := by
  ext <;> simp [deposit_coll, liquidate_coll]

/-- Liquidation + fee collection decompose redemption:
    (vault→SP) + (vault→protocol) is NOT the same as redemption
    (which is vault→external + vault→protocol), but we CAN decompose
    redemption as (vault→external for net) + (vault→protocol for fee). -/
theorem redeem_decomposition (gross fee : ℤ) :
    redeem_coll gross fee = withdraw_coll (gross - fee) + fee_to_protocol fee := by
  ext <;> simp [redeem_coll, withdraw_coll, fee_to_protocol] <;> ring

/-! ## Part 6: Redemption Accounting Identity

The redemption flow satisfies: fee + net = gross.
This is the fundamental accounting equation for fee-bearing transfers. -/

/-- Vault outflow from redemption = gross collateral. -/
theorem redeem_vault_outflow (gross fee : ℤ) :
    (redeem_coll gross fee).Δvault = -gross := by
  unfold redeem_coll; rfl

/-- External inflow from redemption = gross - fee (net to user). -/
theorem redeem_external_inflow (gross fee : ℤ) :
    (redeem_coll gross fee).Δexternal = gross - fee := by
  unfold redeem_coll; rfl

/-- Protocol inflow from redemption = fee. -/
theorem redeem_protocol_inflow (gross fee : ℤ) :
    (redeem_coll gross fee).Δprotocol = fee := by
  unfold redeem_coll; rfl

/-- Fee + net = gross (the accounting identity for fee-bearing transfers).
    This derives the identity from the flow structure, not from assumption. -/
theorem redeem_accounting_identity (gross fee : ℤ) :
    (redeem_coll gross fee).Δexternal + (redeem_coll gross fee).Δprotocol = gross := by
  simp [redeem_coll]

/-! ## Part 7: Sequence Conservation -/

/-- Any finite sequence of conservative flows is conservative. -/
theorem any_sequence_conserves (flows : List CollFlow)
    (h : ∀ f ∈ flows, f.conserves) :
    flows.sum.conserves := by
  induction flows with
  | nil =>
    simp only [List.sum_nil]
    rw [conservation_iff_balanced]; rfl
  | cons hd tl ih =>
    simp only [List.sum_cons]
    exact conservation_compositional
      (h hd (.head _))
      (ih (fun f hf => h f (.tail hd hf)))

/-- A complex transaction (deposit + mint → later → redeem + fee) conserves.
    Witness: deposit 1000 + liquidate 800 + fee_to_protocol 50 + withdraw 150. -/
theorem complex_transaction_conserves :
    let tx := deposit_coll 1000 + liquidate_coll 800 +
              fee_to_protocol 50 + withdraw_coll 150
    tx.conserves := by
  apply conservation_compositional
  apply conservation_compositional
  apply conservation_compositional
  · exact deposit_conserves 1000
  · exact liquidate_coll_conserves 800
  · exact fee_conserves 50
  · exact withdraw_conserves 150

/-! ## Part 8: Flow Uniqueness (the deep algebraic result)

Given a conservative flow with known (Δvault, Δsp, Δprotocol), the
external component is uniquely determined. This is why 3 of the 4
buckets are stored explicitly and the 4th (external) is implicit. -/

/-- External change is determined by the other three buckets.
    This is why zusd.py only tracks vault, SP, and protocol collateral —
    external is the accounting residual. -/
theorem external_determined (f : CollFlow) (h : f.conserves) :
    f.Δexternal = -(f.Δvault + f.Δsp + f.Δprotocol) := by
  rw [conservation_iff_balanced] at h; omega

/-- Two conservative flows agreeing on vault, SP, and protocol must agree on external.
    Conservation + 3 known fields → 4th field unique. -/
theorem flow_uniqueness {f₁ f₂ : CollFlow}
    (h₁ : f₁.conserves) (h₂ : f₂.conserves)
    (hv : f₁.Δvault = f₂.Δvault) (hs : f₁.Δsp = f₂.Δsp)
    (hp : f₁.Δprotocol = f₂.Δprotocol) :
    f₁ = f₂ := by
  ext
  · exact hv
  · exact hs
  · exact hp
  · rw [external_determined f₁ h₁, external_determined f₂ h₂, hv, hs, hp]

/-! ## Part 9: Non-Vacuity Witnesses -/

/-- Witness: deposit 500 units. -/
theorem witness_deposit :
    let f := deposit_coll 500
    f.Δvault = 500 ∧ f.Δexternal = -500 ∧ f.Δsp = 0 ∧ f.Δprotocol = 0 ∧
    f.conserves := by
  refine ⟨by rfl, by rfl, by rfl, by rfl, deposit_conserves 500⟩

/-- Witness: liquidation moves 1000 from vault to SP. -/
theorem witness_liquidation :
    let f := liquidate_coll 1000
    f.Δvault = -1000 ∧ f.Δsp = 1000 ∧ f.conserves := by
  refine ⟨by rfl, by rfl, liquidate_coll_conserves 1000⟩

/-- Witness: redemption with gross=800, fee=40.
    Vault: -800, External: +760, Protocol: +40, SP: 0. -/
theorem witness_redemption :
    let f := redeem_coll 800 40
    f.Δvault = -800 ∧ f.Δexternal = 760 ∧ f.Δprotocol = 40 ∧ f.Δsp = 0 ∧
    f.conserves := by
  refine ⟨by rfl, by rfl, by rfl, by rfl, redeem_conserves 800 40⟩

/-- Witness: accounting identity. 760 + 40 = 800. -/
theorem witness_accounting :
    (redeem_coll 800 40).Δexternal + (redeem_coll 800 40).Δprotocol = 800 := by
  native_decide

/-- Witness: deposit + liquidate composition.
    deposit 500 + liquidate 500 = external→SP(500). -/
theorem witness_deposit_liquidate :
    let f := deposit_coll 500 + liquidate_coll 500
    f.Δvault = 0 ∧ f.Δsp = 500 ∧ f.Δexternal = -500 ∧ f.Δprotocol = 0 := by
  simp [deposit_coll, liquidate_coll]

end ZUSDCollateralFlowAlgebra

end Proofs
