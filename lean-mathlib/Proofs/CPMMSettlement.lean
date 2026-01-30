import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

-- Import our modules
import Proofs.SettlementAlgebra
import Proofs.CPMMInvariants

/-!
# CPMM Settlement Bridge

This file connects the abstract Settlement Algebra to concrete CPMM operations.
It shows how AMM swaps produce settlements and proves they satisfy algebraic properties.

## The Verification Stack

```
  ┌─────────────────────────────────────────┐
  │  Abstract: Settlement Algebra           │
  │  - AddCommGroup Settlement              │
  │  - Δ : Settlement →+ ℤ                  │
  │  - Balanced = Δ.ker                     │
  └─────────────────────────────────────────┘
                    ↑
                    │ This file bridges
                    │
  ┌─────────────────────────────────────────┐
  │  Concrete: CPMM Operations              │
  │  - swapOutput computes dy               │
  │  - K = x*y invariant                    │
  │  - k_monotone_* theorems                │
  └─────────────────────────────────────────┘
```

## Key Results

1. **CPMM swap → Settlement**: Every swap produces a settlement
2. **Equal in/out swaps are balanced**: Δ = 0 when `amount_in = amount_out`
3. **Safe when amt_in ≥ amt_out**: Δ ≥ 0 (scalar, not value conservation)
4. **K-preservation**: `valid_swap_preserves_K` — the ACTUAL CPMM invariant
5. **LP operations compose**: Multiple operations preserve algebraic structure

-/

namespace CPMMSettlement

open SettlementAlgebra
open CPMMInvariants

/-! ## Part 1: CPMM Swap as Settlement

A CPMM swap takes `amount_in` from user, gives `amount_out` to user.
From the pool's perspective:
- dx = +amount_in (pool receives)
- dy = -amount_out (pool gives)
-/

/-- Convert a CPMM swap to a Settlement.
    Pool receives `amount_in`, gives `amount_out`. -/
def cpmmSwapToSettlement (amount_in amount_out : ℕ) : Settlement :=
  ⟨amount_in, -(amount_out : ℤ)⟩

/-- This is exactly Settlement.swap from SettlementAlgebra -/
theorem cpmmSwapToSettlement_eq_swap (amount_in amount_out : ℕ) :
    cpmmSwapToSettlement amount_in amount_out = Settlement.swap amount_in amount_out := by
  rfl

/-! ## Part 2: Zero-Fee Swap is Balanced

For a zero-fee CPMM swap where amount_out = swapOutputZeroFee:
- If amount_in = amount_out, the settlement is balanced (Δ = 0)
- This models a "fair" swap with no protocol extraction

Note: In practice, CPMM swaps are NOT balanced because amount_out < amount_in
due to the constant product formula. The "balanced" case is theoretical.
-/

/-- A swap where in = out is balanced -/
theorem equal_swap_balanced (amt : ℕ) :
    (cpmmSwapToSettlement amt amt).isBalanced := by
  unfold cpmmSwapToSettlement Settlement.isBalanced SettlementAlgebra.Δ SettlementAlgebra.netFlow
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  omega

/-! ## Part 3: Scalar-Safe Swap

When amount_in ≥ amount_out, the settlement satisfies Δ ≥ 0 (non-negative
scalar flow). This is a **conditional** property — it does NOT always hold
for CPMM swaps (when the output token is worth more per unit, amount_out
can exceed amount_in in raw units). See Part 9 for the safety hierarchy.
-/

/-- CPMM swap with amount_in ≥ amount_out is safe -/
theorem cpmm_swap_safe (amount_in amount_out : ℕ) (h : amount_in ≥ amount_out) :
    (cpmmSwapToSettlement amount_in amount_out).isSafe := by
  unfold cpmmSwapToSettlement Settlement.isSafe SettlementAlgebra.Δ SettlementAlgebra.netFlow
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  omega

/-- CPMM output is always ≤ output reserve (from swap_output_le_reserve) -/
theorem cpmm_output_bounded (rin rout net : ℕ) :
    swapOutput rin rout net ≤ rout := by
  exact swap_output_le_reserve

/-! ## Part 4: Net Flow Computation

The net scalar flow of a CPMM swap is `amount_in - amount_out`.
This is a **raw unit difference**, not an economically meaningful
quantity like fee or slippage (which would require a unit-of-account).
-/

/-- Net flow of CPMM swap = amount_in - amount_out -/
theorem cpmm_swap_net_flow (amount_in amount_out : ℕ) :
    Δ (cpmmSwapToSettlement amount_in amount_out) = (amount_in : ℤ) - (amount_out : ℤ) := by
  unfold cpmmSwapToSettlement SettlementAlgebra.Δ SettlementAlgebra.netFlow
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ring

/-- Net flow is non-negative when amount_in ≥ amount_out -/
theorem cpmm_swap_net_flow_nonneg (amount_in amount_out : ℕ) (h : amount_in ≥ amount_out) :
    Δ (cpmmSwapToSettlement amount_in amount_out) ≥ 0 := by
  rw [cpmm_swap_net_flow]
  omega

/-! ## Part 5: Composition of Swaps

Multiple CPMM swaps compose to form a combined settlement.
The total net flow is the sum of individual net flows.
-/

/-- Two CPMM swaps compose -/
theorem cpmm_swap_composition (a₁ a₂ b₁ b₂ : ℕ) :
    cpmmSwapToSettlement a₁ b₁ ∘ₛ cpmmSwapToSettlement a₂ b₂ =
    cpmmSwapToSettlement (a₁ + a₂) (b₁ + b₂) := by
  unfold cpmmSwapToSettlement Settlement.comp
  simp only [HAdd.hAdd, Add.add]
  apply Settlement.ext
  · show (a₁ : ℤ) + (a₂ : ℤ) = ((a₁ + a₂ : ℕ) : ℤ); simp [Nat.cast_add]
  · show -(b₁ : ℤ) + -(b₂ : ℤ) = -((b₁ + b₂ : ℕ) : ℤ); simp [Nat.cast_add]; ring

/-- Net flow is additive over swap composition -/
theorem cpmm_swap_net_flow_additive (a₁ a₂ b₁ b₂ : ℕ) :
    Δ (cpmmSwapToSettlement a₁ b₁ ∘ₛ cpmmSwapToSettlement a₂ b₂) =
    Δ (cpmmSwapToSettlement a₁ b₁) + Δ (cpmmSwapToSettlement a₂ b₂) := by
  exact conservation_homomorphism _ _

/-! ## Part 6: LP Operations as Settlements

Liquidity provider operations can also be modeled as settlements:
- Add liquidity: pool receives tokens (dx > 0, dy > 0)
- Remove liquidity: pool returns tokens (dx < 0, dy < 0)
-/

/-- LP deposit as a settlement -/
def lpDepositToSettlement (amount0 amount1 : ℕ) : Settlement :=
  ⟨amount0, amount1⟩

/-- LP withdrawal as a settlement -/
def lpWithdrawToSettlement (return0 return1 : ℕ) : Settlement :=
  ⟨-(return0 : ℤ), -(return1 : ℤ)⟩

/-- LP deposit is always safe (pool receives, never gives) -/
theorem lp_deposit_safe (amount0 amount1 : ℕ) :
    (lpDepositToSettlement amount0 amount1).isSafe := by
  unfold lpDepositToSettlement Settlement.isSafe SettlementAlgebra.Δ SettlementAlgebra.netFlow
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  omega

/-- LP deposit net flow is positive -/
theorem lp_deposit_net_flow (amount0 amount1 : ℕ) :
    Δ (lpDepositToSettlement amount0 amount1) = (amount0 : ℤ) + (amount1 : ℤ) := by
  unfold lpDepositToSettlement SettlementAlgebra.Δ SettlementAlgebra.netFlow
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- LP withdrawal net flow is negative -/
theorem lp_withdraw_net_flow (return0 return1 : ℕ) :
    Δ (lpWithdrawToSettlement return0 return1) = -((return0 : ℤ) + (return1 : ℤ)) := by
  unfold lpWithdrawToSettlement SettlementAlgebra.Δ SettlementAlgebra.netFlow
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ring

/-! ## Part 7: LP Roundtrip Settlement

When an LP deposits and immediately withdraws, the combined settlement
should have non-negative net flow (LP can't profit from roundtrip).
-/

/-- LP roundtrip as combined settlement -/
def lpRoundtripSettlement (deposit0 deposit1 return0 return1 : ℕ) : Settlement :=
  lpDepositToSettlement deposit0 deposit1 ∘ₛ lpWithdrawToSettlement return0 return1

/-- LP roundtrip net flow = deposits - withdrawals -/
theorem lp_roundtrip_net_flow (d0 d1 r0 r1 : ℕ) :
    Δ (lpRoundtripSettlement d0 d1 r0 r1) =
    ((d0 : ℤ) + d1) - ((r0 : ℤ) + r1) := by
  simp only [lpRoundtripSettlement]
  rw [conservation_homomorphism, lp_deposit_net_flow, lp_withdraw_net_flow]
  ring

/-- If LP gets back ≤ what they deposited, roundtrip is safe -/
theorem lp_roundtrip_safe (d0 d1 r0 r1 : ℕ) (h : r0 + r1 ≤ d0 + d1) :
    (lpRoundtripSettlement d0 d1 r0 r1).isSafe := by
  simp only [Settlement.isSafe]
  rw [lp_roundtrip_net_flow]
  omega

/-! ## Part 8: K-Monotonicity Bridge (THE REAL CPMM INVARIANT)

**Critical insight**: The ACTUAL safety property of CPMM is K-monotonicity,
not Δ ≥ 0. The scalar sum Δ = dx + dy is semantically weak because it adds
different token units.

This section bridges to the REAL invariant from CPMMInvariants.
-/

/-- CPMM pool state: reserves of two tokens -/
structure CPMMState where
  reserve_in : ℕ
  reserve_out : ℕ
  deriving Repr, DecidableEq

/-- A valid CPMM swap transition: amount_out is computed by swapOutputZeroFee -/
structure ValidCPMMSwap (s : CPMMState) where
  amount_in : ℕ
  amount_in_pos : 0 < amount_in
  reserve_in_pos : 0 < s.reserve_in
  reserve_out_pos : 0 < s.reserve_out

/-- Compute the output for a valid swap -/
def ValidCPMMSwap.amount_out {s : CPMMState} (swap : ValidCPMMSwap s) : ℕ :=
  swapOutputZeroFee s.reserve_in s.reserve_out swap.amount_in

/-- New state after a valid swap -/
def ValidCPMMSwap.newState {s : CPMMState} (swap : ValidCPMMSwap s) : CPMMState :=
  { reserve_in := s.reserve_in + swap.amount_in
    reserve_out := s.reserve_out - swap.amount_out }

/-- K-value of a state -/
def CPMMState.K (s : CPMMState) : ℕ := kValue s.reserve_in s.reserve_out

/-- Output of a valid swap is bounded by the output reserve.
    This ensures `newState.reserve_out` does not underflow. -/
theorem ValidCPMMSwap.amount_out_le_reserve {s : CPMMState} (swap : ValidCPMMSwap s) :
    swap.amount_out ≤ s.reserve_out := by
  simp only [ValidCPMMSwap.amount_out, swapOutputZeroFee]
  apply Nat.div_le_of_le_mul
  calc s.reserve_out * swap.amount_in
      ≤ s.reserve_out * (s.reserve_in + swap.amount_in) := by
        nlinarith [Nat.zero_le s.reserve_in]
    _ = (s.reserve_in + swap.amount_in) * s.reserve_out := by ring

/-- THE REAL INVARIANT: Valid CPMM swaps preserve K (uses k_monotone_zero_fee) -/
theorem valid_swap_preserves_K {s : CPMMState} (swap : ValidCPMMSwap s) :
    (swap.newState).K ≥ s.K := by
  simp only [ValidCPMMSwap.newState, CPMMState.K, ValidCPMMSwap.amount_out]
  exact k_monotone_zero_fee swap.reserve_in_pos swap.reserve_out_pos swap.amount_in_pos

/-- Convert a valid swap to a settlement -/
def validSwapToSettlement {s : CPMMState} (swap : ValidCPMMSwap s) : Settlement :=
  cpmmSwapToSettlement swap.amount_in swap.amount_out

/-- Non-vacuity: Concrete swap preserves K -/
theorem witness_K_preservation :
    let s : CPMMState := ⟨1000, 1000⟩
    let swap : ValidCPMMSwap s := ⟨100, by decide, by decide, by decide⟩
    swap.newState.K ≥ s.K := by
  simp only [ValidCPMMSwap.newState, CPMMState.K, ValidCPMMSwap.amount_out,
             swapOutputZeroFee, kValue]
  native_decide

/-- Non-vacuity: Concrete K values
    amount_out = (1000 * 100) / 1100 = 90
    new K = 1100 * 910 = 1,001,000 ≥ 1,000,000 = old K -/
theorem witness_K_values :
    let s : CPMMState := ⟨1000, 1000⟩
    let swap : ValidCPMMSwap s := ⟨100, by decide, by decide, by decide⟩
    s.K = 1000000 ∧
    swap.newState.K = 1001000 ∧  -- 1100 * 910
    swap.newState.K > s.K := by
  native_decide

/-! ## Part 9: Semantic Clarification

**WARNING**: The `isSafe` property (Δ ≥ 0) is NOT the same as K-preservation!

- Δ = dx + dy adds different token units (semantically weak)
- K-preservation is the ACTUAL CPMM invariant

When amount_out (in token Y) is numerically larger than amount_in (in token X),
we have Δ < 0, but K is still preserved. This happens when token X is more
"valuable" than token Y in the pool's ratio.

The correct safety hierarchy is:
1. K-preservation (strongest, always holds for valid swaps)
2. Output bounded by reserve (swap_output_lt_reserve)
3. Δ ≥ 0 (only when same-unit comparison makes sense)
-/

/-! ## Part 10: Non-vacuity Witnesses -/

/-- Witness: concrete CPMM swap net flow -/
theorem witness_cpmm_swap_flow :
    Δ (cpmmSwapToSettlement 100 97) = 3 := by
  unfold cpmmSwapToSettlement SettlementAlgebra.Δ SettlementAlgebra.netFlow
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  native_decide

/-- Witness: CPMM swap is safe -/
theorem witness_cpmm_swap_safe :
    (cpmmSwapToSettlement 100 97).isSafe := by
  exact cpmm_swap_safe 100 97 (by decide)

/-- Witness: swap composition additivity -/
theorem witness_swap_composition_additive :
    Δ (cpmmSwapToSettlement 100 95 ∘ₛ cpmmSwapToSettlement 50 48) =
    Δ (cpmmSwapToSettlement 100 95) + Δ (cpmmSwapToSettlement 50 48) := by
  exact conservation_homomorphism _ _

/-- Witness: LP roundtrip net flow -/
theorem witness_lp_roundtrip_flow :
    Δ (lpRoundtripSettlement 100 200 95 190) = 15 := by
  rw [lp_roundtrip_net_flow]
  native_decide

/-! ## Part 11: Summary

### The Real CPMM Safety Hierarchy

| Property | Meaning | Proved Where |
|----------|---------|--------------|
| K-preservation | `K(new) ≥ K(old)` | `valid_swap_preserves_K` (uses `k_monotone_zero_fee`) |
| Output bounded | `amount_out < reserve_out` | `swap_output_lt_reserve` |
| Δ ≥ 0 | `amount_in ≥ amount_out` (WEAK, different units!) | `cpmm_swap_safe` |

### Key Insight

**Δ = dx + dy is semantically weak** because it adds different token units.
The ACTUAL CPMM invariant is K-preservation, now proved via `valid_swap_preserves_K`.

### Bridge Theorems

| Theorem | Statement |
|---------|-----------|
| **valid_swap_preserves_K** | K(new_state) ≥ K(old_state) for valid swaps |
| cpmm_swap_composition | Settlements compose algebraically |
| lp_roundtrip_safe | LP can't profit from roundtrip (given return ≤ deposit) |
| conservation_homomorphism | Δ is additive (algebraic property) |

### Verification Stack

1. **Concrete invariant**: `k_monotone_zero_fee` in CPMMInvariants
2. **State transition**: `ValidCPMMSwap` models valid swaps
3. **K-preservation**: `valid_swap_preserves_K` bridges to invariant
4. **Settlement view**: `validSwapToSettlement` for algebraic composition
-/

end CPMMSettlement
