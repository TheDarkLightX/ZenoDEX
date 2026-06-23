import Proofs.CPMMInvariants
import Proofs.CPMMEdgeRounding
import Proofs.RoundingErrorBound
import Proofs.AntiFragmentation
import Proofs.CPMMOutputMonotonicity
import Mathlib.Tactic

/-!
# AMM Integer Runtime Bridge

This file bridges from ideal CPMM
math to the integer runtime used by ZenoDEX.

The existing library already proves important local facts:
- `AntiFragmentation.swapOut` is the runtime floor CPMM output.
- `Proofs.CPMMEdgeRounding.ceilSwapOut` is a one-unit ceiling envelope.
- `AntiFragmentation.k_nondecreasing` proves zero-fee integer K monotonicity.
- `CPMMInvariants.k_monotone_with_fee` proves fee-retaining K monotonicity.
- `Proofs.RoundingErrorBound.rounding_gap_bound_general` proves an abstract
  route-level recurrence envelope.

This theorem layer is a certificate-shaped bridge that bundles those facts into
runtime-facing guarantees.
-/

namespace Proofs
namespace AMMIntegerRuntimeBridge

open AntiFragmentation
open CPMMEdgeRounding
open RoundingErrorBound

/-- Runtime floor quote used by the integer CPMM path. -/
def floorQuote (rin rout amountIn : Nat) : Nat := AntiFragmentation.swapOut rin rout amountIn

/-- Ceiling quote: a conservative one-unit ideal envelope for the floor quote. -/
def ceilingQuote (rin rout amountIn : Nat) : Nat := CPMMEdgeRounding.ceilSwapOut rin rout amountIn

/-- A compact proof-carrying receipt for one integer CPMM exact-in edge. -/
structure IntegerSwapBridgeReceipt (rin rout amountIn : Nat) where
  floor_le_ceiling : floorQuote rin rout amountIn ≤ ceilingQuote rin rout amountIn
  ceiling_le_floor_plus_one : ceilingQuote rin rout amountIn ≤ floorQuote rin rout amountIn + 1
  floor_no_overdelivery : floorQuote rin rout amountIn ≤ rout
  k_nondec :
    AntiFragmentation.kValue (rin + amountIn) (rout - floorQuote rin rout amountIn)
      ≥ AntiFragmentation.kValue rin rout
  z_perturbation :
    (↑(floorQuote rin rout amountIn) : Int) ≥ ↑(ceilingQuote rin rout amountIn) - 1

/-- Build the single-edge integer bridge receipt from the existing CPMM lemmas.

Economic reading: the runtime floor output is never above the one-unit ideal
ceiling envelope, never exceeds reserves, and the post-swap constant-product
state does not move backward. -/
theorem build_integer_swap_bridge_receipt (rin rout amountIn : Nat) :
    IntegerSwapBridgeReceipt rin rout amountIn := by
  exact {
    floor_le_ceiling := cpmm_floor_le_ceil rin rout amountIn
    ceiling_le_floor_plus_one := cpmm_edge_gap_le_one rin rout amountIn
    floor_no_overdelivery := swapOut_le_reserve rin rout amountIn
    k_nondec := AntiFragmentation.k_nondecreasing rin rout amountIn
    z_perturbation := cpmm_edge_perturbation rin rout amountIn
  }

/-- Floor output and ceiling output differ by at most one unit.  This is the
standalone form useful for generated validators. -/
theorem integer_swap_rounding_gap_le_one (rin rout amountIn : Nat) :
    ceilingQuote rin rout amountIn ≤ floorQuote rin rout amountIn + 1 := by
  exact cpmm_edge_gap_le_one rin rout amountIn

/-- Runtime floor output cannot overdeliver relative to the reserve. -/
theorem integer_swap_no_overdelivery (rin rout amountIn : Nat) :
    floorQuote rin rout amountIn ≤ rout := by
  exact swapOut_le_reserve rin rout amountIn

/-- Runtime floor output is a one-unit lower perturbation of the conservative
ceiling quote.  This is the Int form used by arbitrage and route certificates. -/
theorem integer_swap_z_perturbation (rin rout amountIn : Nat) :
    (↑(floorQuote rin rout amountIn) : Int) ≥ ↑(ceilingQuote rin rout amountIn) - 1 := by
  exact cpmm_edge_perturbation rin rout amountIn

/-- Fee-retaining exact-in swap preserves or increases K when the fee basis
points are inside the protocol range.  This is stated in the runtime shape:
gross input is added to the pool, while the quote is computed on the fee-netted
input. -/
theorem integer_swap_k_nondec_with_fee
    (rin rout amountIn feeBps : Nat)
    (hrin : 0 < rin)
    (hrout : 0 < rout)
    (hamount : 0 < amountIn)
    (hfee_pos : 0 < feeBps)
    (hfee_bound : feeBps ≤ 10000) :
    let net := CPMMInvariants.netAmount amountIn feeBps
    let amountOut := CPMMInvariants.swapOutput rin rout net
    CPMMInvariants.kValue (rin + amountIn) (rout - amountOut)
      ≥ CPMMInvariants.kValue rin rout := by
  exact CPMMInvariants.k_monotone_with_fee (fee_bps := feeBps)
    hrin hrout hamount hfee_pos hfee_bound

/-- Abstract route rounding envelope, specialized into a reusable certificate
form.  If a route-level gap sequence starts with one-unit error and each next
hop adds at most `step`, then every `k`-hop runtime quote stays inside the
linear envelope `step*k - (step-1)`.

This should preferably be proved by reusing `rounding_gap_bound_general`, but
 -/
theorem integer_route_rounding_envelope
    (gap : Nat → Int)
    (step : Int)
    (hbase : gap 1 ≤ 1)
    (hrec : ∀ k, 1 ≤ k → gap (k + 1) ≤ gap k + step)
    (k : Nat)
    (hk : 1 ≤ k) :
    gap k ≤ step * ↑k - (step - 1) := by
  exact rounding_gap_bound_general gap step hbase hrec k hk

/-- A sharper Lipschitz route envelope: when a composed quote path propagates
prior rounding error with Lipschitz constant at most one, the accumulated integer
rounding error is bounded by the hop count. -/
theorem integer_route_lipschitz_rounding_envelope
    (gap : Nat → Int)
    (hbase : gap 1 ≤ 1)
    (hrec : ∀ k, 1 ≤ k → gap (k + 1) ≤ gap k + 1)
    (k : Nat)
    (hk : 1 ≤ k) :
    gap k ≤ ↑k := by
  exact rounding_gap_lipschitz_bound gap hbase hrec k hk

/-- The single-edge receipt implies all generated validator facts.  This theorem
is deliberately certificate-shaped so a future code generator can emit/check the
same fields. -/
theorem integer_receipt_implies_runtime_safety
    (rin rout amountIn : Nat)
    (receipt : IntegerSwapBridgeReceipt rin rout amountIn) :
    floorQuote rin rout amountIn ≤ rout ∧
    ceilingQuote rin rout amountIn ≤ floorQuote rin rout amountIn + 1 ∧
    AntiFragmentation.kValue (rin + amountIn) (rout - floorQuote rin rout amountIn)
      ≥ AntiFragmentation.kValue rin rout := by
  exact ⟨receipt.floor_no_overdelivery, receipt.ceiling_le_floor_plus_one, receipt.k_nondec⟩

end AMMIntegerRuntimeBridge
end Proofs
