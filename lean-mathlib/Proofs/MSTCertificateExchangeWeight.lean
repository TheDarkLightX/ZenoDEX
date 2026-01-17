import Proofs.MSTCertificateNoImprovingExchange

/-!
MST certificate: numeric exchange inequality (Mathlib-backed, step 5)

This file isolates the arithmetic core of the cycle-exchange argument:

If we have a tree of total weight `W`, and we consider swapping out an edge of weight `h`
for an off-tree edge of weight `o`, then the new total weight is:

  W' = W - h + o

If `h ≤ o` and `h ≤ W` (so subtraction is exact), then `W ≤ W'`, i.e. the swap cannot
decrease total weight.

This lemma is what connects the path-based certificate bound (which yields `h ≤ o`) to
global “no improving exchange” reasoning.
-/

namespace TauSwap
namespace MST

theorem exchange_weight_no_decrease
    (W h o : Nat)
    (hle : h ≤ o)
    (hW : h ≤ W) :
    W ≤ (W - h) + o := by
  -- Use monotonicity in the second addend and the fact (W - h) + h = W when h ≤ W.
  have : (W - h) + h = W := Nat.sub_add_cancel hW
  -- Since h ≤ o, we have (W - h) + h ≤ (W - h) + o.
  have hmono : (W - h) + h ≤ (W - h) + o := Nat.add_le_add_left hle (W - h)
  -- Rewrite left side using the cancellation equality.
  simpa [this] using hmono

end MST
end TauSwap
