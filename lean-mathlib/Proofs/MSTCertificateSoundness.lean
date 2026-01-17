import Proofs.MSTCertificateBasics

/-!
MST certificate soundness (Mathlib-backed, step 2).

We do not attempt to formalize the entire minimum-spanning-tree theorem here (that is a larger
development), but we *do* mechanize the key inequality that powers the classic exchange argument:

If `T` is a tree, and an off-tree edge `(u,v)` satisfies the certificate bound

  maxWeightOnPath_T(u,v) ≤ w(s(u,v)),

then every edge `e` on the unique `u`-`v` path in `T` has weight bounded by that off-tree edge:

  w(e) ≤ w(s(u,v)).

This is exactly the comparison needed to show that swapping in `(u,v)` and removing any edge on the
cycle cannot reduce total weight.
-/

open scoped Classical

namespace TauSwap
namespace MST

open SimpleGraph

variable {V : Type} [DecidableEq V]

variable (T : SimpleGraph V) (w : Sym2 V → Nat)

theorem le_weight_offTreeEdge_of_mem_path
    (hT : T.IsTree) (u v : V)
    (hcert : maxWeightOnPath (T := T) (w := w) hT u v ≤ w s(u, v))
    {e : Sym2 V}
    (he : e ∈ pathEdges (T := T) (w := w) hT u v) :
    w e ≤ w s(u, v) := by
  have h1 : w e ≤ maxWeightOnPath (T := T) (w := w) hT u v :=
    le_maxWeightOnPath_of_mem (T := T) (w := w) hT (u := u) (v := v) he
  exact Nat.le_trans h1 hcert

end MST
end TauSwap

