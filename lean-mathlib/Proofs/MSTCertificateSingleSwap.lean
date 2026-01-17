import Proofs.MSTCertificateNoImprovingExchange
import Proofs.MSTCertificateEdgeWeightSum
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
MST certificate: single-swap weight inequality (Mathlib-backed, step 8)

This file proves the “one exchange step” weight inequality at the level of finite edge sets:

Given:
- a finite tree `T`,
- an off-tree edge `uv` (present in `G` but not in `T`),
- the certificate bound `maxWeightOnPath_T(u,v) ≤ w(uv)`,

then removing the (extracted) heaviest edge `e` on the `u-v` path and inserting `uv`
does not decrease the total weight of the edge multiset.

We prove this purely as a `Finset` inequality on edge sets; later we connect this to a graph-level
exchange construction.
-/

open scoped Classical

namespace TauSwap
namespace MST

open SimpleGraph

variable {V : Type} [DecidableEq V]
variable (G T : SimpleGraph V) (w : Sym2 V → Nat)

section
  variable [Fintype T.edgeSet]

  /-- Total weight of a finite graph's edge set. -/
  def weightEdges : Nat :=
    T.edgeFinset.sum w

  theorem weightEdges_eq_sum : weightEdges (T := T) w = T.edgeFinset.sum w := by
    rfl

  /--
  Core single-step inequality on finsets:

  If `e ∈ T.edgeFinset` and `w e ≤ w uv`, then
    sum(T) ≤ sum(T.erase e) + w uv = sum(insert uv (erase e))
  (when `uv ∉ T.edgeFinset`).
  -/
  theorem weight_single_erase_then_add
      (uv e : Sym2 V)
      (he : e ∈ T.edgeFinset)
      (huv : uv ∉ T.edgeFinset)
      (hle : w e ≤ w uv) :
      T.edgeFinset.sum w ≤ (insert uv (T.edgeFinset.erase e)).sum w := by
    -- First: sum ≤ sum(erase e)+w uv
    have h1 : T.edgeFinset.sum w ≤ (T.edgeFinset.erase e).sum w + w uv :=
      sum_le_sum_erase_add_of_mem (f := w) (s := T.edgeFinset) (a := e) he (o := w uv) hle
    -- Second: since uv ∉ edgeFinset and erase only removes, uv ∉ erase
    have huv2 : uv ∉ T.edgeFinset.erase e := by
      intro hmem
      have : uv ∈ T.edgeFinset := by
        exact Finset.mem_of_mem_erase hmem
      exact huv this
    -- Rewrite RHS using sum_insert
    have hsum : (insert uv (T.edgeFinset.erase e)).sum w = (T.edgeFinset.erase e).sum w + w uv := by
      simpa [Finset.sum_insert, huv2, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    -- Combine
    simpa [hsum] using h1

end

end MST
end TauSwap

