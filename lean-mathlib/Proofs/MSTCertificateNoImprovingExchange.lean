import Proofs.MSTCertificateExchangeStep

/-!
MST certificate: "no improving exchange" statement (Mathlib-backed, step 4).

This file states the certificate consequence in the form most directly aligned with the classic
cycle/exchange argument:

Given a tree `T` and an off-tree edge `(u,v)`, if the certificate inequality holds

  maxWeightOnPath_T(u,v) ≤ w(s(u,v)),

then **every** edge on the unique `u-v` tree path has weight ≤ the off-tree edge weight.

In other words, swapping in `(u,v)` and removing any edge on that cycle cannot decrease total
weight because the added edge is never lighter than the removed edge.

This is the strongest "local" theorem needed before formalizing the actual graph-edge swap
operation and total-weight accounting.
-/

open scoped Classical

namespace TauSwap
namespace MST

open SimpleGraph

variable {V : Type}

variable (T : SimpleGraph V) (w : Sym2 V → Nat)

theorem no_improving_exchange_along_path
    (hT : T.IsTree) (u v : V)
    (hcert : maxWeightOnPath (T := T) (w := w) hT u v ≤ w s(u, v))
    {e : Sym2 V}
    (he : e ∈ pathEdges (T := T) (w := w) hT u v) :
    w e ≤ w s(u, v) :=
  le_weight_offTreeEdge_of_mem_path (T := T) (w := w) hT u v hcert he

theorem exists_exchange_edge_with_max_weight
    (hT : T.IsTree) (u v : V)
    (hne : pathEdges (T := T) (w := w) hT u v ≠ [])
    (hcert : maxWeightOnPath (T := T) (w := w) hT u v ≤ w s(u, v)) :
    ∃ e : Sym2 V,
      e ∈ pathEdges (T := T) (w := w) hT u v ∧
      w e = maxWeightOnPath (T := T) (w := w) hT u v ∧
      w e ≤ w s(u, v) :=
  exists_heaviest_edge_on_path_le_offEdge (T := T) (w := w) hT u v hne hcert

end MST
end TauSwap

