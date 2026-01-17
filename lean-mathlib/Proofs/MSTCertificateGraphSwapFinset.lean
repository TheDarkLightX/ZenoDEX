import Proofs.MSTCertificateGraphSwap
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
MST certificate: graph swap → finset swap (Mathlib-backed, step 11)

This is the precise bridge lemma we need:

For a finite tree `T`, removing a specific edge `e` via `deleteEdges {e}` and then adding an edge
`edge u v` corresponds on `edgeFinset` to `insert s(u,v) (erase e T.edgeFinset)`.

This lemma eliminates the last gap between:
- graph-level swap definitions, and
- our finset weight + cardinality lemmas.
-/

open scoped Classical

namespace TauSwap
namespace MST

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V}
variable [Fintype T.edgeSet]

theorem edgeFinset_deleteEdges_singleton
    (e : Sym2 V)
    [Fintype (edgeSet (T.deleteEdges ({e} : Finset (Sym2 V))))] :
    (T.deleteEdges ({e} : Finset (Sym2 V))).edgeFinset = T.edgeFinset.erase e := by
  -- edgeFinset_deleteEdges says: edgeFinset(deleteEdges s) = edgeFinset \ s
  -- For singleton s={e}, `\ {e}` is `erase e`.
  simpa [Finset.sdiff_singleton_eq_erase] using
    (SimpleGraph.edgeFinset_deleteEdges (G := T) (s := ({e} : Finset (Sym2 V))))

theorem edgeFinset_swapEdge_eq_insert_erase
    (e : Sym2 V) (u v : V)
    [Fintype (edgeSet (T.deleteEdges ({e} : Finset (Sym2 V)) ⊔ SimpleGraph.edge u v))]
    (hn : ¬ (T.deleteEdges ({e} : Finset (Sym2 V))).Adj u v)
    (hne : u ≠ v) :
    (TauSwap.MST.swapEdge (T := T) e u v).edgeFinset
      = insert s(u, v) ((T.edgeFinset.erase e)) := by
  -- Unfold swapEdge and use `edgeFinset_sup_edge`.
  unfold TauSwap.MST.swapEdge
  -- Rewrite deleteEdges edgeFinset into erase form, then apply edgeFinset_sup_edge.
  have hdel :
      (T.deleteEdges ({e} : Finset (Sym2 V))).edgeFinset = T.edgeFinset.erase e := by
    simpa using (edgeFinset_deleteEdges_singleton (T := T) e)
  -- Now apply edgeFinset_sup_edge on G := T.deleteEdges {e}
  -- edgeFinset_sup_edge gives `.cons s(u,v)` which simp rewrites to `insert`.
  have hs :
      (T.deleteEdges ({e} : Finset (Sym2 V)) ⊔ SimpleGraph.edge u v).edgeFinset
        = (T.deleteEdges ({e} : Finset (Sym2 V))).edgeFinset.cons s(u, v) (by simp_all) := by
    simpa using (SimpleGraph.edgeFinset_sup_edge (G := T.deleteEdges ({e} : Finset (Sym2 V)))
      (s := u) (t := v) hn hne)
  -- Convert cons into insert and substitute deleteEdges finset.
  -- `cons_eq_insert` is used internally in Mathlib lemma; we can just simp it out.
  simpa [hs, hdel]

end MST
end TauSwap

