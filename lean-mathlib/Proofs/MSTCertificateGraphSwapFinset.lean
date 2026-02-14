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
    [Fintype (edgeSet (T.deleteEdges ({e} : Set (Sym2 V)) ⊔ SimpleGraph.edge u v))]
    (hn : ¬ (T.deleteEdges ({e} : Set (Sym2 V))).Adj u v)
    (hne : u ≠ v) :
    (TauSwap.MST.swapEdge (T := T) e u v).edgeFinset
      = insert s(u, v) ((T.edgeFinset.erase e)) := by
  have hdel :
      (T.deleteEdges ({e} : Set (Sym2 V))).edgeFinset = T.edgeFinset.erase e := by
    ext x
    simp [SimpleGraph.edgeSet_deleteEdges, and_left_comm, and_assoc, and_comm]
  have hs :
      (TauSwap.MST.swapEdge (T := T) e u v).edgeFinset =
        insert s(u, v) ((T.deleteEdges ({e} : Set (Sym2 V))).edgeFinset) := by
    unfold TauSwap.MST.swapEdge
    simpa using (SimpleGraph.edgeFinset_sup_edge (G := T.deleteEdges ({e} : Set (Sym2 V)))
      (s := u) (t := v) hn hne)
  calc
    (TauSwap.MST.swapEdge (T := T) e u v).edgeFinset
        = insert s(u, v) ((T.deleteEdges ({e} : Set (Sym2 V))).edgeFinset) := hs
    _ = insert s(u, v) (T.edgeFinset.erase e) := by simpa [hdel]

end MST
end TauSwap
