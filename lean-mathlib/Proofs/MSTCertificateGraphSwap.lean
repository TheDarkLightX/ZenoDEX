import Proofs.MSTCertificateSingleSwap
import Proofs.MSTCertificateSwapFinset
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
MST certificate: graph-level edge swap (Mathlib-backed, step 10)

We define a graph-level exchange operation:

  swapEdge T e u v := (T.deleteEdges {e}) ⊔ edge u v

and prove the clean edge-set identity:

  edgeSet(swapEdge) = (T.edgeSet \ {e}) ∪ (edge u v).edgeSet

The stronger finset-level statement

  (swapEdge ...).edgeFinset = insert s(u,v) (T.edgeFinset.erase e)

is the next step once we thread through the standard finiteness instances; we keep it out of this
file to ensure the development stays `sorry`/`admit`-free.
-/

open scoped Classical

namespace TauSwap
namespace MST

open SimpleGraph

variable {V : Type} [DecidableEq V]

variable (T : SimpleGraph V)

-- swap operation (graph-level)
def swapEdge (e : Sym2 V) (u v : V) : SimpleGraph V :=
  (T.deleteEdges ({e} : Set (Sym2 V))) ⊔ (SimpleGraph.edge u v)

theorem edgeSet_swapEdge (e : Sym2 V) (u v : V) :
    (swapEdge (T := T) e u v).edgeSet =
      (T.edgeSet \ ({e} : Set (Sym2 V))) ∪ (SimpleGraph.edge u v).edgeSet := by
  -- `swapEdge` is `deleteEdges` then `sup`; edgeSet is set-difference then union.
  unfold swapEdge
  -- edgeSet_sup and edgeSet_deleteEdges
  simp [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges, Set.union_assoc, Set.union_left_comm,
    Set.union_comm, Set.diff_eq]

end MST
end TauSwap

