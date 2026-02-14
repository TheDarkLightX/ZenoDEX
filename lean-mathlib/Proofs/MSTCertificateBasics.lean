import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Walks.Traversal
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
MST certificate, Mathlib-backed foundations (step 1).

This file sets up the *Mathlib-level* machinery we need to mechanize the MST
certificate used by our MST checker domain:

> For a spanning tree `T`, and any non-tree edge `e=(u,v,w)`, let `P(u,v)` be the
> unique simple path in `T` from `u` to `v`. Then `T` is an MST if every such
> `e` satisfies `maxWeight(P(u,v)) ≤ w`.

Full MST soundness is a larger development; here we mechanize the key ingredients:
- Trees have unique simple paths (Mathlib provides this).
- We define `maxWeightOnPath` using that unique path and list maximum.
 -/

open scoped Classical

namespace TauSwap
namespace MST

open SimpleGraph

variable {V : Type} (T : SimpleGraph V)

/- Mathlib theorem (already proved): trees have unique simple paths. -/
theorem existsUnique_path (hT : T.IsTree) (u v : V) :
    ∃! p : T.Walk u v, p.IsPath :=
  SimpleGraph.IsTree.existsUnique_path hT u v

/- A weight function on undirected edges. -/
variable (w : Sym2 V → Nat)

/- The (noncomputable) unique simple path in a tree. -/
noncomputable def uniqPath (hT : T.IsTree) (u v : V) : T.Walk u v :=
  Classical.choose (existsUnique_path (T := T) hT u v)

theorem uniqPath_isPath (hT : T.IsTree) (u v : V) :
    (uniqPath (T := T) hT u v).IsPath :=
  (Classical.choose_spec (existsUnique_path (T := T) hT u v)).1

/- The list of undirected edges on the unique path. -/
noncomputable def pathEdges (hT : T.IsTree) (u v : V) : List (Sym2 V) :=
  (uniqPath (T := T) hT u v).edges

/- Max edge-weight along the unique path (0 if the path has no edges, i.e. u=v). -/
noncomputable def maxWeightOnPath (hT : T.IsTree) (u v : V) : Nat :=
  ((pathEdges (T := T) hT u v).map w).foldr Nat.max 0

lemma le_foldr_max_of_mem {x : Nat} {xs : List Nat} (hx : x ∈ xs) :
    x ≤ xs.foldr Nat.max 0 := by
  induction xs with
  | nil =>
    cases hx
  | cons a xs ih =>
    simp at hx
    rcases hx with rfl | htail
    · exact Nat.le_max_left _ _
    · exact (ih htail).trans (Nat.le_max_right _ _)

/- Basic lemma: any edge weight on the path is ≤ maxWeightOnPath. -/
theorem le_maxWeightOnPath_of_mem
    (hT : T.IsTree) {u v : V} {e : Sym2 V}
    (he : e ∈ pathEdges (T := T) hT u v) :
    w e ≤ maxWeightOnPath (T := T) (w := w) hT u v := by
  -- unfold definitions to a list maximum statement
  unfold maxWeightOnPath pathEdges
  -- Reduce to: for any x in (map w edges), x ≤ foldr max 0 (map w edges).
  have : w e ∈ ((uniqPath (T := T) hT u v).edges.map w) := by
    simpa [List.mem_map] using ⟨e, he, rfl⟩
  exact le_foldr_max_of_mem this

/- In a tree, the unique path between distinct vertices is non-nil, hence has at least one edge. -/
theorem pathEdges_ne_nil_of_ne
    (hT : T.IsTree) {u v : V} (hne : u ≠ v) :
    pathEdges (T := T) hT u v ≠ [] := by
  -- `uniqPath` is a walk u→v. If u≠v it cannot be Nil, hence edges list is nonempty.
  have hnotNil : ¬ (uniqPath (T := T) hT u v).Nil :=
    SimpleGraph.Walk.not_nil_of_ne (v := u) (w := v) (p := uniqPath (T := T) hT u v) hne
  -- edges_eq_nil ↔ Nil
  have : ¬ (uniqPath (T := T) hT u v).edges = [] := by
    intro hedges
    have hNil : (uniqPath (T := T) hT u v).Nil := (SimpleGraph.Walk.edges_eq_nil).1 hedges
    exact hnotNil hNil
  -- unfold pathEdges
  unfold pathEdges
  exact this

/- Any edge on the unique tree path is an edge of the tree. -/
theorem mem_edgeSet_of_mem_pathEdges
    (hT : T.IsTree) {u v : V} {e : Sym2 V}
    (he : e ∈ pathEdges (T := T) hT u v) :
    e ∈ T.edgeSet := by
  -- `pathEdges` is `edges` of the unique walk in `T`; `edges_subset_edgeSet` gives membership.
  unfold pathEdges at he
  exact (SimpleGraph.Walk.edges_subset_edgeSet (G := T) (p := uniqPath (T := T) hT u v) he)

/- Finite version: path edge membership implies membership in `edgeFinset`. -/
theorem mem_edgeFinset_of_mem_pathEdges
    [Fintype T.edgeSet]
    (hT : T.IsTree) {u v : V} {e : Sym2 V}
    (he : e ∈ pathEdges (T := T) hT u v) :
    e ∈ T.edgeFinset := by
  -- `mem_edgeFinset ↔ mem_edgeSet`
  exact (SimpleGraph.mem_edgeFinset (G := T) (e := e)).2 (mem_edgeSet_of_mem_pathEdges (T := T) hT he)

end MST
end TauSwap
