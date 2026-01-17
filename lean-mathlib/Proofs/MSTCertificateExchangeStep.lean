import Proofs.MSTCertificateSoundness

/-!
MST certificate: exchange step (Mathlib-backed, step 3)

This file strengthens the previous soundness lemma by *extracting* an edge on the unique tree path
whose weight is exactly the path maximum, and therefore is bounded by the off-tree edge weight when
the certificate inequality holds.

This is the key “cycle exchange” ingredient:
- Adding an off-tree edge `(u,v)` to a tree creates a unique cycle consisting of that edge plus the
  unique path from `u` to `v` in the tree.
- Removing the heaviest edge on that cycle yields a spanning tree of no greater total weight.

We do not yet formalize the graph operation / cycle construction here; we mechanize the extracted
heaviest-edge fact that supports that argument.
-/

open scoped Classical

namespace TauSwap
namespace MST

open SimpleGraph

variable {V : Type}

/- List lemma: a nonempty list has an element equal to `foldr Nat.max 0`. -/
theorem exists_mem_eq_foldr_max_of_ne_nil (xs : List Nat) (hne : xs ≠ []) :
    ∃ x, x ∈ xs ∧ xs.foldr Nat.max 0 = x := by
  induction xs with
  | nil =>
    cases (hne rfl)
  | cons a tl ih =>
    by_cases htl : tl = []
    · subst htl
      -- foldr max 0 [a] = max a 0 = a
      refine ⟨a, ?_, ?_⟩
      · simp
      · simp
    · -- tl nonempty: pick max element in tl, then compare with a
      have hne_tl : tl ≠ [] := htl
      obtain ⟨m, hm_mem, hm_eq⟩ := ih hne_tl
      -- foldr max 0 (a :: tl) = max a (foldr max 0 tl)
      have : (a :: tl).foldr Nat.max 0 = Nat.max a (tl.foldr Nat.max 0) := by
        simp
      -- Decide whether max is a or comes from tail
      by_cases ha : (tl.foldr Nat.max 0) ≤ a
      · -- max a tail = a
        refine ⟨a, ?_, ?_⟩
        · simp
        · -- use ha to rewrite max
          simp [this, Nat.max_eq_left ha]
      · -- max a tail = tail
        have ha' : a ≤ tl.foldr Nat.max 0 := Nat.le_of_not_ge ha
        refine ⟨m, ?_, ?_⟩
        · simp [hm_mem]
        · -- max a tail = tail, and tail max equals m
          calc
            (a :: tl).foldr Nat.max 0
                = Nat.max a (tl.foldr Nat.max 0) := by simp
            _   = tl.foldr Nat.max 0 := by simp [Nat.max_eq_right ha']
            _   = m := by simpa [hm_eq]


/- Extract a heaviest edge on the unique `u-v` path in a tree, and bound it via the certificate. -/
theorem exists_heaviest_edge_on_path_le_offEdge
    (T : SimpleGraph V) (w : Sym2 V → Nat)
    (hT : T.IsTree) (u v : V)
    (hne : pathEdges (T := T) (w := w) hT u v ≠ [])
    (hcert : maxWeightOnPath (T := T) (w := w) hT u v ≤ w s(u, v)) :
    ∃ e : Sym2 V,
      e ∈ pathEdges (T := T) (w := w) hT u v ∧
      w e = maxWeightOnPath (T := T) (w := w) hT u v ∧
      w e ≤ w s(u, v) := by
  -- Work on the mapped weight list.
  have hneW : ((pathEdges (T := T) (w := w) hT u v).map w) ≠ [] := by
    intro hnil
    -- If map is empty, original is empty.
    exact hne (List.map_eq_nil.mp hnil)

  obtain ⟨x, hx_mem, hx_eq⟩ :=
    exists_mem_eq_foldr_max_of_ne_nil ((pathEdges (T := T) (w := w) hT u v).map w) hneW

  -- Pull back `x` to an actual edge `e` on the path with `w e = x`.
  have : ∃ e, e ∈ pathEdges (T := T) (w := w) hT u v ∧ w e = x := by
    -- membership in a map gives a preimage
    simpa [List.mem_map] using hx_mem

  obtain ⟨e, he_mem, he_w⟩ := this

  refine ⟨e, he_mem, ?_, ?_⟩
  · -- w e = maxWeightOnPath
    unfold maxWeightOnPath
    -- foldr on weights list equals x, and w e = x
    simpa [he_w] using congrArg (fun t => t) hx_eq
  · -- w e ≤ w off-edge
    have hwe_le_max : w e ≤ maxWeightOnPath (T := T) (w := w) hT u v :=
      le_maxWeightOnPath_of_mem (T := T) (w := w) hT (u := u) (v := v) he_mem
    exact Nat.le_trans hwe_le_max hcert

end MST
end TauSwap

