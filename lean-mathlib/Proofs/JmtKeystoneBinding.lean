import Mathlib

/-!
# JMT keystone — model-level root determinism

Mechanizes the determinism property expected from the planned canonical
multi-lane root: the modeled compact sparse-Merkle root is invariant under
reordering the same leaf multiset. This is the order-independence obligation
that a future implementation must bind to live code; the current repo has no
`src/state/jmt.py` artifact.

Model-level boundary: `rootAux` is an abstract tree model for the
Jellyfish-style root described in `docs/product_discipline/technical_reference_patterns.md`.
The child combiner `combine` and bit-selector `bit` are abstract, so determinism
holds for any deterministic instantiation. A production claim still needs a
live implementation binding, key/hash canonicalization, and concrete hash
collision assumptions.
-/

namespace ZenoDex.JmtKeystone.Binding

abbrev Byte := Nat
abbrev Hash := List Byte

/-- Empty-subtree sentinel (`PLACEHOLDER = b"\x00" * 32`). -/
def PLACEHOLDER : Hash := List.replicate 32 0

/-- Compact-tree root over `(key, leafHash)` leaves: empty → `PLACEHOLDER`, singleton →
its hash, else split by `bit key depth` into the two child subtrees and `combine`. `fuel`
bounds the depth. Mirrors `_subtree_root`. -/
def rootAux (combine : Hash → Hash → Hash) (bit : List Byte → Nat → Bool) :
    Nat → Nat → List (List Byte × Hash) → Hash
  | _, _, [] => PLACEHOLDER
  | _, _, [(_, h)] => h
  | depth, fuel + 1, (p0 :: p1 :: rest) =>
      combine
        (rootAux combine bit (depth + 1) fuel
          ((p0 :: p1 :: rest).filter (fun p => !bit p.1 depth)))
        (rootAux combine bit (depth + 1) fuel
          ((p0 :: p1 :: rest).filter (fun p => bit p.1 depth)))
  | _, 0, (_ :: _ :: _) => PLACEHOLDER

/-- **Determinism: the root is invariant under permutation of the leaf list.**
This proves order-independence for the same leaf multiset. A set-extensional
statement still needs the usual no-duplicate-key precondition. -/
theorem rootAux_perm (combine : Hash → Hash → Hash) (bit : List Byte → Nat → Bool) :
    ∀ (fuel depth : Nat) {l1 l2 : List (List Byte × Hash)},
      l1.Perm l2 → rootAux combine bit depth fuel l1 = rootAux combine bit depth fuel l2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro depth l1 l2 hp
    -- At fuel 0 the result depends only on the length category (0 / 1 / ≥2),
    -- which `Perm` preserves.
    match l1, l2 with
    | [], [] => rfl
    | [], _ :: _ =>
        have hlen := hp.length_eq
        simp at hlen
    | _ :: _, [] =>
        have hlen := hp.length_eq
        simp at hlen
    | [a], [b] =>
        cases List.perm_singleton.mp hp
        rfl
    | [_], _ :: _ :: _ =>
        have hlen := hp.length_eq
        simp at hlen
    | _ :: _ :: _, [_] =>
        have hlen := hp.length_eq
        simp at hlen
    | _ :: _ :: _, _ :: _ :: _ => rfl
  | succ fuel ih =>
    intro depth l1 l2 hp
    match l1, l2 with
    | [], [] => rfl
    | [], _ :: _ =>
        have hlen := hp.length_eq
        simp at hlen
    | _ :: _, [] =>
        have hlen := hp.length_eq
        simp at hlen
    | [a], [b] =>
      cases List.perm_singleton.mp hp
      rfl
    | [_], _ :: _ :: _ =>
        have hlen := hp.length_eq
        simp at hlen
    | _ :: _ :: _, [_] =>
        have hlen := hp.length_eq
        simp at hlen
    | a :: b :: l1', c :: d :: l2' =>
      simp only [rootAux]
      have hf : (a :: b :: l1').Perm (c :: d :: l2') := hp
      rw [ih (depth + 1) (hf.filter (fun p => !bit p.1 depth)),
          ih (depth + 1) (hf.filter (fun p => bit p.1 depth))]

/-- **Binding — inductive step (idealized injective combiner).** Under an injective
child-combiner assumption, equal roots of two ≥2-leaf trees force the two child
subtree roots to be equal. Concrete SHA-256 binding is outside this theorem; this
is the algebraic lift point that a hash-collision argument can discharge for a
real combiner. Remaining J5b work: combine this step with leaf-hash injectivity
and `PLACEHOLDER` distinctness to get full root uniqueness. -/
theorem rootAux_children_eq_of_injective2
    (combine : Hash → Hash → Hash) (bit : List Byte → Nat → Bool)
    (hc : Function.Injective2 combine) (depth fuel : Nat)
    {l1 l2 : List (List Byte × Hash)} (h1 : 2 ≤ l1.length) (h2 : 2 ≤ l2.length)
    (h : rootAux combine bit depth (fuel + 1) l1 = rootAux combine bit depth (fuel + 1) l2) :
    rootAux combine bit (depth + 1) fuel (l1.filter (fun p => !bit p.1 depth))
        = rootAux combine bit (depth + 1) fuel (l2.filter (fun p => !bit p.1 depth))
      ∧ rootAux combine bit (depth + 1) fuel (l1.filter (fun p => bit p.1 depth))
        = rootAux combine bit (depth + 1) fuel (l2.filter (fun p => bit p.1 depth)) := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, l1 = a :: b :: rest := by
    rcases l1 with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at h1
    · simp at h1
    · exact ⟨a, b, rest, rfl⟩
  obtain ⟨c, d, rest2, rfl⟩ : ∃ c d rest2, l2 = c :: d :: rest2 := by
    rcases l2 with _ | ⟨c, _ | ⟨d, rest2⟩⟩
    · simp at h2
    · simp at h2
    · exact ⟨c, d, rest2, rfl⟩
  simp only [rootAux] at h
  exact hc h

/-- Negative witness for the remaining `PLACEHOLDER` distinctness obligation:
if a leaf hash equals the empty-subtree sentinel, a singleton tree is
indistinguishable from the empty tree in this abstract model. -/
theorem rootAux_single_placeholder_eq_empty
    (combine : Hash → Hash → Hash) (bit : List Byte → Nat → Bool)
    (depth fuel : Nat) (key : List Byte) :
    rootAux combine bit depth fuel [(key, PLACEHOLDER)] =
      rootAux combine bit depth fuel [] := by
  simp [rootAux]

/-- Partition reconstruction: a list is a permutation of its `!q`-filter followed by its
`q`-filter (the bit-partition decomposition the root-uniqueness lift recombines). -/
theorem filter_not_append_filter_perm {α : Type} (q : α → Bool) :
    ∀ l : List α, l.Perm (l.filter (fun x => !q x) ++ l.filter q)
  | [] => by simp
  | x :: xs => by
    have ih := filter_not_append_filter_perm q xs
    cases hq : q x with
    | false =>
      simp only [List.filter_cons, hq, Bool.not_false, if_true, if_false, List.cons_append,
        Bool.false_eq_true]
      exact ih.cons x
    | true =>
      simp only [List.filter_cons, hq, Bool.not_true, if_true]
      exact (ih.cons x).trans List.perm_middle.symm

/-- **Recombination step of the root-uniqueness lift.** If the two bit-partition halves of
`l1` and `l2` are pairwise permutations, then `l1` and `l2` are permutations. Combined with
`rootAux_children_eq_of_injective2` (which extracts equal child roots) and an induction on
`fuel`, this is the parent half of full root-uniqueness; the remaining J5b pieces are the
base-case sentinel/leaf/internal distinctness (cf. `rootAux_single_placeholder_eq_empty`,
which shows it is genuinely needed) and the leaf-hash↔key binding
(a future `encode_injective` obligation for the live key/value encoding). -/
theorem perm_of_filter_perms {α : Type} (q : α → Bool) {l1 l2 : List α}
    (hnot : (l1.filter (fun x => !q x)).Perm (l2.filter (fun x => !q x)))
    (hyes : (l1.filter q).Perm (l2.filter q)) : l1.Perm l2 :=
  (filter_not_append_filter_perm q l1).trans
    ((hnot.append hyes).trans (filter_not_append_filter_perm q l2).symm)

end ZenoDex.JmtKeystone.Binding
