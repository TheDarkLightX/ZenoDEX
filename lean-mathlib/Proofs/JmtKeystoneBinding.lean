import Mathlib

/-!
# JMT keystone — root determinism (Mathlib-backed companion to JmtKeystoneSafety)

Mechanizes the determinism property of the compact sparse-Merkle root: the root is
invariant under reordering the same leaf multiset
(`src/state/jmt.py::_subtree_root` is a pure recursive fold over the supplied leaves;
`build_leaves` additionally sorts). This is the order-independence the Python
insertion-order-shuffle tests check, proven here as a `List.Perm` invariance — the
deferred-from-Init-only result that Mathlib's permutation lemmas make tractable.

Model-level (same caveat as `JmtKeystoneSafety`): `rootAux` is hand-transcribed from the
Python recursion; binding model⇔artifact is J4 (Rust parity). The child combiner
`combine` (think `internal_hash`) and bit-selector `bit` (think `_bit`) are abstract, so
determinism holds for *any* deterministic instantiation.
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

end ZenoDex.JmtKeystone.Binding
