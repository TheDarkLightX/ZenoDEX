import Proofs.MSTCertificateExchangeWeight
import Mathlib.Data.Finset.Basic

/-!
MST certificate: edge-set weight algebra (Mathlib-backed, step 7)

This file bridges the gap between the *numeric exchange inequality* and *graph edge sets*.

In the global MST proof, we will repeatedly perform an exchange step that removes one tree-edge and
adds one off-tree edge. At the numeric level, the key inequality is:

  W ≤ (W - h) + o     when h ≤ o and h ≤ W

To lift this to trees/graphs we need facts about `Finset.sum`:

  sum s = sum (s.erase a) + f a   when a ∈ s

and therefore:

  sum s - f a = sum (s.erase a)

This file proves the convenient combined lemma:

  if a ∈ s and f a ≤ o then sum s ≤ sum (s.erase a) + o.
-/

open scoped Classical

namespace TauSwap
namespace MST

theorem sum_le_sum_erase_add_of_mem
    {α : Type} [DecidableEq α]
    (f : α → Nat) (s : Finset α) (a : α)
    (ha : a ∈ s) (o : Nat)
    (hle : f a ≤ o) :
    s.sum f ≤ (s.erase a).sum f + o := by
  -- Let W = sum s f and h = f a.
  have hsum : s.sum f = (s.erase a).sum f + f a := by
    -- standard finset lemma: sum_erase_add (for commutative monoids; Nat works)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Finset.sum_erase_add (s := s) (f := f) ha)

  -- Rewrite goal using hsum, then use monotonicity of addition on the right.
  -- From hle: (eraseSum + f a) ≤ (eraseSum + o).
  have hmono : (s.erase a).sum f + f a ≤ (s.erase a).sum f + o :=
    Nat.add_le_add_left hle ((s.erase a).sum f)

  -- Replace LHS with eraseSum + f a
  simpa [hsum] using hmono

end MST
end TauSwap

