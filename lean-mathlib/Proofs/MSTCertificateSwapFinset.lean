import Proofs.MSTCertificateBasics
import Mathlib.Data.Finset.Card

/-!
MST certificate: finset swap combinatorics (Mathlib-backed, helper)

This file proves basic combinatorics facts about the “erase then insert” finset operation
that represents a one-edge exchange:

  S' = insert uv (S.erase e)

We use these facts when connecting edge-set swaps to the `IsTree` edge-count condition
and to the weight sum inequality.
-/

namespace TauSwap
namespace MST

open scoped Classical

theorem card_insert_erase_eq
    {α : Type} [DecidableEq α]
    (S : Finset α) (e uv : α)
    (he : e ∈ S) (huv : uv ∉ S) :
    (insert uv (S.erase e)).card = S.card := by
  -- erase removes exactly one element
  have hcard_erase : (S.erase e).card = S.card - 1 := Finset.card_erase_of_mem he
  -- uv is not in S, hence also not in erase
  have huv2 : uv ∉ S.erase e := by
    intro h
    have : uv ∈ S := Finset.mem_of_mem_erase h
    exact huv this
  -- insert adds exactly one element
  have hcard_ins : (insert uv (S.erase e)).card = (S.erase e).card + 1 := Finset.card_insert_of_not_mem huv2
  -- combine
  -- (S.card - 1) + 1 = S.card
  simpa [hcard_erase, hcard_ins, Nat.sub_add_cancel (Nat.succ_le_iff.1 (Nat.pos_of_mem he))]

end MST
end TauSwap

