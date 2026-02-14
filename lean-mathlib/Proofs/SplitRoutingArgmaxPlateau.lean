/-!
Split-routing argmax plateau lemmas (manual research tie-in).

These lemmas capture the core structural insight from manual experiments:

- The objective over split index can have a wide argmax plateau.
- If a candidate index lands inside that plateau, it is globally optimal.
- The left edge of the plateau is the canonical deterministic tie-break winner.

This is intentionally arithmetic/lightweight so it can be reused as a local proof
obligation for dense-probe split selectors.
-/

namespace Proofs
namespace SplitRouting

/-- If an index is globally optimal on `[lo, hi]`, and values outside `[pLo, pHi]`
are strictly below `best`, then the index must lie inside `[pLo, pHi]`. -/
theorem optimal_index_mem_plateau
    (f : Nat → Nat)
    (lo hi pLo pHi best a : Nat)
    (h_left : ∀ x, lo ≤ x → x < pLo → f x < best)
    (h_right : ∀ x, pHi < x → x ≤ hi → f x < best)
    (h_opt : lo ≤ a ∧ a ≤ hi ∧ f a = best) :
    pLo ≤ a ∧ a ≤ pHi := by
  have h_a_lo : lo ≤ a := h_opt.1
  have h_a_hi : a ≤ hi := h_opt.2.1
  have h_a_best : f a = best := h_opt.2.2

  have h_lo : pLo ≤ a := by
    have hcmp : a < pLo ∨ pLo ≤ a := Nat.lt_or_ge a pLo
    cases hcmp with
    | inl hlt =>
        have hlt_best : f a < best := h_left a h_a_lo hlt
        exact False.elim ((Nat.lt_irrefl best) (by simpa [h_a_best] using hlt_best))
    | inr hge =>
        exact hge

  have h_hi : a ≤ pHi := by
    have hcmp : pHi < a ∨ a ≤ pHi := Nat.lt_or_ge pHi a
    cases hcmp with
    | inl hgt =>
        have hgt_best : f a < best := h_right a hgt h_a_hi
        exact False.elim ((Nat.lt_irrefl best) (by simpa [h_a_best] using hgt_best))
    | inr hle =>
        exact hle

  exact ⟨h_lo, h_hi⟩

/-- Canonical tie-break property: under a contiguous argmax plateau,
the left edge `pLo` is the smallest optimal index on `[lo, hi]`. -/
theorem plateau_left_edge_is_smallest_optimal
    (f : Nat → Nat)
    (lo hi pLo pHi best : Nat)
    (h_bounds : lo ≤ pLo ∧ pLo ≤ pHi ∧ pHi ≤ hi)
    (h_plateau : ∀ x, pLo ≤ x → x ≤ pHi → f x = best)
    (h_left : ∀ x, lo ≤ x → x < pLo → f x < best)
    (h_right : ∀ x, pHi < x → x ≤ hi → f x < best) :
    (f pLo = best) ∧
      (∀ a, lo ≤ a → a ≤ hi → f a = best → pLo ≤ a) := by
  have h_pLo_best : f pLo = best := h_plateau pLo (Nat.le_refl pLo) h_bounds.2.1
  refine ⟨h_pLo_best, ?_⟩
  intro a h_a_lo h_a_hi h_a_best
  exact (optimal_index_mem_plateau
    f lo hi pLo pHi best a
    h_left h_right
    ⟨h_a_lo, h_a_hi, h_a_best⟩).1

/-- Any selected index inside the argmax plateau has zero objective gap to `best`. -/
theorem zero_gap_if_selected_in_plateau
    (f : Nat → Nat)
    (pLo pHi best aSel : Nat)
    (h_plateau : ∀ x, pLo ≤ x → x ≤ pHi → f x = best)
    (h_sel : pLo ≤ aSel ∧ aSel ≤ pHi) :
    best - f aSel = 0 := by
  have h_eq : f aSel = best := h_plateau aSel h_sel.1 h_sel.2
  simpa [h_eq]

end SplitRouting
end Proofs
