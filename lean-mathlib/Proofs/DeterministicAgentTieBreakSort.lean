import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max

/-!
Deterministic agent tie-break (Mathlib-backed): "sort then pick first" is min'.

This is the cleanest ∀-theorem to align hybrid Rust/Tau implementations:

- Rust can deterministically compute the winner by sorting candidates by a total key and taking the
  first element.
- Tau can deterministically verify by checking the winner is the `Finset.min'` under that same key.

Mathlib already proves:

  s.min' h = s.sort[0]

We re-export that statement in a reusable form.
-/

open scoped Classical

namespace TauSwap
namespace Agent

variable {α : Type} [LinearOrder α]

theorem min'_eq_sorted0 (s : Finset α) (h : s.Nonempty) :
    s.min' h = s.sort[0]'(by
      -- length_sort = card, and card_pos from nonempty
      simpa [Finset.length_sort] using (Finset.card_pos.2 h)) := by
  -- Directly from Mathlib: `Finset.min'_eq_sorted_zero`
  simpa using (Finset.min'_eq_sorted_zero (s := s) (h := h))

theorem sorted0_eq_min' (s : Finset α) (h : 0 < s.sort.length) :
    s.sort[0] = s.min' (Finset.card_pos.1 (by
      -- length_sort = card
      simpa [Finset.length_sort] using h)) := by
  -- Directly from Mathlib: `Finset.sorted_zero_eq_min'`
  simpa using (Finset.sorted_zero_eq_min' (s := s) (h := h))

end Agent
end TauSwap

