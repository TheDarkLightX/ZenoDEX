import Mathlib.Tactic

/-!
# Deterministic Epoch Window Mapping

For set-and-forget deterministic agents, a common pattern is:

- choose a fixed positive window size `w`,
- map timestamp/step `t` to epoch `t / w`,
- execute a single policy branch per epoch window.

This file proves the key arithmetic facts behind that mapping.
-/

namespace Proofs
namespace DeterministicEpochWindow

def epochOf (t window : Nat) : Nat :=
  t / window

theorem epoch_of_in_window {t k window : Nat}
    (hwin : 0 < window)
    (hlo : k * window ≤ t)
    (hhi : t < (k + 1) * window) :
    epochOf t window = k := by
  unfold epochOf
  have hk_le : k ≤ t / window := by
    exact (Nat.le_div_iff_mul_le hwin).2 (by simpa [Nat.mul_comm] using hlo)
  have hdiv_lt : t / window < k + 1 := by
    exact (Nat.div_lt_iff_lt_mul hwin).2 (by
      simpa [Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hhi)
  have hdiv_le : t / window ≤ k := Nat.lt_succ_iff.mp hdiv_lt
  exact le_antisymm hdiv_le hk_le

theorem epoch_window_unique {t k1 k2 window : Nat}
    (hwin : 0 < window)
    (h1lo : k1 * window ≤ t)
    (h1hi : t < (k1 + 1) * window)
    (h2lo : k2 * window ≤ t)
    (h2hi : t < (k2 + 1) * window) :
    k1 = k2 := by
  have hk1 : epochOf t window = k1 := epoch_of_in_window hwin h1lo h1hi
  have hk2 : epochOf t window = k2 := epoch_of_in_window hwin h2lo h2hi
  simpa [hk1] using hk2

end DeterministicEpochWindow
end Proofs

