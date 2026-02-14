import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Volatility Tracker Arithmetic Bounds

Small arithmetic obligations used by the volatility tracker family:

1. Raw score is always nonnegative.
2. Clamped score is always in `[0, 10000]`.
3. Absolute price delta is nonnegative.
-/

namespace Proofs
namespace VolatilityTrackerArithmetic

def absDelta (newPrice lastPrice : Nat) : Nat :=
  if newPrice ≥ lastPrice then newPrice - lastPrice else lastPrice - newPrice

def rawScore (historySum historyCount newPrice : Nat) : Nat :=
  (historySum * 10000) / ((max historyCount 1) * newPrice)

def clamp10000 (v : Nat) : Nat :=
  min v 10000

theorem abs_delta_nonneg (newPrice lastPrice : Nat) :
    0 ≤ absDelta newPrice lastPrice := by
  unfold absDelta
  split <;> omega

theorem raw_score_nonneg (historySum historyCount newPrice : Nat) :
    0 ≤ rawScore historySum historyCount newPrice := by
  exact Nat.zero_le _

theorem clamp10000_le (v : Nat) :
    clamp10000 v ≤ 10000 := by
  unfold clamp10000
  exact min_le_right v 10000

theorem clamp10000_nonneg (v : Nat) :
    0 ≤ clamp10000 v := by
  exact Nat.zero_le _

theorem clamp10000_in_range (v : Nat) :
    0 ≤ clamp10000 v ∧ clamp10000 v ≤ 10000 := by
  constructor
  · exact clamp10000_nonneg v
  · exact clamp10000_le v

end VolatilityTrackerArithmetic
end Proofs
