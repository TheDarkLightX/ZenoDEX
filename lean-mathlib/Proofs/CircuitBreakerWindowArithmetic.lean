import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Circuit Breaker Window Arithmetic

Arithmetic helpers for the reference circuit-breaker model:

1. `volumeAfter` is always nonnegative.
2. Window-expired branch is exactly `volume`.
3. Active-window branch is exactly `accum + volume`.
4. Breach predicate is monotone in `maxVolume`.
-/

namespace Proofs
namespace CircuitBreakerWindowArithmetic

def volumeAfter (expired : Bool) (accum volume : Nat) : Nat :=
  if expired then volume else accum + volume

def isBreached (expired : Bool) (accum volume maxVolume : Nat) : Bool :=
  decide (volumeAfter expired accum volume ≥ maxVolume)

theorem volume_after_nonneg (expired : Bool) (accum volume : Nat) :
    0 ≤ volumeAfter expired accum volume := by
  unfold volumeAfter
  split <;> omega

theorem volume_after_expired (accum volume : Nat) :
    volumeAfter true accum volume = volume := by
  simp [volumeAfter]

theorem volume_after_active (accum volume : Nat) :
    volumeAfter false accum volume = accum + volume := by
  simp [volumeAfter]

theorem breach_monotone_max
    (expired : Bool) (accum volume max1 max2 : Nat)
    (h : max1 ≤ max2)
    (hb : volumeAfter expired accum volume ≥ max2) :
    volumeAfter expired accum volume ≥ max1 := by
  omega

end CircuitBreakerWindowArithmetic
end Proofs

