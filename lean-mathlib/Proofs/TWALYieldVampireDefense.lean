import Mathlib

/-!
# TWAL Yield Vampire Defense

Internal proof note for Campaign 5's just-in-time reward vampire witness.

Snapshot pro-rata rewards allocate by liquidity at one boundary. Time-weighted
average liquidity (TWAL) allocates by integrated exposure:

`weight = liquidity * duration`

The core comparison is cross-multiplied, avoiding division and floating point.
If an attacker supplies positive liquidity for strictly less time than honest
liquidity, TWAL gives the attacker a strictly smaller share than snapshot
pro-rata.
-/

namespace Internal
namespace TWALYieldVampireDefense

/-- Snapshot share comparison numerator for attacker liquidity. -/
def SnapshotWeight (liquidity : Nat) : Nat :=
  liquidity

/-- TWAL weight is liquidity integrated over discrete epoch duration. -/
def TWALWeight (liquidity duration : Nat) : Nat :=
  liquidity * duration

/-- Integer reward allocation by TWAL weight. This is the deterministic floor
form a runtime can use directly. -/
def TWALReward (epochReward attackerLiquidity attackerDuration honestLiquidity honestDuration : Nat) : Nat :=
  let attackerWeight := TWALWeight attackerLiquidity attackerDuration
  let honestWeight := TWALWeight honestLiquidity honestDuration
  epochReward * attackerWeight / (attackerWeight + honestWeight)

/-- Snapshot reward allocation by boundary liquidity. -/
def SnapshotReward (epochReward attackerLiquidity honestLiquidity : Nat) : Nat :=
  epochReward * attackerLiquidity / (attackerLiquidity + honestLiquidity)

/--
Cross-multiplied statement of:

`attackerTWALShare < attackerSnapshotShare`

under positive liquidity and shorter attacker duration.
-/
theorem twal_share_strictly_below_snapshot_for_shorter_duration
    {attackerLiquidity honestLiquidity attackerDuration honestDuration : Nat}
    (hAttackerLiq : 0 < attackerLiquidity)
    (hHonestLiq : 0 < honestLiquidity)
    (hShorter : attackerDuration < honestDuration) :
    attackerLiquidity * attackerDuration * (attackerLiquidity + honestLiquidity) <
      attackerLiquidity * (attackerLiquidity * attackerDuration + honestLiquidity * honestDuration) := by
  nlinarith [
    Nat.mul_pos hAttackerLiq hHonestLiq,
    Nat.mul_lt_mul_of_pos_left hShorter hHonestLiq,
    Nat.mul_lt_mul_of_pos_left hShorter (Nat.mul_pos hAttackerLiq hHonestLiq)
  ]

/-- The attacker cannot receive more than the epoch reward from the floor-form
TWAL allocator. -/
theorem twal_reward_bounded_by_epoch_reward
    {epochReward attackerLiquidity attackerDuration honestLiquidity honestDuration : Nat} :
    TWALReward epochReward attackerLiquidity attackerDuration honestLiquidity honestDuration ≤ epochReward := by
  unfold TWALReward TWALWeight
  apply Nat.div_le_of_le_mul
  have hWeightLe :
      attackerLiquidity * attackerDuration ≤
        attackerLiquidity * attackerDuration + honestLiquidity * honestDuration :=
    Nat.le_add_right _ _
  have hMul := Nat.mul_le_mul_right epochReward hWeightLe
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hMul

/-- Campaign 5 witness: the one-block attacker receives less share under TWAL
than under snapshot pro-rata. -/
theorem campaign5_twal_reduces_jit_witness :
    9900000 * 1 * (9900000 + 100000) <
      9900000 * (9900000 * 1 + 100000 * 1000) := by
  norm_num

/-- Campaign 5 numeric floor allocation for the TWAL witness. -/
theorem campaign5_twal_reward_floor :
    TWALReward 10000 9900000 1 100000 1000 = 900 := by
  norm_num [TWALReward, TWALWeight]

/-- Campaign 5 numeric floor allocation for the vulnerable snapshot witness. -/
theorem campaign5_snapshot_reward_floor :
    SnapshotReward 10000 9900000 100000 = 9900 := by
  norm_num [SnapshotReward]

end TWALYieldVampireDefense
end Internal
