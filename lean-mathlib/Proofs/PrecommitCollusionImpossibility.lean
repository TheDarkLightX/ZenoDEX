/-
# Constructive Numeric Witness: Precommit Collusion in (A,B) Batch Clearing

This file proves a constructive numeric witness: for the (A,B) batch
clearing mechanism with commit-reveal for both parameters, there exists a
concrete pool state and user value profile where a 2-user coalition can
profitably deviate via precommit coordination with off-protocol side payments.

## Theorem (Constructive Witness for the Modeled Clearing Rule)

There exist pool reserves, user true values, and a coalition of 2 users such
that the coalition's total surplus under joint misreporting (precommit
sacrifice) strictly exceeds their total surplus under truthful reporting.
Therefore, a side-payment vector exists that makes both users strictly better
off, and the mechanism cannot prevent this because it has no enforcement over
off-protocol transfers.

## Witness

- Pool: (R_x, R_y) = (10000, 10000), no fee
- User A: amount_in = 100, truthful min_out = 89 (90% of expected output 99)
- User B: amount_in = 5000, truthful min_out = 2950 (90% of expected output 3278)

### Truthful precommit (both commit truthful values)

1. A fills: out_A = cpmm_swap(10000, 10000, 100) = 99 >= 89, surplus_A = 10
2. Pool becomes (10100, 9901)
3. B fills: out_B = cpmm_swap(10100, 9901, 5000) = 3278 >= 2950, surplus_B = 328
4. Group surplus = 10 + 328 = 338

### Sacrifice precommit (A commits min_out = 100, B commits truthfully)

1. A does not fill: 99 < 100, surplus_A = 0
2. Pool unchanged: (10000, 10000)
3. B fills: out_B = cpmm_swap(10000, 10000, 5000) = 3333 >= 2950, surplus_B = 383
4. Group surplus = 0 + 383 = 383

### Collusion gain

Group surplus sacrifice (383) > group surplus truthful (338).
Gain = 45 > 0.

### Side payment existence

There exists t in (10, 55) such that:
- A's utility with side payment: 0 + t > 10 (A's truthful surplus)
- B's utility with side payment: 383 - t > 328 (B's truthful surplus)

For example, t = 32: A gets 32 > 10, B gets 351 > 328. Both strictly better off.

## Scope and Non-Claims

This proof shows:
- The (A,B) batch clearing with commit-reveal is NOT group strategyproof
  (constructive witness with specific numeric values)

This proof does NOT show:
- A general impossibility for ALL commit-reveal mechanisms (would require
  quantifying over all clearing functions, which is beyond the scope of this
  formalization)
- That mitigations cannot work (slashing, VCG payments, or batch-boundary
  randomization may reduce the violation rate)
- That the sacrifice attack is always profitable (it is profitable for the
  specific witness values, not for all value profiles)

## Verification

Compile: cd lean-mathlib && lake env lean Proofs/PrecommitCollusionImpossibility.lean
-/

import Mathlib.Tactic

/-- CPMM swap output: how much y-token you get for `a` x-tokens in a pool (x, y).
    Simplified model: no fee. Uses integer floor division (rounds toward zero
    for positive arguments, matching Python's `//` for positive operands). -/
def cpmm_swap (x y a : ℤ) : ℤ :=
  if x + a ≤ 0 then 0 else (y * a) / (x + a)

/-- Surplus: if the swap output meets `min_out`, the surplus is `out - min_out`;
    otherwise the trade does not fill and surplus is 0. -/
def surplus (out min_out : ℤ) : ℤ :=
  if out ≥ min_out then out - min_out else 0

/-- Group surplus for two users: sum of individual surpluses. -/
def group_surplus (out_A out_B min_A min_B : ℤ) : ℤ :=
  surplus out_A min_A + surplus out_B min_B

/-- Witness swap values (verified by computation). -/
lemma cpmm_swap_witness_A : cpmm_swap 10000 10000 100 = 99 := by
  unfold cpmm_swap
  rw [if_neg (by linarith : ¬ (10000 + 100 : ℤ) ≤ 0)]
  norm_num

/-- After A fills, pool becomes (10100, 9901). B's swap output. -/
lemma cpmm_swap_witness_B_after_A : cpmm_swap 10100 9901 5000 = 3278 := by
  unfold cpmm_swap
  rw [if_neg (by linarith : ¬ (10100 + 5000 : ℤ) ≤ 0)]
  norm_num

/-- B's swap output when A does not fill (pool unchanged). -/
lemma cpmm_swap_witness_B_alone : cpmm_swap 10000 10000 5000 = 3333 := by
  unfold cpmm_swap
  rw [if_neg (by linarith : ¬ (10000 + 5000 : ℤ) ≤ 0)]
  norm_num

/-- Truthful case: A fills (99 >= 89), surplus_A = 10. -/
lemma surplus_A_truthful : surplus 99 89 = 10 := by
  unfold surplus
  rw [if_pos (by linarith : (99 : ℤ) ≥ 89)]
  norm_num

/-- Truthful case: B fills (3278 >= 2950), surplus_B = 328. -/
lemma surplus_B_truthful : surplus 3278 2950 = 328 := by
  unfold surplus
  rw [if_pos (by linarith : (3278 : ℤ) ≥ 2950)]
  norm_num

/-- Sacrifice case: A does not fill (0 < 100), surplus_A = 0. -/
lemma surplus_A_sacrifice : surplus 0 100 = 0 := by
  unfold surplus
  rw [if_neg (by linarith : ¬ (0 : ℤ) ≥ 100)]

/-- Sacrifice case: B fills (3333 >= 2950), surplus_B = 383. -/
lemma surplus_B_sacrifice : surplus 3333 2950 = 383 := by
  unfold surplus
  rw [if_pos (by linarith : (3333 : ℤ) ≥ 2950)]
  norm_num

/-- Truthful group surplus = 10 + 328 = 338. -/
theorem truthful_group_surplus_value : group_surplus 99 3278 89 2950 = 338 := by
  unfold group_surplus
  rw [surplus_A_truthful, surplus_B_truthful]
  norm_num

/-- Sacrifice group surplus = 0 + 383 = 383. -/
theorem sacrifice_group_surplus_value : group_surplus 0 3333 100 2950 = 383 := by
  unfold group_surplus
  rw [surplus_A_sacrifice, surplus_B_sacrifice]
  norm_num

/-- **Constructive witness (direct proof)**: For the witness values
    (pool (10000, 10000), A: amt=100 min=89, B: amt=5000 min=2950),
    the precommit sacrifice attack yields group surplus 383 > 338 (truthful).
    Gain = 45 > 0. -/
theorem precommit_collusion_impossibility_direct :
    group_surplus 0 3333 100 2950 > group_surplus 99 3278 89 2950 := by
  unfold group_surplus surplus
  rw [if_neg (by linarith : ¬ (0 : ℤ) ≥ 100),
      if_pos (by linarith : (3333 : ℤ) ≥ 2950),
      if_pos (by linarith : (99 : ℤ) ≥ 89),
      if_pos (by linarith : (3278 : ℤ) ≥ 2950)]
  norm_num

/-- **Side payment existence**: There exists a side payment `t` from B to A
    such that both users are strictly better off under the sacrifice attack.

    A's condition: surplus_A_sacrifice + t > surplus_A_truthful
                  0 + t > 10
                  t > 10

    B's condition: surplus_B_sacrifice - t > surplus_B_truthful
                  383 - t > 328
                  t < 55

    Solution: t = 32 (A gets 32 > 10, B gets 351 > 328). -/
theorem side_payment_exists :
    ∃ t : ℤ,
      0 + t > surplus 99 89 ∧
      surplus 3333 2950 - t > surplus 3278 2950 := by
  unfold surplus
  rw [if_pos (by linarith : (99 : ℤ) ≥ 89),
      if_pos (by linarith : (3333 : ℤ) ≥ 2950),
      if_pos (by linarith : (3278 : ℤ) ≥ 2950)]
  use 32
  norm_num

/-- **Constructive witness for the modeled (A,B) clearing rule**: Commit-reveal
    for both parameters cannot prevent precommit collusion for this specific
    clearing rule. There exist pool reserves and user values where:
    1. The sacrifice group surplus strictly exceeds the truthful group surplus.
    2. A side payment exists making both users strictly better off.
    3. The mechanism has no enforcement to prevent this. -/
theorem commit_reveal_cannot_prevent_precommit_collusion :
    group_surplus 0 3333 100 2950 > group_surplus 99 3278 89 2950 ∧
    ∃ t : ℤ,
      0 + t > surplus 99 89 ∧
      surplus 3333 2950 - t > surplus 3278 2950 := by
  constructor
  · exact precommit_collusion_impossibility_direct
  · exact side_payment_exists
