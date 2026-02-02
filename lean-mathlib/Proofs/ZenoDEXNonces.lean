/-!
Replay-protection lemma for sequential nonces.

ZenoDex currently uses a simple per-sender nonce rule:
- Track `last` (the last accepted nonce for that sender).
- A valid batch for that sender contains nonces `last+1, last+2, ..., last+m`.
- After accepting the batch, update `last := last + m` (equivalently: `last := max_nonce`).

This file proves the core safety fact:
no nonce from an accepted batch can ever appear in any later valid batch,
because all later valid nonces must be >= (last+m)+1.

This is intentionally minimal (no Mathlib dependencies) so it can be typechecked
in lightweight environments.
-/

namespace Proofs

namespace ZenoDEX

def lastAfterBatch (last m : Nat) : Nat :=
  last + m

theorem nonce_seq_le_lastAfter (last m i : Nat) (hi : i < m) :
  last + 1 + i ≤ lastAfterBatch last m := by
  unfold lastAfterBatch
  have hi' : i + 1 ≤ m := Nat.succ_le_of_lt hi
  have hle : last + (i + 1) ≤ last + m := Nat.add_le_add_left hi' last
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle

theorem nonce_from_previous_batch_lt_next_expected (last m i : Nat) (hi : i < m) :
  last + 1 + i < lastAfterBatch last m + 1 := by
  have hle : last + 1 + i ≤ lastAfterBatch last m := nonce_seq_le_lastAfter last m i hi
  exact Nat.lt_succ_of_le hle

theorem no_replay_in_later_valid_seq (last m i j : Nat) (hi : i < m) :
  (last + 1 + i) ≠ (lastAfterBatch last m + 1 + j) := by
  have hlt0 : last + 1 + i < lastAfterBatch last m + 1 :=
    nonce_from_previous_batch_lt_next_expected last m i hi
  have hle0 : lastAfterBatch last m + 1 ≤ lastAfterBatch last m + 1 + j :=
    Nat.le_add_right _ _
  have hlt : last + 1 + i < lastAfterBatch last m + 1 + j :=
    Nat.lt_of_lt_of_le hlt0 hle0
  exact Nat.ne_of_lt hlt

end ZenoDEX

end Proofs
