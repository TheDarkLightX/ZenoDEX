/-!
Batch-wrapper nonce safety for the sorted-fold law.

This file is deliberately separate from `Proofs.ZenoDEXNonces`, which is already
pinned by the SPOT proof receipt. The theorem surface here follows the Phase-2c
review rule:

  validator accept decision -> safety property

The accept decision is `batchAccepts groups = true`. The conclusion states that
every nonce group is the exact successor range `{last+1, ..., last+k}` and that
the post-batch final nonce is `last+k`. The definitions model the live wrapper
after grouping by sender and sorting each sender's nonce list; the PR-gated
runtime binding test checks that `src.state.nonces` matches this model over a
finite domain sweep.

Review note [B+ -> A-]: the first proof surface accepted a raw `List
SenderGroup`, which made duplicate sender groups representable even though the
runtime wrapper canonicalizes one group per sender. `CanonicalBatch` carries the
sender-ID `Nodup` proof in the type, and the receipt now pins the canonical
decision-to-safety theorem. The remaining gap is refinement breadth: the Python
binding sweeps the grouped/sorted construction, but the grouping algorithm itself
is still tested rather than formally proven in Lean.

REVIEW [A- -> A]: the earlier theorem surface proved a useful but weak property:
accepted nonces were above the prior `last`, below the final nonce, and nodup.
That did not explicitly state the live authority's exact contiguous-range
contract. The strengthened surface below proves accepted groups are exactly the
recursive successor range and that the final nonce is `last + length`.
-/

namespace Proofs
namespace ZenoDEX
namespace NonceBatchWrapper

structure SenderGroup where
  sender : Nat
  last : Nat
  nonces : List Nat
deriving Repr

def acceptsSortedFold : Nat -> List Nat -> Bool
  | _, [] => true
  | last, n :: rest => decide (n = last + 1) && acceptsSortedFold n rest

def finalAfterSortedFold : Nat -> List Nat -> Nat
  | last, [] => last
  | _, n :: rest => finalAfterSortedFold n rest

def successorRange : Nat -> Nat -> List Nat
  | _, 0 => []
  | last, k + 1 => (last + 1) :: successorRange (last + 1) k

def groupAccepts (group : SenderGroup) : Bool :=
  acceptsSortedFold group.last group.nonces

def groupFinal (group : SenderGroup) : Nat :=
  finalAfterSortedFold group.last group.nonces

def groupSafe (group : SenderGroup) : Prop :=
  ∀ n, n ∈ group.nonces -> group.last < n ∧ n ≤ groupFinal group

def groupExactRange (group : SenderGroup) : Prop :=
  group.nonces = successorRange group.last group.nonces.length ∧
    groupFinal group = group.last + group.nonces.length

def batchAccepts : List SenderGroup -> Bool
  | [] => true
  | group :: groups => groupAccepts group && batchAccepts groups

def batchFinals (groups : List SenderGroup) : List (Nat × Nat) :=
  if batchAccepts groups then
    groups.map (fun group => (group.sender, groupFinal group))
  else
    groups.map (fun group => (group.sender, group.last))

structure CanonicalBatch where
  groups : List SenderGroup
  senderIds_nodup : (groups.map (fun group => group.sender)).Nodup

def canonicalBatchAccepts (batch : CanonicalBatch) : Bool :=
  batchAccepts batch.groups

def canonicalBatchFinals (batch : CanonicalBatch) : List (Nat × Nat) :=
  batchFinals batch.groups

theorem canonical_batch_sender_ids_nodup (batch : CanonicalBatch) :
    (batch.groups.map (fun group => group.sender)).Nodup :=
  batch.senderIds_nodup

theorem acceptsSortedFold_cons_eq_true {last n : Nat} {rest : List Nat}
    (h : acceptsSortedFold last (n :: rest) = true) :
    n = last + 1 ∧ acceptsSortedFold n rest = true := by
  unfold acceptsSortedFold at h
  rw [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.left, h.right⟩

theorem finalAfterSortedFold_ge_start {last : Nat} {nonces : List Nat}
    (h : acceptsSortedFold last nonces = true) :
    last ≤ finalAfterSortedFold last nonces := by
  induction nonces generalizing last with
  | nil =>
      simp [finalAfterSortedFold]
  | cons n rest ih =>
      have hc := acceptsSortedFold_cons_eq_true h
      have htail : n ≤ finalAfterSortedFold n rest := ih hc.right
      have hlastn : last ≤ n := by
        rw [hc.left]
        exact Nat.le_succ last
      exact Nat.le_trans hlastn htail

theorem successorRange_length (last k : Nat) :
    (successorRange last k).length = k := by
  induction k generalizing last with
  | zero =>
      simp [successorRange]
  | succ k ih =>
      simp [successorRange, ih]

theorem acceptsSortedFold_final_eq_start_add_length {last : Nat} {nonces : List Nat}
    (h : acceptsSortedFold last nonces = true) :
    finalAfterSortedFold last nonces = last + nonces.length := by
  induction nonces generalizing last with
  | nil =>
      simp [finalAfterSortedFold]
  | cons head tail ih =>
      have hc := acceptsSortedFold_cons_eq_true h
      have htail : acceptsSortedFold (last + 1) tail = true := by
        simpa [hc.left] using hc.right
      rw [hc.left]
      simp [finalAfterSortedFold]
      rw [ih htail]
      omega

theorem acceptsSortedFold_eq_successorRange {last : Nat} {nonces : List Nat}
    (h : acceptsSortedFold last nonces = true) :
    nonces = successorRange last nonces.length := by
  induction nonces generalizing last with
  | nil =>
      simp [successorRange]
  | cons head tail ih =>
      have hc := acceptsSortedFold_cons_eq_true h
      have htail : acceptsSortedFold (last + 1) tail = true := by
        simpa [hc.left] using hc.right
      have htail_eq : tail = successorRange (last + 1) tail.length := ih htail
      rw [hc.left]
      rw [htail_eq]
      simp [successorRange, successorRange_length]

theorem acceptsSortedFold_member_safe {last n : Nat} {nonces : List Nat}
    (h : acceptsSortedFold last nonces = true)
    (hin : n ∈ nonces) :
    last < n ∧ n ≤ finalAfterSortedFold last nonces := by
  induction nonces generalizing last with
  | nil =>
      cases hin
  | cons head tail ih =>
      have hc := acceptsSortedFold_cons_eq_true h
      cases hin with
      | head =>
          constructor
          · rw [hc.left]
            exact Nat.lt_succ_self last
          · simp [finalAfterSortedFold]
            exact finalAfterSortedFold_ge_start hc.right
      | tail _ htailMem =>
          have htailSafe := ih hc.right htailMem
          constructor
          · have hlastHead : last < head := by
              rw [hc.left]
              exact Nat.lt_succ_self last
            exact Nat.lt_trans hlastHead htailSafe.left
          · simpa [finalAfterSortedFold] using htailSafe.right

theorem acceptsSortedFold_nodup {last : Nat} {nonces : List Nat}
    (h : acceptsSortedFold last nonces = true) :
    nonces.Nodup := by
  induction nonces generalizing last with
  | nil =>
      exact List.nodup_nil
  | cons head tail ih =>
      have hc := acceptsSortedFold_cons_eq_true h
      have hnot : head ∉ tail := by
        intro hin
        have hsafe := acceptsSortedFold_member_safe hc.right hin
        exact (Nat.lt_irrefl head) hsafe.left
      exact List.nodup_cons.mpr ⟨hnot, ih hc.right⟩

theorem batchAccepts_cons_eq_true {group : SenderGroup} {groups : List SenderGroup}
    (h : batchAccepts (group :: groups) = true) :
    groupAccepts group = true ∧ batchAccepts groups = true := by
  unfold batchAccepts at h
  rw [Bool.and_eq_true] at h
  exact h

/-- Decision-to-safety theorem for the multi-sender wrapper model.

If the batch wrapper accepts all sender groups, then every nonce in every group is
inside that sender's strict post-batch range. This is the load-bearing direction:
the accept decision is the hypothesis, and the safety property is the conclusion.
-/
theorem batch_accept_decision_implies_safety {groups : List SenderGroup}
    (haccept : batchAccepts groups = true) :
    ∀ group, group ∈ groups -> groupSafe group := by
  induction groups with
  | nil =>
      intro group hin
      cases hin
  | cons head tail ih =>
      have hc := batchAccepts_cons_eq_true haccept
      intro group hin
      cases hin with
      | head =>
          intro n hn
          exact acceptsSortedFold_member_safe hc.left hn
      | tail _ htail =>
          exact ih hc.right group htail

theorem batch_accept_decision_implies_group_nodup {groups : List SenderGroup}
    (haccept : batchAccepts groups = true) :
    ∀ group, group ∈ groups -> group.nonces.Nodup := by
  intro group hin
  have hsafety := batch_accept_decision_implies_safety haccept
  clear hsafety
  induction groups with
  | nil =>
      cases hin
  | cons head tail ih =>
      have hc := batchAccepts_cons_eq_true haccept
      cases hin with
      | head =>
          exact acceptsSortedFold_nodup hc.left
      | tail _ htail =>
          exact ih hc.right htail

theorem group_accept_decision_implies_exact_range {group : SenderGroup}
    (haccept : groupAccepts group = true) :
    groupExactRange group := by
  constructor
  · exact acceptsSortedFold_eq_successorRange haccept
  · exact acceptsSortedFold_final_eq_start_add_length haccept

theorem batch_accept_decision_implies_exact_ranges {groups : List SenderGroup}
    (haccept : batchAccepts groups = true) :
    ∀ group, group ∈ groups -> groupExactRange group := by
  induction groups with
  | nil =>
      intro group hin
      cases hin
  | cons head tail ih =>
      have hc := batchAccepts_cons_eq_true haccept
      intro group hin
      cases hin with
      | head =>
          exact group_accept_decision_implies_exact_range hc.left
      | tail _ htail =>
          exact ih hc.right group htail

/-- Canonical decision-to-safety theorem for the runtime-shaped batch type.

This is the stronger receipt-pinned surface: duplicate sender groups are not
inhabitants of `CanonicalBatch`, so the theorem's domain matches the wrapper
after sender grouping rather than a raw list supplied by an adversary. -/
theorem canonical_batch_accept_decision_implies_safety {batch : CanonicalBatch}
    (haccept : canonicalBatchAccepts batch = true) :
    ∀ group, group ∈ batch.groups -> groupSafe group :=
  batch_accept_decision_implies_safety haccept

/-- Canonical exact-range theorem for the runtime-shaped batch type.

If the live-shaped wrapper accepts, then each sender group is exactly the
successor range `{last+1, ..., last+k}` and its final nonce is `last+k`. This is
the stronger proof surface needed for the batch wrapper binding: no gaps, no
duplicates, and the post-state last nonce is determined by the accepted range.
-/
theorem canonical_batch_accept_decision_implies_exact_ranges {batch : CanonicalBatch}
    (haccept : canonicalBatchAccepts batch = true) :
    ∀ group, group ∈ batch.groups -> groupExactRange group :=
  batch_accept_decision_implies_exact_ranges haccept

def witnessAcceptedGroups : List SenderGroup :=
  [
    { sender := 0, last := 0, nonces := [1, 2] },
    { sender := 1, last := 5, nonces := [6] }
  ]

theorem witness_batch_accepts :
    batchAccepts witnessAcceptedGroups = true := by
  rfl

theorem witness_batch_accept_safety :
    ∀ group, group ∈ witnessAcceptedGroups -> groupSafe group :=
  batch_accept_decision_implies_safety witness_batch_accepts

def witnessCanonicalBatch : CanonicalBatch :=
  {
    groups := witnessAcceptedGroups,
    senderIds_nodup := by
      decide
  }

theorem witness_canonical_batch_accepts :
    canonicalBatchAccepts witnessCanonicalBatch = true := by
  rfl

theorem witness_reject_gap :
    batchAccepts [{ sender := 0, last := 0, nonces := [2] }] = false := by
  rfl

theorem witness_reject_is_noop_finals :
    batchFinals [{ sender := 0, last := 0, nonces := [2] }] = [(0, 0)] := by
  rfl

end NonceBatchWrapper
end ZenoDEX
end Proofs
