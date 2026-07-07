import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic

import Proofs.SettlementAlgebra
import Proofs.SettlementPipeline

/-!
# Sharded Batch Clearing Conservation Theorem

This file proves the key scaling theorem: sharded batch clearing preserves
conservation. If a batch of intents is partitioned into shards, each shard
is cleared independently, and each shard produces a balanced settlement,
then the union of all shard settlements is also balanced.

## Main Results

1. `sharded_conservation`: If every shard produces a balanced settlement,
   the aggregate is balanced.
2. `aggregate_concat`: Aggregate of concatenated shardings is the sum.
3. `conservation_any_partition`: Conservation holds for any partition.
4. `shard_failure_isolation`: Failed shards don't corrupt conservation.
5. `cross_shard_netting_balanced`: Cross-shard netting preserves balance.
-/

namespace ShardedBatchClearing

open SettlementAlgebra

abbrev Shard := List Settlement
abbrev Sharding := List Shard

def shardSettlement (shard : Shard) : Settlement :=
  SettlementPipeline.foldSettlements shard

/-- The aggregate settlement: sum of all shard settlements. -/
def aggregateSettlement : Sharding → Settlement
  | [] => 0
  | shard :: rest => shardSettlement shard + aggregateSettlement rest

/-! ## Section 2: Shard Conservation -/

theorem shard_netFlow (shard : Shard) :
    Δ (shardSettlement shard) = (shard.map Δ).sum := by
  exact SettlementPipeline.foldSettlements_netFlow shard

theorem shard_balanced (shard : Shard)
    (hAll : ∀ st ∈ shard, st.isBalanced) :
    (shardSettlement shard).isBalanced := by
  exact SettlementPipeline.foldSettlements_balanced shard hAll

theorem aggregate_netFlow (sharding : Sharding) :
    Δ (aggregateSettlement sharding) =
      (sharding.map (fun shard => Δ (shardSettlement shard))).sum := by
  induction sharding with
  | nil => simp [aggregateSettlement, Δ.map_zero]
  | cons shard rest ih =>
    simp [aggregateSettlement, Δ.map_add, ih, List.map_cons, List.sum_cons]

/-- THE MAIN THEOREM: Sharded batch clearing conservation.

    If every shard produces a balanced settlement, the aggregate
    settlement is balanced. This is the mathematical foundation for
    horizontal scaling. -/
theorem sharded_conservation (sharding : Sharding)
    (hAll : ∀ shard ∈ sharding,
      (shardSettlement shard).isBalanced) :
    (aggregateSettlement sharding).isBalanced := by
  unfold Settlement.isBalanced at *
  rw [aggregate_netFlow]
  induction sharding with
  | nil => simp
  | cons shard rest ih =>
    rw [List.map_cons, List.sum_cons]
    have hmem : shard ∈ shard :: rest := List.mem_cons.mpr (Or.inl rfl)
    rw [hAll shard hmem]
    rw [ih (fun s hs => hAll s (List.mem_cons_of_mem _ hs))]
    ring

/-! ## Section 2b: Body-Pinned Posting-Summary Sets -/

/-- Abstract shape of a runtime posting summary: a canonical summary hash and
the shard settlement it represents. -/
structure PostingSummary (Hash : Type) where
  postingHash : Hash
  shard : Shard

def postingSummaryHashes {Hash : Type}
    (summaries : List (PostingSummary Hash)) : List Hash :=
  summaries.map PostingSummary.postingHash

def postingSummarySharding {Hash : Type}
    (summaries : List (PostingSummary Hash)) : Sharding :=
  summaries.map PostingSummary.shard

/-- Body evidence pins exactly the emitted posting summaries when the emitted
summary hashes equal the body-pinned canonical hash list. -/
def BodyPinnedPostingSummarySet {Hash : Type}
    (expectedHashes : List Hash)
    (summaries : List (PostingSummary Hash)) : Prop :=
  postingSummaryHashes summaries = expectedHashes

def PostingSummarySetBalanced {Hash : Type}
    (summaries : List (PostingSummary Hash)) : Prop :=
  ∀ summary ∈ summaries, (shardSettlement summary.shard).isBalanced

/-- If the body-pinned posting-summary set is exact and every selected summary
is balanced, then the selected aggregate is balanced and the emitted hashes are
exactly the body-pinned hashes. -/
theorem body_pinned_summary_set_conservation_and_exactness
    {Hash : Type} {expectedHashes : List Hash}
    {summaries : List (PostingSummary Hash)}
    (hPinned : BodyPinnedPostingSummarySet expectedHashes summaries)
    (hBalanced : PostingSummarySetBalanced summaries) :
    (aggregateSettlement (postingSummarySharding summaries)).isBalanced ∧
      postingSummaryHashes summaries = expectedHashes := by
  constructor
  · apply sharded_conservation
    intro shard hmem
    rw [postingSummarySharding] at hmem
    rcases List.mem_map.mp hmem with ⟨summary, hSummary, hShard⟩
    rw [← hShard]
    exact hBalanced summary hSummary
  · exact hPinned

/-- Exact body pinning preserves the canonical expected cardinality. This is the
formal count side of "no missing or extra posting summaries". -/
theorem body_pinned_summary_set_no_missing_or_extra_count
    {Hash : Type} {expectedHashes : List Hash}
    {summaries : List (PostingSummary Hash)}
    (hPinned : BodyPinnedPostingSummarySet expectedHashes summaries) :
    summaries.length = expectedHashes.length := by
  have hlen := congrArg List.length hPinned
  simpa [postingSummaryHashes] using hlen

/-- If the body-pinned hash list has no duplicates, neither does the emitted
summary hash list. -/
theorem body_pinned_summary_set_supplied_hashes_nodup
    {Hash : Type} {expectedHashes : List Hash}
    {summaries : List (PostingSummary Hash)}
    (hPinned : BodyPinnedPostingSummarySet expectedHashes summaries)
    (hExpectedNodup : expectedHashes.Nodup) :
    (postingSummaryHashes summaries).Nodup := by
  rw [hPinned]
  exact hExpectedNodup

/-- Exact body pinning gives the membership contract consumed by runtime
validators: a hash is expected exactly when some supplied summary carries it. -/
theorem body_pinned_summary_set_hash_mem_iff
    {Hash : Type} {expectedHashes : List Hash}
    {summaries : List (PostingSummary Hash)}
    (hPinned : BodyPinnedPostingSummarySet expectedHashes summaries)
    (h : Hash) :
    h ∈ expectedHashes ↔
      ∃ summary ∈ summaries, summary.postingHash = h := by
  constructor
  · intro hMem
    rw [← hPinned] at hMem
    exact List.mem_map.mp hMem
  · intro hMem
    rcases hMem with ⟨summary, hSummary, hHash⟩
    rw [← hPinned]
    exact List.mem_map.mpr ⟨summary, hSummary, hHash⟩

/-! ## Section 2c: Body-Pinned Terminal Admission Sets -/

/-- Runtime shape after terminal body evidence is enforced: a posting-summary
hash, terminal-admission hash, and the shard settlement represented by that
terminally admitted summary. -/
structure TerminalPostingSummary (Hash : Type) where
  postingHash : Hash
  terminalAdmissionHash : Hash
  shard : Shard

def terminalPostingSummaryHashes {Hash : Type}
    (summaries : List (TerminalPostingSummary Hash)) : List Hash :=
  summaries.map TerminalPostingSummary.postingHash

def terminalAdmissionHashes {Hash : Type}
    (summaries : List (TerminalPostingSummary Hash)) : List Hash :=
  summaries.map TerminalPostingSummary.terminalAdmissionHash

def terminalPostingSummarySharding {Hash : Type}
    (summaries : List (TerminalPostingSummary Hash)) : Sharding :=
  summaries.map TerminalPostingSummary.shard

/-- Body evidence pins exactly both artifact families consumed by the runtime
writer: posting summaries and terminal admissions. -/
def BodyPinnedTerminalPostingSummarySet {Hash : Type}
    (expectedPostingHashes expectedTerminalAdmissionHashes : List Hash)
    (summaries : List (TerminalPostingSummary Hash)) : Prop :=
  terminalPostingSummaryHashes summaries = expectedPostingHashes ∧
    terminalAdmissionHashes summaries = expectedTerminalAdmissionHashes

def TerminalPostingSummarySetBalanced {Hash : Type}
    (summaries : List (TerminalPostingSummary Hash)) : Prop :=
  ∀ summary ∈ summaries, (shardSettlement summary.shard).isBalanced

/-- Terminal body pinning composes the selected shard settlements and preserves
both exact artifact hash lists. -/
theorem terminal_body_pinned_summary_set_conservation_and_exactness
    {Hash : Type} {expectedPostingHashes expectedTerminalAdmissionHashes : List Hash}
    {summaries : List (TerminalPostingSummary Hash)}
    (hPinned :
      BodyPinnedTerminalPostingSummarySet
        expectedPostingHashes
        expectedTerminalAdmissionHashes
        summaries)
    (hBalanced : TerminalPostingSummarySetBalanced summaries) :
    (aggregateSettlement (terminalPostingSummarySharding summaries)).isBalanced ∧
      terminalPostingSummaryHashes summaries = expectedPostingHashes ∧
      terminalAdmissionHashes summaries = expectedTerminalAdmissionHashes := by
  constructor
  · apply sharded_conservation
    intro shard hmem
    rw [terminalPostingSummarySharding] at hmem
    rcases List.mem_map.mp hmem with ⟨summary, hSummary, hShard⟩
    rw [← hShard]
    exact hBalanced summary hSummary
  · exact hPinned

/-- Exact terminal body pinning prevents missing or extra posting summaries and
terminal admissions at the count level. -/
theorem terminal_body_pinned_summary_set_no_missing_or_extra_count
    {Hash : Type} {expectedPostingHashes expectedTerminalAdmissionHashes : List Hash}
    {summaries : List (TerminalPostingSummary Hash)}
    (hPinned :
      BodyPinnedTerminalPostingSummarySet
        expectedPostingHashes
        expectedTerminalAdmissionHashes
        summaries) :
    summaries.length = expectedPostingHashes.length ∧
      summaries.length = expectedTerminalAdmissionHashes.length := by
  constructor
  · have hlen := congrArg List.length hPinned.1
    simpa [terminalPostingSummaryHashes] using hlen
  · have hlen := congrArg List.length hPinned.2
    simpa [terminalAdmissionHashes] using hlen

/-- If the body-pinned terminal-admission hash list is duplicate-free, then the
supplied terminal admissions are duplicate-free. -/
theorem terminal_body_pinned_summary_set_terminal_hashes_nodup
    {Hash : Type} {expectedPostingHashes expectedTerminalAdmissionHashes : List Hash}
    {summaries : List (TerminalPostingSummary Hash)}
    (hPinned :
      BodyPinnedTerminalPostingSummarySet
        expectedPostingHashes
        expectedTerminalAdmissionHashes
        summaries)
    (hExpectedNodup : expectedTerminalAdmissionHashes.Nodup) :
    (terminalAdmissionHashes summaries).Nodup := by
  rw [hPinned.2]
  exact hExpectedNodup

/-- Terminal body pinning gives the terminal-admission membership contract
consumed by runtime validators. -/
theorem terminal_body_pinned_summary_set_terminal_hash_mem_iff
    {Hash : Type} {expectedPostingHashes expectedTerminalAdmissionHashes : List Hash}
    {summaries : List (TerminalPostingSummary Hash)}
    (hPinned :
      BodyPinnedTerminalPostingSummarySet
        expectedPostingHashes
        expectedTerminalAdmissionHashes
        summaries)
    (h : Hash) :
    h ∈ expectedTerminalAdmissionHashes ↔
      ∃ summary ∈ summaries, summary.terminalAdmissionHash = h := by
  constructor
  · intro hMem
    rw [← hPinned.2] at hMem
    exact List.mem_map.mp hMem
  · intro hMem
    rcases hMem with ⟨summary, hSummary, hHash⟩
    rw [← hPinned.2]
    exact List.mem_map.mpr ⟨summary, hSummary, hHash⟩

/-! ## Section 3: Partition Properties -/

theorem aggregate_concat (s₁ s₂ : Sharding) :
    aggregateSettlement (s₁ ++ s₂) =
    aggregateSettlement s₁ + aggregateSettlement s₂ := by
  induction s₁ with
  | nil => simp [aggregateSettlement]
  | cons shard rest ih =>
    simp [aggregateSettlement, List.cons_append, ih, add_assoc]

theorem aggregate_swap_adjacent (s₀ : Sharding) (s₁ s₂ : Shard) (s₃ : Sharding) :
    aggregateSettlement (s₀ ++ [s₁, s₂] ++ s₃) =
    aggregateSettlement (s₀ ++ [s₂, s₁] ++ s₃) := by
  rw [aggregate_concat, aggregate_concat, aggregate_concat, aggregate_concat]
  simp [aggregateSettlement, add_comm]

/-! ## Section 4: Shard Count Independence -/

theorem conservation_any_shard_count (sharding : Sharding)
    (hAll : ∀ shard ∈ sharding,
      (shardSettlement shard).isBalanced) :
    (aggregateSettlement sharding).isBalanced := by
  exact sharded_conservation sharding hAll

theorem monolithic_is_single_shard (settlements : List Settlement)
    (hAll : ∀ st ∈ settlements, st.isBalanced) :
    (shardSettlement settlements).isBalanced := by
  exact shard_balanced settlements hAll

/-! ## Section 5: Cross-Shard Netting -/

theorem cross_shard_netting_preserves_flow (sharding : Sharding) :
    Δ (aggregateSettlement sharding) =
      (sharding.map (fun s => Δ (shardSettlement s))).sum := by
  exact aggregate_netFlow sharding

theorem cross_shard_netting_balanced (sharding : Sharding)
    (hAll : ∀ shard ∈ sharding,
      (shardSettlement shard).isBalanced) :
    (aggregateSettlement sharding).isBalanced := by
  exact sharded_conservation sharding hAll

/-! ## Section 6: Shard Failure Isolation -/

theorem failed_shard_zero :
    shardSettlement [] = 0 := by
  unfold shardSettlement SettlementPipeline.foldSettlements
  rfl

theorem failed_shard_zero_flow :
    Δ (shardSettlement []) = 0 := by
  exact Δ.map_zero

theorem shard_failure_isolation (sharding : Sharding)
    (hAll : ∀ shard ∈ sharding,
      shard ≠ [] → (shardSettlement shard).isBalanced) :
    (aggregateSettlement (sharding.filter (fun s => s ≠ []))).isBalanced := by
  apply sharded_conservation
  intro shard hmem
  rw [List.mem_filter] at hmem
  have hne : shard ≠ [] := by
    have := hmem.2
    simp at this
    exact this
  exact hAll shard hmem.1 hne

theorem remove_empty_shards_preserves_aggregate (sharding : Sharding) :
    aggregateSettlement (sharding.filter (fun s => s ≠ [])) =
    aggregateSettlement sharding := by
  induction sharding with
  | nil => rfl
  | cons shard rest ih =>
    by_cases he : shard = []
    · -- Empty shard: filter removes it, aggregate unchanged
      rw [he]
      show aggregateSettlement (List.filter (fun s => s ≠ []) rest) =
           shardSettlement [] + aggregateSettlement rest
      rw [failed_shard_zero, zero_add, ih]
    · -- Non-empty shard: filter keeps it
      have hfilter : (shard :: rest).filter (fun s => s ≠ []) =
                     shard :: rest.filter (fun s => s ≠ []) := by
        simp [List.filter, he]
      rw [hfilter]
      show shardSettlement shard + aggregateSettlement (rest.filter (fun s => s ≠ [])) =
           shardSettlement shard + aggregateSettlement rest
      rw [ih]

/-! ## Section 7: Any-Partition Conservation -/

theorem conservation_any_partition (settlements : List Settlement)
    (partition : List (List Settlement))
    (hPartition : partition.flatten = settlements)
    (hAll : ∀ st ∈ settlements, st.isBalanced) :
    (aggregateSettlement partition).isBalanced := by
  apply sharded_conservation
  intro shard hmem
  apply shard_balanced
  intro st hst
  apply hAll
  rw [← hPartition]
  exact List.mem_flatten.mpr ⟨shard, hmem, hst⟩

/-! ## Section 8: Concrete Witnesses -/

theorem witness_3_shard_conservation :
    let s1 : Settlement := ⟨100, -100⟩
    let s2 : Settlement := ⟨50, -50⟩
    let s3 : Settlement := ⟨200, -200⟩
    (shardSettlement [s1]).isBalanced ∧
    (shardSettlement [s2]).isBalanced ∧
    (shardSettlement [s3]).isBalanced ∧
    (aggregateSettlement [[s1], [s2], [s3]]).isBalanced ∧
    Δ (aggregateSettlement [[s1], [s2], [s3]]) = 0 := by
  simp [shardSettlement, SettlementPipeline.foldSettlements,
        aggregateSettlement, Settlement.isBalanced, Δ, netFlow]
  decide

theorem witness_multi_settlement_shards :
    let s1 : Settlement := ⟨100, -100⟩
    let s2 : Settlement := ⟨50, -50⟩
    let s3 : Settlement := ⟨200, -200⟩
    (shardSettlement [s1, s2]).isBalanced ∧
    (shardSettlement [s3]).isBalanced ∧
    (aggregateSettlement [[s1, s2], [s3]]).isBalanced ∧
    Δ (aggregateSettlement [[s1, s2], [s3]]) = 0 := by
  simp [shardSettlement, SettlementPipeline.foldSettlements,
        aggregateSettlement, Settlement.isBalanced, Δ, netFlow]
  decide

theorem witness_10_shard_scaling :
    let s : Settlement := ⟨10, -10⟩
    let sharding : Sharding := List.replicate 10 [s]
    (aggregateSettlement sharding).isBalanced ∧
    Δ (aggregateSettlement sharding) = 0 ∧
    sharding.length = 10 := by
  simp [shardSettlement, SettlementPipeline.foldSettlements,
        aggregateSettlement, Settlement.isBalanced, Δ, netFlow]
  decide

/-! ## Section 9: Scaling Properties -/

theorem sharded_throughput_scaling (k n : ℕ)
    (hk : 0 < k) (_hn : 0 < n) :
    k * n ≥ n := by
  nlinarith

theorem empty_sharding_zero :
    aggregateSettlement [] = 0 := by
  rfl

theorem single_shard_aggregate (shard : Shard) :
    aggregateSettlement [shard] = shardSettlement shard := by
  simp [aggregateSettlement, add_zero]

end ShardedBatchClearing
