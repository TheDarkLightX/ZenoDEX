import Init.Data.List.Basic
import Init.Data.List.Perm
import Init.Data.List.Pairwise

namespace ZenoDEX.ZenoLedgerZkTeeProofComposition

/-
This file models the ZenoLedger proof-composition layer at the mathematical
boundary. It abstracts cryptographic soundness: Risc0/SP1 verification, TEE
vendor attestation, and hash collision resistance are external assumptions.

The in-repo target is deterministic composition:
- recursive proof segments expose the aggregate pre/post roots;
- proof segments bind program/schedule metadata;
- pairwise-commuting scheduled chunks may be proved separately and recomposed
  without changing the final state.
-/

structure Segment where
  preRoot : Nat
  postRoot : Nat
  journalHash : Nat
  metadataHash : Nat
deriving DecidableEq

def Chains : List Segment -> Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a.postRoot = b.preRoot ∧ Chains (b :: rest)

def FirstPre : List Segment -> Nat
  | [] => 0
  | s :: _ => s.preRoot

def LastPost : List Segment -> Nat
  | [] => 0
  | [s] => s.postRoot
  | _ :: rest => LastPost rest

def SegmentValid (expectedProgram expectedSchedule : Nat) (s : Segment) : Prop :=
  s.journalHash = expectedProgram ∧ s.metadataHash = expectedSchedule

def AllSegmentsValid (expectedProgram expectedSchedule : Nat) (xs : List Segment) : Prop :=
  ∀ s ∈ xs, SegmentValid expectedProgram expectedSchedule s

theorem chains_cons_cons
    {a b : Segment}
    {rest : List Segment}
    (hchain : Chains (a :: b :: rest)) :
    a.postRoot = b.preRoot ∧ Chains (b :: rest) := by
  exact hchain

theorem chain_first_two_roots_match
    {a b : Segment}
    {rest : List Segment}
    (hchain : Chains (a :: b :: rest)) :
    a.postRoot = b.preRoot := by
  exact (chains_cons_cons hchain).1

/-- In a non-empty segment list, some element witnesses `LastPost`. -/
private theorem lastPost_mem :
    ∀ (xs : List Segment), xs ≠ [] → ∃ s ∈ xs, s.postRoot = LastPost xs
  | [], h => absurd rfl h
  | [s], _ => ⟨s, List.Mem.head _, rfl⟩
  | _ :: b :: rest, _ => by
    have ⟨s, hs, he⟩ := lastPost_mem (b :: rest) (List.cons_ne_nil _ _)
    exact ⟨s, List.Mem.tail _ hs, by simp [LastPost]; exact he⟩

/-- A valid recursive receipt chain exposes the first pre-root and last post-root.
This is the abstract theorem behind recursive epoch proof aggregation. -/
theorem chain_bridge_nonempty
    {xs : List Segment}
    (hne : xs ≠ [])
    (_hchain : Chains xs) :
    ∃ first last, first ∈ xs ∧ last ∈ xs ∧
      first.preRoot = FirstPre xs ∧ last.postRoot = LastPost xs := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x rest =>
    have ⟨s, hs, he⟩ := lastPost_mem (x :: rest) (List.cons_ne_nil _ _)
    exact ⟨x, s, List.Mem.head _, hs, rfl, he⟩

/-- If every segment binds the expected program and schedule hashes, then any
segment chosen from the aggregate receipt binds the same public proof metadata. -/
theorem aggregate_metadata_binding
    {expectedProgram expectedSchedule : Nat}
    {xs : List Segment}
    (hall : AllSegmentsValid expectedProgram expectedSchedule xs)
    {s : Segment}
    (hs : s ∈ xs) :
    s.journalHash = expectedProgram ∧ s.metadataHash = expectedSchedule := by
  exact hall s hs

inductive ProofKind where
  | deterministicReplay
  | risc0Zkvm
  | sp1Zkvm
  | teeAttestation
  | recursiveEpoch
deriving DecidableEq

def IsZkKind : ProofKind → Prop
  | ProofKind.risc0Zkvm => True
  | ProofKind.sp1Zkvm => True
  | _ => False

structure HeaderBinding where
  chainId : Nat
  height : Nat
  preRoot : Nat
  postRoot : Nat
  txRoot : Nat
  evidenceRoot : Nat
  bodyRoot : Nat
  proofJournalHash : Nat
deriving DecidableEq

structure ProofMetadata where
  chainId : Nat
  height : Nat
  kind : ProofKind
  programId : Nat
  verifierId : Nat
  proofCommitment : Nat
  publicInputHash : Nat
  journalHash : Nat
  preRoot : Nat
  postRoot : Nat
  txRoot : Nat
  evidenceRoot : Nat
  bodyRoot : Nat
  conflictScheduleHash : Nat
  featureSuiteHash : Nat
  dependencyLockHash : Nat
  teeMeasurementHash : Nat
  childReceiptsRoot : Nat
deriving DecidableEq

/-
`metadataDigest` abstracts the canonical hash of proof metadata. Any theorem
that derives equality of full metadata values from equal digests names digest
injectivity explicitly. In the runtime, that obligation is hash collision
resistance plus canonical serialization.
-/
def MetadataHeaderBinding
    (metadataDigest : ProofMetadata → Nat)
    (metadata : ProofMetadata)
    (header : HeaderBinding) : Prop :=
  metadata.chainId = header.chainId ∧
  metadata.height = header.height ∧
  metadata.preRoot = header.preRoot ∧
  metadata.postRoot = header.postRoot ∧
  metadata.txRoot = header.txRoot ∧
  metadata.evidenceRoot = header.evidenceRoot ∧
  metadata.bodyRoot = header.bodyRoot ∧
  metadataDigest metadata = header.proofJournalHash

def TeeMeasurementOk (metadata : ProofMetadata) : Prop :=
  if metadata.kind = ProofKind.teeAttestation then
    metadata.teeMeasurementHash ≠ 0
  else
    metadata.teeMeasurementHash = 0

def RecursiveChildRootOk (metadata : ProofMetadata) : Prop :=
  if metadata.kind = ProofKind.recursiveEpoch then
    metadata.childReceiptsRoot ≠ 0
  else
    metadata.childReceiptsRoot = 0

def ZkProgramVerifierOk (metadata : ProofMetadata) : Prop :=
  IsZkKind metadata.kind → metadata.programId ≠ metadata.verifierId

def ProofMetadataAccepted
    (metadataDigest : ProofMetadata → Nat)
    (metadata : ProofMetadata)
    (header : HeaderBinding) : Prop :=
  metadata.proofCommitment ≠ 0 ∧
  MetadataHeaderBinding metadataDigest metadata header ∧
  TeeMeasurementOk metadata ∧
  RecursiveChildRootOk metadata ∧
  ZkProgramVerifierOk metadata

theorem accepted_metadata_header_binding
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (haccept : ProofMetadataAccepted metadataDigest metadata header) :
    MetadataHeaderBinding metadataDigest metadata header := by
  exact haccept.2.1

theorem header_binding_chain_id_matches
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (hbind : MetadataHeaderBinding metadataDigest metadata header) :
    metadata.chainId = header.chainId := by
  exact hbind.1

theorem header_binding_height_matches
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (hbind : MetadataHeaderBinding metadataDigest metadata header) :
    metadata.height = header.height := by
  exact hbind.2.1

theorem header_binding_pre_root_matches
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (hbind : MetadataHeaderBinding metadataDigest metadata header) :
    metadata.preRoot = header.preRoot := by
  exact hbind.2.2.1

theorem header_binding_post_root_matches
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (hbind : MetadataHeaderBinding metadataDigest metadata header) :
    metadata.postRoot = header.postRoot := by
  exact hbind.2.2.2.1

theorem header_binding_tx_root_matches
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (hbind : MetadataHeaderBinding metadataDigest metadata header) :
    metadata.txRoot = header.txRoot := by
  exact hbind.2.2.2.2.1

theorem header_binding_evidence_root_matches
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (hbind : MetadataHeaderBinding metadataDigest metadata header) :
    metadata.evidenceRoot = header.evidenceRoot := by
  exact hbind.2.2.2.2.2.1

theorem header_binding_body_root_matches
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (hbind : MetadataHeaderBinding metadataDigest metadata header) :
    metadata.bodyRoot = header.bodyRoot := by
  exact hbind.2.2.2.2.2.2.1

theorem header_binding_digest_matches
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (hbind : MetadataHeaderBinding metadataDigest metadata header) :
    metadataDigest metadata = header.proofJournalHash := by
  exact hbind.2.2.2.2.2.2.2

theorem accepted_metadata_binds_header_roots
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (haccept : ProofMetadataAccepted metadataDigest metadata header) :
    metadata.preRoot = header.preRoot ∧
    metadata.postRoot = header.postRoot ∧
    metadata.txRoot = header.txRoot ∧
    metadata.evidenceRoot = header.evidenceRoot ∧
    metadata.bodyRoot = header.bodyRoot := by
  have hbind := accepted_metadata_header_binding haccept
  exact ⟨
    header_binding_pre_root_matches hbind,
    header_binding_post_root_matches hbind,
    header_binding_tx_root_matches hbind,
    header_binding_evidence_root_matches hbind,
    header_binding_body_root_matches hbind
  ⟩

theorem accepted_metadata_digest_matches_header
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (haccept : ProofMetadataAccepted metadataDigest metadata header) :
    metadataDigest metadata = header.proofJournalHash := by
  exact header_binding_digest_matches (accepted_metadata_header_binding haccept)

theorem accepted_tee_requires_measurement
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (haccept : ProofMetadataAccepted metadataDigest metadata header)
    (hkind : metadata.kind = ProofKind.teeAttestation) :
    metadata.teeMeasurementHash ≠ 0 := by
  have htee := haccept.2.2.1
  simp [TeeMeasurementOk, hkind] at htee
  exact htee

theorem accepted_non_tee_measurement_zero
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (haccept : ProofMetadataAccepted metadataDigest metadata header)
    (hkind : metadata.kind ≠ ProofKind.teeAttestation) :
    metadata.teeMeasurementHash = 0 := by
  have htee := haccept.2.2.1
  simp [TeeMeasurementOk, hkind] at htee
  exact htee

theorem accepted_recursive_requires_child_root
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (haccept : ProofMetadataAccepted metadataDigest metadata header)
    (hkind : metadata.kind = ProofKind.recursiveEpoch) :
    metadata.childReceiptsRoot ≠ 0 := by
  have hrec := haccept.2.2.2.1
  simp [RecursiveChildRootOk, hkind] at hrec
  exact hrec

theorem accepted_non_recursive_child_root_zero
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (haccept : ProofMetadataAccepted metadataDigest metadata header)
    (hkind : metadata.kind ≠ ProofKind.recursiveEpoch) :
    metadata.childReceiptsRoot = 0 := by
  have hrec := haccept.2.2.2.1
  simp [RecursiveChildRootOk, hkind] at hrec
  exact hrec

theorem accepted_zk_program_verifier_distinct
    {metadataDigest : ProofMetadata → Nat}
    {metadata : ProofMetadata}
    {header : HeaderBinding}
    (haccept : ProofMetadataAccepted metadataDigest metadata header)
    (hzk : IsZkKind metadata.kind) :
    metadata.programId ≠ metadata.verifierId := by
  exact haccept.2.2.2.2 hzk

theorem bound_metadata_unique_under_digest_injective
    {metadataDigest : ProofMetadata → Nat}
    (hdigestInjective : ∀ a b, metadataDigest a = metadataDigest b → a = b)
    {a b : ProofMetadata}
    {header : HeaderBinding}
    (ha : MetadataHeaderBinding metadataDigest a header)
    (hb : MetadataHeaderBinding metadataDigest b header) :
    a = b := by
  apply hdigestInjective
  exact (header_binding_digest_matches ha).trans (header_binding_digest_matches hb).symm

theorem accepted_metadata_unique_under_digest_injective
    {metadataDigest : ProofMetadata → Nat}
    (hdigestInjective : ∀ a b, metadataDigest a = metadataDigest b → a = b)
    {a b : ProofMetadata}
    {header : HeaderBinding}
    (ha : ProofMetadataAccepted metadataDigest a header)
    (hb : ProofMetadataAccepted metadataDigest b header) :
    a = b := by
  exact bound_metadata_unique_under_digest_injective
    hdigestInjective ha.2.1 hb.2.1

structure BoundSegment where
  metadata : ProofMetadata
  header : HeaderBinding

def BoundSegment.toSegment (s : BoundSegment) : Segment :=
  {
    preRoot := s.header.preRoot
    postRoot := s.header.postRoot
    journalHash := s.header.proofJournalHash
    metadataHash := s.metadata.proofCommitment
  }

def BoundSegmentAccepted
    (metadataDigest : ProofMetadata → Nat)
    (s : BoundSegment) : Prop :=
  ProofMetadataAccepted metadataDigest s.metadata s.header

def BoundSegmentsAccepted
    (metadataDigest : ProofMetadata → Nat)
    (xs : List BoundSegment) : Prop :=
  ∀ s ∈ xs, BoundSegmentAccepted metadataDigest s

def BoundSegmentsChain (xs : List BoundSegment) : Prop :=
  Chains (xs.map BoundSegment.toSegment)

theorem bound_segment_accepted_roots_match
    {metadataDigest : ProofMetadata → Nat}
    {s : BoundSegment}
    (haccept : BoundSegmentAccepted metadataDigest s) :
    s.metadata.preRoot = (BoundSegment.toSegment s).preRoot ∧
    s.metadata.postRoot = (BoundSegment.toSegment s).postRoot := by
  have hbind := accepted_metadata_header_binding haccept
  exact ⟨
    header_binding_pre_root_matches hbind,
    header_binding_post_root_matches hbind
  ⟩

theorem accepted_bound_chain_bridge_nonempty
    {metadataDigest : ProofMetadata → Nat}
    {xs : List BoundSegment}
    (hne : xs ≠ [])
    (hchain : BoundSegmentsChain xs)
    (haccepted : BoundSegmentsAccepted metadataDigest xs) :
    ∃ first last, first ∈ xs ∧ last ∈ xs ∧
      BoundSegmentAccepted metadataDigest first ∧
      BoundSegmentAccepted metadataDigest last ∧
      first.metadata.preRoot = FirstPre (xs.map BoundSegment.toSegment) ∧
      last.metadata.postRoot = LastPost (xs.map BoundSegment.toSegment) := by
  have hmap_ne : xs.map BoundSegment.toSegment ≠ [] := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  rcases chain_bridge_nonempty hmap_ne hchain with
    ⟨firstSeg, lastSeg, hfirstMem, hlastMem, hfirstRoot, hlastRoot⟩
  rcases List.mem_map.mp hfirstMem with ⟨first, hfirstIn, hfirstEq⟩
  rcases List.mem_map.mp hlastMem with ⟨last, hlastIn, hlastEq⟩
  have hfirstAccepted := haccepted first hfirstIn
  have hlastAccepted := haccepted last hlastIn
  have hfirstRoots := bound_segment_accepted_roots_match hfirstAccepted
  have hlastRoots := bound_segment_accepted_roots_match hlastAccepted
  refine ⟨first, last, hfirstIn, hlastIn, hfirstAccepted, hlastAccepted, ?_, ?_⟩
  · exact hfirstRoots.1.trans (hfirstEq.symm ▸ hfirstRoot)
  · exact hlastRoots.2.trans (hlastEq.symm ▸ hlastRoot)

structure Chunk (Key State : Type) where
  touched : List Key
  step : State → State

def DisjointChunks (xs : List (Chunk Key State)) : Prop :=
  xs.Pairwise (fun a b => ∀ k, k ∈ a.touched → k ∈ b.touched → False)

def Commutes (a b : Chunk Key State) : Prop :=
  ∀ st, a.step (b.step st) = b.step (a.step st)

def PairwiseCommutes (xs : List (Chunk Key State)) : Prop :=
  xs.Pairwise Commutes

def ApplyChunks : List (Chunk Key State) → State → State
  | [], st => st
  | c :: rest, st => ApplyChunks rest (c.step st)

/-- `Commutes` is symmetric. -/
private theorem commutes_symm {Key State : Type} {a b : Chunk Key State}
    (h : Commutes a b) : Commutes b a :=
  fun st => (h st).symm

/-- Pairwise-commuting proof chunks may be reordered without changing the final
state. This is the core confluence theorem for ZenoLedger scheduled shard proofs. -/
theorem apply_chunks_perm_invariant
    {Key State : Type}
    {xs ys : List (Chunk Key State)}
    (hperm : xs.Perm ys)
    (hcomm : PairwiseCommutes xs)
    (st : State) :
    ApplyChunks xs st = ApplyChunks ys st := by
  revert st
  induction hperm with
  | nil => intro st; rfl
  | cons x _ ih =>
    intro st
    simp only [ApplyChunks]
    exact ih (List.pairwise_cons.mp hcomm).2 (x.step st)
  | swap x y _ =>
    intro st
    simp only [ApplyChunks]
    have hc := (List.pairwise_cons.mp hcomm).1 x (List.Mem.head _)
    congr 1
    exact (hc st).symm
  | trans h1 _ ih1 ih2 =>
    intro st
    have hcomm2 : PairwiseCommutes _ := h1.pairwise hcomm (fun h => commutes_symm h)
    exact (ih1 hcomm st).trans (ih2 hcomm2 st)

end ZenoDEX.ZenoLedgerZkTeeProofComposition
