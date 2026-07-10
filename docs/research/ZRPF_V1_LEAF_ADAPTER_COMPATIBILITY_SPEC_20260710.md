# ZRPF V1 Leaf Adapter Compatibility Specification

Date: 2026-07-10

Status: pure Spot mapping and receipt-authenticated guest implemented; four
temporary-path Succinct adapter receipts feed a verified structural proof tree

## Purpose

This specification defines the compatibility bridge from the current
ZenoDEX RISC0 V1 Spot transition journal to a ZRPF `NodeJournalV3` leaf. It
preserves the authenticated V1 statement and opaque commitment meanings while
making missing V1 facts explicit.

The implemented function is:

```text
project_policy_bound_v1_journal(
  source_kind,
  exact_source_journal_bytes,
  assigned_leaf_ordinal,
  expected_adapter_image_id
) -> SourceBindingV3 + NodeJournalV3
```

It is a pure mapping. It accepts exact journal bytes and does not authenticate
them. Receipt authority begins only after a RISC0 guest verifies the governed
source image and those exact bytes.

## Compile-Time Source Policy

The initial source policy contains one source:

| Field | Pinned value |
| --- | --- |
| source kind | `spot` |
| proof type | `risc0.zenodex_recursive_spot_leaf.v1` |
| proof profile | `recursive_spot_leaf_v1` |
| lane kind | `spot` |
| image ID | `1275ef413f6513e7671bce019d22fbdcf10bffe1b71dcf68731a056e710a7403` |
| program SHA-256 | `d1fd8915a3c1650b42527e6b878f203679cd447b506916c6a9a56008ed0951a8` |
| local source-tree root | `7a3bed2a1d8fff3ad2e93f2d406df435a9990d1a9c0462ff3323fb028327564e` |

The local source-tree root is compatibility provenance. It does not establish
release provenance, whole-build isolation, or cross-host reproducibility.

`config/proof_profiles/zrpf_v1_leaf_adapter_source_policy_v1.json` is checked
against the source-pinned recursive rebuild reference and the Rust constants by
`tools/check_zrpf_v1_leaf_adapter_source_policy.py`. The checker rejects
duplicate JSON keys, unknown policy fields, image-word substitution, reference
hash drift, and receipt-authority promotion.

## Exact Source Boundary

The pure mapping enforces:

```text
1 <= source_journal_bytes.len <= 4,096
exact Postcard decode consumes every byte
canonical Postcard re-encoding equals the input
RecursiveEffectSummaryV1 shape validation succeeds
image ID, proof profile, and lane kind equal the static policy
accepted receipt IDs, rejected receipt IDs, outbox, and inbox are empty
assigned_leaf_ordinal + 1 does not overflow
expected_adapter_image_id is nonzero
```

The implemented receipt-authenticated guest executes:

```text
bounded envelope decode
  -> select compile-time source policy
  -> env::verify(policy.image_id, exact_source_journal_bytes)
  -> exact source-journal decode
  -> pure compatibility mapping
  -> commit exact canonical NodeJournalV3 bytes
```

Decoding before receipt verification is forbidden in the authority-bearing
guest. The pure mapping remains separately testable and deterministic.

`expected_adapter_image_id` is a host-proposed private input because a RISC0
guest cannot derive its own receipt image ID without a circular build. The guest
commits this value. Every outer consumer must verify the adapter receipt under
the governed adapter image and require:

```text
NodeJournalV3.actual_program_id
  == program ID bytes of the image used for Receipt::verify
```

`VerifiedNodeReceiptV3` makes this order a construction rule. Its fields are
private. It verifies the Succinct receipt, exact journal, and program equality,
then derives the RISC0 claim binding locally and exposes the child descriptor.
A proof-bearing negative control confirms that a valid receipt with a false
nonzero self-label is rejected at this outer equality check.

## Source Binding

`SourceBindingV3` commits:

```text
source_protocol_id
source_program_id
source_profile_id
source_verifier_id
source_manifest_root
source_claim_hash
source_journal_hash
source_statement_hash
source_effect_hash
source_scope_hash
source_lane_id_hash
```

The source claim and journal hashes use the existing V1 functions. The source
effect hash is `recursive_effect_summary_hash_v1`. The source program ID uses
the canonical RISC0 digest byte order: each `[u32; 8]` word contributes its
little-endian bytes to `ProgramIdV3`. A fixed test pins the current Spot vector.

The V3 leaf commits the singleton source-binding hash in both
`provenance_root` and the profile-specific `semantic_source_set_root`. Distinct
domains keep the two meanings separate.

## Adapter Manifest Identity

The compatibility `program_manifest_root` is:

```text
H_framed(
  "zenodex.zrpf.v1_adapter_manifest.v1",
  adapter_program_id,
  adapter_profile_id,
  "unreleased_compatibility_manifest"
)
```

It is deliberately independent of source-provided dependency and toolchain
locks. Those locks remain in `SourceBindingV3`. A metamorphic test changes both
source lock values and requires the source binding and node statement to change
while the adapter manifest identity stays fixed. This compatibility commitment
does not establish a release manifest, source closure, ELF provenance, or
cross-host reproducibility.

## Count Semantics

V1 Spot summaries do not expose the number of transactions inside the proved
transition. The adapter therefore emits:

```text
operation_count = 1
count_unit_id    = H("source_transition_receipt")
```

This means one compatibility transition receipt. It makes no transaction-count
claim. `NodeJournalV3::new_aggregate` rejects children with different count
unit IDs before adding their counts.

## Commitment Disposition

| `NodeCommitmentsV3` field | Compatibility derivation | Claim status |
| --- | --- | --- |
| `pre_state_vector_root` | V1 singleton lane-vector root over lane and pre-state | derived |
| `post_state_vector_root` | V1 singleton lane-vector root over lane and post-state | derived |
| `input_root` | V1 verification-claim hash over source image and exact journal | derived |
| `transaction_root` | authenticated V1 `tx_root` | opaque V1 meaning |
| `evidence_root` | authenticated V1 `evidence_root` | opaque V1 meaning |
| `provenance_root` | singleton canonical `SourceBindingV3` hash | derived |
| `receipt_root` | authenticated V1 `receipt_root` | opaque lane-specific meaning |
| `accepted_receipts_root` | authenticated V1 root, required canonical empty | empty-only |
| `rejected_receipts_root` | authenticated V1 root, required canonical empty | empty-only |
| `effect_root` | V1 recursive effect-summary hash | derived |
| `write_set_root` | authenticated V1 coarse write commitment | whole-lane scheduling only |
| `asset_delta_root` | authenticated V1 asset-delta commitment | opaque without rows |
| `cross_lane_outbox_root` | authenticated V1 root, required canonical empty | empty-only |
| `cross_lane_inbox_root` | authenticated V1 root, required canonical empty | empty-only |
| `cross_lane_message_ids_root` | canonical V1 empty message-ID root | empty-only |
| `conflict_schedule_hash` | singleton task, partition, V1 write root, statement | derived compatibility schedule |
| `data_availability_root` | source-journal payload commitment | payload binding only |
| `data_availability_certificate_root` | source-bound unsupported sentinel | no DA-certificate claim |
| `carry_queue_pre_root` | source-bound unsupported sentinel | no carry claim |
| `carry_queue_post_root` | distinct source-bound unsupported sentinel | no carry claim |
| `task_set_root` | singleton task-ID root | derived |
| `semantic_source_set_root` | singleton source-binding root | derived |
| `partition_plan_root` | singleton task and assigned half-open partition | derived |

The unsupported sentinels are nonzero, field-specific, source-bound
commitments. They cannot be confused with a canonical empty certificate or an
empty carry queue. Any admission profile requiring those facts must reject this
compatibility leaf.

## Identity And Partition Rules

The task ID binds source scope, claim, statement, lane, and profile. It excludes
the assigned ordinal, so wrapping the same source receipt at two positions
produces the same task ID and is rejected as a duplicate by an aggregate.

The partition is:

```text
[assigned_leaf_ordinal, assigned_leaf_ordinal + 1)
```

The partition plan and node statement bind the assignment. Reassigning the
same source changes the partition plan, node statement, and journal hash while
preserving task identity.

## Implemented Evidence

The pure mapping tests cover:

- current pinned Spot image/profile/lane acceptance;
- exact RISC0 word-to-digest conversion;
- all 23 mandatory nonzero commitment fields;
- exact direct V1 commitment mappings and singleton lane-state roots;
- wrong image, profile, lane, and summary-test profile rejection;
- nonempty undisclosed receipt and message root rejection;
- empty, oversized, trailing, and nonminimal source-byte rejection;
- ordinal overflow and zero adapter-image rejection;
- task identity stability across partition assignment;
- statement mutation changing source binding, task, provenance, and node
  statement;
- source-policy/reference/Rust-constant parity and negative policy tests.
- an independent Python reconstruction of the V1 source Postcard, V1 claim and
  journal hashes, source binding, task ID, all commitments, node statement, V3
  journal hash, and V3 Postcard bytes, cross-checked against fixed Rust vectors.

The receipt-authenticated evidence additionally covers:

- four Succinct adapter receipts under temporary-path image
  `71f282b5517fc6108988c1cc9b4601807a40ae331c0e0f0f5505d12b241e5574`;
- strict replay of the persisted receipt through `VerifiedNodeReceiptV3`;
- source artifact duplicate-field, unknown-field, canonical-byte, complete
  metadata, and receipt-security-profile checks;
- rejection when the source assumption is omitted;
- rejection when one exact source-journal byte is substituted while retaining
  the original receipt assumption;
- outer rejection of a cryptographically valid adapter receipt whose journal
  carries a false nonzero adapter program label;
- authenticated inclusion of all four adapter receipts in two level-one
  structural receipts and one level-two structural root receipt.

Receipt proof bytes are not deterministic across proving runs. Evidence pins
the exact receipt instance used by its SHA-256 digest.

The structural tree uses level-one image
`4272be5165f65e29cb134f815d6c6fc40d7f492979f596082cac10c3f0d43c2b`
and level-two image
`3b858d113cb155b2946e1c733fdf5fe5592b6bf46c903d0a3cfb322099845736`.
Its root journal hash is
`2089ecc187077d4b719c8539076651753c1ead1415724c9bc788758bddfa3768`,
and the exact persisted root receipt SHA-256 is
`021af13025e7dc7c40e06d689ad30e3194e58793435cd11ae07d684c80ddfd33`.

## Non-Claims

This phase establishes no claim of:

- source witness privacy;
- an underlying Spot transaction count;
- nonempty receipt or cross-lane-message disclosure;
- exact read/write key disclosure or a multi-leaf conflict-free schedule;
- durable data availability or a valid DA certificate;
- carry-queue continuity;
- asset-delta-row conservation from the summary alone;
- native V3 semantic aggregation or a semantic receipt-authenticated proof
  tree;
- a release-backed adapter image, public replay, cross-host reproducibility,
  settlement, ledger admission, or production readiness.

`RS-CBC-016` and `RS-CBC-022` are `implemented_partial` for this bounded Spot
adapter and two-level structural profile. Governed release admission remains
open. `RS-CBC-023` remains pending until a separate semantic profile recomputes
parent commitments and enforces provenance, conservation, descendant
uniqueness, scheduling, carry, and DA policy.
