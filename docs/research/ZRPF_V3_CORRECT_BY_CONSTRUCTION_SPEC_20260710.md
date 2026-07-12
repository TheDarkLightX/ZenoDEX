# ZRPF V3 Correct-by-Construction Protocol Specification

Date: 2026-07-10

Status: bounded structural ABI, temporary-path two-level RISC0 structural proof
tree, and current hardened same-host retained-receipt replay implemented;
semantic and release authority pending

## Claim Scope

This document specifies the current Zeno Recursive Proof Fabric (ZRPF) V3
common-node candidate for ZenoDEX. The implemented slice is a proof-system-
neutral `no_std` library. It provides typed commitments, strict canonical
decoding, a shared leaf-and-aggregate journal shape, derived verifier IDs,
canonical child ordering, dense partition rules, and a bounded 8-by-8 tree.

The existing `RecursiveNodeJournalV2` remains the authenticated output of the
source-pinned, fixed-height RISC0 evidence lane. Its bytes, hash domains, image
IDs, and evidence records remain immutable. V3 is additive:

```text
RecursiveEffectSummaryV1          fixed-height migration leaf
RecursiveNodeJournalV2            fixed-height aggregate evidence
NodeJournalV3                     bounded common-node candidate
```

The V3 protocol library validates protocol structure. Receipt authentication
belongs to a proof-system adapter. The additive `zk/zrpf_risc0` workspace now
implements a pure, policy-bound Spot V1 journal projection, a receipt-
authenticated adapter guest, a sealed host verifier, and two bounded structural
aggregate guests. The level-one guest accepts adapter receipts. The level-two
guest accepts level-one receipts. Each guest verifies every exact child receipt
under a compile-time image before decoding the child journal and deriving the
parent `NodeJournalV3`.

The structural profile derives field-specific roots over authenticated child
commitments. It does not verify the ZenoDEX meaning of those commitments.
Native V3 leaves and a separate semantic aggregate profile must establish
conservation, receipt-set, message, schedule, carry, and data-availability
properties.

Passing the current gates supports this claim:

```text
bounded V3 common-node journal plus one temporary-path four-leaf, two-level
receipt-authenticated structural Succinct proof tree and one current-source
same-host exact retained-receipt verifier replay implemented and locally
verified
```

This evidence supports computational-integrity claims for the exact structural
profile, recorded temporary images, and exact retained receipt bytes. It
supports no proof-generation provenance, guest source-to-image, semantic,
settlement, ledger-admission, reproducible-release, public-replay promotion, or
production claim.

## Design Method

Each proof lane is reviewed through four artifacts:

1. information-flow topology;
2. external interfaces;
3. falsifiable security properties;
4. concrete resource bounds.

This structure is informed by
[Principled Design and Analysis of Zero-Knowledge Protocols for Intent-Centric Private State Machines](https://medium.com/@gwrx2005/principled-design-and-analysis-of-zero-knowledge-protocols-for-intent-centric-private-state-99632c60a898).
The article is design input. Executable checkers, proofs, tests, pinned
manifests, and governed admission rules decide ZRPF claims.

## Information-Flow Topology

| Fact | Prover | Aggregate guest | Host verifier | Ledger admission | Public observer |
| --- | --- | --- | --- | --- | --- |
| source transition witness | supplies to source guest | does not receive | does not receive | does not receive | does not receive |
| child journal bytes | supplies | verifies receipt, then decodes | verifies exact bytes | checks governed bindings | profile-dependent |
| receipt bytes | creates | receives as an assumption | verifies | consumes verified fact | profile-dependent |
| scope and policy roots | proposes | checks equality | checks expectations | checks governed values | public |
| semantic disclosures | absent from current structural profile | unavailable | checks journal binding only | unsupported | unavailable |
| child commitment fields | supplies through authenticated journal | derives field-specific parent roots | checks exact parent journal | unsupported | profile-dependent |
| proof size and timing | observes | observable | observes | may log a bounded class | metadata leakage |
| origin and cadence | observes | outside relation | outside relation | outside relation | metadata leakage |

Current RISC0 evidence establishes computational integrity only within its
recorded scope. It establishes no witness-privacy or system-privacy claim.
Privacy profiles require a network adversary model, a leakage budget, and tests
for timing, size, error-shape, and request-correlation channels.

## Implemented Interfaces

The workspace `zk/zrpf_protocol` currently defines:

```text
ApplicationIdV3
DomainIdV3
TaskIdV3
ProgramIdV3
ProfileIdV3
VerifierIdV3
CommitmentV3
NodeScopeV3
NodeCommitmentsV3
PartitionV3
NodeJournalV3
ProjectedChildDescriptorV3
LeafNodeInputV3
AggregateNodeInputV3
```

All identifiers and commitments reject the all-zero value. Construction inputs
use named fields. Validated fields are private. `NodeJournalV3` can be decoded
from Postcard or diagnostic JSON only through validation.

Decoded structural validity carries no proof authority. Public deserialization
and `ProjectedChildDescriptorV3::project_canonical_journal` do not verify a
receipt. The sealed `VerifiedNodeReceiptV3` boundary owns that seam for the
current RISC0 profile. It verifies a Succinct receipt under the expected image,
requires the exact compiled RISC0 3.0.5 verifier-parameter digest, Poseidon2
hash suite, control ID, and metadata equality, and verifies through an explicit
dev-mode-disabled context containing only that hash suite. It then
strict-decodes the exact journal, enforces journal program-image equality, and
derives the claim binding locally before exposing a descriptor. Receipt
security profile identity remains separate from the node computation profile.
Every public constructor for `VerifiedNodeReceiptV3` accepts bounded canonical
receipt bytes. Fresh prover outputs serialize through the exactly pinned JSON
codec and cross that same boundary. The 16 MiB pre-decode cap and exact typed
JSON round-trip equality reject duplicate, unknown, and noncanonical fields
before proof verification.

The RISC0 workspace additionally defines:

```text
V1LeafAdapterInputV1
VerifiedNodeReceiptV3
StructuralAggregateInputV1
StructuralAggregatePolicyV1
StructuralAggregateProjectionV1
```

Its bounded structural method graph is:

```text
Spot V1 receipt
  -> V1 adapter image
  -> NodeJournalV3 leaf
  -> level-one structural image
  -> NodeJournalV3 aggregate
  -> level-two structural image
  -> NodeJournalV3 root
```

## Implemented Profile Bounds

The compiled V3 candidate enforces:

```text
MAX_IMMEDIATE_CHILDREN_V3       = 8
MAX_NODE_LEVEL_V3              = 2
MAX_LEAF_COUNT_V3              = 64
MAX_SUBTREE_NODE_COUNT_V3      = 73
MAX_OPERATIONS_PER_LEAF_V3     = 128
MAX_OPERATIONS_PER_ROOT_V3     = 8,192
MAX_NODE_JOURNAL_BYTES_V3      = 4,096
```

The architecture describes a future ceiling of fanout 16, depth 4, and 65,536
leaves. Those values are unimplemented and carry no present capacity claim.
Profile-selected limits and a scale profile require separate governed policy,
benchmarks, and security evidence.

These bounds describe construction capacity. They are not TPS, latency, proof-
size, or proving-cost measurements.

## Node Scope

`NodeScopeV3` binds the replay domain shared by an aggregate and all immediate
children:

```text
NodeScopeV3 {
  application_id
  chain_or_domain_id
  epoch_start
  epoch_end
  public_policy_hash
  feature_suite_hash
  dependency_lock_hash
  toolchain_lock_hash
}
```

The epoch interval is inclusive and must satisfy `epoch_start <= epoch_end`.
The aggregate constructor requires every child scope hash to equal its parent
scope hash. This closes structural cross-application, cross-domain, cross-epoch,
and policy relabeling at the common-node boundary. A governed verifier must
still provide the expected scope independently.

## ZenoDEX Commitment Surface

`NodeCommitmentsV3` contains named, mandatory nonzero roots:

```text
pre_state_vector_root
post_state_vector_root
input_root
transaction_root
evidence_root
provenance_root
receipt_root
accepted_receipts_root
rejected_receipts_root
effect_root
write_set_root
asset_delta_root
cross_lane_outbox_root
cross_lane_inbox_root
cross_lane_message_ids_root
conflict_schedule_hash
data_availability_root
data_availability_certificate_root
carry_queue_pre_root
carry_queue_post_root
task_set_root
semantic_source_set_root
partition_plan_root
```

Canonical nonzero empty-set hashes represent empty sets. Zero never means
"unused." Every ZenoDEX profile must define each root's empty value and
composition rule.

`provenance_root` binds the disclosures that justify a leaf projection, such
as an authenticated source receipt, source program, source profile, exact
source journal, and source statement. The structural crate treats that root as
opaque. A receipt adapter must derive it from a versioned source-binding object.

The reference constructor accepts these roots as structural claims. It does not
prove conservation, receipt-set uniqueness, message cancellation, conflict
freedom, data availability, or carry semantics. Leaf adapters must derive their
singleton and effect roots from the verified source transition. Aggregate
guests must verify disclosures or certificates and recompute parent roots.

## Common Node Journal

The serialized journal has this normative field order:

```text
NodeJournalV3 {
  journal_version
  task_id
  node_kind                       // leaf | aggregate
  node_level
  partition
  immediate_child_count
  leaf_count
  operation_count
  count_unit_id
  subtree_node_count

  scope
  proof_profile_id
  actual_program_id
  verifier_id                     // derived, never caller-selected
  node_statement_hash
  program_manifest_root
  commitments

  child_tasks_root
  child_claims_root
  child_journals_root
  child_programs_root
  child_profiles_root
  child_verifiers_root            // ordered sequence, multiplicity preserved
  immediate_verifier_set_root     // sorted unique set
  child_statements_root
  child_manifests_root
  child_effects_root
  child_provenance_roots
  child_data_availability_roots
}
```

`verifier_id` is derived from the domain-separated tuple
`(actual_program_id, proof_profile_id, journal_version)`. Decoding rejects any
independently supplied verifier ID that differs from this derivation.

`count_unit_id` is a nonzero domain-separated identifier for the meaning of
`operation_count`. An aggregate constructor accepts only children whose count
unit equals the parent count unit, so it cannot add transaction counts to
transition-receipt counts or any other unlike quantities.

The unique `immediate_verifier_set_root` commits the actual child verifier set.
It does not authorize that set. A governed program manifest or admission policy
must independently provide the allowed verifier set.

### Leaf construction

A leaf constructor derives:

```text
node_kind              = leaf
node_level             = 0
immediate_child_count  = 0
leaf_count             = 1
subtree_node_count     = 1
```

Its partition width is one, its operation count is in `1..=128`, and every
child root equals the domain-separated canonical empty-list root. The selected
proof profile must define the count-unit semantics and any stricter cap.

### Aggregate construction

An aggregate constructor derives:

- parent level from `child_level + 1`;
- parent partition from the first and last canonical child partitions;
- leaf, operation, and subtree-node counts with checked arithmetic after count-
  unit equality succeeds;
- all twelve child roots from canonical children;
- its verifier ID from its own program and profile.

The proof-neutral reference constructor permits a caller to supply the
aggregate statement, manifest, and ZenoDEX commitment claims. The implemented
RISC0 structural composer instead derives its statement, compatibility
manifest, and all 23 parent commitments as field-specific roots over the
authenticated child journals. A future semantic aggregate profile must verify
the application meaning of those commitments before journal commitment.

The structural request supplies the aggregate guest's expected self image ID
because a guest cannot derive its own image without a circular build. The next
recursive guest or the sealed outer verifier must verify the receipt under the
governed aggregate image and require the journal program ID to equal that image.
Until this equality check succeeds, a structurally valid aggregate journal has
no receipt authority.

## Partition Semantics

`PartitionV3` is a half-open interval of assigned leaf ordinals:

```text
[start, end_exclusive)
```

Its width must equal `leaf_count`. In the implemented dense profile, canonical
children are sorted by `(start, end_exclusive, task_id)` and adjacent ranges
must touch exactly:

```text
next.start == previous.end_exclusive
```

Overlaps and gaps reject. This detects omission inside the supplied parent
range. A governed expected range and `partition_plan_root` remain necessary to
detect omitted leading or trailing work.

## Child Descriptor

`ProjectedChildDescriptorV3` is a private-field projection derived from exact canonical
journal bytes:

```text
ProjectedChildDescriptorV3 {
  child_task_id
  child_kind
  child_level
  partition
  leaf_count
  operation_count
  count_unit_id
  subtree_node_count
  child_profile_id
  child_program_id
  child_verifier_id
  child_claim_hash
  child_journal_hash
  child_node_statement_hash
  child_program_manifest_root
  child_scope_hash
  child_effect_root
  child_provenance_root
  child_data_availability_root
}
```

The descriptor cannot be directly deserialized. Metadata copies are derived
locally from strict-decoded journal bytes. The `child_claim_hash` remains an
untrusted input until `VerifiedNodeReceiptV3` or an aggregate guest verifies
that the exact receipt claim authenticates the exact journal bytes.

Immediate child construction rejects:

- empty or fanout-plus-one child sets;
- duplicate task IDs, claim hashes, or journal hashes;
- a parent task ID reused by a child;
- mixed child levels;
- mixed operation-count units;
- scope mismatch;
- partition overlap or gaps;
- count overflow or impossible level/count combinations;
- depth, leaf, subtree-node, operation, or byte limit violations.

Heterogeneous child profiles are allowed and committed. Their authorization is
a governed verifier-policy decision. Equivalent child permutations produce the
same parent.

## Hashing And Encoding

Manual protocol hashes are independent from the transport codec. Each hash
starts with:

```text
u16_be(domain_length) || domain_bytes
```

Integers in manual hashes use fixed-width big-endian encoding. List roots add a
`u32_be` element count followed by fixed 32-byte elements. The journal hash
follows the normative field order above. It expands all `NodeScopeV3` and
`NodeCommitmentsV3` fields inline in their documented order. It does not insert
the nested objects' canonical hashes. The commitments hash follows the exact
commitment-surface order in this specification.

| Object | Exact domain string |
| --- | --- |
| node journal | `zenodex.zrpf.node_journal_hash.v3` |
| node scope | `zenodex.zrpf.node_scope_hash.v3` |
| node commitments | `zenodex.zrpf.node_commitments_hash.v3` |
| verifier ID | `zenodex.zrpf.verifier_id.v3` |
| projected child descriptor | `zenodex.zrpf.child_descriptor_hash.v3` |
| child tasks | `zenodex.zrpf.child_tasks_root.v3` |
| child claims | `zenodex.zrpf.child_claims_root.v3` |
| child journals | `zenodex.zrpf.child_journals_root.v3` |
| child programs | `zenodex.zrpf.child_programs_root.v3` |
| child profiles | `zenodex.zrpf.child_profiles_root.v3` |
| ordered child verifiers | `zenodex.zrpf.child_verifiers_root.v3` |
| immediate verifier set | `zenodex.zrpf.immediate_verifier_set_root.v3` |
| child node statements | `zenodex.zrpf.child_statements_root.v3` |
| child manifests | `zenodex.zrpf.child_manifests_root.v3` |
| child effects | `zenodex.zrpf.child_effects_root.v3` |
| child provenance | `zenodex.zrpf.child_provenance_roots.v3` |
| child data availability | `zenodex.zrpf.child_data_availability_roots.v3` |

Postcard is the internal transport codec. Exact decoding enforces:

- a 4,096-byte cap before decoding;
- no trailing bytes;
- canonical re-encoding equality;
- validation before a `NodeJournalV3` is returned;
- strict unknown-field rejection for diagnostic JSON structs.

The Rust fixture pins a 1,547-byte leaf encoding, its SHA-256 digest, its manual
journal hash, and its canonical commitments hash.
`tools/check_zrpf_v3_hash_vector.py` reconstructs all four values in Python
using `hashlib` and an independent Postcard unsigned-varint encoder.

V1 host request, proof, metadata, structural disclosure, and all three reachable
leaf-generation payload families now have bounded duplicate-key and exact
nested-field guards. They remain outside V3 authority because their source
JSON bytes are not canonical authority objects. `RS-CBC-021` keeps that
canonical-byte boundary pending.

## Security Games And Current Status

| Game | Required acceptance property | Current status |
| --- | --- | --- |
| wrong program | actual program, derived verifier, and governed manifest match | structural derivation implemented; governance pending |
| child substitution | exact verified receipt claim authenticates exact journal bytes | adapter, level-one, and level-two guests pass; release policy pending |
| child omission | task set, expected range, partition plan, and counts are complete | internal gaps reject; external completeness pending |
| partition overlap | assigned leaf ordinals are dense, disjoint, and canonical | constructor implemented and tested; decoded journal remains non-authoritative |
| cross-level child | every child level is exactly parent level minus one | constructor implemented and tested; decoded journal remains non-authoritative |
| domain replay | application, domain, epoch, and policy match governed expectations | child equality implemented; governed expectation pending |
| metadata strengthening | duplicate metadata is derived from authenticated journal bytes | strict Spot artifact parity and structural aggregate derivation implemented; semantic disclosures pending |
| unbalanced effects | disclosed ZenoDEX rows satisfy conservation | pending semantic composer |
| duplicate descendant | descendant tasks, receipts, and messages are unique or cancel by policy | immediate tasks only; descendant evidence pending |
| DA overclaim | a governed DA certificate policy verifies | roots present; verification pending |
| malformed bytes | decoder rejects without panic or excessive allocation | fixed-size journal boundary implemented and tested |
| rejected admission | application, replay, carry, and reward state remain unchanged | pending ledger admission |

Fiat-Shamir construction and zkVM constraint soundness belong to the selected
proof backend and pinned manifest. The structural library provides no claim
about either property.

## Witness-To-Binding Rule

Every private or host-proposed field must have exactly one disposition:

| Disposition | Required action |
| --- | --- |
| checked directly | guest or deterministic verifier enforces the predicate |
| recomputed | guest derives and commits the canonical value |
| proof-authorized | guest verifies the exact receipt claim first |
| irrelevant | specification proves non-interference for the scoped claim |

Any field without a disposition is unconstrained and must be removed or
rejected. The Spot adapter and structural aggregate profile document their
field dispositions. The future semantic aggregate profile must add a
field-by-field semantic disposition before proof generation.

## Evidence

Current reference evidence includes:

- leaf and aggregate constructor checks;
- an in-memory protocol-constructor test of a saturated 64-leaf, 73-node 8-by-8
  structural tree;
- all six permutations of a three-child set;
- overlap, gap, duplicate claim, duplicate journal, duplicate task, mixed
  level, mixed count unit, scope mismatch, fanout-plus-one, and depth-plus-one
  rejection;
- zero commitment, zero operation, operation-cap, count-overflow, and
  impossible-count rejection;
- trailing-byte, oversize, unknown-field, partition-width, and verifier-ID
  tamper rejection;
- heterogeneous child-profile commitment;
- independently replayed manual hash and canonical Postcard-byte fixtures;
- four temporary-path Succinct Spot V1-to-V3 adapter receipts whose exact
  public journals match their independent host projections;
- persisted adapter-receipt replay through the retained pre-hardening sealed
  verifier;
- unit rejection of verifier-parameter, hash-suite, control-ID, and metadata
  mutations before invalid-seal verification;
- bounded canonical persisted-receipt tests covering empty, oversized,
  duplicate-field, unknown-field, and noncanonical JSON;
- missing source assumption and exact source-journal substitution rejection;
- a proof-bearing false adapter self-label that verifies cryptographically and
  is rejected by the outer program-image equality check;
- two Succinct level-one structural receipts, each authenticating two exact
  adapter journals;
- one Succinct level-two structural root authenticating both exact level-one
  journals;
- verifier-only replay that reconstructs both expected level-one journals and
  the expected level-two journal from seven persisted receipts;
- swapped level-one receipt rejection at exact-journal equality;
- a missing level-one child-assumption rejection at the RISC0 assumption
  boundary.

The evidenced method identities are:

| Method | Temporary image ID |
| --- | --- |
| V1 Spot adapter | `71f282b5517fc6108988c1cc9b4601807a40ae331c0e0f0f5505d12b241e5574` |
| structural level one | `4272be5165f65e29cb134f815d6c6fc40d7f492979f596082cac10c3f0d43c2b` |
| structural level two | `3b858d113cb155b2946e1c733fdf5fe5592b6bf46c903d0a3cfb322099845736` |

The level-two root journal hash is
`2089ecc187077d4b719c8539076651753c1ead1415724c9bc788758bddfa3768`.
The exact persisted root receipt SHA-256 is
`021af13025e7dc7c40e06d689ad30e3194e58793435cd11ae07d684c80ddfd33`.
Proof serialization can differ across proving runs. This is one local evidence
instance tied to temporary compiler-visible build paths.

The receipt-profile change does not alter guest programs or `NodeJournalV3`
bytes. It does change host verifier source and binary identity. The prior
source-frozen verifier manifest therefore remains a historical stale gate and
does not attest the new boundary.

The separate current hardened replay record retains seven exact Succinct
receipts and one exact seal mutation. Its root receipt SHA-256 is
`edd25fca20b0205c2f778b866605b343922615623256abcc1a098957664c2d16`
and authenticates the same
`2089ecc187077d4b719c8539076651753c1ead1415724c9bc788758bddfa3768`
journal. The source-built
verifier binds all eight files by name, size, and SHA-256 before receipt
verification, recomposes both level-one journals and the level-two journal,
and requires the exact seal mutation to reject at receipt verification.
The live gate builds from a private detached worktree at the pinned commit,
checks its exact source closure before and after compilation, disables checkout
hooks, rejects unpinned ancestor Cargo config, isolates Cargo home config,
disables automatic Cargo target discovery, remaps compiler-visible paths, and
uses an allowlisted `execve` environment. The exact selected source closure now
contains 44 files.
Normal and `RISC0_DEV_MODE=1` outputs are byte-identical. The record is
`docs/research/ZRPF_V3_RETAINED_SOURCE_BUILT_REPLAY_EVIDENCE_20260712.json`,
SHA-256
`8bc75ace0cc0f699979efc40d3c93cab1fa7be57b2e471be829eeb203faa9a4d`.
The recorded verifier bytes have SHA-256
`0e71d8f4ebb6e15d531bc367244e0ede33d0a9e76ba1c38be855cda30788e78f`
and were executed from a fully sealed Linux memfd.

This record establishes a same-host current-source host-verifier replay of the
exact retained bytes. It does not establish how those proofs were generated,
bind guest source to the temporary image IDs, authenticate complete build
inputs, the compiler, linker, dependency cache, or runtime rootfs, demonstrate
receipt-byte determinism, or authorize release or public-replay promotion.

## Promotion Boundary

The current implementation does not support:

- a release-backed V3 RISC0 image or receipt;
- a semantic or release-backed V3 receipt-authenticated tree;
- complete leaf or aggregate semantic composition;
- descendant task, receipt, message, or write-set uniqueness;
- governed child-profile or verifier-set authorization;
- an implemented 16-by-4 scale profile;
- arbitrary or unbounded recursion;
- production, settlement, or ledger-admission authority;
- verified data availability or conflict scheduling;
- complete ZenoDEX value-flow coverage;
- witness or system privacy;
- cross-host reproducibility;
- throughput or proving-cost claims.

`RS-CBC-016` remains `implemented_partial`. `RS-CBC-021` remains pending for
canonical source-byte authority and a versioned strict-decoding ABI.
`RS-CBC-022` is `implemented_partial` for the Spot adapter and bounded
structural aggregate boundaries. The semantic composer, governed release
profile, and `RS-CBC-023` remain open.

## Dependency Decision

The new crate reuses versions already present in the recursive proof workspaces:

| Dependency | Purpose | Determinism and removal note |
| --- | --- | --- |
| `serde` declared 1.0.219, resolved 1.0.228 | typed transport | locked; replaceable with a manual decoder |
| `postcard` 1.1.3 | compact `no_std` transport | locked; manual canonical hash remains independent |
| `sha2` 0.10.9 | domain-separated SHA-256 | locked; required for parity with existing commitments |
| `serde_json` exactly 1.0.150 | bounded canonical receipt artifacts at the host verifier boundary | exact pin and lock required; absent from guests and replaceable by a reviewed canonical codec |
| `risc0-zkvm` exactly 3.0.5 | Succinct receipt decoding and cryptographic verification | host verifier and retained replay disable default features and enable only `std` plus `disable-dev-mode`; replacement requires a new proof-system adapter |
| `rustix` exactly 1.1.4 | safe descriptor-relative `openat`, `fstat`, non-following, and nonblocking receipt reads | host replay only, already present in the locked graph; removable when equivalent reviewed standard-library APIs exist |

The workspace lockfile pins the resolved transitive graph. No network,
filesystem, clock, randomness, locale, or unordered iteration enters protocol
construction.

## Next Safest Build

1. Generate fresh current-source leaf and aggregate proofs, bind guest source to
   the resulting image IDs, and record the proof-generation and verifier build
   closures without replacing the historical evidence records.
2. Keep the exact retained-byte replay as a regression lane and preserve the
   proof-bearing wrong-image, seal-mutation, non-Succinct, exact-journal, and
   descriptor-boundary controls in the new proof-generation evidence.
3. Define a separate closed-epoch semantic disclosure profile and native V3
   leaves that can recompute every parent commitment without compatibility
   sentinels.
4. Add duplicate-descendant, unbalanced-asset, unmatched-message, invalid-
   schedule, missing-DA-certificate, and carry-replay negative evidence.
5. Add governed verifier policy before any admission integration.

A level-three super-root and the 16-by-4 architecture ceiling remain future
profiles because the compiled V3 candidate intentionally caps level at two.
