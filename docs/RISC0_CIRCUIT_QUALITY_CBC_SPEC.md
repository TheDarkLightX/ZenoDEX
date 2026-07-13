# RISC0 Circuit Quality CBC Spec

Date: 2026-07-04
Status: design and implementation policy

## Claim Scope

This document defines the correct-by-construction quality contract for ZenoDEX
RISC0 circuits, journals, proof metadata, recursive aggregation, and verifier
admission. It is a design and implementation policy. The v1 workspace implements
pre-release one-level composition under a dedicated aggregate guest. The sibling
recursive-v2 workspace implements an experimental fixed-height
leaf-to-subtree-to-epoch-root composition. This policy does not claim
arbitrary-depth recursion or production-ready recursive aggregation.

Status update, 2026-07-12: the active V1 and recursive-v2 lockfiles now pin
`anyhow 1.0.103`. Fresh current-source evidence now binds a Spot leaf, zUSD
leaf, two-child V1 root, two-leaf recursive-v2 inner node, and recursive-v2
epoch root. The active V1 aggregate image ID is
`c4bde351d48e8e775c2e831fc37fb98a9e45ed59455afe761572d2e11ceed6c4`;
the active V2 aggregate image ID is
`0a678da608708af7bd6c35bf825ffe8815efd67f0a8041466929fb2fcda7ae68`.
The active V3 reference and checker bind the exact source inventories, guest
programs, host verifiers, toolchain observations, five positive receipts, and
nine negative controls. This closes `RS-CBC-014` only for the recorded
same-host bounded computational-integrity profile. The active audit policy
permits no unsound-warning disposition.

Status update, 2026-07-10: fanout-oriented composition repairs changed
guest-linked v1 and v2 source. At that revision, RISC0 3.0.5 v1 leaf/root receipts
and a fixed-height v2 inner/root pair have now been generated and separately
verified locally. The current aggregate-v2 image ID is
`fe131b0ec697a9bd703218f3733e44b84c8e347eb8ebfc8776be2200958fbe53`.
This closes `RS-CBC-014` for the pinned one-leaf smoke and one source-frozen,
fixed-height spot-plus-zUSD fanout-two local computational-integrity run. The
host constructor accepts a bounded `1..=8` leaf set. Current real proof evidence
covers one heterogeneous pair and one same-profile distinct-statement spot
pair. The heterogeneous source-pinned evidence record is
`docs/research/RECURSIVE_STARK_V2_TWO_LEAF_SOURCE_PINNED_EVIDENCE_20260710.json`,
SHA-256
`9a98b947f76a599109f5238861d010fd3dbb8a8299ef6e3f03685b3cac51ad74`.
The earlier unpromoted prototype remains recorded separately for cross-run
comparison. The fresh receipt bytes differ across runs, and both authenticated
journals match. Proof-byte determinism remains unestablished. A governed
general fanout profile, nonempty receipt partitions, public replay, cross-host
reproducibility, release authority, durable atomic value-moving admission,
privacy, and production readiness remain open.

The dedicated two-leaf replay checker uses the committed manifest and v2
reference as fixed trust roots. It rejects path, hash, size, ordering, topology,
transcript, executable, and toolchain drift. Its live replay covers both leaf
orders, the repository-pinned specialized verifier, duplicate-leaf and
swapped-node policy rejections, the one-leaf policy rejection, and the
missing-child-assumption control. This supplies bounded replay evidence.
Correctness proof and release authorization remain absent.

A separate same-profile run proved two spot leaves under the same then-current image
and profile with distinct authenticated statement and semantic-source IDs. Its
inner journal contains one unique derived verifier ID for two child receipts.
The repository-owned verifier binds authenticated lane kinds, rejects duplicate
lanes and lane aliases of one semantic source, and independently recomputes the
descendant-source and scoped assigned-leaf roots. The evidence record is
`docs/research/RECURSIVE_STARK_V2_SAME_PROFILE_TWO_SPOT_EVIDENCE_20260710.json`,
SHA-256
`18141ffae7279b1a717edb41674b4fae101a489e2d7870b920c45c8d6810512a`.
Its checker replays both leaf orders from digest-verified private staging and
requires duplicate-lane, duplicate-source, swapped-node, and one-word Succinct
seal mutation rejections. This closes the bounded same-profile verifier-set
evidence gap for fanout two. The accepted statements do not represent two
value-moving batches, and no throughput claim follows.

The v1 pinned reference also binds the positive verifier request and a
cryptographic malformed-proof case that changes exactly one Succinct seal word.
The checker requires the mutated proof envelope, mutated verifier request, and
rejection transcript to match that mutation and reports
`malformed_proof_reject_verified=true`. This strengthens local fail-closed proof
evidence without changing the artifact-only, non-production claim scope. The
handled reject exits zero, so consumers must parse the canonical response and
must not treat process exit status as proof acceptance. The artifact checker
does not attest execution provenance.

The historical current-image promotion gate enumerated every bounded regular file in the
declared v1 and v2 source scopes. The scopes must contain no `target` directory;
evidence builds use an external target root. Binary `include_bytes!` payloads
and other non-Rust compiler inputs therefore participate in the source root,
and attempts to hide inputs under an excluded target tree fail closed.

The V1 state-proof CLI now rejects duplicate object keys recursively before
typed construction, including escaped-key aliases and embedded application
state JSON. It also rejects unknown fields in the closed recursive composition,
descriptor, effect-summary, asset-row, message, and recursive leaf-wrapper
objects through a CLI-local exact wire validator. This hardening does not
change guest-visible types, image IDs, journals, or retained receipts.

The recursive verification entry point additionally requires the exact six
fields of the V1 verification request, the exact six fields of its recursive
proof envelope, and every field emitted by the V1 recursive `proof.meta`
profile. Missing and unknown fields, wrong schema names or versions, wrong
field types, mismatched request/proof state hashes, and wrong public proof type,
domain, profile, receipt codec, receipt kind, or image ID reject before receipt
authentication. Structure-preserving mutation tests assert this pre-crypto
ordering, including request-over-proof-over-metadata reject precedence.

The matrix-cited missing-assumption harness uses the same strict parser and a
16 MiB request bound. The recursive smoke proof loader uses the same strict
parser and a 16 MiB per-artifact bound. These host evidence utilities reject
duplicate decoded keys, escaped aliases, and trailing JSON documents.

Current receipts authenticate the parsed typed value rather than canonical
outer JSON bytes. The host leaf-generation ingress now requires every field and
exact JSON type in the three reachable Spot, perps, and zUSD application
schemas. This includes every current mixed Tau Spot intent variant, required
explicit `null` for absent optional values, nested exact-field rejection, and
integer range checks. The recursive-root verification request rejects all three
leaf-generation payloads before receipt authentication; this host ingress
hardening does not turn those payloads into authenticated recursive-root
semantics.

Canonical-byte enforcement remains required before a V1-derived envelope can
carry production authority. The next recursive ABI should make this boundary
unrepresentable with strict canonical decoding. The request, proof, metadata,
and leaf-generation guards are bounded host-side closures; `RS-CBC-021`
remains a pending critical promotion obligation.

The host CLI changes invalidated the prior V1 current-source verifier replay
claim because the retained V1 verifier source closure includes the CLI. The
subsequent `anyhow 1.0.103` migration changed both active V1 and V2 build
closures and image identities. The active V3 reproof reference restores only a
same-host current-image computational-integrity claim. Historical receipts
remain bounded regression evidence. Public replay, cross-host reproducibility,
release authority, settlement authority, privacy, and production readiness
remain false.

Before the active dependency migration, a local pinned-toolchain V1 rebuild
produced the exact 30-file source
root `81f5dc170de45306b7427f8379ea23add429f5c6325a06c0bb4fa6c4315f78bf`
and static PIE verifier
`8836f22431e2ce241eec9e6503f741b92673e2fec054208b0c36dea4f1bcf146`.
That binary reproduced the retained positive transcript and the exact
cryptographic-invalid response for the one-bit seal mutation with empty
stderr and process exit code zero.

The executable live checker first requires the complete pinned artifact check,
seals the exact verifier into a fully sealed Linux memfd, and applies bounded
stdin, stdout, stderr, CPU, address-space, file, descriptor, process, and stack
limits before execution. It reproduced the accepted transcript with
`RISC0_DEV_MODE` absent and set to `0`; it rejected enabled aliases `1`,
`true`, `yes`, and `on`; and it reproduced the exact cryptographic-invalid
response for the one-bit seal mutation. The retained report has canonical
SHA-256
`7b33cea014263fe0841fc291d9ce8097fcfa3a85cc7d1f18b832a52380df43c6`
and binds the exact checker-source closure and numeric runtime limits.

The required workflow validates this retained record, its source closure, and
its bounded privacy scan without re-executing the V1 verifier. The CBC matrix
records its integrity as historical evidence and requires the exact non-claim
`no_authenticated_historical_execution_provenance_for_v1_live_replay_record`.
The record does not restore current V1 image or receipt evidence after the
`anyhow 1.0.103` migration.
`config/proof_profiles/risc0_recursive_rebuild_reference.json` is frozen as
the immutable historical V1 replay reference. Fresh active V1/V2 reproof work
must use
`config/proof_profiles/risc0_recursive_active_reproof_reference_v3.json` or a
later separately reviewed path; it must not overwrite the historical trust
root.
Historical execution provenance, public replay, network isolation, sandbox,
settlement, release, privacy, and production authority remain false.

The additive ZRPF V3 candidate under `zk/zrpf_protocol` now implements a
proof-system-neutral, bounded 8-by-8 structural journal nucleus. It provides a
shared leaf and aggregate journal shape, nonzero typed commitments, application
and domain scope binding, derived verifier IDs, canonical dense partitions,
checked counts, strict 4,096-byte Postcard decoding, and independently replayed
hash fixtures. This is structural reference evidence. A temporary-path RISC0
profile now authenticates four Spot V1-to-V3 adapter receipts, two level-one
structural aggregate receipts, and one level-two structural root receipt.
Each aggregate guest verifies every exact child receipt under its compile-time
child image before strict decoding and deterministic structural composition.
Decoded journals and raw projected child descriptors carry no authority by
themselves. `RS-CBC-022` is implemented for this bounded adapter and structural
aggregate path. `RS-CBC-023` pins semantic composition of state, effects,
receipt sets, messages, schedules, carry, and data availability. The
normative candidate scope and non-claims are recorded in
`docs/research/ZRPF_V3_CORRECT_BY_CONSTRUCTION_SPEC_20260710.md`.

The retained Semantic Epoch V1 profile supplies the first receipt-backed
sub-obligation for `RS-CBC-023`. Under its recorded RISC0 3.0.5 image IDs, the
D guest verifies exact B
receipts before interpreting their disclosed A journals, recomposes each B
journal, recomposes the governed structural C journal locally, binds semantic
source openings, and enforces global source-claim, semantic-source, and task
uniqueness. One retained three-leaf, two-L1-group D receipt passed exact outer
verification. A separate cross-subtree repeated-semantic-source execution
reached the dedicated guest reject after both L1 assumptions were supplied. An
exact one-word Succinct seal mutation of the positive D receipt rejected as
`ReceiptArtifact(ReceiptVerificationFailed)`.

This historical evidence leaves `RS-CBC-023` pending. The V1 adapter profile authenticates
empty receipt and message sets and has no nullifier surface. It does not prove
global asset conservation, authorized mint or burn, pre-state to post-state
continuity, nonempty receipt or message composition, schedules, carry, or data
availability. The scoped specification and fail-closed artifact checker are:

- `docs/research/ZRPF_SEMANTIC_EPOCH_V1_SPEC_20260711.md`;
- `docs/research/ZRPF_SEMANTIC_EPOCH_V1_LOCAL_PROOF_EVIDENCE_20260711.json`;
- `tools/check_zrpf_semantic_epoch_v1_local_evidence.py`.

Status update, 2026-07-12: active semantic source uses the V2 statement. Its
guest input and proof-neutral proposal omit runtime image D. The sealed host
verifier enforces the pinned Succinct receipt-security profile and attaches D
only after receipt verification. V2 has source-level and host-test evidence;
no fresh V2 guest ELF, image ID, receipt, seal-mutation replay, admission,
release, settlement, or production authority is claimed.

Status update, 2026-07-12: the additive source-opened ordinary Spot V6 profile
implements one bounded source-to-settlement path under four pinned program
identities:

```text
source-opened leaf V6  67494a413c729cbb4b6095036425ba0b86edcc30625c19b525409f8e8ff022d1
aggregate L1 V6        a2b4c32ef76c0a81643f1758c476fc21f6a7c2afd11d2a6e08fae022418e2e15
aggregate L2 V6        5c8f94b4ada70ad5ba0d6ac6bd6b0055a9e148c329372e7b24a81249ff07a76f
settlement V6          73a1c5c275d85f39443f68803932df9caac670b420b9948b7e7b2dffe1f2e98d
```

The leaf host boundary verifies and independently recomposes the typed source
transition and verifies the governed adapter receipt. Each aggregate guest
verifies its exact child receipt before decoding and independently recomposes
the V5 proposal. The settlement guest verifies the exact L2 receipt before
interpretation, reconstructs the singleton source relation, derives one
state-bound ordinary Spot certificate, full-blob replay content certificate, and
exact effect plan, and commits them through the fixed `ZRPFSAV1` admission
journal. The strict Rust verifier verifies the settlement receipt once and
recomposes the expected journal from the exact guest input. The independent
Python adapter checks the same frame and projects only the shared singleton
ordinary Spot semantics.

SQLite schema V4 atomically persists the exact receipt, guest input, admission
journal, reconstructed replay, content certificate, settlement certificate,
effect plan, governed proof identities, projection binding, replay rows, and
nullifiers. This closes exact local proof-to-plan persistence for the bounded
V6 profile. It does not apply a live ZenoLedger balance tree and fixes
`settlement_authority=false`.

Local Succinct receipts have been generated for the leaf, L1, and L2 programs.
The settlement proof, external-verifier replay, checked retained inventory, and
final evidence record remain the promotion gate for the complete local-chain
claim. The current harness represents one action and uses deterministic
synthetic sparse-Merkle siblings. Multi-leaf fanout, live authorization and
state continuity, provider retrievability, external finality, governed release,
cross-host reproducibility, privacy, throughput, settlement authority, and
production authority remain unestablished. The bounded contract is documented
in `docs/research/ZRPF_SOURCE_OPENED_SPOT_V6_CBC_SPEC_20260712.md`.

The local durable replay-index profile implements a separate partial
sub-obligation under `RS-CBC-012` and `RS-CBC-025`. A release-bound static
verifier can pass authenticated root facts and exact verification provenance
to one private SQLite store method. The store uses rollback-journal `DELETE`,
`synchronous=EXTRA`, `BEGIN IMMEDIATE`, unique indexes, a revision-and-root
compare-and-swap, and a hash-chained cursor. It commits root, slot, child,
receipt, message, provenance, and canonical outcome rows together. An exact
retry returns the stored outcome, including after a process loses the first
response. Concurrent same-root and same-slot tests, maximum unsigned-64 epoch
storage, restart, schema drift, symlink, and pre-commit process-exit controls
pass locally. The detailed contract is
`docs/research/ZRPF_DURABLE_REPLAY_ADMISSION_CBC_SPEC_20260712.md`.

This store contains no economic effect plan. Its hash-chained cursor commits to
and internally binds replay-index history, conditional on an externally trusted
head. Balance, collateral, mint, burn, fee, reward, carry, message-delivery,
application-state, and settlement commits must share one future ZenoLedger
transaction before durable atomic value-moving admission can be claimed. Fresh
V2 receipt evidence and governed live release configuration also remain
required.

The additive `zk/zrpf_risc0` workspace contains the pure Spot V1-to-V3 mapping,
a receipt-authenticated adapter guest, a private-construction host verifier,
and an evidence harness. The guest verifies the exact governed Spot receipt
assumption before decoding and projecting its journal. The host verifier then
requires the compiled RISC0 3.0.5 Succinct verifier-parameter digest,
Poseidon2 hash suite, control ID, and metadata equality. It verifies through an
explicit dev-mode-disabled context. Persisted receipts first cross a 16 MiB
pre-decode cap and exact typed JSON round-trip check. The verifier then enforces
exact journal equality, compares the journal program ID with the image actually
verified, derives the child claim binding locally, and only then exposes a
child descriptor. The retained temporary-path adapter image is
`71f282b5517fc6108988c1cc9b4601807a40ae331c0e0f0f5505d12b241e5574`.
Positive proving, persisted-receipt replay, missing assumption, exact-journal
substitution, and proof-bearing false self-label controls pass locally.
The path-redacted adapter evidence record is
`docs/research/ZRPF_V1_SPOT_ADAPTER_TEMPORARY_LOCAL_EVIDENCE_20260710.json`.

The bounded structural aggregate profile uses level-one image
`4272be5165f65e29cb134f815d6c6fc40d7f492979f596082cac10c3f0d43c2b`
for adapter children and level-two image
`3b858d113cb155b2946e1c733fdf5fe5592b6bf46c903d0a3cfb322099845736`
for level-one children. One local four-leaf proof produced a root journal hash
of `2089ecc187077d4b719c8539076651753c1ead1415724c9bc788758bddfa3768`.
The exact persisted root receipt has SHA-256
`021af13025e7dc7c40e06d689ad30e3194e58793435cd11ae07d684c80ddfd33`.
Receipt bytes may vary across proving runs. These temporary compiler-visible
images have no release authority.
The path-redacted structural-tree evidence record is
`docs/research/ZRPF_V3_STRUCTURAL_TREE_TEMPORARY_LOCAL_EVIDENCE_20260710.json`.
Their Python checkers verify reviewed facts, source closures, and optional
artifact bytes; the Rust verifier-only harness remains the receipt-seal and
exact-journal authority. The exact receipt-profile hardening changes the host
verifier source and binary without changing guest or `NodeJournalV3` bytes.
Both retained adapter and structural-tree evidence records predate that host
change, so both historical source-closure checkers continue to reject current
source. Those records remain unchanged as stale regression gates.

A separate hardened replay lane anchored at commit `ff76ff9c` builds a dedicated
source-only verifier whose selected dependency graph excludes the methods,
guests, harness, Bonsai, client, and `risc0-build` paths. It binds eight exact
retained artifacts by fixed name, size, and SHA-256 through descriptor-relative
bounded non-following reads. It verifies four adapter leaves, independently
recomposes and exact-verifies both level-one journals and the level-two journal,
binds the reviewed root topology and journal hash, and requires the exact
single-word root-seal mutation to reject as `receipt_verification_failed`.
The live gate builds from a mode-0700 detached worktree at the pinned commit,
checks the 44-file closure before and after compilation, disables automatic
Cargo target discovery and checkout hooks, rejects unpinned ancestor Cargo
config, isolates Cargo home config, remaps compiler-visible paths, and passes an
allowlisted `execve` environment to the build and verifier processes.
Static validation reconstructs that closure from the pinned Git commit and
checks the durable tag, commit tree, file count, byte count, and closure digest.
Forward integration source therefore remains separate from the historical
replay build identity.
Normal execution and `RISC0_DEV_MODE=1` execution produced byte-identical
5,920-byte output with SHA-256
`7751395663a33c1ae58fa403346dc90618e842dd1df2f2fdc37f18599e50c288`.
The path-clean evidence record is
`docs/research/ZRPF_V3_RETAINED_SOURCE_BUILT_REPLAY_EVIDENCE_20260712.json`,
SHA-256
`8bc75ace0cc0f699979efc40d3c93cab1fa7be57b2e471be829eeb203faa9a4d`.
The recorded verifier bytes have SHA-256
`0e71d8f4ebb6e15d531bc367244e0ede33d0a9e76ba1c38be855cda30788e78f`
and were executed from a fully sealed Linux memfd.
Its live checker also rejects altered receipt bytes, swapped level-one nodes,
extra and missing inventory, receipt symlinks, FIFO input, a directory symlink,
and missing arguments with stable reject classes and empty stdout.

This closes the current hardened host-verifier replay gap for the exact retained
bytes. It does not attest the historical proof-generation source, rebuild guest
images, bind guest source to image IDs, or authenticate complete build inputs,
the compiler, linker, dependency cache, or runtime rootfs. Cross-host
reproducibility and public-replay, release, semantic, ledger, settlement,
privacy, throughput, and production authority remain unestablished. The
retained root receipt
`edd25fca20b0205c2f778b866605b343922615623256abcc1a098957664c2d16`
and the earlier `021af130...fd33` receipt authenticate the same root journal;
that fact establishes no receipt-byte determinism.

The compatibility journal labels its count as one source-transition receipt
and uses explicit unsupported sentinels for DA-certificate and carry facts. Its
adapter manifest is a source-independent unreleased compatibility identity;
source lock hashes remain in source provenance and cannot select the adapter
manifest. This evidence partially closes `RS-CBC-016` and `RS-CBC-022` for the
bounded structural profile. It does not close native semantic aggregation,
data-availability assurance, carry policy, ledger admission, reproducible
release identity, or `RS-CBC-023`. The field disposition and non-claims are
specified in
`docs/research/ZRPF_V1_LEAF_ADAPTER_COMPATIBILITY_SPEC_20260710.md`.

A subsequent target-absent recursive-v2 rebuild froze and rechecked the current
source closure, used the pinned outer and observed nested Cargo executable,
independently recomputed the image ID, and matched the pinned program, raw ELF,
and both host pair verifiers, then verified the pinned authenticated proof pair. It
returned
`same_host_clean_recursive_v2_rebuild_match`. The evidence report SHA-256 is
`a366d6e0d00f963c061cd7c9be9bbc531d6502f49950834f4297b773db05aeb1`.
The path-redacted record is
`docs/research/RECURSIVE_STARK_V2_CURRENT_EVIDENCE_20260710.json`, pinned by
file SHA-256
`6063b2def168c59d0f187a46e8384979441f4bad8ef1a795f2163c86a7849ea1`.
This remains same-host evidence. Cross-environment reproducibility, release
authority, public replay, privacy, settlement authority, and production
readiness remain false or unestablished. Proof-regeneration determinism remains
false because the clean build did not regenerate the receipts.

The spec applies to:

- `zk/state_proof_risc0/**`, `zk/recursive_stark_v2_risc0/**`,
  `zk/zrpf_protocol/**`, and `zk/zrpf_risc0/**`;
- proof metadata and proof-profile code under `tools/**` and `src/integration/**`;
- ZenoLedger/Tau admission paths that consume RISC0 receipts or journals;
- future recursive proof aggregation work.

Related guidance:

- `AGENTS.md`
- `zk/AGENTS.md`
- `docs/research/RECURSIVE_STARK_V2_BOUNDED_FANOUT_GUIDE_20260710.md`
- `docs/research/RECURSIVE_STARK_SCALING_ARCHITECTURE_20260704.md`

## Core Law

Circuit quality is a statement-construction problem.

```text
TypedStatement
  -> deterministic witness builder
  -> guest verifies the witness
  -> canonical journal
  -> verifier checks receipt, image ID, journal hash, profile, and metadata roots
```

The prover may propose data. The guest and verifier decide what is trusted.

## Non-Claims

This spec does not claim:

- the implemented bounded one-level and two-level profiles provide
  arbitrary-depth or production-ready recursion;
- current proof profiles are production-ready;
- every ZenoDEX transition has a RISC0 leaf proof;
- data availability is solved by proof recursion;
- any RISC0 version-specific API is stable across upgrades;
- a successful local proof smoke is production evidence by itself.

## Disaster States

Every circuit and verifier change must name which disaster states it affects.

| Disaster state | Primary defense |
| --- | --- |
| proof from wrong program accepted | expected image ID in typed statement and receipt verify |
| proof paired with wrong journal | canonical journal hash checked by verifier |
| proof replayed across chain/config/domain | domain separator, chain ID, config hash, policy hash |
| production accepts dev proof | dev mode prohibited by production profile gate |
| host witness lies | guest recomputes or checks claim-relevant witness fields |
| child proof omitted in recursive root | child count/root and in-guest child receipt verification |
| child proof swapped | child journal digest and child verifier ID bound in root |
| stale verifier accepted | verifier ID membership in `verifier_set_root` |
| metadata stronger than proof | metadata roots must equal journal and block roots |
| unbalanced asset movement | typed delta rows and aggregate conservation check |
| unauthorized mint/burn/slash/reward | authority root membership and lane-specific policy |
| rejected proof mutates state | reject-is-no-op test and transition staging |
| data hidden behind a proof | data availability root plus DA policy verifier |
| ambiguous schema evolution | append-only schema, explicit version, reject unknown criticals |
| overflow or truncation | checked arithmetic, bounded counts, explicit widths |

## Typed Statement Contract

Every proof family must define a typed statement before implementing the guest.
The statement is the public contract. It must be hashable, canonical, bounded,
and versioned.

Minimum fields:

```text
Risc0StatementV1 {
  domain_separator
  schema_version
  chain_id
  config_hash
  epoch_or_height_range
  proof_profile
  expected_image_id
  verifier_set_root
  public_policy_hash
  feature_suite_hash
  dependency_lock_hash
  toolchain_lock_hash
  pre_state_root
  post_state_root
  tx_root
  evidence_root
  receipt_root
  data_availability_root
  max_witness_bytes
  max_public_rows
}
```

Recursive statements additionally require:

```text
RecursiveStatementV1 {
  child_verification_claims_root
  child_journals_root
  child_effect_summaries_root
  child_count
  max_child_journal_bytes
  max_total_child_journal_bytes
  cross_shard_message_ids_root
  conflict_schedule_hash
  carry_queue_pre_root
  carry_queue_post_root
}
```

The constructor must reject:

- missing required roots;
- all-zero image ID, verifier ID, or root where nonzero is required;
- unknown critical fields;
- ambiguous defaults;
- duplicate IDs;
- unsorted rows;
- row counts above configured bounds;
- profile/image/profile-kind mismatch;
- stale schema version;
- domain, chain, config, policy, feature, or toolchain mismatch.

If a field affects acceptance, ordering, conservation, authority, replay, or
public claims, it must be in the statement hash or in a root committed by the
statement hash.

## Witness Contract

Witnesses are private inputs. A witness field is admissible only if it falls
into one of these categories:

1. The guest checks it directly.
2. The guest recomputes a digest/root from it and commits that digest/root.
3. The guest verifies a proof or receipt that authorizes it.
4. A documented theorem shows it is irrelevant to the public statement.

Any other witness field is unconstrained and must be removed or rejected from
the production profile.

Witness builders must be deterministic:

- no wall clock;
- no randomness unless explicitly seeded and committed;
- no environment-dependent behavior;
- no unordered map/set iteration in canonical output;
- no hidden filesystem or network reads;
- no machine-specific paths in committed artifacts.

## Journal Contract

The journal is the public output ABI. It must be stable, canonical, and small.

Minimum fields:

```text
Risc0JournalV1 {
  journal_version
  domain_separator
  chain_id
  config_hash
  proof_profile
  risc0_image_id
  statement_hash
  pre_state_root
  post_state_root
  tx_root
  evidence_root
  receipt_root
  data_availability_root
  public_policy_hash
  feature_suite_hash
  dependency_lock_hash
  toolchain_lock_hash
}
```

Recursive journals additionally require:

```text
RecursiveJournalV1 {
  verifier_set_root
  child_verification_claims_root
  child_journals_root
  child_effect_summaries_root
  child_count
  conflict_schedule_hash
  carry_queue_pre_root
  carry_queue_post_root
  aggregate_asset_delta_root
}
```

The verifier must check:

```text
receipt.verify(expected_image_id)
journal.risc0_image_id == expected_image_id
hash(canonical_journal) == expected_journal_hash
statement_hash == expected_statement_hash
metadata roots == journal roots == block/header/body roots
proof_profile == expected_profile
```

Proof generation is never enough. A generated receipt must be verified against
the expected image ID and expected journal before it is used by a higher layer.

## Tau-Unavailable Fallback

Tau compatibility is an admission target, not a hidden dependency inside the
RISC0 statement. If Tau execution, linting, or trace tooling is unavailable, the
proof lane may still produce replayable local or testnet evidence only through a
deterministic host checker that enforces the same Boolean contract:

```text
proof_requested
&& proof_verified
&& proof_profile_supported
&& leaf_rows_derived
&& asset_delta_root_bound
&& aggregate_rows_balanced
&& authority_roots_allowed
&& unsupported_lifecycle_absent
&& tau_header_binding_ok
&& transcript_binding_ok
```

The fallback checker must recompute roots from public metadata and journals. It
must not accept host-supplied row verdicts without recomputation. If Tau is down
or incompatible, public status must be downgraded to local replay or testnet
evidence; production or Tau-compatible claims remain false until the Tau spec,
semantic contract lint, and admission traces pass again.

## RISC0 Receipt Profiles

Receipt kind must be explicit at every boundary.

```text
CompositeReceipt:
  purpose: local development and fastest proving
  claim: local proof artifact only unless explicitly accepted by profile

SuccinctReceipt:
  purpose: aggregation and constant-size STARK-style receipt lane
  claim: recursive composition candidate

Groth16Receipt:
  purpose: compact on-chain verifier target where supported
  claim: verifier-adapter-specific public proof
```

Production profiles must reject:

- implicit default prover options;
- dev-mode receipts;
- placeholder methods;
- all-zero image IDs;
- receipt kind missing from metadata;
- receipt kind different from declared profile;
- proof generated under one image ID and reported under another.

The CLI should expose the profile explicitly. Silent fallback between receipt
kinds is forbidden for production proof claims.

## Recursive Composition Contract

Recursive aggregation must verify child receipts in the guest.

Intended shape:

```text
host:
  build child receipts
  compute child journal bytes and verification-claim digests
  add child receipts as assumptions

guest:
  parse bounded child descriptors
  verify every child receipt assumption against child image ID and exact child
  journal bytes
  check child image ID is allowed by verifier_set_root
  decode child summary journal after verification
  compose EffectSummaryV1 values
  commit RecursiveJournalV1
```

Child journal bytes without in-guest receipt verification are data. They do not
carry proof authority.

RISC0 guest recursion verifies a claim of the form `(child_image_id,
child_journal_bytes)`. Exact serialized child receipt hashes are useful host
audit metadata, but they are not what the guest verifier checks. Recursive
journals therefore bind `child_verification_claims_root` and
`child_journals_root`, with any receipt-artifact root kept outside the guest
trust boundary.

The verifier set must not be a free host label. A child verifier ID must be
derived from `(child_image_id, child_profile)` and the recursive guest must
reject any descriptor whose `child_verifier_id` does not equal that derived ID.
The committed `verifier_set_root` is the sorted set of those derived IDs.

The recursive root profile describes the aggregate proof, not every child leaf.
For v1, the aggregate profile is `recursive_epoch_v1`. Child leaves may use
different profiles, such as `recursive_spot_leaf_v1`,
`recursive_zusd_leaf_v1`, and `recursive_perps_np_leaf_v1`, as long as each
child descriptor binds its own `child_profile`, `child_image_id`, verifier ID,
journal hash, statement hash, and effect summary hash. The root still requires
common chain, epoch, policy, feature, dependency, and toolchain hashes.

`recursive_epoch_v1` is implemented by the dedicated `aggregate` guest image.
The generic guest rejects recursive inputs. The aggregate guest accepts leaf
`RecursiveEffectSummaryV1` journals, so v1 provides one-level composition.
An aggregate root journal cannot be used as a v1 child journal. Multi-level
root-as-child recursion requires a versioned common node journal.
The 2026-07-09 changes are a pre-release v1 replacement. They added lane-bound
state roots and `cross_shard_message_ids_root`, regenerated every image ID, and
invalidate all earlier local v1 receipts. No released compatibility claim
exists for the superseded local images.

The `risc0.zenodex_recursive_summary_leaf.v1` method is a dedicated
summary-leaf image for recursive plumbing and smoke tests. It accepts only
`recursive_summary_leaf_test_v1`. It proves that a bounded summary was committed
by that image, with a 4096-byte postcard input cap and 128-byte caps on summary
text fields. It does not prove spot, perps, zUSD, oracle, or ledger transition
semantics, uses a `Composite` test receipt, and is inadmissible to an aggregate
root. Production recursive leaves must use transition-specific images that
derive their `EffectSummaryV1` from the checked transition, or an adapter proof
that verifies the source receipt and proves the summary binding.

The `risc0.zenodex_recursive_spot_leaf.v1` method is the first
transition-specific recursive leaf. It accepts `SpotRecursiveLeafInputV1`,
executes the checked spot transition, requires `pre_app_hash` to be present,
requires the leaf `state_hash` to equal the checked post app root, and derives
`EffectSummaryV1` from the resulting `StateProofJournalV1`. Its
`receipt_root` is the native spot accepted-receipts root. Its recursive
accepted/rejected receipt ID sets and cross-shard message sets are empty in v1.
For lifecycle accounting, the leaf derives asset-delta rows from checked
transition input data: faucet mints become authorized mint rows under an
asset/lane/effect-scoped root derived from the public policy hash, and native
balance sync becomes ordinary debit/credit rows for the
native asset. The CLI metadata must expose the exact rows and their recomputed
root must equal the journal `asset_delta_root`. This profile proves local spot
app-state transitions and row-root binding for the spot lifecycle verbs present
in `StateProofInputV1`. It does not claim cross-shard settlement or native-chain
source finality.

The `risc0.zenodex_recursive_zusd_leaf.v1` method is the second
transition-specific recursive leaf. It accepts `ZusdRecursiveLeafInputV1`,
executes the checked zUSD transition, requires `pre_app_hash` to be present,
requires the leaf `state_hash` to equal the checked post app root, requires the
inner zUSD journal image ID to match the zUSD-leaf image ID, and derives
`EffectSummaryV1` from `ZusdTransitionJournalV1`. Its `tx_root` is the zUSD
operation hash. Its `evidence_root` binds the oracle binding, zUSD balance root,
zUSD vault root, participant set, minted amount, collateral value, and MCR. Its
`receipt_root` is the checked zUSD balance root. Recursive accepted/rejected
receipt ID sets and cross-shard message sets are empty in v1. For deposit-mint
transitions, the leaf derives one authorized `zUSD` mint asset-delta row from
`minted_zusd_e8` and binds that row through `asset_delta_root`. Its authority
root is scoped by policy, lane kind, asset, and effect kind. This profile proves
one local zUSD transition under the existing zUSD surface and exposes the
authorized mint effect to recursive aggregation. It does not claim full zUSD
lifecycle coverage, native collateral ledger balance deltas, cross-shard
mint/burn accounting, redemption/burn rows, or oracle truth.

The `risc0.zenodex_recursive_perps_np_leaf.v1` method is the third
transition-specific recursive leaf. It accepts `PerpsNpRecursiveLeafInputV1`,
executes the checked perps NP transition, requires `pre_app_hash` to be present,
requires the leaf `state_hash` to equal the checked post app root, requires the
inner perps journal image ID to match the perps-NP-leaf image ID, requires net
base position zero, and derives
`EffectSummaryV1` from `PerpsNpTransitionJournalV1`. Its `tx_root` is the perps
operation hash. Its `evidence_root` binds oracle bindings, collateral bindings,
participant set, receipt root, participant count, net position, total
collateral, funding residual, and matched base volume. Its `receipt_root` is the
checked perps receipt root. Recursive accepted/rejected receipt ID sets,
cross-shard message sets are empty in v1. For lifecycle accounting, the leaf
derives self-balancing local rows for `InitMarket`, `DepositCollateral`, and
`WithdrawCollateral`. These rows bind local transition amounts and do not prove
an external collateral source or destination. `SubmitIntent` and
`RunEpoch` emit no external asset rows in the current Rust transition language;
the four-participant floor is scoped to `RunEpoch`. The CLI metadata must expose
the exact rows and their recomputed root must equal the journal
`asset_delta_root`. This profile proves checked local perps NP lifecycle and
epoch transitions under the existing perps surface. It does not claim cross-shard
collateral movement, native ledger source finality, zUSD collateral source
verification beyond hash-bound references, or oracle truth.

Repeatable local smoke path:

```bash
cd zk/state_proof_risc0
RISC0_FORCE_BUILD=1 cargo build --locked -p tau-state-proof-risc0-cli --all-targets

SPOT_IMAGE_ID_HEX=<hex spot leaf image ID from generated methods.rs>
cargo run -q -p tau-state-proof-risc0-cli --example recursive_summary_leaf_smoke -- \
  spot "$SPOT_IMAGE_ID_HEX" > /tmp/spot-leaf.request.json
RISC0_PROVER=ipc cargo run -q -p tau-state-proof-risc0-cli \
  < /tmp/spot-leaf.request.json > /tmp/spot-leaf.proof.json
cargo run -q -p tau-state-proof-risc0-cli --example recursive_summary_leaf_smoke -- \
  root /tmp/spot-leaf.proof.json > /tmp/spot-recursive-root.request.json
RISC0_PROVER=ipc cargo run -q -p tau-state-proof-risc0-cli \
  < /tmp/spot-recursive-root.request.json > /tmp/spot-recursive-root.proof.json

ZUSD_IMAGE_ID_HEX=<hex zUSD leaf image ID from generated methods.rs>
cargo run -q -p tau-state-proof-risc0-cli --example recursive_summary_leaf_smoke -- \
  zusd "$ZUSD_IMAGE_ID_HEX" > /tmp/zusd-leaf.request.json
RISC0_FORCE_BUILD=1 cargo run -q -p tau-state-proof-risc0-cli \
  < /tmp/zusd-leaf.request.json > /tmp/zusd-leaf.proof.json
cargo run -q -p tau-state-proof-risc0-cli --example recursive_summary_leaf_smoke -- \
  root /tmp/zusd-leaf.proof.json > /tmp/zusd-recursive-root.request.json
RISC0_FORCE_BUILD=1 cargo run -q -p tau-state-proof-risc0-cli \
  < /tmp/zusd-recursive-root.request.json > /tmp/zusd-recursive-root.proof.json

PERPS_IMAGE_ID_HEX=<hex perps NP leaf image ID from generated methods.rs>
cargo run -q -p tau-state-proof-risc0-cli --example recursive_summary_leaf_smoke -- \
  perps "$PERPS_IMAGE_ID_HEX" > /tmp/perps-np-leaf.request.json
RISC0_FORCE_BUILD=1 cargo run -q -p tau-state-proof-risc0-cli \
  < /tmp/perps-np-leaf.request.json > /tmp/perps-np-leaf.proof.json
cargo run -q -p tau-state-proof-risc0-cli --example recursive_summary_leaf_smoke -- \
  root /tmp/perps-np-leaf.proof.json > /tmp/perps-np-recursive-root.request.json
RISC0_FORCE_BUILD=1 cargo run -q -p tau-state-proof-risc0-cli \
  < /tmp/perps-np-recursive-root.request.json > /tmp/perps-np-recursive-root.proof.json

cargo run -q -p tau-state-proof-risc0-cli --example recursive_summary_leaf_smoke -- \
  root /tmp/spot-leaf.proof.json /tmp/zusd-leaf.proof.json \
  /tmp/perps-np-leaf.proof.json > /tmp/multi-leaf-recursive-root.request.json
RISC0_FORCE_BUILD=1 cargo run -q -p tau-state-proof-risc0-cli \
  < /tmp/multi-leaf-recursive-root.request.json \
  > /tmp/multi-leaf-recursive-root.proof.json
```

The 2026-07-09 RISC0 1.2.6 spot and aggregate run is revoked as assurance
evidence. RISC0 1.2.6 is affected by GHSA-jqq4-c7wq-36h7, whose malicious-host
`sys_read` vulnerability compromises guest soundness. The recorded receipt
sizes, aggregate image ID, proof hash, and root journal hash may be retained only
as historical regression inputs. They must not authorize admission, release,
or claim promotion. The replacement evidence lane requires an exact RISC0 3.0.5
force-build, canonical image IDs, versioned depth-limited receipt encoding, and
independent replay against pinned receipt-profile expectations.

Before the 2026-07-10 composition repair, the replacement local lane produced
and verified an exact RISC0 3.0.5 spot leaf and one-child aggregate Succinct
receipt. All six historical embedded program
image IDs matched independent `r0vm --id` results. A static, SHA-256-pinned
verifier executed from a sealed snapshot admitted the authenticated aggregate
root once and rejected its replay without changing admission state. The
transcript-bound bundle status is `local_artifact_pinned_replay`.

A separate clean-rebuild comparison used distinct source and target roots on the
same host with unchanged compiler-visible dependency and home paths. All six
combined guest program bytes, their image IDs, the artifact report, and the
static host verifier matched. A third build held those paths fixed, forced
nested Cargo offline from a source-root config, and reproduced those bytes plus
the authenticated proof transcript. This is constrained manual same-host
evidence. The committed v1 artifact checker reports only
`pinned_rebuild_artifact_match`; it explicitly does not attest a clean build,
command, environment, toolchain execution, or cross-environment equality.

A stricter same-host build relocated `HOME` and the Cargo dependency path and
forced nested Cargo offline with `[net] offline = true`. It completed, while all
six combined-program hashes and the static verifier hash differed from the
reference. Independent `r0vm --id` checks also produced six different image IDs,
and guest strings expose the differing Cargo dependency paths. This is guest
image-identity drift. The pre-composition-repair proof is bound to those
reference images and does not verify against the relocated images. The exact
positive and negative rows are
recorded in
`docs/research/RECURSIVE_STARK_REBUILD_PATH_EXPERIMENT_20260709.json`. This
counterexample keeps canonical
compiler-visible dependency paths and guest path remapping open as required build
controls. Neither rebuild changes the replay bundle's
`local_artifact_pinned_replay` status.

The fixed-height recursive-v2 lane is isolated in the sibling workspace so
adding its packages cannot perturb the six byte-pinned v1 Cargo units. Its local
pre-repair two-level smoke verified a Succinct inner receipt as the assumption
of a Succinct epoch-root receipt under historical aggregate-v2 image ID
`8cd39919e79085bb357f1aa316175809c461c648c5b86481879a12e5c3c826ae`.
The host pair verifier independently binds the root to the exact inner claim,
journal, verifier set, scope, flat projection, and leaf-set commitments.

The current post-repair local run uses aggregate-v2 combined-program SHA-256
`3fc45f1cfc7ffd401119ad8eb3779db19d4a060942de70e25c7c9b706e1c8376`
and image ID
`fe131b0ec697a9bd703218f3733e44b84c8e347eb8ebfc8776be2200958fbe53`.
The inner and epoch-root artifact SHA-256 values are
`9aa0bd06a2c0e31f6f9b17375a85bced5a65b9b774350eb80a919b2a5b87ff9b`
and
`8fb245914b38726b67ebed74c6210c06660156fc17772f679d225381401e26e7`.
Their canonical receipt SHA-256 values are
`7f513a978b9d34e219cf96672cec92b46245d2627c8b4d1cd16d1a2dfabd72b1`
and
`d315b3c463a13127f896a5ebc34c39dac30fd58894e87cd742536fa3c5197a69`.
The authenticated inner and root journal SHA-256 values are
`0f48196d86fe5c5551449d56f783cae81d6a1349933045c3ae53350424abc95b`
and
`af9485a9ef9e12020f11b20ac385a91a8d13910428ca8f6851e4882e291a7139`.
The pinned host pair verifier SHA-256 is
`79f16282cd5146a6407b995d32dbbfa9e9eea7fb7b5f6e7e6146c66b88d5360e`,
and its accepted output SHA-256 is
`469573a876ff43695b440b63fb589cbfdf071c6f36c266c507be9af24c13219b`.
The pinned v2 reference and fail-closed checker bind these values. The same
verifier rejected swapped levels, wrong outer image metadata, authenticated
journal mutation, and noncanonical outer JSON. Missing child-assumption
execution also rejected under the current image. This verifier is dynamically
linked, despite the reference schema's historical `static_verifier` field name;
the checker therefore keeps `runtime_rootfs_authenticated` false.

RISC0 3.0.5 build provenance must include nested Cargo. `risc0-build` removes
`RUSTUP_TOOLCHAIN` and every `CARGO*` variable before invoking bare `cargo`.
Therefore `cargo +risc0` does not by itself pin the guest Cargo executable.
Evidence builds must invoke the pinned Cargo binary directly, put its directory
first on `PATH`, and make nested offline mode a source-root Cargo config or an
externally enforced network boundary. The outer and nested Cargo executable,
version, compiler, dependency path, and config digest belong in the build
receipt.

Evidence capture must also exclude concurrent source mutation. The source
closure is frozen before the target-absent build and checked again after the
build. Reference assembly is rejected if the two closures differ. An immutable
source archive is preferred because an advisory workspace lock cannot stop an
uncooperative writer. Program bytes, image IDs, proofs, verifier bytes, and the
source root must be promoted atomically. A post-edit source root paired with a
pre-edit cached program is an internally inconsistent evidence record even
when each hash is well formed.

Dependency-path-independent equality, public replay, independently provisioned
cross-host rebuild equality, reproducible-release evidence, source or builder
authenticity, separately governed authority binding, settlement authorization,
and production admission remain false. The corresponding build controls,
authority evidence, and admission evidence remain open.

The verifier adapter accepts canonical authority-manifest bytes plus an
externally supplied manifest digest. It derives the executable digest, static
format policy, and trusted recursive expectations exclusively from that
manifest. The current manifest is local evidence; a ledger or release authority
must anchor its digest before production use.

The canonical recursive release-binding loader binds that authority-manifest
digest and the replay-manifest digest to chain, epoch, and proof profile under a
domain-separated config digest. Its Python value type is not an authorization
capability. Consumers must re-run the loader with expectations sourced from
governed state. That authority source and runtime admission integration remain
pending.

This lane claims computational integrity only. RISC0's all-version
GHSA-5xgj-pmjj-gw49 privacy advisory keeps zero-knowledge and witness privacy
outside the claim scope.

Every child descriptor must bind:

```text
ChildDescriptorV1 {
  child_image_id
  child_verification_claim_hash
  child_journal_hash
  child_effect_summary_hash
  child_statement_hash
  child_verifier_id
  child_profile
}
```

The root guest must reject:

- child proof from the wrong chain;
- child proof from the wrong epoch or height range;
- child image ID absent from `verifier_set_root`;
- child receipt kind absent from allowed profile;
- duplicate child lane where uniqueness is required;
- missing child lane where the partition requires it;
- child journal digest mismatch;
- child effect summary hash mismatch;
- child policy, feature, dependency, or toolchain mismatch;
- unbalanced aggregate deltas;
- duplicated receipts or cross-shard messages;
- cross-shard messages that neither cancel nor carry forward exactly once.

## Effect Summary Contract

For recursive scaling, every leaf proof should commit a canonical
`EffectSummaryV1`.

```text
EffectSummaryV1 {
  summary_version
  lane_id
  lane_kind
  chain_id
  epoch_or_height_range
  proof_profile
  image_id
  statement_hash
  pre_state_root
  post_state_root
  tx_root
  evidence_root
  receipt_root
  accepted_receipts_root
  rejected_receipts_root
  asset_delta_root
  cross_shard_outbox_root
  cross_shard_inbox_root
  write_set_root
  public_policy_hash
  feature_suite_hash
  dependency_lock_hash
  toolchain_lock_hash
}
```

`EffectSummaryV1` is the composition object. It must have:

- canonical field order;
- append-only schema evolution;
- explicit zero-root semantics;
- sorted, unique leaf IDs;
- sorted, unique receipt IDs;
- sorted, unique message IDs;
- bounded row counts;
- no opaque host-only side conditions.

## Conservation And Authority

Use construction over cancellation when possible.

Preferred pattern:

```text
debit_atoms = sum(inputs consumed)
credit_atoms = deterministic output from transition
fee_atoms = deterministic residual with explicit recipient
```

Then verify:

```text
debit_atoms + authorized_mint_atoms
  = credit_atoms + authorized_burn_atoms
```

Mint, burn, slash, reward, or protocol-fee effects require an authority root and
lane-specific policy. Ordinary spot settlement should have zero mint and burn.

No circuit should hide value movement inside an untyped journal blob. Every
asset movement needs a row with units and authority.

## Reject-Is-No-Op

All verifier and admission rejects must be no-op at the committed state layer.

Implementation pattern:

```text
parse -> validate statement -> stage transition -> verify bindings -> commit
```

Rejects before commit return a typed reason and leave state unchanged.

Every new proof-admission path needs at least:

- one accept-invariant test;
- one reject-is-no-op test;
- one malformed-proof or malformed-journal test;
- one cross-domain replay test.

## Canonical Encoding And Schema Evolution

Canonical bytes are consensus-critical.

Rules:

- include a domain separator in every hash;
- sort rows by explicit stable keys;
- reject duplicate keys;
- reject unknown critical fields;
- keep schema evolution append-only;
- distinguish empty, absent, and zero root where semantics differ;
- never hash re-encoded ambiguous objects;
- use explicit integer widths and checked conversions;
- keep field names unit-bearing at boundaries, for example `_atoms`, `_bps`,
  `_hash`, `_epoch`, `_height`, `_image_id`.

Any field reorder, serialization change, or root-construction change requires a
version bump or an explicit compatibility theorem/test.

## Rust Implementation Rules

For `zk/state_proof_risc0/**`:

- use typed structs and enums for statements, journals, profiles, reject
  reasons, receipt kinds, and lane kinds;
- avoid stringly typed modes in production paths;
- prefer checked arithmetic for all amounts, counts, and offsets;
- avoid `unwrap` or `expect` in production verifier/guest/shared paths;
- return typed errors or stable reject strings where existing ABI requires
  strings;
- avoid implicit `Default` for critical statement fields;
- use `serde(default)` only for append-only compatibility fields with explicit
  validation;
- keep host-only helpers outside guest authority assumptions;
- keep shared semantics aligned with Python core through parity tests or
  explicit non-claims.

Guest functions should be small enough to audit locally. When a guest function
mixes parsing, validation, transition, and journal construction, split it into:

```text
parse_input
validate_statement
verify_witness
run_transition
build_journal
commit_journal
```

## Circuit Complexity Budget

These are review budgets, not automatic rejection rules:

| Surface | Budget |
| --- | --- |
| guest public entry | dispatch only plus one call per proof family |
| verifier helper | one invariant family per function |
| function length | prefer under 60 lines on critical paths |
| branching | prefer under 12 decision points per critical function |
| nesting | prefer depth at most 3 |
| verifier panic paths | none in host verifier or shared production logic |
| guest abort paths | explicit `risc0_zkvm::guest::abort` for invalid witness rejection |
| public roots | bounded and named |
| witness rows | bounded by statement |

Exceeding a budget requires an explanation in review and stronger focused
tests. It does not justify broad refactoring during unrelated work.

## Required Evidence Matrix

Every circuit, journal, verifier, or CLI parser behavior change needs evidence
from the relevant rows.

| Change type | Required evidence |
| --- | --- |
| statement schema | constructor reject tests, canonical hash fixture, unknown critical reject |
| journal schema | canonical journal hash fixture, metadata equality rejects |
| RISC0 image ID | wrong-image negative test, all-zero image ID reject |
| RISC0 dependency baseline | offline affected-version, mixed-version, checksum, and feature rejects |
| proof profile | wrong receipt kind reject, dev profile reject |
| receipt envelope | exact codec marker, depth-limited decode, legacy-codec reject, metadata/verified-profile parity |
| guest witness check | mutation test that removes/inverts the check |
| asset deltas | conservation property or exhaustive bounded test |
| cross-shard messages | duplicate, missing, carry, and cancellation tests |
| recursive child verification | child substitution and child omission tests |
| CLI parser | malformed input, overflow, truncation, and unknown-mode tests |
| Python/Rust parity | shared fixture corpus or explicit non-claim |
| public claim update | claims registry or coverage matrix checker |

Use BDD-style scenario tests only for cross-layer user-visible behavior. For
proof correctness, prefer invariant-named unit/property/parity/mutation tests.

## Minimum Promotion Gate

Before a RISC0 circuit lane can be described as implemented, all of these must
hold:

1. Typed statement and journal are defined.
2. Production verifier rejects all-zero image IDs and placeholder methods.
3. Proof generation path verifies the produced receipt before emitting a report.
4. Admission verifier checks image ID, journal hash, proof profile, and metadata
   root equality.
5. An offline minimum advisory baseline rejects affected or mixed RISC0
   dependency graphs, and the release lane also performs a current advisory
   review.
6. Negative tests cover wrong image ID, wrong journal hash, wrong chain/config,
   wrong profile, stale verifier, malformed journal, and reject-is-no-op.
7. Python/Rust parity exists for any shared economic or settlement semantics.
8. Public docs name remaining gaps.

Before a recursive proof lane can be described as implemented, add:

1. Root guest verifies child receipts in guest.
2. Child verifier IDs are checked against `verifier_set_root`.
3. `EffectSummaryV1` composition checker exists outside the circuit.
4. Recursive root journal binds child verification-claim root, child journal
   root, and child summary root.
5. Negative tests cover omitted child, swapped child, duplicate receipt,
   duplicate message, unbalanced aggregate delta, missing DA root, and metadata
   drift.
6. At least one real proof smoke produces and verifies a root proof.

Before any production-ready claim, add:

1. Release manifest entry.
2. Claims registry update.
3. Public replay or smoke evidence with malformed-proof rejects.
4. Independent review of the circuit statement, journal, and verifier boundary.
5. Source/hash-pinned guest compiler, RISC0 binaries, ELFs, and image IDs.
6. Durable exact-once state committed atomically with value-moving effects.
7. A depth-limited receipt codec or resource-isolated decode boundary.

## Implementation Workflow

Use this sequence for new RISC0 proof work:

1. Read `AGENTS.md`, `zk/AGENTS.md`, and this spec.
2. Define the typed statement, journal, reject reasons, and profile before guest
   code.
3. Implement a deterministic non-ZK checker for the statement.
4. Add constructor, canonicalization, and malformed-input tests.
5. Implement or update the guest.
6. Add real receipt verification in the host path.
7. Add proof metadata and admission checks.
8. Add negative tests and parity tests.
9. Run the narrow RISC0 gate:

```bash
cd zk/state_proof_risc0 && cargo test --all
cd zk/state_proof_risc0 && cargo clippy --all -- -D warnings
```

For a real guest force-build, invoke the pinned RISC0 Cargo binary directly and
place its directory first on `PATH`. Confirm the nested Cargo executable and
version in the build receipt. A rustup proxy plus `cargo +risc0` is insufficient
for this purpose under `risc0-build` 3.0.5.

10. Run the relevant metadata or claims checker when public docs or proof
    profiles change.

## Review Checklist

Use this checklist before merging or promoting a circuit change:

- What is the exact typed statement?
- Which fields are public, private, committed, or irrelevant?
- Which private witness fields does the guest check?
- Which image ID is expected, and where is it bound?
- Which receipt profile is accepted?
- Which metadata roots must equal journal roots?
- What rejects are typed and stable?
- Is reject-is-no-op tested?
- Are all rows bounded?
- Are rows canonical, sorted, and duplicate-free?
- Is all arithmetic checked?
- Are public claims scoped to current evidence?
- Which disaster states remain possible, and what bounds them?

## Next Frontier

The highest-value implementation target is nonempty receipt-partition proof
evidence under the current image, followed by larger bounded-fanout evidence.
Same-profile distinct-leaf fanout-two evidence is complete at the bounded local
claim level described above. The next authority target is integration of
authenticated semantic V2 effects, the durable replay indexes, and independently
derived ZenoLedger value changes into one atomic transaction. Release-manifest
evidence, governed production header binding, and dedicated source-finality
certificates remain required for native-chain or cross-lane collateral
movements. zUSD still only exposes the current Rust
`DepositMint` lifecycle verb; later zUSD repay, redeem, or liquidation verbs must
add exhaustive row extractors before they can share the same recursive
asset-conservation claim.

Historical Spot Value Node V4 contributes bounded value disclosures and exact
retained-receipt replay. Its guest ABI also carries a host-declared self image.
Only the exact historical sealed verifier compares that declaration with the
image used for receipt authentication. Generic V4 journal decoding therefore
has no runtime-identity authority. The active value successor must follow the
Semantic V2 pattern: the guest commits a proof-neutral proposal, and a sealed
verifier attaches program identity, backend manifest, receipt-security profile,
and claim binding after cryptographic verification. Economic admission also
requires a canonical authorization-consumption nullifier independent of proof
program, receipt encoding, intent salt, and signature representation.
