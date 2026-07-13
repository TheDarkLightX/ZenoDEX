# ZRPF sharded recursive proof review

Date: 2026-07-13

Source reviewed: [Sharded Recursive zk-SNARK Proofs](https://ethresear.ch/t/sharded-recursive-zk-snark-proofs/19480), Ethereum Research, 2024-05-06.

## Decision

The source contains one useful architectural decomposition for ZRPF:

```text
authenticated local shard transition proofs
    -> authenticated shard summaries
    -> deterministic global merge relation
    -> one recursively verified global proof
```

ZRPF should retain this decomposition. Its current proof-neutral
`parallel_shard_epoch_v1` is a bounded two-shard precursor. A later proof
profile may make each shard summary recursively verifiable after the
current-source V6 settlement path has fresh identity and receipt evidence.

The source's numerical throughput, proof-size, verification-complexity, and
privacy claims are not ZRPF evidence. ZRPF remains witness-public and makes no
zero-knowledge privacy claim.

## Technical cautions

The post is an informal construction sketch rather than a complete security or
performance argument. In particular:

- Constant-size final proof bytes do not imply constant proving work. The
  coordinator relation verifies every admitted shard proof and merges every
  admitted shard summary, so coordinator proving work and input acquisition
  remain at least linear in the number of immediate children unless another
  evidenced aggregation layer changes that bound.
- The stated `O(log shards)` final-verification cost is scheme- and statement-
  dependent. A recursively wrapped proof can have verification cost independent
  of the represented shard count; membership checks or a partially exposed tree
  can add logarithmic work. The post does not derive which case applies.
- The quoted transaction-throughput figures assume shard execution, proving,
  aggregation, data availability, communication, and consensus all sustain the
  selected parameters. They are capacity arithmetic rather than measurements.
- The Verkle comparison counts neither the concrete polynomial-commitment
  opening bytes nor multi-opening, transcript, field, and security-parameter
  costs. It cannot support the claimed bit sizes or savings without a concrete
  commitment scheme and benchmark.
- The cross-shard relation does not fully specify message identities,
  single-consumption nullifiers, delivery or cancellation, ordering, rollback,
  or atomicity. A valid local transition proof alone cannot prevent duplicate
  or inconsistent cross-shard economic effects.
- Zero knowledge is a property of a concrete proving system and statement. The
  post's honesty and privacy assertions do not account for public balance
  vectors, shard assignment, timing, access patterns, coordinator metadata, or
  data-availability leakage. They do not transfer to ZRPF's current
  witness-public RISC0 receipt profile.

These cautions do not invalidate the local-proof/global-merge decomposition.
They define the additional obligations needed before the decomposition can
support a ZRPF scaling, settlement, or privacy claim.

## Local shard statement

A future recursive shard statement should bind at least:

```text
application_id
domain_id
epoch_id
shard_id
shard_set_root
shard_partition_policy_root
proof_profile_id
program_manifest_root

shard_pre_state_root
shard_post_state_root
shard_semantic_values_root
shard_action_nullifiers_root
shard_conservation_root
cross_shard_outbox_root
cross_shard_inbox_root
carry_queue_pre_root
carry_queue_post_root
data_availability_commitment
```

The guest must derive these fields from authenticated child transitions and
typed state witnesses. Host-provided roots remain proposals until the guest
recomputes them.

## Global merge statement

The global guest should verify every immediate child receipt before decoding
its journal, enforce the declared shard set exactly, and derive:

```text
global_pre_state_root
global_post_state_root
global_semantic_values_root
global_action_nullifiers_root
global_conservation_root
global_outbox_root
global_inbox_root
global_carry_pre_root
global_carry_post_root
semantic_epoch_root
proof_tree_root
```

`semantic_epoch_root` should depend on the canonical keyed shard map and stay
independent of a valid proof-tree grouping. `proof_tree_root` should bind the
actual programs, receipts, child journals, and aggregation topology.

For the first promoted profile, cross-shard inbox, outbox, and carry channels
may remain empty-only. Nonempty channels require exact message identities,
single-consumption rules, ordering, cancellation or delivery semantics, and
durable replay indexes.

## Scaling contract

Recursion compresses final verification. It does not remove proving,
aggregation, communication, data-availability, or coordination work.

For `s` shards and a balanced fanout `k`, the proof-tree depth is

\[
D = \lceil \log_k s \rceil.
\]

With sufficient parallel workers, a useful latency model is

\[
T_{root} \approx T_{leaf} + D T_{aggregate} + T_{coordination}.
\]

Coordinator input remains at least proportional to the number of immediate
child summaries it receives. The promoted profile must state measured bounds
for fanout, depth, journal bytes, proof bytes, memory, cycles, wall time, and
data-availability bandwidth.

## Required evidence before promotion

1. A typed recursive shard journal with an exact bounded codec.
2. Child receipt verification before child journal interpretation.
3. Canonical declared-shard-set and keyed-state-map enforcement.
4. Pre/post state continuity and exact state-update witnesses per shard.
5. Global action-nullifier uniqueness independent of proof encoding and tree
   position.
6. Conservation and authorized transformation proofs over the merged shard
   summaries.
7. Negative controls for missing, duplicated, reordered, substituted, and
   cross-epoch shards.
8. Nonempty cross-shard message evidence before enabling those channels.
9. A separate data-availability certificate and a separate finality
   certificate.
10. Durable atomic admission of the verified global transition and every
    replay/nullifier index.
11. Current-source program identities, fresh receipts, mutation rejection,
    reproducible release evidence, and independent review.
12. A measured full-profile benchmark. Architecture arithmetic does not
    qualify as throughput evidence.

## Current boundary

`parallel_shard_epoch_v1` currently establishes a bounded, proof-neutral
composition law for exactly two declared shards. It binds shard identity,
scope, profile, state scheme, pre/post roots, semantic values, action
nullifiers, message roots, carry roots, a topology-independent semantic root,
and a topology-binding proposal hash. Its present message and carry policy is
empty-only.

It does not verify recursive shard receipts, authorize settlement, prove data
availability, establish finality, or support arbitrary shard counts. Those
properties remain separate CBC obligations.
