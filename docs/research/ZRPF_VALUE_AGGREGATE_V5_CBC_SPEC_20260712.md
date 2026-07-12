# ZRPF Value Aggregate V5 CBC Specification

Date: 2026-07-12

Status: protocol proposal in implementation; recursive guest, receipt evidence,
and settlement authority pending

## Purpose

Value Aggregate V5 is the proof-neutral statement shared by bounded value
aggregation guests. It carries one complete `SemanticSubtreeV2`, the exact
execution scope, and the authenticated child projections used to derive that
subtree. Runtime self-image identity is intentionally absent.

The first governed profile is bounded to two aggregate levels, eight children
per node, and 64 represented leaves. It preserves the existing V4 state-chain,
asset-flow, issuance-use, transaction-uniqueness, and source-uniqueness rules.

## Authority progression

```text
bounded child receipt bytes
  -> verify each exact governed child image and journal
  -> strict child journal decode
  -> derive child descriptor from verified image plus journal
  -> merge child SemanticSubtreeV2 values
  -> construct ProposedValueAggregateV5
  -> commit exact canonical proposal bytes
  -> outer verifier authenticates parent receipt and attaches runtime identity
```

The protocol constructor and decoder authenticate no receipt. They establish
canonical shape, boundedness, child ordering, scope agreement, and deterministic
hashes only.

## Proposal fields

```text
proposal version
aggregate level
full NodeScopeV3
merged SemanticSubtreeV2
ordered child descriptors
child descriptors root
child claims root
child journals root
child programs root
child manifests root
dependency manifest root
derived operational-commitment bundle
proposal commitment
```

Each child descriptor binds:

```text
child level
partition
verified child program ID
child proof profile ID
child program manifest root
exact child journal hash
RISC0 verified-claim binding
child semantic-subtree root
child operational-commitment bundle
```

The operational bundle contains exactly:

```text
data availability root
data availability certificate root
conflict schedule root
cross-lane outbox root
cross-lane inbox root
cross-lane message-IDs root
carry-queue pre-root
carry-queue post-root
```

At level one, each child bundle is projected from the exact V4 structural
journal after the receipt-verification precondition. The V4
`conflict_schedule_hash` is carried as the V5 `conflict_schedule_root`. At
level two, each child bundle is projected from the exact V5 child proposal.
Every parent field is a distinct domain-separated ordered root over the same
field in its immediate children. The canonical bundle hash enters every child
descriptor hash and the parent proposal commitment.

These operations authenticate and aggregate opaque commitments. They do not
interpret the committed data or establish operational semantics.

The proposal requires:

```text
1 <= child count <= 8
parent level in 1..=2
every child level == parent level - 1
child partitions are ordered, contiguous, and cover the merged subtree
child journal hashes are unique
child claim bindings are unique
scope.canonical_hash == semantic_subtree.scope_hash
scope represents exactly one epoch
dependency manifest is derived from the ordered child dependency descriptors
all eight parent operational commitments are derived from ordered child values
all stored roots and the proposal commitment recompute exactly
```

## Runtime identity rule

The proposal contains child runtime identities because a parent guest derives
them from the images used by `env::verify`. It contains no parent runtime image
or parent program manifest. The sealed outer verifier attaches those values
after cryptographically verifying the parent receipt.

## Required negative controls

1. zero or excessive children;
2. mixed or skipped child levels;
3. reordered, overlapping, or gapped child partitions;
4. duplicate child claim or journal identity;
5. child semantic root substitution;
6. child program, profile, or manifest substitution;
7. scope hash, epoch, application, or domain substitution;
8. dependency-manifest substitution;
9. merged semantic-subtree substitution;
10. mutation of any child operational-commitment field;
11. mutation of any derived parent operational-commitment field;
12. trailing, oversized, or noncanonical encoding.

## Explicit non-claims

This proposal supplies no receipt, recursive proof, image ID for the parent,
source finality, data availability, data-availability certificate validity,
conflict-schedule validity, cross-lane message uniqueness or cancellation,
carry continuity, economic-action normalization, settlement plan binding,
ledger admission, release authority, privacy, throughput, or production
authority. Operational-root propagation alone advances none of these claims.

Promotion requires the two governed aggregate guests, sealed receipt verifier,
current-image multi-leaf proof evidence, maximum-topology resource evidence,
and exact negative replay corpus.
