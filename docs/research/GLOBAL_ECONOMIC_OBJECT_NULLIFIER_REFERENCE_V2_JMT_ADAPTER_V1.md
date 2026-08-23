# Global Economic Object Nullifier V2 JMT Adapter V1

Date: 2026-08-23
Status: implemented experimental differential adapter; unmounted; unproved; no authority

## Purpose and claim

This adapter tests whether the existing JMT candidate can represent each
validated archive accepted by the bounded V2 object-nullifier reference. It
defines this projection:

```text
reference object_id                         -> raw decoded 32-byte JMT key
reference first_consumed_by_occurrence_id   -> raw decoded 32-byte JMT value
```

For an archive `A`, the relation `R(A, E)` holds when `E` is exactly the
ordered tuple of those key/value pairs. The adapter computes a candidate root
from `E` and emits bounded canonical membership or absence transcripts. Proof
dataclasses do not cross the adapter boundary.

The adapter does not call the reference transition or digest functions. Tests
apply the unchanged reference transition and independently compare the
projected successor map, candidate root, and witnesses.

## Frozen experimental boundary

- Adapter version: `1`.
- Inputs are exact immutable V2 reference archive and identifier types.
- Roots are exact lowercase `0x`-prefixed 32-byte hexadecimal strings.
- Witnesses are exact canonical JMT JSON bytes, capped at 32,768 bytes.
- Membership binds the raw object ID key to the raw first-occurrence ID value.
- Absence binds the raw object ID query to the supplied candidate root.
- Malformed types, roots, wires, oversized wires, and proof mutations fail
  closed at verification.

The raw key/value projection deliberately has no object-nullifier schema or
version prefix. This keeps the experiment a minimal refinement probe. The
missing binding makes the candidate root ineligible as a final ABI root.

## Evidence obligations

The executable portfolio covers:

- fixed empty, one-row, and two-row roots plus projection bijection;
- accepted-step map extension, old-binding preservation, pre-absence, and
  post-membership;
- rejection precedence and no-successor behavior through the unchanged oracle;
- empty-step identity and claim-order root invariance;
- bounded stateful histories against an independent dictionary model;
- every subset and insertion permutation of six IDs against one canonical root
  per subset;
- claim-count BVA at 0, 1, 63, 64, and 65;
- archive BVA at 4,095, 4,096, and attempted 4,097 rows;
- malformed, noncanonical, wrong-root, wrong-key, wrong-value, and one-bit
  witness mutations;
- retained-alias snapshots and constructor-forged input rejection;
- adjacent nonzero keys with a 256-sibling witness as a negative scalability
  frontier;
- one-way import and release-bundle isolation.

## Negative scalability frontier

The existing compact tree can carry 256 sibling frames for adjacent 256-bit
keys that diverge at the final bit. The test records the exact canonical wire
size and requires it to remain below the 32 KiB adapter envelope. This is a
bounded regression observation. It gives no RISC0 cycle, throughput, storage,
or production-capacity claim.

## Promotion blockers

An authoritative object-nullifier design still requires:

- globally authenticated object-ID provenance and alias resistance across
  chain, deployment, migration, release, route, and profile changes;
- a domain-separated and version-retained key/value/root encoding;
- authenticated incremental batch updates or a canonical multiproof;
- durable version storage, atomic publication, rollback resistance, pruning,
  migration, and historical import;
- proof byte, guest cycle, memory, and storage ceilings;
- Rust and RISC0 refinement plus executable formal-to-runtime bindings;
- a separately versioned nullifier lane or subroot with trusted pre-root
  anchoring and atomic post-root publication;
- release-image, receipt, writer, governance, and emergency-revocation rules.

The adapter is excluded from runtime, release, proof, state-root, publication,
and governance surfaces. It does not alter the existing top-level app-root JMT
or perps source-fact root. `production_authority=NONE` and global production
readiness remains false.

## Replay

```text
PYTHONDONTWRITEBYTECODE=1 python3 -B -m pytest -q -p no:cacheprovider \
  tests/core/test_global_economic_object_nullifier_reference_v2_jmt_adapter_v1.py \
  tests/core/test_global_economic_object_nullifier_reference_v2.py \
  tests/core/test_global_economic_object_nullifier_reference_v2_isolation.py \
  tests/state/test_jmt.py
```

The exact source hashes and required pytest nodes are recorded in
`THV1-20260823-global-economic-object-nullifier-reference-v2-jmt-adapter-v1`.
