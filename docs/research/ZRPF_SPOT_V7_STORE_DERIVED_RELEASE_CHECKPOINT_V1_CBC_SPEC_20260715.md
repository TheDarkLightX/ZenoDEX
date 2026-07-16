# Spot V7 Store-Derived Release Checkpoint V1 CBC Specification

Status: authority-neutral implementation contract

Date: 2026-07-15

## Purpose

The canonical release-checkpoint codec validates bytes, field relationships,
and checkpoint hashes. Raw checkpoint bytes remain caller-proposed data. This
contract defines the stronger provenance transition:

```text
exact Store V3 object
  -> complete Store V3 replay
  -> complete replayed cursor history and immutable store identity
  -> reconstruct every canonical checkpoint from genesis
  -> exact internally derived parent-chain validation
  -> private StoreDerivedReleaseStateCheckpointV1
```

No raw checkpoint document, cursor, mapping, Boolean, path, or caller-created
status may substitute for the direct Store V3 replay.

## Construction

The derivation function accepts only the exact final Store V3 implementation.
It invokes one Store-owned complete-history replay under one read transaction
and reads the immutable configured identity. It reconstructs genesis and every
successor checkpoint from the returned cursor sequence. Genesis receives the
zero parent. Every later parent hash is derived from the immediately preceding
checkpoint produced in the same call. No parent argument exists.

This structure prevents a valid checkpoint from another Store file with the
same configured identity from supplying lineage. It also permits a reopened
non-genesis Store to reconstruct the exact head without a retained in-memory
parent object.

The derived checkpoint retains only canonical checkpoint bytes. Every data
projection reparses those bytes and rechecks the checkpoint hash. Normal
construction, mutation, copying, deep copying, and serialization reject.

## Authority boundary

The private derived type establishes only that the bytes were constructed from
one successful local Store V3 complete-history replay and its internally
reconstructed parent chain during that call. It does not establish currentness after return, external finality,
external monotonicity, same-UID rollback resistance, release authority, runtime
authority, settlement authority, or production authority.

A future finality adapter may consume the private derived type. It must not
consume the raw codec document type.

## Required negative evidence

Tests must reject:

1. direct construction of the derived type;
2. any caller-supplied parent argument or raw parent document;
3. a noncontiguous replayed cursor history;
4. substitution of a same-identity divergent Store history;
5. failure to reproduce the exact head after a cold restart;
6. raw arbitrary genesis or standalone-revocation bytes as provenance;
7. mutation, copying, serialization, or authority promotion;
8. a retained-byte or parsed-document hash mismatch.

## Pending external obligation

An externally monotonic highest-observed event watermark is required before an
older finalized checkpoint can be treated as current after local rollback. The
counterexample is:

```text
finalized selection F1
  -> locally authenticated revocation R2 is observed
  -> local database is restored to L1
  -> operation remains paused because the external watermark remembers R2
```

This module cannot satisfy that obligation with another local file or SQLite
database.
