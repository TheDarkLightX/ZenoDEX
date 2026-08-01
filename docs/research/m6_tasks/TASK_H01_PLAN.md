# FCIS M6 Task H01 Plan

TASK_ID: H01
BASE_SHA: a9eba746a5913649e2977ca5517ce8c42b470cae
SOURCE_HEAD_SHA: 476ec022e755ff049c39bf9f08c6606ac87532ca
SOURCE_HEAD_TREE: a1d495eae0b26a369487ceb48cad5472abec74db

## Objective

Freeze a field-to-column matrix for the durable-retraction publication atom.
The matrix must cover every field of `PublicationAtomV1`, identify one
canonical logical table location or one deterministic projection, and state
the relation that a future SQLite/PostgreSQL adapter must check.

## Scope

This task covers the research model in
`src/core/fcis_durable_retraction.py` and its canonical reconstruction
functions:

- `PublicationAtomV1`;
- `AuthorityStateV1` and its ordered writer-set projection;
- `DurableSnapshotV1`;
- `_evidence_rows`, `_nullifier_rows`, `_outbox_rows`;
- `_snapshot_root_without_cache`, `encode_history`, and `reopen_snapshot`.

The output defines logical table names and constraints for refinement. It does
not implement a datastore adapter or claim that any production database has
these tables.

## Acceptance

Every atom field appears exactly once in the machine-readable matrix. Each
entry names either a canonical column or a deterministic projection and gives
an explicit equality, ordering, cardinality, or foreign-key relation. The
checker must report `H01_TABLE_MATRIX_MATCH`.

## Procedure

1. Freeze the reviewed source identities above.
2. Enumerate `dataclasses.fields(PublicationAtomV1)` in declaration order.
3. Map scalar fields to `publication_atoms`, context fields to the canonical
   `snapshot_meta` header with checked atom-row copies, and `outbox` to the
   ordered `publication_outbox` projection.
4. Add the authority, evidence, nullifier, acknowledgment, and snapshot
   relation tables needed to make the projection complete.
5. Record the exact fixed-point relations used by `encode_history` and
   `reopen_snapshot`.
6. Run the standalone matrix checker and the ordinary Python quality gates.

## Evidence boundary

The matrix is a checked refinement contract for H01. It does not establish
transaction atomicity, crash durability, SQL isolation, concurrent
linearization, destination idempotency, runtime reachability, or value
movement. Those are H02-H08 and later M6 obligations.
