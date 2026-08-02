# FCIS M6 E03: database uniqueness and atomic identity publication

E03 is a research-only refinement of the E02 nullifier relation into a
small datastore boundary. The pure input is a verifier-derived E02 nullifier
and one complete commit identity aggregate. The SQLite shell publishes the
commit row, its nullifier projection, and all derived effect rows in one
transaction.

## Identity contract

The verifier-owned aggregate contains:

```text
sequence
commit_id
E02 nullifier witness
ordered effect specifications
```

The aggregate retains the E02 `nullifier_root` and
`request_identity_root`. Every effect ID is derived by the DRA effect-ID
function from:

```text
commit_id, ordinal, destination, payload_root, writer_profile_root
```

The fingerprint is:

```text
H("zenodex/fcis/m6/e03/commit-fingerprint/v1" || 0x00 || canonical_json(
  schema, sequence, commit_id, nullifier_root, request_identity_root,
  ordered derived effect rows
))
```

The effect collection is an exact tuple, canonically ordered by contiguous
ordinals from zero, and bounded by `MAX_OUTBOX_PER_TRANSITION`.

The fingerprint is retained as an immutable seal and is freshly recomputed
from the complete source fields at every verifier and persistence boundary.
Verification independently derives a second E03 aggregate from the retained
E02 nullifier, sequence, commit ID, and effect tuple. No process-global object
registry or object-ID snapshot participates in acceptance.

## SQL constraints

`fcis_m6_e03_uniqueness_v1.sql` defines three logical relations:

| Relation | Authority and constraint |
| --- | --- |
| `e03_publication_commits` | `sequence` primary key; `commit_id` and `nullifier_root` unique; exact digest checks; composite identity uniqueness |
| `e03_publication_nullifiers` | `nullifier_root` primary key; one nullifier per commit; composite foreign key binds commit, nullifier, and fingerprint to the commit row |
| `e03_publication_effects` | `effect_id` primary key; foreign key to the commit; unique `(commit_id, ordinal)`; bounded ordinal and exact digest checks |

The Python adapter verifies the complete staged rows before commit. SQLite
constraints remain the final collision authority. Before opening the
transaction, the adapter requires:

```text
no caller-owned active transaction
foreign_keys = ON
exact main-schema descriptor = descriptor produced by the pinned migration
```

After acquiring `BEGIN IMMEDIATE`, the adapter repeats the foreign-key and
exact-schema checks before its first write. The acquired write reservation
closes the cross-connection DDL window for the remaining transaction. The
exact descriptor rejects pre-existing loose tables, added triggers, views,
indexes, and other schema drift.

The adapter records whether `BEGIN IMMEDIATE` succeeded and rolls back only a
transaction it acquired. A caller transaction present at entry, or started in
the interval before E03 acquires its transaction, is rejected without E03
rolling it back. A constraint or SQLite failure after acquisition rolls back
the entire adapter-owned transaction, so a commit row cannot survive a failed
nullifier or effect insertion.

## Rejection rules

```text
invalid candidate, schema, pragma, or transaction ownership -> INVALID_REQUEST
duplicate commit/nullifier/effect/ordinal -> CONSTRAINT_COLLISION
malformed staged row, denied write, busy, or other SQLite failure -> SQL_ROLLBACK
valid complete aggregate -> COMMITTED
```

The E03 port does not classify an exact duplicate as an already-committed
retry. E04 owns the durable retry partition after reading the stored
fingerprint, command identity, expected root, and current state.

## Evidence boundary

The tests cover successful complete insertion, deterministic source replay,
nested mutation rejection, duplicate commit identity,
same-nullifier/different-commit collision, direct effect-ID constraint
collision, rollback after a denied partial insert, loose-schema rejection,
point-of-use schema and foreign-key drift, schema drift between the precheck
and transaction acquisition, caller-owned transaction preservation at entry
and after the precheck, exact-type rejection, and two concurrent duplicate
insertions with exactly one committed winner.

The adapter is an isolated SQLite experiment. It does not prove filesystem
durability, WAL/fsync configuration, process-crash recovery, production
authentication, global caller coverage, destination idempotency, runtime
mounting, migration authority, accounting, backing, zUSD safety, or value
movement.
