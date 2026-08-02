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

## SQL constraints

`fcis_m6_e03_uniqueness_v1.sql` defines three logical relations:

| Relation | Authority and constraint |
| --- | --- |
| `e03_publication_commits` | `sequence` primary key; `commit_id` and `nullifier_root` unique; exact digest checks; composite identity uniqueness |
| `e03_publication_nullifiers` | `nullifier_root` primary key; one nullifier per commit; composite foreign key binds commit, nullifier, and fingerprint to the commit row |
| `e03_publication_effects` | `effect_id` primary key; foreign key to the commit; unique `(commit_id, ordinal)`; bounded ordinal and exact digest checks |

The Python adapter verifies the complete staged rows before commit. SQLite
constraints remain the final collision authority. A constraint failure rolls
back the entire transaction, so a commit row cannot survive a failed
nullifier or effect insertion.

## Rejection rules

```text
invalid candidate or connection -> INVALID_REQUEST
duplicate commit/nullifier/effect/ordinal -> CONSTRAINT_COLLISION
trigger, malformed staged row, busy, or other SQLite failure -> SQL_ROLLBACK
valid complete aggregate -> COMMITTED
```

The E03 port does not classify an exact duplicate as an already-committed
retry. E04 owns the durable retry partition after reading the stored
fingerprint, command identity, expected root, and current state.

## Evidence boundary

The tests cover successful complete insertion, duplicate commit identity,
same-nullifier/different-commit collision, direct effect-ID constraint
collision, rollback after a partial-insert trigger, exact-type and mutation
rejection, and two concurrent duplicate insertions with exactly one committed
winner.

The adapter is an isolated SQLite experiment. It does not prove filesystem
durability, WAL/fsync configuration, process-crash recovery, production
authentication, global caller coverage, destination idempotency, runtime
mounting, migration authority, accounting, backing, zUSD safety, or value
movement.
