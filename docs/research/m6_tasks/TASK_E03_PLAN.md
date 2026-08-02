# E03 plan: database uniqueness constraints

Status: implemented and tested in an isolated SQLite adapter; research-only
and unmounted.

## Objective

Refine the E02 verifier-owned nullifier into a complete unique-commit identity
aggregate and publish its commit, nullifier, and derived effect rows in one
transaction. The datastore must reject duplicate commit IDs, nullifiers,
effect IDs, and per-commit ordinals through actual constraints.

## Contract

```text
verified E02 nullifier + complete commit/effect aggregate
  -> one atomic INSERT set
  -> COMMITTED
  | CONSTRAINT_COLLISION / SQL_ROLLBACK / INVALID_REQUEST
```

The SQL migration is the authoritative schema artifact for this bounded slice.
The Python adapter performs canonical staged-row revalidation and relies on
SQLite primary keys, unique constraints, foreign keys, and transaction
rollback for the final datastore decision.

## Required evidence

- migration SQL with exact digest and collection bounds;
- canonical E03 vector derived from E02;
- successful complete insertion;
- duplicate commit and same-nullifier collision rejection;
- effect-ID and `(commit_id, ordinal)` uniqueness rejection;
- rollback after an injected partial-insert failure;
- concurrent duplicate insertion with exactly one winner;
- exact-type, forged-witness, mutation, Boolean, bound, and canonical-order
  rejection tests;
- focused Python quality gates and packet manifest validation.

## Nonclaims

E03 does not implement cryptographic authentication, production database
durability, filesystem/WAL/fsync policy, crash recovery, retry
classification, destination idempotency, runtime caller mounting, authority
switching, accounting, backing, zUSD safety, or value movement. E04 must
classify durable collisions and indeterminate client observations. M6 remains
research-only, unmounted, and non-promotable.
