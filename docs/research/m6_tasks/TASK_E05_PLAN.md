# E05 plan: expected-root atomic CAS

Status: implemented and tested in the isolated E04-dependent research slice.

## Objective

Make the current-state root and authority epoch part of the same linearized
transaction that installs a publication, its nullifier, and all derived
effects. The E04 classifier must run over the verifier-owned predecessor and
matching reopen receipt inside that transaction.

## Procedure

1. Define a typed E05 request containing verified E04 attempt, predecessor,
   successor, and reopen-receipt values.
2. Reject crossed sequence, state, authority, writer, deployment, verifier,
   successor, and receipt subjects before any write.
3. Create a closed SQLite research schema with singleton head, publication,
   nullifier, and effect tables.
4. Begin `BEGIN IMMEDIATE` before reading the head.
5. Run E04 classification and compare the complete predecessor projection.
6. Execute one SQL CAS over all head fields, then insert all publication and
   uniqueness rows in the same transaction.
7. Reopen and compare the exact successor projection before commit.
8. Preserve stale-root, stale-authority, nested-corruption, uniqueness, and
   partial-insert rollback witnesses.

## Required evidence

- valid publication returns one commit receipt and one complete row set;
- the trace begins with `BEGIN IMMEDIATE` and the head update precedes inserts;
- old predecessor retries reject without changing rows;
- state and authority mutations reject without changing rows;
- nested attempt, missing effect, and crossed nullifier projections reject on
  reopen;
- SQL uniqueness and trigger rollback behavior remain typed;
- independent vector/checker replay, Ruff, strict mypy, compilation, and
  focused tests pass.

## Nonclaims

This slice is an isolated research adapter. It does not establish production
authentication, datastore receipt authenticity, filesystem/WAL/fsync
durability, process-crash recovery, production isolation settings,
concurrent linearizability, runtime no-bypass coverage, destination
idempotency, migration mounting, accounting, backing, zUSD safety, or value
movement. E05 does not close H02's complete DRA publication path or promote M6.
