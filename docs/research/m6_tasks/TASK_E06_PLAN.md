# E06 plan: real concurrency harness

Status: implemented and tested in the isolated E05-dependent research slice.

## Objective

Exercise E05 with independent database connections and barriers. Show that
same-command retries, same-sender/nonce commands, duplicate IDs with changed
fingerprints, and authority-context races have one linearized outcome and
leave no partial publication rows.

## Procedure

1. Seed each temporary SQLite database through the E05 initializer.
2. Construct two verifier-owned E05 requests for each race family.
3. Open an independent connection per worker and synchronize at a barrier.
4. Collect typed results after both workers finish.
5. Reopen the full durable layout and compare publication, nullifier, and
   effect cardinalities.
6. For quiescence and authority-switch races, let the head-changing worker
   acquire `BEGIN IMMEDIATE` before the publisher is released.
7. Repeat the complete campaign and require byte-identical summaries.

## Required evidence

- five named race families are present;
- first three have one `committed` and one `stale_snapshot_cas` result;
- authority races have one head change and one `stale_authority_cas` result;
- no race leaves mismatched publication, nullifier, and effect counts;
- independent vector/checker replay and focused tests pass;
- Ruff, strict mypy, compilation, and formatting pass.

## Nonclaims

E06 remains an isolated SQLite research harness. It does not prove production
isolation or linearizability, real migration authority, crash recovery,
runtime no-bypass coverage, destination authenticity/idempotency, accounting,
backing, zUSD safety, or value movement. M6 remains unmounted.
