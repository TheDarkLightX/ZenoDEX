# FCIS M6 E06 independent-connection concurrency schema

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

E06 exercises the E05 transaction through independent SQLite connections. Each
race uses a barrier and fresh connections against a fresh temporary database.
The E05 `BEGIN IMMEDIATE` transaction owns the linearization point. Results
are summarized only after every worker has joined and the complete durable
projection has been reopened.

## Required race families

```text
same exact command retried concurrently
two different commands with the same sender/nonce/nullifier
same commit ID with different fingerprints
commit racing a quiescence head change
commit racing an authority-switch head change
```

The first three races produce exactly one committed publication and one stale
predecessor rejection. The loser does not reach a second semantic publication;
a fresh E04 lookup is the later operation that distinguishes an already
committed retry from an absent retry.

The last two races hold `BEGIN IMMEDIATE` on the head-change connection before
releasing the barrier. The authority change linearizes first, the publisher
then observes the changed epoch/context, and the publication returns
`STALE_AUTHORITY_CAS`. The final durable layout has no publication, nullifier,
or effect rows.

## Evidence boundary

This harness proves repeatable behavior for the isolated SQLite model under
the tested connection settings. It does not prove production database
isolation, network transport behavior, a real migration phase machine,
authenticated runtime callers, process-crash recovery, destination
idempotency, accounting, backing, zUSD safety, or value movement.
