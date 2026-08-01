# I08 plan: honest delivery contract

Status: implemented and tested as a fail-closed claim registry; research-only
and unmounted. The contract does not promote I02-I07 to production behavior.

## Objective

Keep documentation and API vocabulary aligned with the actual outbox model:

```text
atomic enqueue
at-least-once attempts
stable idempotent semantic identity
provenance-bound acknowledgment
```

The claim checker freezes those four supported phrases, rejects unsupported
exactly-once wording in positive claims and API names, requires the explicit
network/destination/mounting nonclaims, and checks that the human contract
document contains exactly four positive Claim lines.

## Evidence boundary

I08 is a documentation and claim-surface gate. It does not prove atomic
datastore behavior, destination idempotency, receipt bytes, local journal
durability, network delivery, runtime mounting, migration, no-bypass
coverage, accounting, backing, or zUSD safety. M6 remains unmounted and
non-promotable.
