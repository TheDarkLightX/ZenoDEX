# I04 plan: destination deduplication contract

Status: implemented and tested in an immutable deterministic destination
model; research-only and unmounted. I07-I08 remain pending.

## Objective

Represent the minimum acceptable destination contract for a stable semantic
effect identity. The verifier accepts exactly one of:

```text
native idempotency key
query by effect ID
application-owned destination receipt table
```

The model consumes a verifier-produced contract witness and a canonical
`OutboxEffectV1`. The contract witness has verifier registration and an
unchanged-field snapshot that are checked again at delivery. It records
accepted effects by effect ID, destination, and payload root, with at most
8,192 destination receipt records. A duplicate attempt returns
`ALREADY_ACCEPTED` with the same destination receipt root. A same-ID payload or
destination change returns a typed rejection with no successor state. A new
effect at exact capacity and an invalid contract do the same. Accepted delivery
owns the exact successor state and matching receipt in one immutable aggregate.
Nested records and the accepted state/receipt relation are revalidated at every
boundary. Because the transition is pure, callers retain their immutable
pre-state on every rejection.

Unsupported mechanisms and forged contract roots return `UNMOUNTABLE`; no
effect type is mountable on a merely asserted exactly-once claim.

## Evidence boundary

I04 covers verifier provenance and fresh-use validation, the verifier-gated
contract shape, three mechanism branches, observational duplicate idempotence,
payload/destination/profile binding, closed collection capacity, and canonical
destination-record collections. Rejection carries no substitute successor or
receipt. It does not prove any real network
destination, native idempotency implementation, query behavior, receipt
provenance, worker delivery, lost-ack recovery, production datastore behavior,
or runtime mounting. M6 remains unmounted and non-promotable.
