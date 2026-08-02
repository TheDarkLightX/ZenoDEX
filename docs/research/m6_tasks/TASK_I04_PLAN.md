# I04 plan: destination deduplication contract

Status: implemented and tested in an immutable deterministic destination
model; research-only and unmounted. I05-I08 remain pending.

## Objective

Represent the minimum acceptable destination contract for a stable semantic
effect identity. The verifier accepts exactly one of:

```text
native idempotency key
query by effect ID
application-owned destination receipt table
```

The model consumes a verifier-produced contract witness and a canonical
`OutboxEffectV1`. It records accepted effects by effect ID, destination, and
payload root, with at most 8,192 destination receipt records. A duplicate
attempt returns `ALREADY_ACCEPTED` with the same destination receipt root. A
same-ID payload or destination change rejects without changing destination
state. A new effect at exact capacity returns a typed capacity rejection
without changing destination state.

Unsupported mechanisms and forged contract roots return `UNMOUNTABLE`; no
effect type is mountable on a merely asserted exactly-once claim.

## Evidence boundary

I04 covers the verifier-gated contract shape, three mechanism branches,
observational duplicate idempotence, payload/destination/profile binding,
closed collection capacity, and canonical destination-record collections. It
does not prove any real network
destination, native idempotency implementation, query behavior, receipt
provenance, worker delivery, lost-ack recovery, production datastore behavior,
or runtime mounting. M6 remains unmounted and non-promotable.
