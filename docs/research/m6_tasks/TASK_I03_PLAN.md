# I03 plan: safe outbox leasing

Status: implemented and tested in the isolated SQLite adapter; research-only
and unmounted. Later I04-I08 slices are recorded separately.

## Objective

Provide a typed worker lease port over the committed outbox. A worker supplies
an already committed `effect_id`, an opaque worker label, and explicit logical
time. The adapter derives the lease expiry, reads the canonical effect and
operational row, and updates the row with one `BEGIN IMMEDIATE` transaction.

The only claimable states are:

```text
PENDING
LEASED with lease_expiry <= now
```

An expired lease is first reclassified to `PENDING` inside the same
transaction, then claimed by the new worker. Attempt count increases exactly
once. The returned payload, destination, adapter profile, and `effect_id` are
copied from the canonical committed atom; the request cannot supply any of
those semantic fields.

## Evidence boundary

I03 covers explicit-time lease expiry arithmetic, atomic acquisition, active
lease exclusion, expiry reaping, attempt-count overflow rejection, missing
effect rejection, and stable effect/payload identity across workers. It does
not implement destination delivery, deduplication, acknowledgment provenance,
lost-ack recovery, retry scheduling, production datastore behavior, or
runtime mounting. M6 remains unmounted and non-promotable.
