# I02 plan: committed outbox schema

Status: implemented and tested in the isolated SQLite adapter; research-only
and unmounted. I03-I08 remain pending.

## Objective

Make each semantic outbox effect a durable row inserted with its publication
atom. The row carries the stable semantic fields plus typed operational state:

```text
status
lease owner and expiry
attempt count
last error
acknowledgment receipt root
```

The isolated adapter treats `payload_root` as the canonical payload reference.
Operational changes are excluded from `derive_effect_id` and therefore cannot
mint a second semantic effect.

## Evidence boundary

I02 covers schema constraints, initial pending-row insertion for a nonempty
canonical seed, typed operational reconstruction, semantic-ID stability, and
orphan rejection. It does not implement worker leasing, destination
deduplication, acknowledgment provenance, lost-ack recovery, or production
datastore behavior. M6 remains unmounted and non-promotable.

