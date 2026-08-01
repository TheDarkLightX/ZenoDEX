# I01 plan: stable semantic effect identity

Status: implemented and tested in the isolated durable-retraction model;
research-only and unmounted. I02-I08 remain pending.

## Objective

Freeze executable vectors for the semantic effect identity used by the DRA
outbox contract. The identity is derived from the committed semantic atom:

```text
H(commit_id, ordinal, destination, payload_root, writer_profile_root)
```

The adapter profile is operational provenance stored in the outbox and
acknowledgment rows. Rotating it must not mint a second semantic effect.

## Acceptance evidence

The vector suite recomputes two frozen identities, repeats each derivation,
changes every semantic preimage field, and rotates the adapter profile. Each
semantic mutation changes the identity. Adapter-profile rotation preserves it.

## Boundary

I01 does not prove that a production writer inserts the identity atomically,
that a worker preserves it across lease expiry, or that a destination honors
it idempotently. Those obligations belong to I02-I08. M6 remains unmounted and
non-promotable.

