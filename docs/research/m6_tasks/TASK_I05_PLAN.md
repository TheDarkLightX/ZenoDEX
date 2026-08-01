# I05 plan: provenance-bound acknowledgment

Status: implemented and tested against the I04 deterministic destination
model; research-only and unmounted. I06-I08 remain pending.

## Objective

Verify an acknowledgment only after the destination evidence and the
acknowledgment subject agree on every required provenance field:

```text
effect_id
destination
payload_root
destination_receipt_root
adapter_profile_root
verifier_profile_root
```

The verifier requires the receipt to be present in the exact I04 destination
record set for the effect. It recomputes the canonical destination receipt
root from the verified contract and effect, then recomputes the acknowledgment
subject root from the complete field tuple. A merely well-shaped foreign digest,
an acknowledgment before delivery, a crossed receipt, or a foreign profile
rejects.

## Evidence boundary

I05 covers receipt ancestry, delivery-state membership, adapter/verifier
profile binding, subject-root recomputation, and typed rejection. It does not
prove receipt bytes from a real destination, production verifier identity,
network delivery, lost-ack recovery, concurrent behavior, datastore behavior,
or runtime mounting. M6 remains unmounted and non-promotable.
