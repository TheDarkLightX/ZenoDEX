# I06 plan: lost-ack recovery

Status: implemented and tested against the I04 deterministic destination and
I05 provenance verifier; research-only and unmounted. I07-I08 remain pending.

## Objective

Model the crash window after destination acceptance and before the local
acknowledgment is durable:

```text
same effect ID redelivery
-> destination ALREADY_ACCEPTED
-> same receipt root
-> I05 provenance verification
-> one local durable acknowledgment
```

The immutable reference state retains the destination record while dropping
the local acknowledgment at the simulated crash point. Recovery does not
accept a caller-supplied receipt or effect identity. It redelivers the stored
effect, consumes I04's owned successor-and-receipt accept aggregate, derives
the acknowledgment subject from that receipt, passes the result through I05,
and writes one immutable local journal entry. A later redelivery verifies the
same acknowledgment and leaves its write count at one. An I04 rejection carries
no successor state for recovery to apply accidentally.

Recovery-state construction and revalidation require the live I04 verifier
provenance at point of use. An exact-class copied contract without that
provenance is a typed invalid-state rejection.

## Evidence boundary

I06 covers the named crash window, stable effect identity, destination
duplicate outcome, receipt provenance, typed recovery rejection, attempt
overflow, and one-ack idempotence in a deterministic in-memory model. It does
not prove filesystem or power-loss durability, a real worker, network
delivery, destination adapter refinement, concurrent linearizability,
production datastore behavior, runtime mounting, migration, no-bypass
coverage, accounting, backing, or zUSD safety. M6 remains unmounted and
non-promotable.
