# FCIS M6 I08 Honest Delivery Contract

Status: `RESEARCH_ONLY_UNMOUNTED`.

The outbox contract uses these four claim terms:

- Claim: atomic enqueue
- Claim: at-least-once attempts
- Claim: stable idempotent semantic identity
- Claim: provenance-bound acknowledgment

Interpretation:

- Atomic enqueue means a committed publication atom contains the outbox row,
  or the transaction exposes no durable enqueue.
- At-least-once attempts means a committed pending effect may be attempted
  again after lease expiry, crash, timeout, or response loss.
- Stable idempotent semantic identity means retries reuse the committed effect
  identity and payload binding, while destination deduplication controls
  duplicate semantic application.
- Provenance-bound acknowledgment means a local acknowledgment requires exact
  delivery membership, receipt provenance, adapter identity, verifier
  identity, and subject binding.

The contract deliberately does not claim:

- network-level exactly-once delivery
- production destination semantics without a verified dedup contract
- runtime mounting or value movement
- filesystem or power-loss durability
- whole-system accounting, backing, or zUSD safety

API vocabulary is correspondingly explicit:

```text
atomic_enqueue
at_least_once_attempt
stable_effect_identity
provenance_bound_ack
```

The I04-I07 models are deterministic research evidence. A production adapter
must refine their contracts and pass the corresponding authority, datastore,
destination, and recovery gates before any operational claim is promoted.
