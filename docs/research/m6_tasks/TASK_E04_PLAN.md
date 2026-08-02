# E04 plan: total stored-state classifier

Status: implemented and tested in the isolated E03-dependent research slice.

## Objective

Give every valid retry against one canonical stored-state view exactly one
durable outcome, while carrying transport knowledge separately. The classifier
must be a pure function with typed fail-closed rejection at the verifier-owned
attempt, state, and fresh-reopen subject boundaries.

## Contract

```text
same commit ID + same complete attempt fingerprint -> ALREADY_COMMITTED
same commit ID + different fingerprint            -> DEFINITE_REJECTION
same nullifier under another commit               -> DEFINITE_REJECTION
current root != expected pre-root                 -> STALE_STATE
head/authority/profile mismatch                   -> DEFINITE_REJECTION
all exact head conditions hold                    -> ABSENT_RETRYABLE
```

The request-context sequence and publication-history sequence are distinct
coordinates. E04 requires a verifier-owned `E04SequenceBindingV1` containing
both projections, their domain labels, and a mapping-profile root. The model
does not assert numeric equality between the two coordinates.

Classification also requires `E04ReopenReceiptV1`, bound to the complete
stored-state snapshot, current head, authority context, deployment/verifier
profiles, datastore profile, read version, and freshness epoch. A receipt whose
subject differs from the state is a typed rejection.

The durable outcome enum also retains `NEWLY_COMMITTED` for the E05
linearization result. E04 itself does not claim a commit occurred.

## Implementation procedure completed

1. Reused E01 request identity and E03 verifier-owned commit/effect identity.
2. Added a private-constructor E04 attempt aggregate with a canonical full
   attempt root.
3. Added a private-constructor E04 stored-state aggregate with a complete
   sequence/state-chain check and canonical snapshot root.
4. Added a pure classifier whose precedence matches the taskbook exactly.
5. Added an explicit `CONFIRMED`/`INDETERMINATE` knowledge coordinate.
6. Added a typed sequence binding and fresh-reopen receipt subject.
7. Added source-pinned vector generation, independent replay checks, focused
   tests, and a Lean partition theorem source artifact.

## Required evidence

- all five durable enum values are closed and named;
- exact duplicate, collision, nullifier, stale, authority, and absent cases;
- confirmed and indeterminate observations resolve to the same durable class;
- forged values, mutation, nested-state mutation, receipt mismatch, wrong
  types, bounded-path overflow, and bad enum values fail closed;
- vector regeneration and independent checker pass;
- formal classifier partition source is present.

## Nonclaims

E04 does not implement cryptographic authentication, a production datastore
reader or reopen verifier, a transactional CAS, crash recovery, filesystem
durability, runtime caller mounting, destination delivery, destination
idempotency, migration authority switching, accounting, backing, zUSD safety,
or value movement. The E04 constructor registries and private receipt mint are
research-model provenance guards, not a production authentication mechanism.
The external datastore/freshness verifier is an explicit premise. M6 remains
research-only, unmounted, and non-promotable.
