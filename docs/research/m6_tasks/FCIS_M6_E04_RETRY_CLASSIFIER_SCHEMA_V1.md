# FCIS M6 E04 total stored-state classifier

Status: implemented and tested as an isolated research model. The slice is
unmounted and non-promotable.

## Boundary

E04 consumes four verifier-owned model-port values:

```text
E01 request identity
E03 complete commit/effect identity
E04 structurally validated stored-state view
E04 reopen receipt naming the fresh read subject
```

The pure function performs no I/O and no mutation:

```text
(attempt, stored_state, client_knowledge, reopen_receipt)
  -> E04RetryResolution | E04Reject
```

The attempt root includes the request identity, complete E03 commit, expected
pre-state root, writer profile, authority root, verifier profile, and a typed
sequence binding. The request-context sequence and publication-history
sequence are separate coordinates. The binding names both domains and a
verifier-owned mapping profile, so co-hashing them does not imply numeric
equality. E03's fixture intentionally uses that distinction: request sequence
42 maps to publication position 1 under the declared model profile.

The stored-state view carries the complete committed attempt chain, current
state root, current authority epoch/root, allowed writers, deployment profile,
verifier profile, and a canonical snapshot root. Its private construction
boundary and registry detect direct construction, forged instances, and
post-construction mutation in this model.

The reopen receipt binds the state snapshot root, current state root, authority
epoch/root, deployment and verifier profiles, datastore profile, read version,
and freshness epoch. Classification requires a verified receipt whose subject
matches the supplied state. The receipt is the model port for a successful
canonical reopen and fresh-read verifier. The external datastore adapter and
its authenticity/freshness proof remain unimplemented research premises.

## Precedence

The classifier applies this order:

```text
same commit ID and same complete attempt fingerprint -> ALREADY_COMMITTED
same commit ID and different fingerprint            -> DEFINITE_REJECTION
nullifier consumed by another commit                -> DEFINITE_REJECTION
expected pre-root differs from current root         -> STALE_STATE
sequence, epoch, authority, writer, or profile differs -> DEFINITE_REJECTION
otherwise                                            -> ABSENT_RETRYABLE
```

`NEWLY_COMMITTED` is part of the complete durable outcome enum. E04 does not
emit it because E04 classifies a retry against stored state. The linearizing
publication operation is owned by E05.

Client knowledge is an independent enum:

```text
CONFIRMED
INDETERMINATE
```

A fresh canonical state read can resolve an indeterminate observation to the
same durable class as a confirmed observation.

## Closed-domain rules

- exact enum values are required; booleans do not substitute for knowledge;
- roots are lowercase 64-character SHA-256 digests;
- sequences, epochs, collections, and writer sets have explicit bounds;
- rejection paths have a closed maximum length;
- all committed sequences are contiguous and state-linked;
- commit IDs and nullifiers are unique in the state view;
- a state snapshot root must equal the canonical root of its complete content;
- invalid or unverified attempt, state, reopen-receipt, and knowledge inputs
  return typed rejection;
- a receipt bound to a different state is rejected before classification.

## Evidence boundary

The focused suite covers the five durable enum values, all four retry classes,
both client-knowledge values, exact duplicate replay, changed-fingerprint
collision, cross-commit nullifier collision, stale head, authority/sequence
failure, constructor forgery, mutation, nested-state invalidation, wrong
types, reopen receipt forgery and subject mismatch, rejection-path capacity,
and result lineage.

The independent checker regenerates the vector and repeats the class partition
and provenance checks.
