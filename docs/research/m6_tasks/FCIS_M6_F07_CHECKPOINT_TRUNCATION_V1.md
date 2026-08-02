# FCIS M6 F07 checkpoint and truncation semantics

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

F07 defines a value-level compaction certificate over an F04 whole-layout fixed
point and an accepted F05 genesis relation. The certificate is a new
authenticated-genesis-like value for the compacted state. It binds:

```text
complete prior layout root
complete prior history root
checkpoint sequence and state root
deployment and verifier roots
F05 genesis admission root
complete nullifier accumulator root
complete authority epoch summary root
complete outbox accumulator root
all unacknowledged outbox identities
deterministic replay-proof root
checkpoint genesis root
```

## Full-tip policy

F07-v1 admits only a checkpoint at the complete current history tip. This
removes ambiguity around a retained suffix: the replacement snapshot starts at
the checkpoint state root, and no old history atom remains authoritative.
Partial-prefix truncation is a typed rejection until a later schema carries the
retained suffix's sequence, pre-state, authority, nullifier, and outbox
ancestry explicitly.

The checkpoint includes the full outbox accumulator and a complete
`F07PendingOutboxV1` value for each committed effect without a durable
acknowledgment. A pending effect therefore retains its commit, sequence,
writer, destination, payload, adapter, effect, and idempotency identity after
the old history is compacted.

Only deterministic replay proof is admitted. The approved-snapshot enum is
reserved and rejects without an external certificate verifier.

## Authority boundary

`F07CheckpointV1` and the compacted snapshot are ordinary immutable data. Their
constructors do not authorize row deletion or value movement. The
`validate_f07_checkpoint_v1` relation rederives the certificate from the exact
F04 fixed point and F05 acceptance value at use. No datastore adapter,
signature verifier, crash protocol, or mounted compaction caller is included.

## Adversarial coverage

The checker and tests reject:

```text
each checkpoint root substituted and recomputed
omitted pending outbox identity
unverified approved-snapshot proof mode
zero/partial checkpoint sequence
untyped source and genesis inputs
```

The independent vector records one canonical pending effect in its pending
source fixture, so the retention obligation is exercised even though the
canonical acknowledged fixture has no pending rows.

## Nonclaims

F07 does not delete physical history, prove datastore crash recovery, prove
atomic publication, authenticate an external approved-snapshot certificate,
implement concurrent compaction, mount runtime authorization, or establish
M6/R13 production closure.
