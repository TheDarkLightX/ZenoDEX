# F07 plan: checkpoint and truncation semantics

Status: implemented and tested in the isolated public research slice.

## Objective

Define a source-bound checkpoint that can replace a complete authoritative
history while retaining every nullifier, authority epoch, and unacknowledged
outbox identity needed by the next reopen.

## Procedure

1. Revalidate the F04 fixed-point source and its canonical layout bytes.
2. Revalidate the F05 genesis acceptance and bind the history's initial state,
   configuration, and first authority root to it.
3. Derive complete prior-history, nullifier, authority, and outbox roots.
4. Extract every unacknowledged outbox row into a complete pending identity.
5. Derive the deterministic replay-proof root and checkpoint genesis root.
6. Expose a compacted snapshot rooted in the checkpoint value.
7. Recompute the expected checkpoint at use and reject every crossed value.
8. Reject partial-prefix truncation and approved-snapshot proof mode until their
   successor schemas and verifier premises exist.

## Required evidence

- typed checkpoint, pending-outbox, compacted-snapshot, acceptance, and reject
  values;
- independent deterministic checker and vector;
- focused and property tests;
- pending-delivery retention witness;
- root-substitution, proof-mode, partial-sequence, and wrong-type mutants;
- Ruff, strict mypy, Python compilation, JSON, adjacent regression, and packet
  manifest validation.

## Nonclaims

F07 is an unmounted value-level relation. It does not perform a datastore
compaction, certify an external snapshot signer, or authorize value movement.
