# FCIS M6 Task J09 Plan

TASK_ID: J09
BASE_SHA: 7a921783a8e0b3e706f4dcaa86bd3a9ad0aa6321
SOURCE_HEAD_SHA: fdbbe7813621f0f4ae8c393f83ee2a99072bf8cc
SOURCE_HEAD_TREE: fe7c15b3c5aca5d25e797d958ee2e47f0460dd64

## Objective

Explore the complete bounded migration control relation with all seven phases,
crash PRE/POST observations, retry identity, restart reauthorization, old and
new writer attempts, pending outbox effects, delivery acknowledgments, and
permanent fail-closed mutants.

## Scope

The slice covers:

- exact phase-prefix progression from LEGACY through LEGACY_DISABLED;
- one configured writer and one active writer latch at every phase;
- fresh authorization after commit and after restart;
- complete pending publication rows with sequence, authority, evidence,
  residual, nullifier, state, and effect identity fields;
- atomic publish, PRE discard, POST publish, and restart quiescence;
- same-attempt retry confirmation with bound commit fingerprint;
- complete history, residual, nullifier, outbox, delivery, and acknowledgment
  relationships;
- evidence-version rebind at authority switch with no V1/V2 mixture;
- independent Python exploration, focused/property tests, TLA+ TLC checks,
  public vector, and permanent mutants.

## Acceptance

The bounded campaign must be repeatable, reach all seven phases without an
invariant failure, preserve one writer and complete evidence cardinality, kill
the skipped-phase, dual-writer, missing-residual-transport, and mixed-evidence
mutants, and pass the independent TLA+ model checks.

## Nonclaims

J09 is a bounded research model. It does not authenticate external state,
implement a production datastore transaction, prove filesystem durability,
establish process-level atomicity, prove destination authenticity, show that
all runtime writers consult the model, or authorize migration/value movement.
M6 remains research-only, unmounted, and non-promotable.
