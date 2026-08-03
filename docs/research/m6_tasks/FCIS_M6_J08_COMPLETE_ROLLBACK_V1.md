# FCIS M6 J08 complete rollback

J08 is an isolated research relation for a compensating rollback after the
J07 authority switch. It consumes a verifier-owned J07 switch atom, a
complete post-switch state witness, and a complete pre-switch anchor.

The complete state aggregate binds:

```text
current state
deployment configuration
authority and epoch
history
residual state
nullifier accumulator
outbox identity
effect identity
context snapshot
canonical complete snapshot
```

The source and anchor must agree on the non-authority roots across the
authority-only J07 switch. The rollback target restores every one of those
roots from the anchor, appends a rollback commitment to history, derives a new
authority and snapshot lineage, advances the authority epoch exactly once,
and enters POST_SWITCH_VALIDATION with no active writer. The result requires
fresh authorization and exposes no value-moving capability.

## Evidence

- independent checker: `J08_ROLLBACK_MATCH`
- public vector builder: `J08_ROLLBACK_VECTOR_MATCH`
- focused and property tests: 11 passed;
- adjacent J01-J07, F05, and F06 regression: 55 passed;
- exact implementation commit:
  `d92c98fd9911741c2be6a3a1af9d7d1ff1bccbb3`;
- exact implementation tree:
  `f409c5381210827160a016f9eec78755b3f4690c`;
- pinned rollback root:
  `f7f6f445cc6958380925d5f7fb4c6cc1e7033a6ddfcd88214ec92c1462ddc6a1`.

The negative evidence covers balance-only and partial auxiliary rollback,
history erasure, forged source/anchor complete-state disagreement, stale or
wrong rollback sequence, wrong reason, wrong switch type, and bounded typed
rejection paths.

## Boundary

J08 uses verifier-owned construction and identity registries as bounded
research provenance mechanisms. The complete-state verifier is an external
premise. No production datastore, transaction, crash worker, runtime writer,
destination, migration deployment, or value-moving caller consumes this
relation. M6 remains unmounted and non-promotable.
