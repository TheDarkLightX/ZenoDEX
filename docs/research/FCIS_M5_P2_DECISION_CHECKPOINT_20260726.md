# FCIS M5-P2 Controlled Decision Checkpoint

Date: 2026-07-26

Source checkpoint: `79e3ff11`

Parent checkpoint: `b19bb0e1`

Status: `M5_P2_COMPLETE_UNMOUNTED`

## Scope

This checkpoint adds the controlled decision boundary between exact FCIS step
evaluation and later atomic publication. It does not mount the new path in
`DexState`, construct an atomic commit bundle, or claim a production datastore
transaction.

The authoritative result algebra is exhaustive:

```text
DecisionV1
  = AcceptV1
  | RejectV1
  | CommittedFailureV1
```

The current spot profile has no committed-failure rule, so
`CommittedFailureV1` is deliberately uninhabited. Ordinary rejection contains
one canonical rejection receipt and no successor state, patch, effects, replay
update, outbox plan, or retained private evaluation trace.

## Authority and invariant impact

The public entry point now performs this deterministic sequence:

```text
closed budget admission
-> exact command/context/state admission
-> pure candidate evaluation
-> actual-read containment
-> same-lineage revalidation
-> complete patch/replay/effects derivation
-> resource-budget enforcement
-> canonical receipt binding
-> AcceptV1 | RejectV1
```

`AcceptV1` and `RejectV1` require a module-private construction capability.
The structural checker verifies their only construction sites. An acceptance
binds the evaluator algorithm and version, canonical command root, budget hash,
execution-context hash, expected pre-root, next-state root, support root and
support-set commitment, snapshot commitment, patch root, and commit-plan root.

Patch and replay derivation independently apply each exact patch to the
retained immutable pre-state and require the result to equal the retained
successor. Roots and canonical context bytes are recomputed before acceptance.
Post-evaluation substitution therefore produces a typed no-output rejection.

## Evidence

The following focused gates passed against the checkpoint diff:

```text
Ruff check                                           PASS
Ruff format --check                                  PASS
Python compilation                                   PASS
Focused authority-source mypy                        PASS
P2 semantic and authority tests                      69 passed
Structural checker and mutation tests                221 passed
state-substrate profile                              ok=true
authority-graph profile                              ok=true
exact-replay profile                                 ok=true
exact-consumers profile                              ok=true
normative packet checker                             ok=true
security red-flag scan                               0 findings
```

The checker mutation suite kills omissions of committed state fields, canonical
encoding, root hashing, exhaustive decision variants, rejection minimality,
controlled construction, same-candidate derivation, lineage revalidation,
replay derivation, and evaluator routing.

The standalone checker still has 13 pre-existing strict-mypy AST-narrowing
findings. The two type errors introduced during P2 were removed. Its executable
checker and mutation suite are the checkpoint gate.

## Explicit nonclaims

- The final FCIS authority mount is not complete.
- No `CommitBundleV1` or pure reference commit port is promoted by P2.
- No production datastore linearizability, crash recovery, or outbox delivery
  claim is made.
- No Python/Rust byte-level refinement claim is made.
- Existing exact-replay and exact-consumer compatibility findings are not
  promoted away.
- This checkpoint does not remove the legacy differential oracle.

The `final-mount` profile remains fail-closed with 79 findings. They are the
explicit M5-P4/M6 migration surface, including mounted `Any`, broad legacy
admission, generic deep freeze, mutable inheritance, seal flags, and legacy
support-root consumers.

## Next checkpoint

M5-P3 must add a controlled immutable commit bundle, receipt-derived outbox
identities, and a pure immutable expected-root commit reference. Invalid,
stale, duplicate, and injected-crash paths must expose either the unchanged
store or one complete publication, never a partial state/effect/receipt/replay/
outbox result.
