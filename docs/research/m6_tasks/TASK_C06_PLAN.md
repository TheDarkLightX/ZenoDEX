# FCIS M6 Task C06 Plan

TASK_ID: C06
TITLE: Add rotation and reset mutation suite

## Scope

Add a typed, unmounted rotation snapshot and a deployment-bound migration
comparison around the C02 key, C03 complete state, and C04 sign-dual
transport.

Ordinary policy, destination, and custody configuration values are represented
outside the four-field entitlement key. Their rotation is accepted only when
the exact state key, representation, and complete ordered entry history remain
unchanged. Representation migration is checked through the C04 transport and
is allowed to change representation while preserving the complete mapped
history.

The migration comparison binds the source context to the current deployment,
authority epoch, and current state before checking the target. It rejects
cross-deployment substitution, zero-reset targets, partial entry sets, and
other C04 transport divergence with typed results.

## Permanent tests

- policy rotation preserves key and residual entries;
- destination rotation preserves key and residual entries;
- custody rotation preserves key and residual entries;
- representation migration preserves exact mapped history;
- zero-reset migration rejects;
- partial-entry migration rejects;
- cross-deployment state substitution rejects before transport.

## Nonclaims

C06 is tested executable research evidence for the declared typed snapshots
and comparisons. It does not authenticate external roots, create an opaque
production authority witness, mount a runtime caller or datastore, implement a
real migration switch, establish destination idempotency, or move value.
