# FCIS M6 D09 Crossed-Axis and Temporal Mutant Schema V1

TASK_ID: D09

## Purpose

D09 exercises the D08 composition boundary with two independently derived
valid source-bound transitions. It preserves the individual transition
identities, crosses semantic, receipt, bundle, outbox, TCG, DRA, and lineage
axes, and requires the D08 verifier or the D07 stutter verifier to reject each
mutation.

D09 is a mutation-evidence task. It grants no runtime authority and performs
no external I/O.

## Valid transition fixtures

Transition 1 is the frozen D08 exact-input swap fixture. Transition 2 is a
deterministically derived single-event swap with the same state and context
profile and a distinct intent ID and input amount. Both are built through the
D08 fixture builder and independently return a verifier-minted ANF root.

The two roots and base bundle roots are recorded in the D09 vector. The
crossed-axis test does not treat matching shape as matching identity.

## Required crossed-axis mutants

The checker constructs and rejects:

- semantic from transition 1 with the base decision/receipt axis from
  transition 2;
- receipt from transition 1 with the base bundle axis from transition 2;
- bundle from transition 1 with the foreign bundle/outbox axis from transition
  2;
- a TCG certificate from a foreign topology;
- a DRA atom with a foreign authority epoch root;
- an ANF with the semantic root retained and a different lineage root.

The first three mutations are expected to fail at the source/base lineage
coherence boundary. The exact reject stage is part of the frozen vector.

## Required temporal mutants

The D07 stutter verifier receives same-root candidates classified as:

- new_commit;
- migration.

Both are non-stutter operation kinds and must return the closed
forbidden_operation rejection. A visible commit or migration cannot be hidden
inside a quotient stutter.

## Boundary

D09 is tested unmounted evidence over two finite research fixtures. It does not
prove that production callers cannot assemble crossed rows, that a datastore
enforces atomic publication, that TCG topology inventories are complete, that
proof context is cryptographically verified, or that a destination is
idempotent. No migration, authority switch, deployment, or value movement is
mounted.

