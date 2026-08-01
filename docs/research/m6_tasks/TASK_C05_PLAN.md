# FCIS M6 Task C05 Plan

TASK_ID: C05
TITLE: Prove Lean trace conjugacy

## Scope

Extend the one-step AGQE/SRGD sign-duality theorem to the complete nested
SLNF word. The formal carrier retains segment boundaries as
`List (List (AuthenticatedOccurrence D))`. A shared signed-state carrier
defines the sign map

```text
phi(c0, c1, c2) = (-c0, -c1, -c2)
```

and the two folds use the existing SRGD deficit and AGQE surplus update
relations. The module proves one-step conjugacy, segment-fold conjugacy,
word-fold conjugacy, validity transport, `phi(phi(state)) = state`, and
preservation of a four-field trace key.

## Formal boundaries

- Each occurrence keeps its authenticated-policy witness and denominator.
- Source and target validity relations preserve every segment and word
  boundary; no nested SLNF word is flattened.
- The theorem uses the existing checked one-step relation
  `bonus_relation_sign_dual` and `update_sign_dual`.
- The proof is compiled into the Lean `Proofs` registry and audited for
  placeholders and theorem axioms.

## Nonclaims

C05 is a machine-checked research theorem over the declared Lean carriers. It
does not establish that the production Python/Rust allocator, runtime parser,
authority context, datastore, or migration switch refines these carriers. The
`TraceKey` is a formal key-preservation carrier, not a production authority
witness. C06 owns broader rotation/reset mutation coverage.
