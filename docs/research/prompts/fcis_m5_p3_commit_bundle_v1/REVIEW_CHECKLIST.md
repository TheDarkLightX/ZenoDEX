# M5-P3 reviewer checklist

This checklist is for the primary reviewer after the implementation agent
returns a local commit. It is not evidence by itself.

## Automatic no-go review

Reject the implementation immediately if any item is true:

- a generic freeze/copy mechanism or mutable-class wrapper appears;
- a second hand-written admission/encoding system appears;
- decoded claim data reaches the commit port as authority;
- bundle/outbox roots or identities are caller supplied;
- `CommitBundleV1` duplicates state, plan, effects, replay, or receipt;
- ordinary rejection can create a bundle;
- current-profile code constructs `CommittedFailureV1`;
- reference store or publication is mutable;
- commit logic publishes state, effects, receipt, replay, or outbox separately;
- stale, invalid, or crash-before paths change the store;
- crash-after can expose a partial shape;
- a broad exception catch erases stable failure classification;
- mounted `dex.py` or a production adapter changed;
- a test, checker, or final-mount profile was weakened.

## Contract-by-contract inspection

### P2 correction

- `max_outbox_records` is enforced from retained settlement events.
- Boundary and one-over evidence exists.
- `CommittedFailureV1.receipt` is exact and privately constructible.
- Current profile still has zero constructor call sites.

### Controlled bundle

- One private capability controls the authority wrapper.
- Existing P0 claim/outbox schemas are reused unchanged unless a demonstrated
  schema defect required a separately reviewed correction.
- The builder accepts one decision and no replacement component arguments.
- Reject returns unchanged.
- Receipt/outbox/bundle bytes and roots are derived internally.
- Canonical claim round-trip is rechecked before authority escapes.

### Outbox

- Only exact retained settlement events produce records.
- Event tuple order is preserved.
- No proof/index effects are invented.
- Identity preimages exactly match the prompt and golden vectors.
- Payload canonicalization uses the repository codec.
- The closed grammar constructs the final outbox plan.

### Reference port

- Store, publication, result, status, and crash point are exact immutable
  values.
- Input store is never mutated.
- Nested bundle, receipt, plan, replay, outbox, bytes, and roots are
  revalidated.
- Applying patch and replay exactly reproduces the successor.
- Duplicate check occurs only after bundle revalidation.
- Root mismatch returns unchanged stale result.
- One returned new store is the linearization point.
- Post-linearization crash retains the complete new store.

### Structural checker

- Both new modules are explicitly covered.
- Constructor call sites are exact allowlists.
- Authority versus claim types are distinguished.
- Mechanism mutants cover every item in P3-D07.
- Checker tests fail when each mutant is applied, then pass on source.

## Independent reviewer attacks

Manually attempt at least these substitutions:

1. Bundle decision A with outbox B.
2. Decision state A with commit plan B.
3. Receipt A with state/plan B.
4. Valid bundle with one nested object mutated via `object.__setattr__`.
5. Valid bundle on a state with the same shape but different pre-root.
6. Retry a corrupted bundle whose cached root matches a prior publication.
7. Event reorder, deletion, duplication, and payload mutation.
8. Crash before and after the modeled linearization point.
9. Decoded `CommitBundleClaimV1` passed where authority is expected.
10. Direct constructor calls from an unauthorized module.

## Grading

| Category | Weight | Passing evidence |
| --- | ---: | --- |
| Frozen-design fidelity | 25% | no automatic no-go; exact module roles |
| Same-decision bundle derivation | 20% | substitution attacks and roots fail closed |
| Atomic reference semantics | 20% | stale/crash/retry laws over immutable store |
| Closed outbox derivation | 15% | golden identities and grammar-only construction |
| Structural and mutation evidence | 15% | every required mutant killed |
| Evidence discipline | 5% | exact SHA/results/nonclaims |

Use grades `A`, `B`, `C`, or `NO-GO`. Any automatic no-go produces `NO-GO`
regardless of test count. Only `A` or a corrected `B` should be considered for
push to the shared M5 branch.

## Reviewer output file

Create:

```text
docs/research/FCIS_M5_P3_IMPLEMENTOR_REVIEW_20260726.md
```

Record exact reviewed SHA, findings by severity, fixes made by the reviewer,
commands and results, grade, nonclaims, and the next permitted checkpoint. Do
not approve a mount from P3.
