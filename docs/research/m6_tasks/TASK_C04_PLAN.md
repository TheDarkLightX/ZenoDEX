# FCIS M6 Task C04 Plan

TASK_ID: C04
TITLE: Implement exact SRGD-to-AGQE transport

## Scope

Implement the unmounted typed transport relation

```text
sigma_i = -deficit_i
```

for complete `EntitlementStateV1` values. The source must be an exact,
strictly valid SRGD state. The derived target preserves the exact C02 semantic
key and ordered complete entry set while changing only the representation ID
and negating every coordinate. The inverse AGQE-to-SRGD function is included
to make the involution executable.

When a target state is supplied for comparison, C04 checks its exact type,
validity, target representation, key, ordered entry identity, and every
coordinate. Missing and surplus entries reject as one entry-set mismatch.
Changing a nonzero source entry to an all-zero target entry is classified as a
zero-reset rejection.

## Fail-closed boundaries

- Wrong exact source or target types return typed rejection values.
- Invalid state internals are revalidated before transport or comparison.
- Source and target representation IDs are direction-specific.
- Key equality preserves the semantic profile and fixed role order from C02.
- Ordered entry IDs must match exactly; no partial or surplus entry is ignored.
- Every target coordinate must equal the negation of its source coordinate.
- Zero-reset and all other target divergence are distinct typed rejection
  classes.

## Nonclaims

C04 is tested executable research evidence for a typed sign-dual state
transport. It does not prove the complete allocator trace, authenticate a
migration authority, mount a datastore or runtime caller, perform a migration
switch, establish destination behavior, or move value. C05 owns the Lean
trace-conjugacy theorem and C06 owns the broader rotation/reset suite.
