# FCIS M5-P3 implementor review

Date: 2026-07-26

Contract: `zenodex/fcis-m5-p3-commit-bundle/v1`

Implementation branch: `agent/fcis-m5-p3-commit-bundle-20260726`

Exact implementation head reviewed: `c98b8e91dcdcbeea5d548a15060777d81289b543`

Exact packet start head: `28f755cb`

## Verdict

The implementor checkpoint was an automatic `NO-GO`. The reviewer-corrected
P3 checkpoint is graded `A` for the frozen, unmounted P3 scope. This grade does
not approve a runtime mount, production datastore adapter, external delivery
worker, or release claim.

The original result had useful substrate and was worth repairing. Its main
failure was evidence that established outcomes without enforcing every required
construction mechanism.

## Original findings

### Critical

1. A test imported the private decision-construction capability and used it to
   construct `CommittedFailureV1` successfully. P3-D02 requires zero production
   construction sites and forbids adding a reserved construction path merely to
   exercise the variant. The corrected test admits the exact receipt claim and
   proves that an external capability cannot construct the authority wrapper.
2. Nonempty outbox derivation supplied the string value
   `canonical_event` where the closed grammar requires the exact
   `OutboxEffectKindV1` enum member. The original tests used empty plans or
   independently recomputed formulas and missed that every real event plan
   rejected. The corrected test exercises a nonempty closed-admitted plan and
   binds a literal golden vector.
3. Bundle derivation inconsistencies could escape instead of producing one
   stable ordinary rejection with no bundle. The corrected public builder
   converts only `OverflowError`, `TypeError`, and `ValueError` from the
   controlled derivation into the registered
   `canonical_binding_rejected` receipt at path `commit_bundle`.

### High

1. The reference commit port did not recursively revalidate the exact store,
   decision state, plan, receipt, outbox plan, cached bytes, or cached root.
   Post-construction corruption could therefore reach later logic or duplicate
   detection. The corrected port revalidates the whole bundle and every stored
   publication before computing a result.
2. The structural checker mostly proved that calls were present. A mutant could
   call `_revalidate_bundle_v1` or `_revalidate_store_v1`, ignore the Boolean
   result, and continue to publication. The corrected checker binds required
   negative guards, return values, and linearization ordering.
3. P3-D07 was not fully represented by mutation tests. The corrected suite
   kills 27 focused mutants spanning every listed P3-D07 category.

### Medium

1. The checkpoint lacked literal golden digests. It now binds receipt root,
   event payload bytes, effect identity, idempotency key, bundle root, and the
   canonical bundle-byte digest.
2. The property evidence was mostly single examples. Bounded exhaustive cases
   now cover event payload sensitivity, deterministic derivation, deterministic
   commit replay, and idempotent retry.
3. Independent substitution attacks did not separately swap state, plan,
   replay, or event sequence variants. The corrected suite covers state, plan,
   replay, receipt, decision, outbox, event reorder, deletion, duplication,
   payload mutation, nested corruption, and a corrupted retry retaining a
   previously published cached root.

## Corrected authority design

```text
controlled DecisionV1
  -> controlled CommitBundleV1 | unchanged RejectV1
  -> exact recursive revalidation
  -> compare-and-replace patch and replay
  -> expected-root decision
  -> one immutable ReferenceCommitStoreV1 result
```

- `CommitBundleV1` retains one committable decision and one internally derived
  outbox plan. State, plan, replay, effects, and receipt remain reachable only
  through the decision lineage.
- Outbox records preserve retained settlement-event tuple order and are admitted
  through the existing closed authority grammar.
- Effect identity and idempotency preimages bind every frozen field with explicit
  domain separation and fixed-width length framing.
- Ordinary rejection has no successor, plan, bundle, or outbox authority.
- The reference store, publication, and result are final frozen slotted values.
  The input store is never mutated.
- Stale, invalid, and crash-before outcomes return the identical input store.
  Crash-after and published outcomes expose the one complete new store.

## Independent attacks

All ten reviewer attacks from `REVIEW_CHECKLIST.md` are executable:

1. decision A with outbox B;
2. state A with plan B, including an independent replay swap;
3. receipt A with state and plan B;
4. nested `object.__setattr__` corruption;
5. a same-type different-root pre-state;
6. a corrupted retry whose cached root equals a prior publication root;
7. event reorder, deletion, duplication, and payload mutation;
8. crashes before and after the modeled linearization point;
9. decoded `CommitBundleClaimV1` supplied to the commit edge;
10. constructor calls outside the exact allowlist.

All fail closed or return the exact expected immutable result.

## Evidence

### Frozen P3 gates

- `python3 -m py_compile ...`: passed for the three P3 core modules and checker.
- `python3 -m ruff check ...`: passed for all eight changed source/test paths.
- `python3 -m ruff format --check ...`: eight files already formatted.
- `python3 -m mypy ...`: success, no issues in three source files.
- focused core and authority-admission suite: `81 passed`.
- full checker suite: `252 passed`.
- combined P3 semantic and checker suite: `333 passed`.
- P3-D07 focused mutation selection: `27 passed`.
- `state-substrate`: `ok=true`, zero violations.
- `authority-graph`: `ok=true`, zero violations.
- `exact-replay`: `ok=true`, zero violations; inherited compatibility findings
  remain informational.
- `exact-consumers`: `ok=true`, zero violations; inherited compatibility
  findings remain informational.
- packet checker: `ok=true`, 39 requirements and 103/103 declared tests bound.
- production-boundary audit: `ok=true`.
- `git diff --check`: passed.
- `src/core/dex.py`: byte-for-byte unchanged from the packet start head.
- required ancestry checks for `79e3ff11` and `28f755cb`: passed.

### Deliberately blocked gate

`final-mount` remains `ok=false` with exactly 79 violations:

| Code | Count |
| --- | ---: |
| `BROAD_ADMISSION` | 50 |
| `SNAPSHOT_SEAL_FLAG` | 12 |
| `OPEN_AUTHORITY_TYPE` | 5 |
| `FORBIDDEN_RECONSTRUCTION` | 4 |
| `MUTABLE_BASE` | 4 |
| `GENERIC_DEEP_FREEZE` | 3 |
| `COERCIVE_CONTAINER_COPY` | 1 |

This is the required fail-closed pre-mount posture. No finding was suppressed.

### Repository policy tools

- style classifier: all three P3 core files classified as deterministic
  functional core; the checker classified as evidence-first release tooling.
- security red flags: zero findings across the four changed authority/tool
  modules.
- trust-surface inventory: completed against the isolated worktree.
- design metrics: flagged the existing checker file as a hotspot and flagged
  the new P3 checker/reference functions for length. The straight-line reference
  function is retained because its ordered guards and single publication point
  are directly audited by the mutation suite. Checker decomposition remains a
  maintainability follow-up and is not required to change P3 semantics.

### Broad gate

`bash tools/run_critical_quality_gate.sh` was run using the repository's locked
development virtual environment. Ruff, shell syntax, mypy, all four pre-mount
FCIS profiles, the packet checker, 252 checker tests, and 555 acceptance-TCB
tests passed. The gate then failed one inherited branch-coverage floor:

```text
src/core/settlement_strong_validator.py: 77.1% < 78.0%
```

P3 does not change that module or its production callers. The floor and tests
were not weakened. Therefore the repository-wide critical gate remains
non-green even though the frozen P3 checkpoint gates pass.

## Grade

### Original implementor head

`NO-GO` because an automatic-no-go private capability path existed and a real
nonempty outbox plan could not pass the closed grammar.

### Reviewer-corrected P3 checkpoint

| Category | Score |
| --- | ---: |
| Frozen-design fidelity | 25 / 25 |
| Same-decision bundle derivation | 20 / 20 |
| Atomic reference semantics | 20 / 20 |
| Closed outbox derivation | 15 / 15 |
| Structural and mutation evidence | 15 / 15 |
| Evidence discipline | 5 / 5 |
| **Total** | **100 / 100, A** |

The grade is scoped to P3 and remains compatible with a blocked overall FCIS
release profile.

## Nonclaims and residual risk

- The reference port does not prove datastore linearizability, crash recovery,
  transaction durability, or external destination idempotency.
- P3 is unmounted. No runtime authority path changed.
- Rust, Tau, ESSO, Lean, RISC0, proof-guest, and cross-language byte parity were
  not promoted by this checkpoint.
- `final-mount` remains blocked on 79 findings.
- The repository-wide critical gate retains the unrelated branch-coverage
  failure recorded above.
- Python frozen values remain bypassable by hostile in-process
  `object.__setattr__`; recursive commit-time revalidation is the P3 defense.

## Next permitted checkpoint

Prepare a separate, exact-head reviewed M5-P4 packet. P4 may mount the controlled
decision and bundle only after it defines the runtime authority switch,
compatibility oracle, rollback boundary, and mount-specific fail-closed tests.
P3 itself does not authorize that switch.
