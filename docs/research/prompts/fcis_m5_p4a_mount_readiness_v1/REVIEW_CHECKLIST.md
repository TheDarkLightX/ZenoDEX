# M5-P4A reviewer checklist

This checklist reviews the baseline/readiness checkpoint. It cannot authorize
the P4B switch by itself.

## Automatic no-go

Reject immediately if any item is true:

- `src/core/dex.py` or another mounted authority/deployment path changed;
- fixtures labeled legacy were produced by the exact FCIS evaluator;
- a golden value was refreshed to accommodate a mismatch;
- comparison omits effects, replay, rejection precedence, receipt, or outbox;
- the command inventory is hand-maintained without source exhaustiveness;
- missing Rust/verifier evidence is labeled parity;
- `UNKNOWN`, skip, timeout, xfail, or missing tool can produce `READY`;
- a new generic freeze/copy, mutable inheritance, seal flag, reflection, broad
  authority type, dual admission, or mutable authority builder appears;
- artifact input can widen the expected-difference allowlist;
- the checker ignores undeclared files or duplicate JSON keys;
- tests, coverage floors, packet rules, or final-mount findings were weakened;
- the checkpoint pushes, mounts, deletes legacy code, or begins P4B/P5/M6.

## Contract review

### Inventory

- Mounted commands come from actual dispatch/registry source.
- Exact-only, legacy-only, unsupported, and unknown variants are distinct.
- Adding a source variant kills the coverage test.
- Every mounted command has accepted, boundary, and rejected fixtures.

### Legacy baseline

- The builder calls only the mounted legacy oracle for legacy results.
- Canonical inputs, pre-state, context, versions, and outputs are bound.
- Generation twice is byte-identical.
- Source, generator, artifact, and toolchain hashes verify.
- No `repr`, pickle, object identity, hash-seed, or incidental order leaks into
  bytes.

### Differential oracle

- Both sides bind the same command, pre-state, and context.
- Accept/reject kind, rejection precedence, state, patch, effects, fees, replay,
  receipts, and outbox are compared wherever authority-visible.
- Versioned v5 differences are explicit and fixed by trusted code.
- Divergence reports a stable minimized field path.
- Exact rejection exposes no committable output.

### Mounted graph

- External ingress through publication and delivery is traced.
- All 79 P3 final-mount findings map exactly once.
- Raw mutable, legacy authority, mixed-output, or unknown edges are blockers.
- `LEGACY_DIFFERENTIAL_ONLY` code is unreachable from mounted authority.

### Cross-language matrix

- `PASS_EXACT_BYTES` cites executable exact-byte replay.
- Similar types, source inspection, or compilation do not count as parity.
- Missing promoted Rust/proof/Tau fields force blocked readiness.
- Shadow-only rows cannot authorize value-moving mount.

### Readiness checker

- Honest blocked receipts validate in normal mode.
- `--require-ready` rejects every blocker, unknown, stale hash, or gap.
- Runtime-file hashes prove P4A did not mount anything.
- All 15 required mechanism mutants are killed.
- Extra, stale, `.orig`, `.rej`, and duplicate-key artifacts fail closed.

## Independent attacks

Apply at least these attacks yourself:

1. Remove one mounted command from the inventory.
2. Replace a legacy fixture result with the exact evaluator result.
3. Delete one rejection field from comparison.
4. Change only an effect, nonce/replay, receipt, or outbox field.
5. Reorder two semantically ordered effects/events.
6. Change command, pre-root, or context on one side only.
7. Add a new final-mount violation without a ledger row.
8. Mark a missing Rust row `PASS_EXACT_BYTES` without a replay artifact.
9. Add a duplicate JSON key or unknown status.
10. Change one mounted runtime byte after artifact generation.
11. Add an undeclared file or `.orig` file.
12. Run generation under two fixed hash seeds and compare bytes.

## Required evidence

- exact start/end SHAs and clean isolated worktree;
- exact reviewed P3 ancestor;
- deterministic artifact hashes;
- fixture and command counts by kind;
- exact-vs-legacy result for every fixture;
- all four pre-mount structural profiles;
- exact final-mount count and categories;
- packet checker result;
- focused tests and mutation count;
- Ruff, format, mypy, production-boundary, style, security, and metrics results;
- broad critical gate result, including inherited failures;
- explicit unrun formal/cross-language/datastore lanes.

## Grade

| Category | Weight | Passing evidence |
| --- | ---: | --- |
| Frozen-design fidelity | 20% | no authority switch or forbidden mechanism |
| Inventory and provenance | 15% | exhaustive source-derived command set |
| Legacy golden baseline | 15% | deterministic source-pinned fixtures |
| Differential completeness | 20% | every authority-visible observable compared |
| Mounted graph completeness | 15% | all edges and 79 findings mapped |
| Cross-language honesty | 5% | exact parity or explicit blockers |
| Checker/mutation evidence | 10% | all required mutants killed |

Use `A`, `B`, `C`, or `NO-GO`. Any automatic no-go overrides the numeric
score. `READY` may be accepted only with grade `A` and no open evidence row. A
well-formed `BLOCKED` checkpoint may receive `A` for evidence honesty while
still prohibiting P4B.

## Reviewer output

Create:

```text
docs/research/FCIS_M5_P4A_IMPLEMENTOR_REVIEW_20260726.md
```

Record the exact reviewed SHA, findings, reviewer fixes, attacks, commands,
grade, readiness outcome, blockers, and the next authorized checkpoint. Do not
approve a switch from an honestly blocked receipt.
