---
name: zeno-suite-distiller
description: Reduce Zeno test and harness bloat using mutant kill vectors, oracle roles, and obligation traceability. Use when test SLOC or runtime grows rapidly, wrappers repeat build logic, examples duplicate a closed vocabulary, a mutation campaign completes, or evidence files repeat inventories.
---

# Zeno Suite Distiller

## Principle

Coverage equivalence is not evidence equivalence. Distill with fault
discrimination, observables, and oracle roles.

Protect independent models and atlases, theorem/solver bridges, public vectors,
smallest counterexamples, end-to-end authority tests, crash/concurrency
reproducers, catastrophic mutant controls, and externally required tests.

## Workflow

1. Inventory obligation IDs, oracle grade, observables, mutants killed, runtime,
   flake history, harness dependencies, protected roles, and retained witnesses.
2. Compute each test's non-equivalent mutant kill signature.
3. Group identical and subsumed signatures.
4. Keep tests separate when they check distinct error precedence, no-effect
   state, public bytes, implementation/language, or authority boundary.
5. Prefer:
   - repeated examples to a parameterized table;
   - small finite cases to exhaustive enumeration;
   - copied formal/subprocess wrappers to one manifest-driven harness;
   - repeated setup to a fixture or builder;
   - gate arrays to one authority manifest;
   - evidence counts and paths to generated reports;
   - copied field failures to a generated mutation table.
6. Delete ritual AAA comments, literal test-count assertions, passthrough
   runners, duplicate happy paths, impossible-state tests, and stale generated
   prose.
7. Rerun baseline, mutation, properties, seeds, and release gates after every
   consolidation.

Use constrained set-cover as a suggestion:

```text
maximize critical mutants, obligations, and protected roles retained
minimize runtime, test SLOC, and duplicate harness SLOC
```

Require a human-readable rationale. Never delete based on line coverage alone
or generate golden vectors from the implementation under test.

## Report

Record before/after test and support SLOC, runtime, critical mutants killed,
removed and merged tests, protected evidence, the new manifest or harness,
evidence equivalence, and nonclaims.
