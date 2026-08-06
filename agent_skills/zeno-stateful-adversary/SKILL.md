---
name: zeno-stateful-adversary
description: Design state-machine, property, linearizability, and bounded crash tests for ZRM, ZenoDEX settlement, ZenoLedger admission, replay, lifecycle, migration, and exact-once behavior. Use when correctness depends on command sequences, status, concurrency, CAS, retries, lost responses, persistence, restart, or migration.
---

# Zeno Stateful Adversary

## Principle

Define a small independent sequential model and generate histories. Avoid
encoding temporal behavior as a large set of isolated examples.

```text
ModelState + Command
  -> ExpectedResult + NextModelState
  -> execute SUT
  -> compare exact result and observable state
```

The model must not call the production transition to compute expectations.

## Observations

Snapshot applicable balances, ownership, roots, accepted journal/history,
replay and nonce indexes, policy/release identity, context revision, commit
result, effect plan, durable rows, emitted messages, and rejection state.

## Sequential workflow

1. Generate well-typed legal commands with state preconditions.
2. Generate invalid commands as a separate fail-closed class.
3. Compare model and system after every step.
4. Require state equality on rejection unless the contract records a failed
   attempt.
5. Shrink command sequences and payloads.
6. Retain the smallest counterexample with seed and replay command.

Prefer bounded exhaustive enumeration for small command alphabets and depths.
Canonicalize symmetric actors and prune equivalent model states.

## Concurrency workflow

1. Define the sequential specification.
2. Generate histories with invocation and response intervals.
3. Check for a legal sequential order respecting real-time precedence.
4. Explore deterministic scheduler interleavings where possible.
5. Shrink to the smallest non-linearizable history.

Wall-clock stress and sleeps are not the primary oracle.

## Crash workflow

Inject named crashes before and after intent, journal, root, effect, replay,
commit/fsync, response, and migration-switch boundaries. Restart from persisted
state, recover, compare with the legal recovery set, retry, and require the
contracted zero-or-one effect with consistent history and roots.

Useful metamorphic relations include exact-retry idempotence, independent
command commutativity, response-loss equivalence, restart invariance,
batch/sequential equivalence, and reject-is-no-op.

## Required output

- model, command grammar, invariants, and observations;
- bounds, scheduler/concurrency oracle, crash points, and legal recovery states;
- shrinker and deterministic replay artifact;
- executed mutants and explicit nonclaims.
