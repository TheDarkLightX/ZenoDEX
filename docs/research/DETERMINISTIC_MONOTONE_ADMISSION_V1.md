# Deterministic Monotone Admission V1

## Status

This document specifies the narrow authority of
`src/core/deterministic_parallel_admission.py`.

It is a functional-core primitive for parallel **admission fact construction**.
It does not execute value-moving transitions, mutate committed state, deliver
external effects, or authorize a production parallel-execution claim.

## Denotation

Given one immutable execution context `X`, one ordered logical partition profile
`P`, and exactly one worker bundle for every partition, the join denotes either:

```text
Reject(canonical failure)
```

or:

```text
FrozenFacts(canonical pointwise join)
```

Physical worker count, thread/process layout, work stealing, completion order,
and bundle arrival order do not appear in the input language.

## FCIS boundary

The functional core receives values only:

```text
ParallelExecutionContext
+ expected logical partition identifiers
+ immutable WorkerBundle values
    -> ParallelAdmissionJoinResult
```

Workers return facts and typed rejection data. They cannot mutate a shared
`DexState` and cannot execute an effect. The imperative shell may schedule
workers, retry operational failures, and collect bundles. It may pass an accepted
`FrozenFactSet` to the normative sequential transition. Only the sequential
transition may construct next-state and exact effect-plan values, and only the
shell may atomically commit those values against the expected pre-state root.

This follows the repository FCIS rule:

```text
untrusted bytes
-> bounded canonical authenticated values
-> pure transition
-> next state + exact effect plan + receipt draft
-> atomic commit + idempotent delivery
```

## LVar-derived restrictions

The design takes one useful result from *Freeze After Writing: Quasi-
Deterministic Parallel Programming with LVars*: shared facts can be safely built
through a monotone join when writes commute, and an exact result can be exposed
after quiescence/freeze.

ZenoDEX adopts a stricter consensus subset:

1. Fact state grows only by pointwise set/map union.
2. Identical writes to one key are idempotent.
3. Different values for one key become a deterministic conflict.
4. Every logical partition must produce exactly one bundle.
5. Every bundle binds the same state, command, execution-context, policy,
   module, algorithm, and partition-profile identities.
6. Semantic rejection precedence is determined by logical partition ID and local
   command index, never completion time.
7. Freezing happens only after all expected logical partitions are present.
8. Missing, duplicate, failed, mismatched, or conflicting bundles return no
   frozen candidate.

The general LVar theorem allows “same answer or an error.” Consensus cannot use
a schedule-dependent value-versus-error result, so this module does not permit a
write to race a freeze. There is no public open/frozen mutable cell. The join
receives the complete immutable bundle collection and constructs one frozen
value.

## Authority bindings

Every worker bundle binds `context_hash`, which commits to:

- pre-state root;
- command-set root;
- execution-context hash;
- policy hash;
- module-version digest;
- algorithm-version digest;
- logical-partition profile version.

A bundle with a different binding is an exact no-candidate rejection.

## Monotone fact relation

For a key `k` and payload values `a` and `b`:

```text
Absent(k) join a = a

a join a = a

a join b = Conflict(k, a, b), when a != b

Conflict join anything = Conflict
```

At runtime the implementation groups immutable byte payloads by canonical fact
key. A key with one distinct payload freezes to that payload. A key with more
than one distinct payload rejects the whole join. No last-writer-wins or
completion-order rule exists.

## Canonical rejection order

Join-shape and authority failures are evaluated in ordered logical partition
space. Semantic rejections are selected by:

```text
(logical_partition_id, local_command_index, code, evidence_hash)
```

Fact conflicts are selected by canonical fact key. This makes the externally
visible rejection invariant under bundle arrival order.

## Intended first use

The first safe mounting target is read-only admission work:

- signature verification results;
- proof-verification results;
- canonical decoding and bounds-check results;
- authenticated evidence digests;
- read/write footprint discovery;
- candidate or typed rejection facts.

After the facts freeze, the sequential functional core remains the executable
reference and constructs the economic result.

## Explicit nonclaims

This module does not establish:

- that the current touched-cell extractor is complete;
- that two value-moving transactions commute;
- sequential/parallel equivalence for spot, perps, zUSD, vault, or FIRE;
- a correct fixed reduction tree for non-associative integer arithmetic;
- atomic state/effect/receipt/outbox commit;
- exactly-once external effect delivery;
- cross-language or cross-platform encoding parity;
- recursive-proof binding to the live transition;
- production throughput, safety, or release authority.

## Promotion gate

Any later value-moving parallel profile `p` must remain blocked until differential
replay establishes:

```text
Encode(ParallelStepV1_p(S, C, X))
=
Encode(SequentialStepV1(S, C, X))
```

for acceptance, rejection precedence, post-state, state root, effect-plan bytes,
nonces, replay identities, receipts, events, outbox entries, overflow, division,
rounding, dust, fee allocation, limits, tie-breaking, and claimant semantics.

Operational worker failure must produce no candidate state and no effects. A
stale compare-and-swap must discard the candidate and either return the governed
stale-root rejection or recompute from the newly authorized snapshot.
