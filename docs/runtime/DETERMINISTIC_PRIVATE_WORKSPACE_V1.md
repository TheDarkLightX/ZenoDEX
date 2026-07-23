# Deterministic Private Workspace V1

## Decision

ZenoDEX should adopt the **private-workspace and explicit-input principles** of
system-enforced deterministic parallelism, but it should not depend on the
Determinator research operating system or make worker execution authoritative.

The ZenoDEX adaptation is:

```text
canonical immutable assignment
→ separately enforced private worker workspace
→ canonical data-only response
→ complete fixed-order join
→ normative sequential replay
→ one expected-root atomic candidate commit
```

Parallel workers are untrusted accelerators. They cannot mutate committed state,
execute external effects, choose protocol-visible ordering, or authorize value
movement.

## Research mapping

The Determinator work isolates concurrent activities between synchronization
points, uses local application-chosen names, requires explicit synchronization
participants, treats time as controlled I/O, and separates scheduling from
application logic. Its private workspaces reconcile child changes at explicit
parent/child synchronization and report conflicting writes rather than allowing
races to select a result.

ZenoDEX maps those principles as follows:

| Determinator principle | ZenoDEX protocol rule |
|---|---|
| Private spaces | One immutable assignment per logical partition; no shared mutable state |
| Local names | Canonical logical partition IDs chosen by the protocol |
| Explicit participants | Parent-to-specific-partition request/response only |
| Time as I/O | Oracle, epoch, time and policy facts are committed in `execution_context_hash` |
| Scheduling separated from logic | Physical worker count, placement and completion order are absent from protocol bytes |
| Snapshot/merge conflicts | Canonical read/write footprints; write/write and either-direction read/write conflicts fail closed |
| Instruction quotas | Deterministic fuel, memory and output budgets; wall-clock timeout is operational failure only |

## Rust protocol

`zenodex_runtime_core::deterministic_worker` defines:

- `WorkerContext`: exact pre-state, command-set, execution-context, policy,
  module, algorithm and partition-profile identities;
- `WorkerAssignment`: a protocol-chosen logical partition and its exact input
  root;
- `DeterministicBudget`: fuel, memory and output limits, with no wall-clock
  field;
- `AccessFootprint`: strictly sorted, duplicate-free read, write and context
  cells;
- `WorkerResponse`: a context-bound data-only result;
- `join_worker_responses`: complete partition validation, canonical semantic
  rejection precedence, operational-failure no-candidate behavior and
  read/write conflict detection.

Every plan, response and successful join has an explicit domain-separated hash.
The strict sandbox profile is itself hashed and bound into both plan and
response values.

## Required shell enforcement

The Rust protocol records the sandbox profile but does not by itself prove that
the host enforced it. A production worker runner must deny:

```text
shared writable memory
wall-clock and process CPU clocks
randomness and getrandom-style APIs
network access
filesystem access
ambient environment variables
child-process creation
thread creation inside one logical worker
wait-any or first-completed synchronization
```

The preferred implementation order is:

1. read-only proof, validation and indexing workers;
2. a no-import WebAssembly worker or equivalently narrow Linux sandbox with
   deterministic fuel metering;
3. signed or locally verified sandbox-attestation records bound to the worker
   response;
4. dynamic trace containment proving:

   ```text
   actual reads    ⊆ declared reads
   actual writes   ⊆ declared writes
   actual contexts ⊆ declared contexts
   ```

5. exact differential replay proving:

   ```text
   Encode(parallel candidate)
   =
   Encode(normative sequential result)
   ```

No value-moving profile may be promoted before steps 4 and 5 close.

## Failure semantics

- A missing, duplicate, extra or misbound logical response yields no candidate.
- A worker crash, fuel exhaustion, memory exhaustion, timeout or sandbox
  violation is an operational failure and yields no candidate.
- Multiple semantic rejections are selected by logical partition and local
  command order, never by completion time.
- A write/write or read/write conflict yields no candidate.
- A successful worker join is still only evidence for sequential replay.
- A stale expected-root compare-and-swap discards the complete candidate.

## Nonclaims

This profile does not:

- prove that the current conflict-graph extractor has complete read/write sets;
- implement the production sandbox runner;
- prove the host kernel, hypervisor or WebAssembly runtime deterministic;
- authorize parallel value-moving transitions;
- replace Rust/Python/formal differential refinement;
- implement atomic state/effect/receipt/nonce/outbox commitment;
- establish Value-Movement Closure.

The safe release posture remains sequential authority with parallelism used only
for non-authoritative candidate construction until the complete refinement and
commit obligations are satisfied.
