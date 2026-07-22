# Assurance Factorization and Promotion Boundaries

Status: **normative addendum to `DECISIONS.md`**

This addendum incorporates the exact Research Kernel, Morph, ESSO, Lean, and
typed-parser decisions recovered after the first packet files were written.

## 1. Independently checked contracts

The FCIS claim is an assume-guarantee composition of these contracts:

```text
canonical parser contract
committed ownership contract
pure transition contract
footprint contract
patch and canonical-join contract
atomic commit contract
receipt and trace contract
cross-implementation refinement contract
economic terminal-lifecycle contracts
```

PR #477 addresses committed ownership. PR #478 addresses owned authority and
effect values plus part of the canonical parser boundary. Neither PR may claim
closure of the other contracts.

## 2. Typed authority pipeline

```text
RawBytes
  -> CanonicalBytes
  -> ParsedCommand
  -> AuthenticatedCommand
  -> AuthorizedCommand
  -> EvaluatedCandidate
  -> CommittedReceipt
```

Each arrow is total over its declared profile and returns one typed successor
or one stable typed rejection. A later phase must not accept an earlier phase's
type. Stable ownership proves data stability only. It does not prove parsing,
authentication, authorization, evaluation, or commitment.

The canonical raw-byte boundary requires:

```text
complete consumption
duplicate-key rejection before erasure
one integer spelling
one fixed-width hexadecimal spelling
declared Unicode policy
no floats, NaN, infinity, exponent aliases, or negative zero
bounded bytes, depth, items, tokens, and recursion
stable typed rejects
versioned grammar and algorithm
cross-language acceptance/rejection and byte parity
```

## 3. Tool authority

```text
Research Kernel = durable claims, evidence, refutations, promotion gates
Morph           = reformulation candidates and obligation discovery
ESSO            = bounded counterexample search and invariant checking
Lean            = small-kernel checking of scoped mathematical statements
```

These tools propose or check scoped obligations. Tool output changes the frozen
design only through a reviewed decision-record update and locally replayed
evidence. Retrieval score, LLM review, or bounded `UNSAT` does not authorize a
runtime design or a production claim. Private tools and artifacts remain
outside this repository unless licensing, provenance, pinning, and supply-chain
review explicitly admits them.

## 4. Parallelism remains downstream

Disjoint writes are insufficient for state-dependent tasks. A future promoted
footprint must bind:

```text
command_hash
pre_state_root
execution_context_hash
algorithm_version
read_cells
write_cells
context_cells
possible_effect_kinds
```

The extractor must satisfy:

```text
ActualReads    subset DeclaredReads
ActualWrites   subset DeclaredWrites
ActualContexts subset DeclaredContexts
```

Two tasks may commute only after read/write noninterference or direct step
commutation is established. The current undifferentiated `touched_cells`
conflict graph remains advisory for value-moving work.

Parallel equivalence must cover acceptance, rejection precedence, next state,
roots, effects and order, receipt, nonces, outbox, rounding, dust, fees, and
overflow behavior.

## 5. Atomic commit remains downstream

The shell's eventual committed unit is:

```text
AtomicCandidate {
  expected_pre_root,
  execution_context_hash,
  algorithm_version,
  next_state,
  next_state_root,
  effects,
  effects_root,
  receipt,
  receipt_root,
  nonce_updates,
  outbox_entries
}
```

Required storage semantics:

```text
root mismatch -> publish none
root match    -> publish all at one linearization point
```

The bounded ESSO model explains the partial-publication disaster state. It does
not prove the production datastore transaction, crash recovery, or idempotent
external delivery.

## 6. Exact evidence and release claim

Every satisfied requirement binds exact source/base SHAs, toolchain,
configuration, command, result, and relevant artifact hashes. Older-head
evidence becomes stale after any source change until replayed.

The versioned transition claim has this shape:

```text
StepP(State, Command, Context)
  -> Reject(Error)
   | Accept(NextState, Effects, Receipt)
```

The complete release profile separately tracks totality, deterministic bytes,
reject-is-no-output, invariant preservation, same-candidate output derivation,
canonical encoding injectivity, implementation refinement, parallel
equivalence when enabled, atomic commitment, and exact evidence binding. The
profile remains blocked while any required contract is open.

## 7. Priority after #477 and #478

The synthesis priority is preserved:

1. remaining economic terminal lifecycles;
2. bounded lifecycle models and runtime differential references;
3. concrete canonical-parser cross-language refinement;
4. canonical matching certificates;
5. source-derived footprint containment;
6. full parallel equivalence;
7. one production atomic candidate commit and idempotent outbox.

Persistent data structures and a thin Rust ownership boundary remain separate
representation/performance projects with their own parity and evidence gates.
