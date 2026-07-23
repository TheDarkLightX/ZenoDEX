# FCIS patterns alignment with “Values as Boundaries”

**Date:** 2026-07-22  
**Status:** Architecture review and correction note  
**Applies to:** `FCIS_PATTERNS_REPORT_2026_07_22.md` in draft PR #479  
**Runtime impact:** None

## Purpose

The Formal Methods Philosophy tutorial [Functional Core, Imperative Shell: How Immutable Values Become Boundaries](https://thedarklightx.github.io/Formal_Methods_Philosophy/tutorials/functional-core-imperative-shell-values-as-boundaries/) is the semantic and assurance baseline for ZenoDEX FCIS design.

The patterns report has a narrower role: it proposes concrete Python/Rust representations, deterministic combinators, persistent collections, benchmark gates, and implementation sequencing. It must not redefine the core/shell contract more weakly than the tutorial.

When this note identifies a conflict, this note and the tutorial take precedence until the main report is edited.

## What the tutorial establishes

The tutorial treats FCIS as a separation of meaning, authority, and effects rather than a directory convention. Its transition shape is:

```text
immutable state
+ canonical command
+ committed policy
+ authenticated evidence
    -> typed rejection
     | acceptance(next state, exact effect plan, receipt draft)
     | committed failure(next state, exact effect plan, receipt draft)
```

The shell is responsible for exact input binding, canonical decoding, provenance capture, atomic compare-and-swap publication, recovery, and idempotent delivery. The core remains authoritative for semantic admission, authorization, arithmetic, ordering, replay policy, rejection precedence, and effect-plan construction.

The tutorial also establishes:

- transitive rather than shallow immutability;
- total, bounded, deterministic transitions;
- explicit distinction between semantic replay and shell-refinement evidence;
- atomic publication of state, receipt, replay identity, nonce/nullifier state, and outbox records;
- typed effect plans interpreted by a capability-bearing shell;
- read/write footprints, commutativity, monotonicity, and sequential/parallel parity as prerequisites for deterministic parallel execution;
- persistent data structures as performance mechanisms that do not define protocol meaning;
- fresh, exclusively owned local mutation as compatible with a pure observable transition.

## Resolution of the main report

### 1. Decision is three-way, not universally binary

The main report currently models only `Accept` and `Reject`, and states that every rejection leaves state unchanged. That is correct only for an ordinary rejection.

ZenoDEX also needs a distinct committed-failure outcome for protocols that intentionally consume a nonce, charge a fee, record an attempted action, advance a breaker, or make another authoritative change despite not completing the requested operation.

Recommended algebra:

```rust
pub enum Decision<S, R, E, X, F> {
    Accept {
        next: S,
        receipt: R,
        effects: CommitPlan<E>,
    },
    Reject {
        reason: X,
        receipt: R,
    },
    CommittedFailure {
        reason: F,
        next: S,
        receipt: R,
        effects: CommitPlan<E>,
    },
}
```

Required laws:

```text
Reject
  => post_root = pre_root
  ∧ authoritative effects = empty

CommittedFailure
  => post_root/effects are exactly those returned by the core
  ∧ the outcome cannot be represented as Reject
```

### 2. The receipt is part of the atomic commit bundle

The report’s pipeline currently shows the shell committing the effect plan and then persisting the receipt. That ordering can leave an accepted state without the receipt needed to explain or replay it.

The atomic publication unit must bind at least:

```text
expected pre-root
next state / state patch
receipt
replay identity
nonce/nullifier changes
protocol effects
outbox records
algorithm and codec versions
```

A crash before publication leaves the old state authoritative. A crash after publication leaves the entire new bundle authoritative and recoverable.

### 3. Separate protocol commit effects from post-commit shell obligations

The main report’s one effect list mixes transfers, state writes, receipt persistence, event delivery, and proof requests. Those operations have different atomicity and authority semantics.

Use two explicit layers:

```rust
pub struct AcceptedTransition<S, R, C, O> {
    pub next: S,
    pub receipt: R,
    pub commit_plan: CommitPlan<C>,
    pub outbox: OutboxPlan<O>,
}
```

`CommitPlan` contains authoritative changes that must publish atomically:

```text
state patch
balance/value movement
mint/burn
nonce/nullifier/replay update
receipt record
outbox record creation
```

`OutboxPlan` describes effects delivered after commit:

```text
canonical event publication
allowlisted external notification
proof-generation request
index/cache refresh
```

The outbox plan is committed as data with the transition. Delivery is retried afterward using a canonical identity derived from the replay identity, effect index, destination, and payload commitment. The effect-plan hash alone is insufficient because distinct commands can authorize equal plans.

### 4. Split canonical representation from protocol ordering

The proposed `CanonicalKey` currently serves encoding, ordering, deduplication, and tie-breaking. These are related but not identical contracts.

Prefer:

```rust
pub trait CanonicalEncode {
    fn canonical_bytes(&self) -> Box<[u8]>;
}

pub trait ProtocolOrd {
    fn protocol_cmp(&self, other: &Self) -> core::cmp::Ordering;
}
```

A byte key may implement both only when the protocol explicitly proves/specifies:

```text
protocol_cmp(a, b)
  = lexicographic_cmp(order_key(a), order_key(b))

order_key(a) = order_key(b)
  iff a and b are equal under the relevant protocol identity
```

Canonical encoding can be injective without preserving numeric or semantic order. No implementation should infer an ordering merely because an encoding is canonical.

### 5. `OrderedFold` consumes an explicitly ordered sequence

The correct rule is not “sort every fold.” Some sequences already have semantic order: nonces, route hops, price-time priority, proof ancestry, and rejection precedence.

The rule is:

```text
unordered domain
  -> normalize using a unique versioned protocol order

semantically ordered domain
  -> preserve and validate that order

already canonical sequence
  -> consume without an incidental second ordering rule
```

Every consensus-visible fold must state where its order originates and why that order is unique.

### 6. Strengthen `CanonicalPatch` with preconditions

Sorted, duplicate-free `Put/Delete` operations do not by themselves prevent stale or semantically ambiguous application.

A patch should bind the state it was derived from and, where useful, the prior value expected at each key:

```rust
pub struct CanonicalPatch<K, V> {
    pub version: PatchVersion,
    pub expected_pre_root: StateRoot,
    ops: Box<[PatchOp<K, V>]>,
}

pub enum PatchOp<K, V> {
    Insert {
        key: K,
        value: V,
    },
    Update {
        key: K,
        expected_old_hash: ValueHash,
        value: V,
    },
    Delete {
        key: K,
        expected_old_hash: ValueHash,
    },
}
```

Required laws:

```text
apply(S, P) succeeds => root(S) = P.expected_pre_root
failed apply          => no partial state is observable
normalize(P) twice    = normalize(P) once
empty patch           = identity
```

The exact per-key precondition scheme is workload-dependent. The global pre-root binding is mandatory for authority-bearing application.

### 7. Keep the existing `DisjointMerge` rule

The full report already gives the correct default conflict condition:

```text
W1 ∩ W2 = ∅
W1 ∩ R2 = ∅
W2 ∩ R1 = ∅
```

This is stronger than write/write disjointness and should remain. Specialized commutative deltas may relax it only under an explicitly identified algebra and proof obligation.

### 8. Exact search requires an optimality certificate

`BoundedSearch` may omit a certificate only when it does not claim global optimality.

```text
Exact search
  -> finite candidate-domain definition
  -> feasibility result
  -> winning objective and total tie-break key
  -> replayable optimality certificate

Deterministic heuristic
  -> bounded algorithm id/version
  -> feasibility certificate
  -> explicit non-claim of global optimality
```

For exact-out minimality, a compact certificate is often enough:

```text
quote(dx) delivers at least dy
quote(dx - 1) does not deliver dy
```

### 9. Remainder allocation needs a fairness policy

Canonical ordering makes allocation deterministic but not automatically fair or manipulation-resistant.

`AllocateRemainder` should carry a versioned policy such as:

```text
stable canonical order
rotating order from a precommitted epoch seed
signed user-salt order fixed before outcome knowledge
```

The receipt must identify the policy and winning priority keys. Claims of fairness require a separate argument; determinism alone is not fairness.

### 10. Make resource determinism explicit

Result determinism is insufficient when an adversarial input can induce unbounded or implementation-divergent resource use.

Each transition/combinator should declare deterministic limits where relevant:

```text
maximum canonical input bytes
maximum integer bit width
maximum reads and writes
maximum patch operations
maximum candidates
maximum effects
maximum witness/proof bytes
maximum tree/proof depth
maximum retained snapshots
```

A shared value can make these limits reviewable:

```rust
pub struct TransitionBudget {
    pub max_reads: u32,
    pub max_writes: u32,
    pub max_candidates: u32,
    pub max_effects: u32,
    pub max_witness_bytes: u32,
}
```

Budget admission should occur before expensive work wherever the model permits.

## Okasaki and the tutorial

The tutorial and report agree on the important point: Okasaki-style persistence is an implementation technique supporting cheap immutable versions, not the semantic definition of ZenoDEX state.

The report’s collection guidance remains valid:

- use a local one-builder `BTreeMap` for small states or dense batches;
- benchmark persistent ordered maps for large, sparsely updated, snapshot-heavy state;
- retain canonical logical encoding independent of internal tree shape;
- treat an authenticated tree as a separately versioned commitment protocol;
- do not infer eager Rust/Python bounds from a lazy functional implementation without reproducing its evaluation and sharing assumptions.

A production red-black map also depends on a justified deletion implementation, not only Okasaki’s elegant insertion presentation. Deletion-heavy ZenoDEX surfaces include zero-balance removal, filled-order deletion, closed-vault removal, consumed evidence, and expired intents.

## Relationship between the two documents

The tutorial should answer:

```text
What does FCIS mean?
Where is semantic authority?
What exactly crosses the boundary?
What must the shell prove/refine?
Which claims remain outside the core?
```

The patterns report should answer:

```text
Which reusable deterministic combinators should ZenoDEX implement?
Which laws must each combinator satisfy?
Which Python/Rust representations are candidates?
How are patches, ordering, search, allocation, and merge encoded?
How are alternatives benchmarked and promoted without changing semantics?
```

This division prevents the specialized report from becoming a second, weaker FCIS specification.

## Revised implementation sequence

### P0 — semantic contract and safe local improvement

1. Adopt the tutorial’s three-way decision model: accept, ordinary reject, committed failure.
2. Define the atomic commit bundle and distinguish commit data from post-commit delivery.
3. Split canonical encoding from protocol ordering.
4. Define preconditioned canonical patches and shared law tests.
5. Refactor balance transfer to one private builder and one freeze while preserving roots, receipts, and rejection precedence.
6. Add receipt binding for command, context/evidence, pre/post roots, algorithm versions, commit plan, outbox plan, and replay identity.

### P1 — reusable mechanisms and measured scale

7. Implement deterministic choice, ordered sequence, exact reduction, exact/heuristic bounded search, and remainder-policy combinators in Rust and Python reference form.
8. Add resource budgets and deterministic read/write footprint derivation.
9. Benchmark `BTreeMap`, `rpds::RedBlackTreeMap`, `im::OrdMap`, `immutables.Map`, and current reference representations.
10. Pilot a persistent map behind a shadow-only adapter.
11. Pilot deterministic parallel evaluation only where sequential/parallel parity includes state, effects, rejection, roots, receipts, and committed-failure behavior.

### P2 — proof-bearing state and stronger typing

12. Pilot typestate/witness types on one bounded lifecycle.
13. Pilot Flux or another refinement layer in a small leaf crate while retaining Kani on running code.
14. Prototype a versioned authenticated state adapter with migration and history-independence obligations.

## Required non-claims

This documentation does not establish:

- that any persistent collection is faster for the live workload;
- that a pure core makes the shell correct;
- that canonical encoding proves semantic correctness;
- that differential agreement proves the specification correct;
- that read/write disjointness covers specialized commutative effects;
- that deterministic remainder allocation is fair;
- that an authenticated tree preserves the current state-root protocol;
- that a type witness is unforgeable outside its actual language/module/runtime boundary.

## Primary references

1. Gary Bernhardt, “Boundaries.” <https://www.destroyallsoftware.com/talks/boundaries>
2. Chris Okasaki, *Purely Functional Data Structures*. <https://doi.org/10.1017/CBO9780511530104>
3. Will Crichton, “Typed Design Patterns for the Functional Era.” <https://arxiv.org/abs/2307.07069>
4. Maurice Herlihy and Jeannette Wing, “Linearizability: A Correctness Condition for Concurrent Objects.” <https://www.cs.cmu.edu/~wing/publications/HerlihyWing90.pdf>
5. John C. Reynolds, “Separation Logic: A Logic for Shared Mutable Data Structures.” <https://www.cs.cmu.edu/~jcr/seplogic.pdf>
6. Lindsey Kuper et al., “Freeze After Writing: Quasi-Deterministic Parallel Programming with LVars.” <https://hdl.handle.net/2022/34554>
7. Jerome H. Saltzer, David P. Reed, and David D. Clark, “End-to-End Arguments in System Design.” <https://www.cs.princeton.edu/~jrex/teaching/spring2005/reading/saltzer84.pdf>
