# Functional Core / Imperative Shell Patterns for ZenoDEX

**Date:** 2026-07-22  
**Status:** Architecture research report  
**Scope:** Python reference kernels, Rust authority kernels, deterministic state transitions, persistent collections, receipts, proof-oriented decomposition, and deterministic parallel execution.

## Executive conclusion

ZenoDEX is already using many of the right high-assurance patterns:

- pure transition functions;
- explicit accepted/rejected results;
- frozen Python records and private Rust state;
- integer-only arithmetic;
- canonical ordering and domain-separated state/receipt hashes;
- typed Rust rejection enums;
- Python/Rust shadow execution and differential testing;
- small arithmetic helpers that Kani can prove on the implementation that actually runs.

The next architectural improvement should **not** be “replace every map with an Okasaki red-black tree.” The highest-value move is to standardize a **typed deterministic transition algebra**:

```text
canonical command + immutable state + explicit context
    -> accepted(next state, receipt, canonical effect plan)
     | rejected(rejection receipt; state unchanged)
```

Then place persistent collections behind workload-specific adapters.

**Okasaki-style persistent red-black trees do help ZenoDEX**, especially for snapshot-heavy state, rollback, speculative branches, and large maps receiving sparse updates. Path copying and structural sharing can replace whole-map cloning with logarithmic-path updates. But red-black trees do not by themselves provide:

- a consensus-safe canonical byte encoding;
- a cryptographic state commitment or membership proof;
- atomic multi-map transactions;
- deterministic conflict resolution;
- domain-valid values;
- cross-language parity;
- proof that a transition preserves ZenoDEX economic invariants.

The recommended policy is:

1. Keep **logical state semantics**, **canonical consensus encoding**, and **authenticated storage** as separate layers.
2. Introduce typed deterministic combinators for every choice, ordering, allocation, reduction, patch, and merge.
3. Eliminate repeated whole-state copies by applying one normalized patch per transition.
4. Benchmark persistent ordered maps and HAMTs behind the same semantic interface before authority promotion.
5. Never let a library's internal tree shape, hash seed, insertion history, or iterator accident define a state root.
6. Add deterministic parallelism only for proven-compatible patches evaluated from the same committed snapshot.

## 1. Repository-specific findings

### Existing strengths

`src/core/balance_kernel.py` explicitly prohibits floating point, wall-clock access, randomness, and I/O. It uses frozen dataclasses, canonical sorted tuples, stable rejection codes, explicit accepted/rejected values, pre/post roots, receipts, and Python/Rust shadow authority.

`rust-runtime/crates/zenodex-runtime-core/src/balance_kernel.rs` uses:

- a private `BTreeMap` state;
- typed `BalanceRejectedReason` values;
- checked arithmetic;
- a pure `Result<BalanceAccepted, BalanceRejectedReason>` transition;
- canonical key-order traversal for state roots;
- isolated arithmetic helpers proven total and panic-free with Kani.

`rust-runtime/crates/zenodex-runtime-core/src/replay_guard.rs` follows the same pattern and pins rejection precedence as part of semantics.

`docs/runtime/RUNTIME_CBC_CORE_STATUS.md` correctly separates model evidence, implementation evidence, wrapper/serialization evidence, authority promotion, differential testing, and replayable receipts. That distinction is essential: “proved model,” “proved helper,” and “live authority path” are different claims.

### Current collection costs

The existing implementations are semantically clean but may become expensive at larger state cardinalities.

- Python `BalanceState.balance_of` scans a sorted tuple linearly.
- Python `_set` filters and rebuilds the entire tuple.
- Rust `BalanceState::set` clones the whole `BTreeMap` before changing one key.
- Rust `transfer` chains two `set` calls, so a two-key transfer can clone the map twice.
- `ReplayGuardState::with_last` clones the complete map for one sender update.

These costs may be entirely acceptable for small states, golden-vector models, or low-frequency administrative surfaces. They should not be assumed acceptable for a large live balance table, order set, vault set, or batch-settlement state.

### Risk to avoid

A faster collection must not silently become the consensus format. Two implementations may represent the same key/value map with different internal tree shapes because of insertion history, balancing strategy, library version, pointer type, or hash seed. ZenoDEX equality and roots must continue to be defined over **canonical logical entries**, unless an authenticated-tree format is deliberately versioned and promoted as a consensus protocol.

## 2. Target transition architecture

```text
bytes / JSON / RPC / chain input
    -> decode and canonicalize
    -> ValidCommand + ExecutionContext
    -> Kernel::step(&State, &ValidCommand, &ExecutionContext)
    -> Decision
       - Accept { next_state, receipt, effect_plan }
       - Reject { receipt }
    -> shell checks expected pre-root
    -> shell commits the effect plan atomically
    -> shell persists the receipt
```

Abstractly:

```text
Step(S, C, X) -> Accept(S', R, E) | Reject(Rj)
```

Required laws:

```text
Determinism:
  identical logical S, C, X produce byte-identical decisions

Reject no-op:
  Reject implies post_root = pre_root and effect_plan = empty

Canonicality:
  logically equal S, C, X have identical canonical encodings

Replayability:
  receipt binds kernel version, input hashes, context hash, pre-root,
  decision, post-root, effect-plan hash, and witness hash

Persistence:
  evaluating Step never changes the observable value of S
```

A rejection is a first-class deterministic result, not an exception and not “no result.” It should bind the same command, context, pre-root, kernel version, and rejection code in every implementation.

## 3. Closed command/result algebra

Represent every kernel operation and outcome with closed sum types. Decode untrusted data into a validated command before it reaches arithmetic or state logic.

Rust:

```rust
pub trait Kernel {
    type State: Clone + Eq;
    type Command;
    type Context;
    type Receipt;
    type Effect;
    type Reject;

    fn step(
        state: &Self::State,
        command: &Self::Command,
        context: &Self::Context,
    ) -> Decision<Self::State, Self::Receipt, Self::Effect, Self::Reject>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision<S, R, E, X> {
    Accept {
        next: S,
        receipt: R,
        effects: CanonicalEffectPlan<E>,
    },
    Reject {
        reason: X,
        receipt: R,
    },
}
```

Python:

```python
@dataclass(frozen=True, slots=True)
class Accepted(Generic[S, R, E]):
    next_state: S
    receipt: R
    effects: tuple[E, ...]

@dataclass(frozen=True, slots=True)
class Rejected(Generic[R, X]):
    reason: X
    receipt: R

Decision = Accepted[S, R, E] | Rejected[R, X]
```

This makes rejection order, no-op behavior, receipt production, and effect planning part of the function's contract. ZenoDEX already does this per surface; the improvement is a shared schema, including rejection receipts and canonical effects.

**Priority: P0.**

## 4. Smart constructors and canonical domain types

Do not pass consensus-critical raw strings and integers deep into the core. Use private-field types that can exist only in canonical, in-range form.

```text
AssetId        = exactly 32 canonical bytes
PublicKey      = exactly 48 canonical bytes
Amount         = integer in [1, MAX_BALANCE]
FeeBps         = integer in [0, 10_000)
Nonce          = integer in [1, 2^32 - 1]
TimestampMs    = bounded consensus time
OracleAgeMs    = non-negative bounded duration
StateRoot      = domain-tagged 32-byte digest
```

Rust should use private tuple fields with `TryFrom` or smart constructors. Python should use frozen, slotted records with one construction path returning an explicit validation result. Canonical bytes should be retained internally instead of repeatedly parsing hex strings.

This separates representation failures from domain failures and makes illegal scalar states unrepresentable. It also reduces repeated validation, string allocation, accidental Unicode behavior, and divergent wrapper semantics.

Important qualification: types must not accidentally exclude legitimate domain states. Every constructor needs boundary-value and representability tests for **all** legal states.

**Priority: P0.**

## 5. Proposed typed deterministic combinators

ZenoDEX should add a small cross-language library of **typed deterministic combinators**. The goal is to make underspecified operations difficult to express.

### 5.1 `CanonicalKey`

Every item that can be sorted, deduplicated, merged, or selected exposes a versioned canonical key.

```rust
pub trait CanonicalKey {
    fn canonical_key_bytes(&self) -> Box<[u8]>;
}
```

The key must not depend on pointer address, locale, process-random hashing, insertion order, database row order, task completion order, or debug formatting.

### 5.2 `CanonicalChoose`

All routing, settlement, and optimization choices should be total orders, not “take the first maximum.”

```text
candidate key = (primary objective, secondary objective, canonical tie-break)
chosen candidate = minimum under one documented total-order key
```

The receipt should contain the winning comparison key. Existing route-length, pool-id, split-amount, and intent-id rules are natural inputs to this combinator.

### 5.3 `OrderedFold`

A fold over a map, set, or batch must state its order:

```text
OrderedFold(items, canonical_key, initial, step)
```

It validates uniqueness, orders by canonical key, and folds left. The result is independent of container iteration.

### 5.4 `ExactReduction`

Parallel or regrouped reduction is allowed only when the operation has an exact identity and associative semantics over the actual machine domain.

Suitable examples:

- checked integer addition under a proved global bound;
- set union over canonical keys;
- concatenation followed by canonical normalization;
- min/max under a total key.

Unsafe examples without additional proof or a fixed sequential order:

- floating-point sums;
- saturating addition where regrouping changes where saturation occurs;
- “first error” under unspecified scheduling;
- updates with hidden read/write dependencies.

The type should distinguish an ordinary ordered fold from a reduction licensed for regrouping or parallel execution.

### 5.5 `BoundedSearch`

Small finite optimization problems should be encoded as:

```text
BoundedSearch(candidate_generator, feasibility, score, canonical_tie_break)
```

The output includes the selected candidate, candidate bound/count, score, tie-break key, and optionally a witness that no better earlier candidate exists. This is preferable to a clever heuristic whenever exhaustive search is cheap and independently replayable.

### 5.6 `AllocateRemainder`

Fees, rebates, pro-rata fills, and liquidation proceeds need one reusable remainder algorithm:

1. compute exact floor allocations;
2. compute remaining units;
3. order eligible recipients by documented remainder priority and canonical key;
4. allocate units in that order;
5. return a conservation witness.

This prevents each kernel from inventing a subtly different dust rule.

### 5.7 `CanonicalPatch`

State changes should be represented as data before application:

```rust
pub enum PatchOp<K, V> {
    Put { key: K, value: V },
    Delete { key: K },
}

pub struct CanonicalPatch<K, V> {
    // private: sorted, duplicate-free, validated
    ops: Box<[PatchOp<K, V>]>,
}
```

Normalization rejects duplicate writes unless an explicit composition rule exists. A transfer should create one two-key patch and apply it once instead of cloning/updating state twice.

### 5.8 `DisjointMerge`

Parallel results may merge only when their declared read/write sets prove compatibility:

```text
writes(P1) ∩ writes(P2) = ∅
writes(P1) ∩ reads(P2)  = ∅
writes(P2) ∩ reads(P1)  = ∅
```

The merged patch is sorted by canonical key, never by task completion time.

### Rationale

Determinism is currently encoded repeatedly in comments and local sorting rules. A typed combinator layer converts those rules into reusable mechanisms and shared tests, reducing drift between Python, Rust, Tau models, proof harnesses, and UI receipts.

**Priority: P0.**

## 6. Effects as immutable data

The core should not call storage, networking, clocks, proof services, or event buses. It should return a canonical effect plan:

```text
Transfer(asset, from, to, amount)
Mint(asset, to, amount, authority)
Burn(asset, from, amount, reason)
WriteState(surface, expected_pre_root, post_root, patch)
PersistReceipt(receipt_hash, receipt_bytes)
EmitCanonicalEvent(topic, payload_hash, payload_bytes)
RequestProof(statement_hash, witness_commitment)
```

The shell interprets the plan. Alternative interpreters can simulate, audit, shadow, prove, or execute it. This is closely related to algebraic-effects/handler designs: effect operations are described independently of their interpretation.

Required rules:

- plans are canonical and versioned;
- reject plans are empty;
- the shell verifies `expected_pre_root`;
- partial application is impossible or rolled back;
- persistence timing does not change semantic order;
- retries are idempotent by transition/receipt id.

This prevents FCIS from degenerating into a small pure calculator plus a large policy-heavy shell.

**Priority: P0.**

## 7. Okasaki persistent red-black trees

### What they provide

Okasaki's functional red-black tree uses immutable nodes, path copying, structural sharing, and local rebalancing. A new version reuses unaffected subtrees. A persistent implementation typically provides:

- logarithmic lookup, insertion, and deletion;
- constant-time version cloning by sharing a root pointer;
- ordered iteration;
- cheap snapshots and speculative branches;
- old versions that remain valid for replay and comparison.

### Where they help ZenoDEX

Strong candidates include:

- balances and nonces once maps become large and updates remain sparse;
- vault maps;
- order sets indexed by canonical order keys;
- versioned governance state;
- speculative settlement branches;
- pre-state/post-state differential inspection;
- rollback and historical debugging.

They directly address the current Rust pattern of cloning a complete `BTreeMap` for one update and the Python pattern of rebuilding a complete tuple.

### Where they do not help

A red-black tree is not automatically:

- a Merkle tree;
- a canonical serialization;
- a cross-language tree layout;
- a transaction system;
- a conflict detector;
- a domain validator;
- a proof of economic invariants.

Tree shape may depend on update history. Hash canonical logical entries, not internal pointer/tree layout, unless a specific authenticated format is promoted as a versioned protocol.

### Do not hand-roll the production tree

Okasaki's insertion is elegant, but deletion and generalized balancing are easier to get wrong. Hirai and Yamamoto showed that variants of widely copied weight-balanced-tree algorithms had invalid deletion parameter assumptions and used Coq to establish the correct range. The broader lesson is to choose a maintained implementation, add model-based tests, and keep the collection outside consensus semantics.

### Rust candidates

- `rpds::RedBlackTreeMap`: persistent Okasaki-style red-black tree with structural sharing and logarithmic operations.
- `im::OrdMap`: immutable ordered B-tree with structural sharing and potentially better node locality.
- `std::collections::BTreeMap`: ordered and cache-friendly, but the current immutable façade clones the complete map before updates.

The correct choice is empirical. Persistent trees reduce snapshot/update copying but add reference counting and pointer chasing. A one-builder `BTreeMap` may remain fastest for small states or dense batches.

### Python candidates

Python has no standard persistent red-black-tree map. Practical options are:

- `immutables.Map`, a HAMT-backed immutable mapping with efficient evolved versions;
- Pyrsistent `PMap`/`PVector`;
- the existing canonical tuple for tiny reference models and golden vectors.

### Verdict

**Yes: adopt a persistent ordered map as a benchmarked implementation option behind a semantic interface. No: do not make Okasaki tree shape the state root or rewrite every small container immediately.**

**Priority: P1, after the patch/effect algebra.**

## 8. HAMTs for large unordered logical maps

A hash-array-mapped trie provides immutable versions with structural sharing and near-constant expected lookup/update. It may fit balances, nonces, object-id maps, or derived caches when ordered ranges are unnecessary.

Determinism rule:

```text
HAMT entries -> canonical key bytes -> sort -> encode/fold
```

HAMT traversal and hash placement must never define a receipt, root, dust allocation, or rejection order. The hash function is not a protocol identifier unless explicitly fixed and versioned.

HAMTs make updates cheap, but full-state canonical root generation still requires traversal and ordering unless ZenoDEX adopts an incremental authenticated commitment structure.

**Priority: P1 benchmark candidate.**

## 9. Persistent vectors and finger trees

Use persistent vectors for immutable indexed sequences such as effect arrays, witness vectors, route hops, or append-heavy per-transition logs.

Hinze and Paterson's finger trees are useful when a sequence needs efficient access at both ends, concatenation, measured split, or priority search. Possible ZenoDEX uses include batch queues or time-windowed snapshots. They are unnecessary for simple fixed receipts or maps.

The measure must be exact and associative over the actual numeric domain. A finger tree does not make a non-associative or overflow-prone measure safe.

**Priority: P2 unless a concrete sequence workload requires it.**

## 10. Owned/transient builders inside a pure façade

Pure APIs do not require every internal instruction to allocate a new collection. They require mutation to be unobservable outside the function.

```text
borrow immutable state
    -> create unique builder/transient view
    -> apply all normalized patch operations
    -> freeze builder into next immutable state
    -> builder cannot escape
```

Rust ownership is particularly suitable: clone or unwrap a uniquely owned root once, mutate private nodes or a local map, then return a new state. Persistent Rust libraries expose mutable methods that can exploit uniqueness. Python `immutables.Map` offers a mutation context for efficient batches while returning an immutable map.

Immediate ZenoDEX improvement: apply sender debit and recipient credit through one builder so `transfer` performs one state build rather than two chained clones.

Safety conditions:

- no builder alias escapes;
- the pre-state remains observationally unchanged;
- failure discards the builder;
- commit order is canonicalized separately;
- builders are not shared between workers.

**Priority: P0.**

## 11. Authenticated persistent state

Okasaki persistence preserves versions in memory; it does not authenticate them. ZenoDEX also needs commitments and, eventually, efficient membership/non-membership proofs.

Keep three interfaces:

```text
LogicalState<K,V>
    semantic lookup/update/equality

CanonicalStateCodec vN
    logical entries -> unique bytes

AuthenticatedStateStore vM
    versioned root + atomic update batch + inclusion/non-inclusion proofs
```

Initially, the codec may continue to sort and hash all entries. At scale, an authenticated persistent structure can update affected paths only and return a new root plus a node batch.

The Jellyfish Merkle Tree is a relevant engineering pattern: a versioned sparse Merkle tree for blockchain state that derives a new root and update batch from a known version while separating tree logic from storage.

Any promoted authenticated structure must specify:

- key derivation and canonical bytes;
- leaf/internal-node domain separation;
- empty-node hashes;
- duplicate-key rejection;
- proof encoding and verification;
- version/pruning semantics;
- atomic relation among logical patch, tree batch, root, and receipt;
- denial-of-service bounds for depth, proof size, and update amplification;
- migration from the prior root format.

Prototype this only after `CanonicalPatch` is stable. Do not bind kernel semantics to one physical tree.

**Priority: P2, strategically important.**

## 12. Typestate for protocol phases

Typestate refines permitted operations according to an object's abstract state. It is a good fit for a small number of security-critical lifecycle phases.

Rust example:

```rust
struct Batch<P> {
    data: BatchData,
    _phase: PhantomData<P>,
}

struct Collecting;
struct Sealed;
struct Settled;

impl Batch<Collecting> {
    fn add_intent(self, intent: ValidIntent) -> Result<Self, Reject> { ... }
    fn seal(self) -> Batch<Sealed> { ... }
}

impl Batch<Sealed> {
    fn settle(self, snapshot: &Snapshot) -> Result<Batch<Settled>, Reject> { ... }
}
```

Candidate domains:

- batch auction phases;
- oracle fact: decoded -> authorized -> fresh -> consumed;
- proof: bytes -> parsed -> verified -> bound-to-context;
- governance proposal lifecycle;
- vault operations under open/shutdown states.

Python generics can provide static guidance, but runtime construction paths remain necessary. Prefer separate frozen phase classes over records with many optional fields and booleans.

Do not encode every orthogonal business flag in generic parameters; the cross-product becomes unusable.

**Priority: P1 pilot.**

## 13. Refinement types and proof-carrying scalar APIs

Ordinary Rust types cannot directly state that `fee_bps < 10_000`, that post-balances equal exact arithmetic expressions, or that an accepted patch conserves an asset. ZenoDEX already uses Kani for implementation contracts. Flux-style refinement types could complement that approach.

Potential pilot obligations:

```text
0 <= fee_bps < 10_000
amount > 0
sender_after = sender_before - amount
recipient_after = recipient_before + amount
sender_before + recipient_before = sender_after + recipient_after
rejected -> post_root = pre_root
```

Use Flux experimentally in a small leaf crate or generated arithmetic module. Do not make an immature verifier build-critical until toolchain reproducibility and maintenance are established. Continue using Kani for executable implementation contracts and Lean/Tau/ESSO for model-level obligations.

**Priority: P2 experiment.**

## 14. Proof-oriented helper decomposition

ZenoDEX already does this well. Make it an explicit rule:

1. isolate heap-free or bounded scalar logic;
2. use checked arithmetic only;
3. make rejection precedence explicit;
4. avoid panics and implicit casts;
5. prove the exact helper invoked by the live transition;
6. separately test parsing, allocation, encoding, hashing, and wrappers;
7. bind evidence to the authority path in a replayable receipt.

This is more tractable than asking one model checker to reason simultaneously about strings, maps, hashing, allocation, and division. It also prevents a verified reimplementation from drifting away from running code.

**Priority: ongoing P0 rule.**

## 15. Deterministic parallel execution

Parallelism is safe only when scheduling cannot alter semantics.

```text
immutable committed snapshot
    -> canonical task partition
    -> pure task evaluation against same snapshot/context
    -> each task returns read set, write set, patch, receipt fragment
    -> deterministic compatibility check
    -> fixed-order canonical merge
    -> one effect plan
    -> atomic expected-root commit
```

Rules:

- no shared mutable logical state between workers;
- no “first task to finish wins” behavior;
- task ids and partitions derive from canonical keys;
- errors are sorted by canonical error key;
- conflicts reject or serialize by a documented total order;
- reductions use exact associative operations and fixed identities;
- all workers bind the same pre-root, context hash, and kernel version;
- failure returns no partial effects;
- parallel and sequential modes interpret the same patch algebra.

Required differential law:

```text
ParallelStep(S, C, X) = SequentialStep(S, C, X)
```

for decision, state, effects, rejection, roots, and receipts.

Kahn process networks and deterministic-parallel programming research support the general principle: deterministic communication topology and restricted shared state can make results independent of execution timing.

Candidate workloads include independent proof checks, stateless intent validation, disjoint-account updates, per-market computations without cross-market writes, candidate scoring before one canonical choice, and fixed-order section hashing.

**Priority: P1 after canonical patches and access sets.**

## 16. Deterministic memoization

Pure quote and proof-helper functions can be cached outside logical state.

Rules:

- key by a versioned canonical input hash;
- hits/misses cannot affect receipts or rejection order;
- no wall-clock TTL inside the core;
- cached values are content-addressed or revalidated;
- caches are excluded from state equality and roots;
- corruption fails closed or recomputes.

This can accelerate repeated quote and route calculations without weakening FCIS.

**Priority: P1 where profiling justifies it.**

## 17. Canonical encoding is a protocol

Every state, command, receipt, effect, witness, rejection, and ordering key should have:

- a domain-separation label;
- explicit version;
- one canonical byte representation;
- fixed integer encoding and bounds;
- fixed string/byte normalization;
- fixed map ordering by canonical key bytes;
- duplicate-key rejection;
- vectors shared by Python, Rust, Tau, and proof systems.

RFC 8785 illustrates the restrictions needed to make JSON invariant and hashable; RFC 8949 specifies deterministic CBOR encodings. ZenoDEX may continue its custom binary framing, but the codec deserves protocol-level rigor.

Collection rule:

- `BTreeMap` key-order iteration is convenient but is not itself the protocol specification.
- `HashMap`, Python `set`, HAMT iteration, database row order, and parallel completion order must be normalized.
- comparators must be pure and total.

**Priority: P0.**

## 18. Versioned algorithms and pure migrations

Every consensus-visible algorithm should identify:

```text
kernel_id
kernel_version
codec_version
state_commitment_version
tie_break_version
math_profile
```

Upgrades become explicit pure migrations:

```text
migrate_vN_to_vN1(old_state) -> new_state + migration_receipt
```

A migration must be deterministic, idempotent under its transition id, and covered by old/new root vectors. A collection-library upgrade must not alter protocol behavior without a version change.

**Priority: P0 for shared infrastructure.**

## 19. Collection selection matrix

| Workload | Recommended first choice | Why | Consensus caution |
|---|---|---|---|
| Tiny reference/golden state | Sorted immutable tuple/vector | Minimal dependencies; obvious canonical form | Linear lookup/update |
| Small/medium ordered state, dense batch updates | Local `BTreeMap` builder, frozen at return | Cache-friendly; one build per transition | Do not clone once per key |
| Large ordered state, sparse updates, many snapshots | Persistent RBT or immutable B-tree | Structural sharing; cheap versions; ordered ranges | Tree shape is not the root |
| Large key/value map, no range queries | HAMT | Efficient persistent lookup/update | Canonical-sort before encoding |
| Indexed immutable sequence | Persistent vector | Efficient versioning/random access | Sequence order must be semantic |
| Split/concat/measured sequence | Finger tree | General measured sequence | Measure must be exact/associative |
| Large proof-bearing consensus state | Authenticated persistent tree | Incremental roots and proofs | Entire format is a versioned protocol |

## 20. Benchmark and promotion plan

Do not choose from asymptotics alone. Benchmark representative ZenoDEX keys and values.

Rust candidates:

- current cloned `BTreeMap`;
- one-builder `BTreeMap` patch application;
- `rpds::RedBlackTreeMap` with `Rc` and, where necessary, `Arc`;
- `im::OrdMap`;
- `rpds::HashTrieMap` where ordering is unnecessary.

Python candidates:

- current sorted tuple;
- `immutables.Map`;
- Pyrsistent `PMap`.

Dimensions:

```text
state cardinality: 10^2, 10^3, 10^4, 10^5, 10^6
updates/transition: 1, 2, 16, 256, 4096
snapshot branches: 1, 2, 8, 32
read/write ratios: balance-like, routing-like, batch-like
```

Measure lookup, single/batch update, snapshot/branch cost, peak and retained memory, canonical iteration, state-root time, Python/Rust conversion, thread-safe pointer overhead, proof-tool compatibility, and adversarial-key behavior.

Promotion requires:

1. identical semantic and canonical-byte vectors;
2. identical rejection precedence;
3. old states unchanged after transitions;
4. differential, property, disaster, and fuzz suites passing;
5. no new panic or allocation ambiguity in the trusted path;
6. material measured benefit;
7. documented fallback and migration.

## 21. Common semantic-law suite

Every kernel should inherit the following properties.

### Core laws

- repeated evaluation is byte-identical;
- rejection leaves state/root unchanged;
- pre-state remains observationally unchanged;
- canonicalization is idempotent;
- canonical encoding is injective over supported semantic values;
- `decode(encode(x)) = x`;
- Python and Rust emit identical bytes and rejection codes;
- multiply-invalid input preserves documented rejection precedence.

### Patch laws

- normalization is idempotent;
- duplicate writes reject unless composition is explicit;
- empty patch is identity;
- disjoint patches commute semantically;
- merged disjoint patch equals canonical sequential application;
- failed application produces no partial state.

### Economic laws

- conservation by asset when mint/burn is absent;
- mint/burn requires explicit authority and receipt;
- fees/rebates/dust sum exactly;
- bounded search returns a feasible optimum with canonical tie-break;
- exact-out minimality is witnessed by success at `dx` and failure/underfill at `dx - 1`;
- all legal states remain representable.

### Parallel laws

- sequential/parallel parity;
- worker count does not change output;
- completion permutation does not change output;
- conflict result is timing-independent;
- fixed-tree reduction agrees with sequential fold for licensed reductions.

## 22. Recommended implementation sequence

### P0 — immediate

1. Define shared `Decision`, rejection receipt, canonical effect plan, and version metadata.
2. Define canonical identifier/value newtypes.
3. Implement `CanonicalKey`, `CanonicalChoose`, `OrderedFold`, `BoundedSearch`, `AllocateRemainder`, and `CanonicalPatch` in Rust and Python reference form.
4. Refactor balance transfer to apply one two-key patch and avoid repeated map clones.
5. Add the shared semantic-law suite.
6. Publish a collection/iteration policy forbidding unspecified consensus order.
7. Bind command hash, context hash, pre/post roots, effect hash, and algorithm versions in receipts.

### P1 — measured structural improvements

8. Add the persistent-collection benchmark harness.
9. Trial `rpds::RedBlackTreeMap` and `im::OrdMap` behind a private balance-state adapter.
10. Trial `immutables.Map` for large Python shadow states while retaining canonical sorted encoding.
11. Pilot typestate on one lifecycle-heavy surface.
12. Add read/write access sets and deterministic patch merge.
13. Add sequential/parallel differential execution for one provably disjoint batch.

### P2 — advanced assurance and scale

14. Prototype a versioned authenticated-state adapter with update batches and proofs.
15. Pilot Flux refinements on one small Rust kernel.
16. Introduce persistent vectors/finger trees only where profiling and operations require them.
17. Build pure root-migration tooling before changing commitment formats.

## 23. Proposed PR decomposition

1. **Architecture/ADR only** — this report and collection/determinism policy.
2. **Deterministic combinators** — no live authority changes; exhaustive/property tests.
3. **Canonical patch layer** — refactor balance/replay updates with unchanged vectors.
4. **Benchmark harness** — compare current and persistent candidates.
5. **Persistent-state pilot** — shadow-only adapter behind a feature flag.
6. **Typestate pilot** — one multi-phase protocol surface.
7. **Deterministic parallel pilot** — one disjoint batch with a sequential parity gate.
8. **Authenticated-state prototype** — no authority promotion before migration and proof obligations close.

## 24. Final recommendation on Okasaki

Okasaki's red-black tree is useful because **structural sharing matches FCIS semantics**: a transition can cheaply produce a new ordered map while preserving the old version. It is especially attractive when state is large, updates are sparse, and several versions remain live.

The deeper lesson is not “use red-black trees everywhere.” It is to choose representations whose invariants and updates are simple enough to reason about compositionally. ZenoDEX's most important representation is the transition:

```text
validated inputs
+ immutable pre-state
+ explicit deterministic context
-> typed decision
+ immutable next-state
+ canonical patch/effect plan
+ replayable proof-bearing receipt
```

Persistent red-black trees, HAMTs, persistent vectors, typestate, refinement types, authenticated trees, and deterministic parallelism should plug into this architecture without redefining its semantics.

## References

1. Chris Okasaki, *Purely Functional Data Structures*, Cambridge University Press, 1998. <https://doi.org/10.1017/CBO9780511530104>
2. Chris Okasaki, “Red-Black Trees in a Functional Setting,” *Journal of Functional Programming* 9(4), 1999. <https://doi.org/10.1017/S0956796899003494>
3. Stefan Kahrs, “Red-Black Trees with Types,” *Journal of Functional Programming* 11(4), 2001. <https://doi.org/10.1017/S0956796801004026>
4. Yoichi Hirai and Kazuhiko Yamamoto, “Balancing Weight-Balanced Trees,” *Journal of Functional Programming* 21(3), 2011. <https://doi.org/10.1017/S0956796811000104>
5. Guy E. Blelloch, Daniel Ferizovic, and Yihan Sun, “Just Join for Parallel Ordered Sets,” SPAA 2016. <https://doi.org/10.1145/2935764.2935768>
6. Phil Bagwell, “Ideal Hash Trees,” EPFL Technical Report, 2001. <https://infoscience.epfl.ch/record/64398>
7. Ralf Hinze and Ross Paterson, “Finger Trees: A Simple General-Purpose Data Structure,” *Journal of Functional Programming* 16(2), 2006. <https://doi.org/10.1017/S0956796805005769>
8. Guy E. Blelloch, “Prefix Sums and Their Applications,” CMU-CS-90-190, 1990. <https://www.cs.cmu.edu/afs/cs.cmu.edu/project/scandal/public/papers/CMU-CS-90-190.html>
9. Robert E. Strom and Shaula Yemini, “Typestate: A Programming Language Concept for Enhancing Software Reliability,” *IEEE Transactions on Software Engineering* 12(1), 1986. <https://doi.org/10.1109/TSE.1986.6312929>
10. Nico Lehmann, Adam Geller, Niki Vazou, and Ranjit Jhala, “Flux: Liquid Types for Rust,” *Proceedings of the ACM on Programming Languages* 7(PLDI), 2023. <https://doi.org/10.1145/3591283>
11. Gilles Kahn, “The Semantics of a Simple Language for Parallel Programming,” IFIP Congress, 1974. <https://dblp.org/rec/conf/ifip/Kahn74>
12. Laure Gonnord, Ludovic Henrio, Lionel Morel, and Gabriel Radanne, “A Survey on Parallelism and Determinism,” *ACM Computing Surveys* 55(10), 2023. <https://doi.org/10.1145/3564529>
13. Robert L. Bocchino Jr. et al., “Parallel Programming Must Be Deterministic by Default,” USENIX HotPar, 2009. <https://www.usenix.org/legacy/event/hotpar09/tech/full_papers/bocchino/bocchino.pdf>
14. Gordon Plotkin and Matija Pretnar, “Handling Algebraic Effects,” *Logical Methods in Computer Science* 9(4), 2013. <https://doi.org/10.2168/LMCS-9(4:23)2013>
15. RFC 8785, “JSON Canonicalization Scheme (JCS),” 2020. <https://www.rfc-editor.org/rfc/rfc8785>
16. RFC 8949, “Concise Binary Object Representation (CBOR),” deterministic encoding requirements, 2020. <https://www.rfc-editor.org/rfc/rfc8949>
17. Diem, “Jellyfish Merkle Tree,” versioned sparse Merkle state design. <https://developers.diem.com/docs/technical-papers/jellyfish-merkle-tree-paper/>
18. Rust standard library, `BTreeMap`: ordered map and key-order iteration. <https://doc.rust-lang.org/std/collections/struct.BTreeMap.html>
19. `rpds`, Rust persistent data structures and `RedBlackTreeMap`. <https://docs.rs/rpds/latest/rpds/map/red_black_tree_map/struct.RedBlackTreeMap.html>
20. `im`, immutable collections for Rust. <https://docs.rs/im/latest/im/>
21. `immutables`, immutable HAMT mapping for Python. <https://github.com/MagicStack/immutables>
22. Pyrsistent, persistent collections for Python. <https://github.com/tobgu/pyrsistent>
