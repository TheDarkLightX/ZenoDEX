# Functional Core / Imperative Shell Patterns for ZenoDEX

**Date:** 2026-07-22  
**Status:** Architecture research report  
**Scope:** Python reference kernels, Rust authority kernels, deterministic state transitions, persistent state, receipts, proof-oriented decomposition, and deterministic parallel execution.

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

Then place persistent collections behind a collection interface selected by workload.

**Okasaki-style persistent red-black trees do help ZenoDEX**, especially for snapshot-heavy state, rollback, speculative branches, and large maps receiving sparse updates. Their path-copying and structural sharing can replace whole-map cloning with logarithmic path updates. But they do not by themselves provide:

- a consensus-safe canonical byte encoding;
- a cryptographic state commitment or membership proof;
- atomic multi-map transactions;
- deterministic conflict resolution;
- domain-valid values;
- cross-language parity;
- proof that a transition preserves ZenoDEX invariants.

The recommended policy is therefore:

1. Keep **logical state semantics**, **canonical consensus encoding**, and **authenticated storage** as separate layers.
2. Introduce typed deterministic combinators for all choice, ordering, allocation, reduction, patching, and merging.
3. Eliminate repeated whole-state copies by applying one normalized patch per transition.
4. Benchmark persistent ordered maps and HAMTs behind the same semantic interface before promotion.
5. Never let a library's internal tree shape, hash seed, insertion history, or iterator accident define a state root.
6. Add deterministic parallelism only for statically or dynamically proven-disjoint patches evaluated from the same committed snapshot.

## 1. Repository-specific observations

### 1.1 Existing strengths

The current repository already demonstrates a strong FCIS/CBC direction.

`src/core/balance_kernel.py` explicitly prohibits floating point, wall-clock access, randomness, and I/O. It uses frozen dataclasses, canonical sorted tuples, stable rejection codes, explicit accepted/rejected values, pre/post roots, receipts, and Python/Rust shadow authority.

`rust-runtime/crates/zenodex-runtime-core/src/balance_kernel.rs` uses:

- a private `BTreeMap` state;
- typed `BalanceRejectedReason` values;
- checked arithmetic;
- a pure `Result<BalanceAccepted, BalanceRejectedReason>` transition;
- canonical key-order traversal for state roots;
- isolated arithmetic helpers that are proven total and panic-free with Kani.

`rust-runtime/crates/zenodex-runtime-core/src/replay_guard.rs` follows the same pattern and pins rejection precedence as part of semantics.

`docs/runtime/RUNTIME_CBC_CORE_STATUS.md` correctly distinguishes model evidence, implementation evidence, wrapper/serialization evidence, authority promotion, differential tests, and replayable receipts. That distinction is essential: “proved model,” “proved helper,” and “live authority path” are different claims.

### 1.2 Current collection costs

The existing implementations are semantically clean but may become expensive at larger state cardinalities.

- Python `BalanceState.balance_of` scans a sorted tuple linearly.
- Python `_set` filters and rebuilds the entire tuple.
- Rust `BalanceState::set` clones the whole `BTreeMap` before changing one key.
- Rust `transfer` chains two `set` calls, so a two-key transfer can clone the map twice.
- `ReplayGuardState::with_last` also clones the whole map for one sender update.

These costs can be entirely acceptable for small states, golden-vector models, or low-frequency administrative surfaces. They should not be assumed acceptable for a large live balance table, order set, vault set, or batch settlement state.

### 1.3 Architectural risk to avoid

A faster collection must not silently become the consensus format. Two implementations may represent the same key/value map with different internal tree shapes because of insertion history, balancing strategy, library version, pointer type, or hash seed. ZenoDEX equality and roots must continue to be defined over **canonical logical entries**, not over internal nodes, unless the authenticated-tree format itself is explicitly versioned as a consensus protocol.

## 2. The target transition architecture

The recommended functional core boundary is:

```text
bytes / JSON / RPC / chain input
    -> decode and canonicalize
    -> ValidCommand + ExecutionContext
    -> Kernel::step(&State, &ValidCommand, &ExecutionContext)
    -> Decision
       - Accept { next_state, receipt, effect_plan }
       - Reject { receipt }
    -> shell validates expected pre-root
    -> shell commits the normalized effect plan atomically
    -> shell persists the receipt
```

A rejection is a first-class deterministic output, not an exception and not “no result.” It should commit no state effects and should bind the same command, context, pre-root, kernel version, and rejection code that every independent implementation observes.

A useful abstract signature is:

```text
Step(S, C, X) -> Accept(S', R, E) | Reject(Rj)
```

with the laws:

```text
Determinism:
  Step(S, C, X) = Step(S, C, X)

Reject no-op:
  Reject implies post_root = pre_root and effect_plan = empty

Canonicality:
  logically equal S, C, X have identical canonical encodings

Replayability:
  receipt binds kernel version, input hashes, pre-root, decision, post-root,
  effect-plan hash, and witness hash

Persistence:
  evaluating Step never changes the observable value of S
```

## 3. Technique 1 — closed command/result algebra

### Pattern

Represent every kernel operation and every outcome with closed sum types. Decode untrusted data into a validated command before it reaches arithmetic or state logic.

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

### Rationale

This makes rejection order, no-op behavior, receipt production, and effect planning part of the function's type-level contract. It also prevents wrappers from translating exceptions or missing values differently in Python and Rust.

### ZenoDEX fit

The repository already uses this pattern per surface. The improvement is to standardize it across all trusted kernels, including a rejection receipt and a normalized effect plan.

**Priority: P0.**

## 4. Technique 2 — smart constructors and canonical domain types

### Pattern

Do not pass consensus-critical raw strings and integers deep into the core. Use private-field types that can exist only in canonical, in-range form.

Examples:

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

Rust should use private tuple fields and `TryFrom`/smart constructors. Python should use frozen, slotted records with a single construction path returning an explicit validation result. Canonical bytes should be retained internally rather than repeatedly parsing hex strings.

### Rationale

This separates representation failures from domain failures and makes illegal scalar states unrepresentable. It reduces repeated validation, string allocation, accidental Unicode behavior, and divergent wrapper semantics.

### Important limitation

“Making illegal states unrepresentable” is not enough. Types must not accidentally exclude legitimate domain states. Every smart constructor requires boundary-value analysis and representability tests for all legal states.

### ZenoDEX fit

The current canonicalization helpers are good, but Rust kernels frequently store canonical identifiers as `String`. Replacing those with fixed-byte newtypes would shrink the trusted parsing surface and make ordering equal to explicit byte ordering.

**Priority: P0.**

## 5. Technique 3 — proposed typed deterministic combinators

This section proposes a small ZenoDEX library of **typed deterministic combinators**. The purpose is to make nondeterministic or underspecified operations difficult to express.

### 5.1 `CanonicalKey`

Every item that can be sorted, deduplicated, merged, or selected must expose a versioned canonical key.

```rust
pub trait CanonicalKey {
    fn canonical_key_bytes(&self) -> Box<[u8]>;
}
```

A canonical key is protocol data. It must not depend on pointer address, locale, process-random hashing, insertion order, or debug formatting.

### 5.2 `CanonicalChoose`

All optimization and routing choices should be total orders, not “take the first maximum.”

```text
candidate key = (primary objective, secondary objective, canonical tie-break)
chosen candidate = minimum under one documented total-order key
```

Examples already present in ZenoDEX include route length, pool-id sequence, bounded split amount, and intent-id dust rules. The combinator should emit the winning comparison key in the receipt.

### 5.3 `OrderedFold`

A fold over a map/set/batch must state its order:

```text
OrderedFold(items, canonical_key, initial, step)
```

The combinator first validates uniqueness, orders by canonical key, then folds left. This makes the result independent of container iteration.

### 5.4 `ExactReduction`

Parallel or regrouped reduction is permitted only when the operation has an exact identity and associative semantics over the actual machine domain.

Good examples:

- checked integer addition under a proved global bound;
- set union over canonical keys;
- concatenation followed by canonical normalization;
- min/max under a total key.

Unsafe examples without extra machinery:

- floating-point sums;
- saturating addition when regrouping changes where saturation occurs;
- “first error” when scheduling order is unspecified;
- state updates with hidden read/write dependencies.

The type should distinguish an ordinary fold from a reduction licensed for regrouping or parallel execution.

### 5.5 `BoundedSearch`

Many ZenoDEX decisions are small finite optimization problems. Encode them as:

```text
BoundedSearch(candidate_generator, feasibility, score, canonical_tie_break)
```

The result includes:

- the selected candidate;
- candidate-count/bound;
- score;
- tie-break key;
- optional witness that no earlier/better candidate exists.

This is preferable to a clever heuristic when the bounded exhaustive search is cheap and independently replayable.

### 5.6 `AllocateRemainder`

Fees, rebates, pro-rata fills, and liquidation proceeds need an explicit remainder algorithm. A reusable combinator should:

1. compute exact floor allocations;
2. compute the remaining units;
3. order eligible recipients by a documented remainder priority and canonical key;
4. allocate one unit at a time in that order;
5. return an allocation witness proving conservation.

This avoids each kernel inventing a subtly different dust rule.

### 5.7 `CanonicalPatch`

State changes should be represented as data before application:

```rust
pub enum PatchOp<K, V> {
    Put { key: K, value: V },
    Delete { key: K },
}

pub struct CanonicalPatch<K, V> {
    // private; sorted, duplicate-free, validated
    ops: Box<[PatchOp<K, V>]>,
}
```

Normalization rejects duplicate writes unless an explicit composition rule exists. Applying a patch is a separate pure operation. A transfer should produce one two-key patch and apply it once, rather than clone/update the state twice.

### 5.8 `DisjointMerge`

Parallel results may merge only when their declared read/write sets prove compatibility. Merge order remains canonical even when patches are disjoint.

```text
DisjointMerge(P1, P2) succeeds iff:
  writes(P1) ∩ writes(P2) = ∅
  writes(P1) ∩ reads(P2)  = ∅
  writes(P2) ∩ reads(P1)  = ∅
```

The merged patch is sorted by canonical key, never by task completion time.

### Rationale

Determinism is currently encoded repeatedly in comments and local sorting rules. A small typed combinator layer turns those rules into reusable, testable mechanisms. This reduces semantic drift between Python, Rust, Tau models, proof harnesses, and UI receipts.

**Priority: P0.**

## 6. Technique 4 — effects as immutable data

### Pattern

The core does not call storage, networking, clocks, proof services, or event buses. It returns a canonical effect plan such as:

```text
Transfer(asset, from, to, amount)
Mint(asset, to, amount, authority)
Burn(asset, from, amount, reason)
WriteState(surface, expected_pre_root, post_root, patch)
PersistReceipt(receipt_hash, receipt_bytes)
EmitCanonicalEvent(topic, payload_hash, payload_bytes)
RequestProof(statement_hash, witness_commitment)
```

The shell interprets the plan. Alternative interpreters can simulate, audit, shadow, prove, or execute it.

### Rationale

A basic FCIS can develop a thin core and a large procedural shell. Representing effects as data keeps policy and sequencing in the core while leaving effect execution outside. It is closely related to algebraic-effects/handler designs: operations are described separately from their interpretation.

### Required laws

- effect plans are canonical and versioned;
- reject plans are empty;
- the shell checks `expected_pre_root` before commit;
- partial application is impossible or rolled back;
- persistence order does not change semantic order;
- retries are idempotent by receipt/transition id.

### ZenoDEX fit

This aligns with the repository's existing receipts, settlement-effect records, authority bridges, and expected-root direction. It should become the common boundary rather than a per-feature convention.

**Priority: P0.**

## 7. Technique 5 — Okasaki persistent red-black trees

### What they provide

Okasaki's functional red-black tree uses immutable nodes, path copying, structural sharing, and local rebalancing. A new version reuses all unaffected subtrees. A persistent implementation typically offers:

- logarithmic lookup, insertion, and deletion;
- constant-time version cloning by sharing a root pointer;
- ordered iteration;
- cheap snapshots and speculative branches;
- old versions that remain valid for replay or comparison.

### Where they help ZenoDEX

They are a strong candidate for:

- balances and nonces when maps become large and updates are sparse;
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

Tree shape can depend on insertion/deletion history. ZenoDEX must therefore hash canonical logical entries, not pointer/tree layout, unless a specific authenticated tree format is promoted as a versioned protocol.

### Should ZenoDEX implement one?

**Do not hand-roll a production red-black tree merely from the paper.** Okasaki's insertion is elegant, but deletion and generalized balancing are easier to get wrong. Hirai and Yamamoto found that variants of widely copied weight-balanced-tree algorithms had incorrect parameter assumptions and used Coq to certify the valid ranges. The lesson is broader: choose a maintained implementation, add model-based tests, and keep the collection outside the consensus semantics.

### Rust candidates

- `rpds::RedBlackTreeMap`: directly based on Okasaki's persistent red-black tree; structural sharing; logarithmic operations; constant-time clone of the persistent root.
- `im::OrdMap`: an immutable ordered B-tree designed for structural sharing and generally better node locality than a binary tree.
- `std::collections::BTreeMap`: excellent ordered iteration and cache behavior, but cloning the complete map before every immutable update is the current cost.

The right choice is empirical. `rpds` may reduce snapshot/update copying but add reference-counting and pointer-chasing overhead. `im::OrdMap` may offer a better large-node tradeoff. `std::BTreeMap` with one local builder per transition may remain fastest for small states or dense batches.

### Python candidates

Python has no standard persistent red-black-tree map. Practical candidates are:

- `immutables.Map`, a HAMT-backed immutable mapping with efficient evolved versions;
- Pyrsistent `PMap`/`PVector`;
- a small canonical tuple for reference models and golden vectors.

For consensus code, prefer established libraries plus a canonical serialization boundary over a bespoke Python balanced tree.

### Verdict

**Yes: adopt persistent ordered maps as a benchmarked implementation option behind a semantic interface. No: do not make “Okasaki tree shape” the state root or rewrite every small state container immediately.**

**Priority: P1 after the patch/effect algebra.**

## 8. Technique 6 — HAMTs for large unordered logical maps

### Pattern

A hash-array-mapped trie provides immutable map versions with structural sharing and near-constant expected lookup/update. It is often a better general mapping structure than a binary tree when ordered range queries are not required.

### ZenoDEX use

Potential fits:

- balances keyed by `(public_key, asset)`;
- nonce maps;
- object-id-to-record maps;
- internal caches excluded from consensus state.

### Determinism constraint

A HAMT's traversal order must never define a receipt, root, dust allocation, or rejection order. Before any consensus-visible operation:

```text
entries -> canonical key bytes -> sort -> encode/fold
```

The hash function also must not be treated as a protocol identifier unless it is explicitly fixed and versioned.

### Tradeoff

HAMTs make updates cheap but canonical full-state root encoding remains at least a traversal plus sorting cost unless ZenoDEX adopts an incremental authenticated commitment structure. That is why collection persistence and authenticated state are separate decisions.

**Priority: P1 benchmark candidate.**

## 9. Technique 7 — persistent vectors and finger trees

### Persistent vectors

Use a persistent vector for immutable indexed sequences such as:

- canonical effect arrays;
- witness vectors;
- append-heavy receipt logs within a transition;
- stable route-hop sequences.

They provide cheap versions without copying an entire Python tuple or Rust `Vec` for each small change.

### Finger trees

Hinze and Paterson's finger trees provide a general persistent sequence with efficient access to both ends and logarithmic concatenation/splitting, parameterized by monoidal measurements. They are useful when ZenoDEX needs sequences that support:

- split at a measured threshold;
- concatenate batches;
- priority search by an accumulated measure;
- deque-like access.

Possible fits include ordered batch queues, time-windowed snapshots, or measured intent sequences. They are unnecessary for simple fixed receipts or maps.

### Constraint

The measure must be exact and associative over the actual domain. A finger tree does not rescue a non-associative or overflow-prone measurement.

**Priority: P2 unless a concrete sequence workload demands it.**

## 10. Technique 8 — transient/owned builders inside a pure façade

Pure APIs do not require every internal instruction to allocate a new collection. They require that mutation be unobservable outside the function.

### Pattern

```text
borrow immutable state
    -> create unique builder / transient view
    -> apply all normalized patch operations
    -> freeze builder into next immutable state
    -> builder cannot escape
```

Rust ownership is especially well suited to this. A function can clone or unwrap a uniquely owned root once, mutate private nodes or a local `BTreeMap`, and return a new state. Persistent libraries such as `rpds` also expose mutable methods that can exploit uniqueness. Python `immutables.Map` provides a mutation context for efficient batches while still returning an immutable map.

### ZenoDEX improvement

For `BalanceState::transfer`, apply sender debit and recipient credit to one builder, then freeze once. Even before changing the underlying collection, this removes the chained double clone.

### Safety conditions

- no alias to the builder escapes;
- the pre-state remains observationally unchanged;
- failure discards the builder;
- iteration/commit order is canonicalized separately;
- builders are not shared across worker threads.

**Priority: P0.**

## 11. Technique 9 — authenticated persistent state

Okasaki persistence preserves versions in memory. It does not authenticate them. ZenoDEX also needs cryptographic commitments and eventually efficient membership/non-membership proofs.

### Layering

```text
LogicalState<K,V>
    semantic lookup/update/equality

CanonicalStateCodec vN
    logical entries -> unique bytes

AuthenticatedStateStore vM
    versioned root + update batch + inclusion/non-inclusion proofs
```

Initially, `CanonicalStateCodec` may continue to sort and hash all logical entries. For large live state, an authenticated persistent structure can update only affected paths and return a new root plus an atomic node batch.

The Jellyfish Merkle Tree is a relevant engineering example: it is a versioned sparse Merkle tree designed for blockchain state, returns a new root and tree-update batch from a known version, and separates tree logic from the storage reader/writer.

### ZenoDEX requirements

Any authenticated structure promoted to consensus must specify:

- key derivation and canonical key bytes;
- leaf and internal-node domain separation;
- empty-node hashes;
- duplicate-key rejection;
- proof encoding and verification;
- version/pruning semantics;
- atomic relation between logical patch, tree batch, state root, and receipt;
- denial-of-service bounds for depth, proof size, and update amplification;
- migration from the previous root format.

### Recommendation

Prototype a JMT-like or canonical sparse-Merkle adapter only after the logical patch algebra is stable. Do not bind kernel semantics to one physical tree implementation.

**Priority: P2, strategically important.**

## 12. Technique 10 — typestate for protocol phases

Typestate represents which operations are legal in a protocol state using types rather than repeated runtime flags. Strom and Yemini introduced typestate as a way to refine the set of permitted operations based on an object's current abstract state.

### Rust fits

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
- governance proposal: draft -> voting -> finalized -> enacted;
- vault operations requiring open/closed/shutdown states.

### Python fit

Python generics and protocols can provide static guidance, but runtime construction paths and validation remain necessary. Use separate frozen classes for materially different phases rather than one record with many optional fields and booleans.

### Caution

Do not encode every orthogonal business flag into generic parameters; the cross-product becomes unusable. Typestate is best for a small number of security-critical lifecycle phases.

**Priority: P1 pilot on one multi-phase surface.**

## 13. Technique 11 — refinement types and proof-carrying scalar APIs

Rust's ordinary types cannot state that `fee_bps < 10_000`, that a post-balance equals a pre-balance plus an amount, or that a patch conserves an asset. ZenoDEX already uses Kani to prove helper-level contracts. Refinement-type tools such as Flux can complement that approach by attaching logical predicates to Rust types and function signatures.

Potential pilot obligations:

```text
0 <= fee_bps < 10_000
amount > 0
sender_after = sender_before - amount
recipient_after = recipient_before + amount
sender_before + recipient_before = sender_after + recipient_after
accepted -> post_root != malformed
rejected -> post_root = pre_root
```

### Recommendation

Use Flux experimentally on a small leaf crate or generated arithmetic module. Do not make an immature verifier a build-critical dependency until toolchain reproducibility and maintenance are demonstrated. Continue using Kani for executable implementation contracts and Lean/Tau/ESSO for model-level obligations.

**Priority: P2 experiment.**

## 14. Technique 12 — proof-oriented helper decomposition

ZenoDEX is already doing this well. The pattern should become an explicit architecture rule:

1. isolate heap-free or bounded scalar logic;
2. use checked arithmetic only;
3. make rejection precedence explicit;
4. avoid panics and implicit casts;
5. prove the actual helper invoked by the live transition;
6. separately test parsing, allocation, encoding, hashing, and wrappers;
7. bind all evidence to the authority path in a replayable receipt.

This is often more tractable than asking a model checker to reason about strings, maps, hashing, allocation, and complex division in one function. It also prevents a “verified reimplementation” from drifting away from the running code.

**Priority: ongoing P0 rule.**

## 15. Technique 13 — deterministic parallel execution

Parallelism is safe only when scheduling cannot change semantics.

### Recommended model

```text
immutable committed snapshot
    -> canonical partition into tasks
    -> pure task evaluation against the same snapshot/context
    -> each task returns read set, write set, patch, receipt fragment
    -> deterministic compatibility check
    -> fixed-order canonical merge
    -> one effect plan
    -> atomic expected-root commit
```

### Rules

- no shared mutable logical state between workers;
- no “first task to finish wins” behavior;
- task ids and partitions derive from canonical input keys;
- errors are sorted by canonical error key;
- conflicts reject or serialize by a documented total order;
- reductions use an exact associative operator and fixed identity;
- all workers bind the same pre-root, context hash, and kernel version;
- failure returns no partial effects;
- parallel and sequential executions are different interpreters of the same patch algebra.

Required differential law:

```text
ParallelStep(S, C, X) = SequentialStep(S, C, X)
```

for decision, state, effects, rejection, roots, and receipts.

Kahn process networks and later deterministic-parallel programming research support the broader principle that deterministic communication/topology and restricted shared state can make parallel results independent of execution timing.

### ZenoDEX candidates

- independent signature/proof checks;
- per-intent stateless validation;
- disjoint-account operations;
- per-market computations with no cross-market writes;
- canonical candidate scoring before a single deterministic choice;
- section hashing where the hash-composition order remains fixed.

**Priority: P1 after canonical patches and access sets.**

## 16. Technique 14 — deterministic memoization

Pure quote and proof-helper functions may be memoized outside logical state.

Rules:

- key cache entries by versioned canonical input hash;
- cache hits/misses cannot affect receipts or rejection order;
- no wall-clock TTL inside the core;
- cached values are revalidated or content-addressed;
- caches are excluded from state equality and roots;
- cache corruption fails closed or recomputes.

This can improve route enumeration and repeated quote calculations without weakening FCIS.

**Priority: P1 where profiling shows repeated pure work.**

## 17. Technique 15 — canonical encoding as a first-class protocol

Canonical encoding is not a utility detail. It is part of consensus.

### Policy

Every state, command, receipt, effect, witness, rejection, and ordering key should have:

- a domain-separation label;
- an explicit version;
- one canonical byte representation;
- fixed integer encoding and bounds;
- fixed string/byte normalization policy;
- fixed map ordering by canonical key bytes;
- duplicate-key rejection;
- test vectors shared by Python, Rust, Tau, and proof systems.

RFC 8785 demonstrates the restrictions needed to make JSON hashable and invariant; RFC 8949 defines deterministic CBOR encodings. ZenoDEX may continue using its own binary framing, but it should treat the codec with the same rigor.

### Collection rule

- `BTreeMap` ordered iteration is convenient but not itself the protocol specification.
- `HashMap`, Python `set`, HAMT iteration, database row order, and parallel completion order must be normalized before consensus use.
- a comparator must be pure and total; it must not observe mutable/global state.

**Priority: P0.**

## 18. Technique 16 — versioned algorithms and pure migrations

Every consensus-visible algorithm should have a version or algorithm id in its receipt:

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

The migration must be deterministic, idempotent under its transition id, and covered by old/new root vectors. Library upgrades must not alter semantics without a protocol-version change.

**Priority: P0 for new shared infrastructure.**

## 19. Collection selection matrix

| Workload | Recommended first choice | Why | Consensus caution |
|---|---|---|---|
| Tiny reference/golden state | Sorted immutable tuple/vector | Minimal dependencies; obvious canonical form | Linear lookup/update |
| Small-to-medium ordered state, dense batch updates | Local `BTreeMap` builder, frozen at return | Cache-friendly; simple; one copy/build per transition | Do not clone once per key |
| Large ordered state, sparse updates, many snapshots | Persistent RBT or immutable B-tree | Structural sharing; cheap versions; ordered ranges | Tree shape is not the root |
| Large key/value map, no range queries | HAMT | Efficient persistent lookup/update | Canonical-sort before encoding |
| Indexed immutable sequence | Persistent vector | Efficient versioning and random access | Sequence order must already be semantic |
| Split/concat/measured sequence | Finger tree | General measured persistent sequence | Measure must be exact/associative |
| Large proof-bearing consensus state | Authenticated persistent tree | Incremental root and proofs | Full format is a versioned protocol |

## 20. Benchmark and promotion plan

Do not choose a persistent collection from asymptotics alone. Add a reproducible benchmark suite using representative ZenoDEX keys and values.

### Implementations

Rust:

- current cloned `BTreeMap`;
- one-builder `BTreeMap` patch application;
- `rpds::RedBlackTreeMap` using `Rc` and, where required, `Arc`;
- `im::OrdMap`;
- `rpds::HashTrieMap` where ordering is unnecessary.

Python:

- current sorted tuple;
- `immutables.Map`;
- Pyrsistent `PMap`;
- optionally a sorted immutable-map implementation if maintained and auditable.

### Dimensions

```text
state cardinality: 10^2, 10^3, 10^4, 10^5, 10^6
updates/transition: 1, 2, 16, 256, 4096
snapshot branches: 1, 2, 8, 32
read/write ratios: balance-like, routing-like, batch-like
```

Measure:

- lookup latency;
- single and batch update latency;
- snapshot/branch cost;
- peak memory and retained historical memory;
- iteration and canonical encoding cost;
- state-root cost;
- Python/Rust conversion cost;
- thread-safe pointer overhead;
- proof-tool compatibility;
- worst-case/adversarial key behavior.

### Promotion criteria

A collection can replace an authority container only when:

1. all semantic and canonical byte vectors remain identical;
2. rejection precedence remains identical;
3. old states remain unchanged after all transitions;
4. differential, property, disaster, and fuzz suites pass;
5. no new panic or allocation-failure ambiguity enters the trusted path;
6. the measured workload shows a material benefit;
7. fallback and migration behavior are documented.

## 21. Required semantic-law test suite

Every kernel should inherit a common property suite.

### Core laws

- repeated evaluation returns byte-identical results;
- rejection leaves state/root unchanged;
- input state is observationally unchanged;
- canonicalization is idempotent;
- canonical encoding is injective over supported semantic values;
- decode(encode(x)) = x;
- Python and Rust emit identical bytes and rejection codes;
- stable rejection precedence for multiply-invalid inputs.

### Patch laws

- patch normalization is idempotent;
- duplicate writes reject unless composition is explicit;
- applying the empty patch is identity;
- disjoint patches commute semantically;
- merged disjoint patch equals sequential application in canonical order;
- failed patch application produces no partial state.

### Economic laws

- conservation by asset where mint/burn is absent;
- explicit authority and receipt for mint/burn;
- fee/rebate/dust allocations sum exactly;
- bounded search returns a feasible optimum with canonical tie-break;
- exact-out minimality is witnessed by accepted input and predecessor failure;
- no legal state becomes unrepresentable.

### Parallel laws

- sequential/parallel parity;
- worker count does not alter output;
- task completion permutation does not alter output;
- conflict result is independent of timing;
- fixed reduction tree and sequential fold agree for licensed reductions.

## 22. Recommended implementation sequence

### P0 — immediate architecture work

1. Define the shared `Decision`, rejection receipt, effect-plan, and version metadata schema.
2. Define canonical identifier/value newtypes.
3. Implement `CanonicalKey`, `CanonicalChoose`, `OrderedFold`, `BoundedSearch`, `AllocateRemainder`, and `CanonicalPatch` in Rust and Python reference form.
4. Refactor balance transfer to produce/apply one two-key patch and avoid repeated map clones.
5. Add the common semantic-law test suite.
6. Publish a collection/iteration policy forbidding unspecified order in consensus output.
7. Include command hash, context hash, pre/post roots, effect hash, and algorithm versions in transition receipts.

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
17. Build pure state-root migration tooling before changing commitment formats.

## 23. Proposed PR decomposition

A safe implementation campaign can be split into reviewable PRs:

1. **Architecture/ADR only** — this report and collection/determinism policy.
2. **Deterministic combinators** — no live authority changes; exhaustive/property tests.
3. **Canonical patch layer** — refactor balance/replay state updates with unchanged vectors.
4. **Benchmark harness** — compare current and persistent collection candidates.
5. **Persistent-state pilot** — shadow-only adapter behind a feature flag.
6. **Typestate pilot** — one multi-phase protocol surface.
7. **Deterministic parallel pilot** — one disjoint batch with sequential parity gate.
8. **Authenticated-state prototype** — not authority-promoted until migration and proof obligations close.

## 24. Final recommendation on Okasaki

Okasaki's red-black tree is useful to ZenoDEX because its **structural sharing matches FCIS semantics**: a transition can cheaply produce a new ordered map while preserving the old version. It is especially attractive when state is large, updates are sparse, and multiple versions remain live.

However, the deeper lesson from Okasaki is not “use red-black trees everywhere.” It is to choose representations whose invariants and update rules are simple enough to reason about compositionally. For ZenoDEX, the most important representation is the transition itself:

```text
validated inputs
+ immutable pre-state
+ explicit deterministic context
-> typed decision
+ immutable next-state
+ canonical patch/effect plan
+ replayable proof-bearing receipt
```

Persistent red-black trees, HAMTs, persistent vectors, typestate, refinement types, authenticated trees, and deterministic parallelism should plug into that architecture without redefining its semantics.

## References

1. Chris Okasaki, *Purely Functional Data Structures*, Cambridge University Press, 1998. <https://doi.org/10.1017/CBO9780511530104>
2. Chris Okasaki, “Red-Black Trees in a Functional Setting,” *Journal of Functional Programming* 9(4), 1999. <https://doi.org/10.1017/S0956796899003494>
3. Stefan Kahrs, “Red-Black Trees with Types,” *Journal of Functional Programming* 11(4), 2001. <https://doi.org/10.1017/S0956796801004026>
4. Yoichi Hirai and Kazuhiko Yamamoto, “Balancing Weight-Balanced Trees,” *Journal of Functional Programming* 21(3), 2011. <https://doi.org/10.1017/S0956796811000104>
5. Guy E. Blelloch, Daniel Ferizovic, and Yihan Sun, “Just Join for Parallel Ordered Sets,” SPAA 2016. <https://doi.org/10.1145/2935764.293576join>
6. Phil Bagwell, “Ideal Hash Trees,” EPFL Technical Report, 2001. <https://infoscience.epfl.ch/record/64398>
7. Ralf Hinze and Ross Paterson, “Finger Trees: A Simple General-Purpose Data Structure,” *Journal of Functional Programming* 16(2), 2006. <https://doi.org/10.1017/S0956796805005769>
8. Guy E. Blelloch, “Prefix Sums and Their Applications,” 1990. <https://www.cs.cmu.edu/~scandal/papers/CMU-CS-90-190.html>
9. Robert E. Strom and Shaula Yemini, “Typestate: A Programming Language Concept for Enhancing Software Reliability,” *IEEE Transactions on Software Engineering* 12(1), 1986. <https://doi.org/10.1109/TSE.1986.6312929>
10. S. K. Lehmann et al., “Flux: Liquid Types for Rust,” *Proceedings of the ACM on Programming Languages* 7(PLDI), 2023. <https://doi.org/10.1145/3591283>
11. Gilles Kahn, “The Semantics of a Simple Language for Parallel Programming,” IFIP Congress, 1974. <https://doi.org/10.1007/978-3-642-65390-3_23>
12. Laure Gonnord et al., “A Survey on Parallelism and Determinism,” *ACM Computing Surveys* 55(10), 2023. <https://doi.org/10.1145/3564282>
13. Robert L. Bocchino Jr. et al., “Parallel Programming Must Be Deterministic by Default,” USENIX HotPar, 2009. <https://www.usenix.org/legacy/event/hotpar09/tech/full_papers/bocchino/bocchino.pdf>
14. Gordon Plotkin and Matija Pretnar, “Algebraic Effects and Handlers,” *Logical Methods in Computer Science* 9(4), 2013. <https://doi.org/10.2168/LMCS-9(4:23)2013>
15. RFC 8785, “JSON Canonicalization Scheme (JCS),” 2020. <https://www.rfc-editor.org/rfc/rfc8785>
16. RFC 8949, “Concise Binary Object Representation (CBOR),” deterministic encoding requirements, 2020. <https://www.rfc-editor.org/rfc/rfc8949>
17. Diem, “Jellyfish Merkle Tree,” versioned sparse Merkle state design. <https://developers.diem.com/docs/technical-papers/jellyfish-merkle-tree-paper/>
18. Rust standard library, `BTreeMap`: ordered map and key-order iteration. <https://doc.rust-lang.org/std/collections/struct.BTreeMap.html>
19. `rpds`, Rust persistent data structures and `RedBlackTreeMap`. <https://docs.rs/rpds/latest/rpds/map/red_black_tree_map/struct.RedBlackTreeMap.html>
20. `im`, immutable collections for Rust. <https://docs.rs/im/latest/im/>
21. `immutables`, immutable HAMT mapping for Python. <https://github.com/MagicStack/immutables>
22. Pyrsistent, persistent collections for Python. <https://github.com/tobgu/pyrsistent>
