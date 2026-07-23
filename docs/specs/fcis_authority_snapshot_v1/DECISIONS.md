# Design Decisions and Rationale

This file records the decisions recovered from the ZenoDEX FCIS discussion.
The implementation agent may implement them. It may not reinterpret them.
Changing an `ADOPTED` decision requires a reviewed decision-record update before
the code change.

## Adopted decisions

### FCIS-D001: Functional core and imperative shell

```text
immutable state + typed command + committed policy + explicit evidence
  -> pure total transition
  -> Reject(reject reason, receipt)
   | Accept(owned next state, canonical commit plan, receipt)
   | CommittedFailure(failure reason, owned next state,
                      canonical commit plan, receipt)
```

The shell acquires authenticated context, loads state, invokes the transition,
and atomically commits the returned candidate. Core code does not read clocks,
environment variables, globals, databases, filesystems, or networks.

Rationale: stable explicit inputs are required for replay, proof binding, and
cross-language refinement.

### FCIS-D002: Semantic unity

Data and execution are separated, while each authority-bearing representation
remains joined to one canonical schema, invariant set, version, and commitment
definition.

Rationale: physical module separation previously allowed multiple meanings of
the same app-state schema.

### FCIS-D003: Closed typed deterministic combinators

Authority admission uses a finite declared combinator language. Each accepted
constructor, record, field, enum, and variant is registered. Unknown values
fail closed. There is no fallback copy or reflective discovery.

Rationale: the earlier generic `deep_freeze(Any) -> Any` accepted a larger
language than the protocol and made caller behavior part of admission.

### FCIS-D004: One-way admission and persistent transition values

Legacy mutable values may appear only at an outer compatibility ingress:

```text
LegacySource
  -> closed exact admission
  -> CommittedValue

DomainStep(CommittedValue, TypedCommand, ExplicitContext)
  -> Reject
   | Accept(NewCommittedValue, EffectPlan, Receipt)
```

`DomainStep` is the two-way leaf relation for domains that have no
protocol-defined committed failure. The aggregate DEX command relation uses
the three-way result in FCIS-D001. Only aggregate `Reject` has the unchanged
state and no-authoritative-effects law.

`LegacySource` may be mutable and caller-owned. Admission owns and validates its
complete graph once. Authority-bearing core functions accept and return exact
committed values. They do not expose `to_scratch_*`, accept a structural view
that a legacy builder can satisfy, or re-admit a mutable domain builder after
each transition.

A pure function may use a fresh private builtin work buffer as an implementation
detail when profiling justifies it. The buffer is created inside the function,
shares no mutable child with caller input, never crosses a function or module
boundary, is discarded on rejection, and is compared against a return-new pure
reference. Such a buffer is not a third domain representation and does not
weaken the normative transition relation.

Rationale: persistent return-new semantics keep old roots valid, eliminate a
public mutation window, and directly match replay and refinement claims. Python
cannot type-enforce the non-escape property used by ST-style encapsulated
mutation, so whole-domain scratch conversion is too weak for the normative
authority boundary.

### FCIS-D005: Composition for committed collections and tables

Committed enums, maps, sequences, balances, LP tables, nonce tables, pools,
intents, settlements, fills, and deltas must not inherit from mutable runtime
classes or built-in mutable containers. They use composition and exact
committed-type APIs. Registered Python enum members are source values only; admission
copies their profile-relative tag/member ordinals into `OwnedEnumV1`.

Rationale: overridden mutators do not block unbound base descriptors,
base-class constructors, or other inherited mutation surfaces.

### FCIS-D006: Exact type admission

Declared scalar and record types use exact checks:

```python
type(value) is int
type(value) is bool
type(value) is ExpectedRecord
type(value) is ExpectedEnum
```

`bool` is never accepted as an integer. Scalar, enum, collection, and record
subclasses are rejected before any semantic operation on their values. Exact
enum type admission does not make the singleton transitively immutable, so the
source member itself is never retained.

Rationale: behavior-bearing subclasses can change arithmetic, copying,
comparison, hashing, serialization, or future execution after validation.

### FCIS-D007: Canonical bytes are a separate ABI

Owned in-memory values do not define canonical bytes by their layout or
iteration order. A versioned encoder declares tags, fields, widths, order, and
normalization. Accepted authority bytes must satisfy:

```text
decode(bytes) = value
encode(value) = bytes
```

Rationale: immutability does not imply unique representation.

### FCIS-D008: Deterministic stable rejection

Admission rejects carry a stable code and field path. Error precedence is
declared. Error text must not contain attacker-controlled `repr`, class names,
hash order, or first-worker timing.

Rationale: rejection is part of deterministic replay and may be observable.

### FCIS-D009: Existing bounded-ingress limits are reused

The immediate implementation uses already-mounted limits rather than inventing
new policy:

| Limit | Value | Existing source |
| --- | ---: | --- |
| canonical JSON depth | 64 | `src/state/canonical.py` |
| canonical JSON items | 200,000 | `src/state/canonical.py` |
| DEX state bytes | 4,000,000 | `state_from_snapshot` |
| balances | 200,000 | `state_from_snapshot` |
| pools | 50,000 | `state_from_snapshot` |
| LP balances/metadata | 200,000 | `state_from_snapshot` |
| nonces | 200,000 | `state_from_snapshot` |
| perps markets | 10,000 | `state_from_snapshot` |
| perps accounts | 200,000 | `state_from_snapshot` |
| strings | 4,096 characters unless a narrower field rule exists | `state_from_snapshot` |
| DEX intent batch | 256 | `DexEngineConfig.max_intents` |

Numeric economic bounds continue to come from the existing domain constants,
kernel schemas, and record invariants. A field with no existing upper bound is
recorded as a residual boundedness gap; the implementation agent must not guess
one.

### FCIS-D010: PR sequencing

PR #477 is repaired and reviewed first. PR #478 is rebased on the final #477
head and then repaired. No dependent PR may duplicate or fork the shared
combinator implementation.

Rationale: #478 inherited the flawed helper and then enlarged its authority
surface.

### FCIS-D011: Python enforcement and nonclaim

The immediate repair is strict Python: exact types, composition, slots,
one-time construction, owned containers, explicit schemas, mypy, and
adversarial tests.

It guarantees defensive ownership against caller-retained source aliases and
exposed supported APIs under trusted CPython and trusted repository code. It
does not defend against arbitrary in-process code using `object.__setattr__`,
`ctypes`, debugger memory writes, monkeypatching trusted classes, or equivalent
interpreter compromise.

### FCIS-D012: Persistent structures are a later PR

Return-new persistent transition semantics apply immediately. The first repair
may implement an update by rebuilding an owned tuple/map, even when that costs
`O(n)`. Specialized persistent maps/vectors with structural sharing remain a
later performance PR. Promotion requires benchmarks, dependency and license
review, canonical iteration/encoding parity, state-root parity, nested
immutability, memory bounds, and adversarial denial-of-service evidence.

Rationale: persistent structures can reduce O(n) ownership cost, while changing
representation now would mix correctness repair with performance migration.

### FCIS-D013: Thin Rust ownership boundary is medium-term

A later PyO3 or equivalent Rust boundary should own committed state and signed
authority values. Python may operate on read-only views or typed projections.
Python/Rust canonical golden vectors and transition parity are required before
promotion.

Rationale: Rust can enforce ownership and borrowing at compile time; Python's
guarantee remains conditional on trusted in-process code.

### FCIS-D014: DSL-generated authority types are long-term

The long-term source of truth should generate Python reference values, Rust
owned values, canonical encoders/decoders, proof-guest inputs, and registry
drift checks from one versioned grammar or typed DSL.

### FCIS-D015: Parallel execution is downstream work

Transitive immutability and stable command meaning are prerequisites for
parallel execution. Parallelism remains an optimization of the sequential
normative transition and must prove byte-identical state, effects, receipt,
rejection, nonce, rounding, fee, and outbox results for every permitted logical
partition.

### FCIS-D016: Atomic candidate commit is a separate shell obligation

The shell commits one `CommitBundle` at one expected-root compare-and-swap
linearization point. Its `CommitPlan` contains authoritative state, value,
nonce/nullifier, and receipt records. Its `OutboxPlan` contains immutable
records for later event, proof, index, or notification delivery. Both plans are
committed atomically as data; external delivery occurs afterward under
receipt-derived idempotency keys. The snapshot PRs do not claim datastore
linearizability or exactly-once external delivery.

### FCIS-D017: Heterogeneous record containers use exact-type union dispatch

`RecordUnionOf` is the closed schema for a container whose values are drawn
from several distinct registered record classes. It selects one `RecordOf`
variant solely from `type(source) is RegisteredSourceType`. Registered source
and owned classes are unique, and subclasses, lookalikes, unknown types, and
fallback variants reject before field access.

Rationale: the mounted perps market map contains four exact market record
classes. A single `MapOf` value schema and `TaggedRecordOf` over one source
class cannot represent that accepted language without a second hand-written
dispatcher.

### FCIS-D020: Canonical encoding and protocol order are separate contracts

Canonical encoding defines one accepted byte representation. Protocol order
defines which semantic value precedes another for selection, folding, or
tie-breaking. One byte key may implement both only when a versioned law and
cross-language vectors prove that lexicographic key order equals the declared
protocol order and that equal order keys imply equal semantic values.

Unordered domains are normalized by their declared protocol order.
Semantically ordered domains, including nonce order, route hops, proof ancestry,
and price-time priority, preserve and validate that order rather than being
re-sorted by an unrelated encoding key.

### FCIS-D018: Character semantics and UTF-8 work have separate bounds

`ExactString` may declare both `max_characters` and `max_utf8_bytes`. The
character bound preserves the mounted state contract. The byte bound limits
canonical encoding work. Generic mounted strings use 4,096 characters and a
16,384-byte conservative UTF-8 ceiling; narrower fields retain their local
bounds.

Rationale: equating 4,096 characters with 4,096 UTF-8 bytes would reject valid
multibyte state accepted by the current mounted decoder and silently change
baseline semantics.

### FCIS-D019: Closed heterogeneous maps use one keyed-map combinator

`ExactKeyedMap` declares an exact ordered string-key set and one child schema
per key. It owns cardinality checks, exact key checks, canonical rejection
precedence, per-key traversal, resource accounting, owned-map construction,
and committed-value revalidation.

Rationale: perps and clearinghouse global-state dictionaries contain booleans
and integers with field-specific bounds. A uniform `MapOf` cannot express that
language. Hand-written field loops would create a second admission system and
allow schema, budget, and rejection precedence to drift.

## Rejected designs

| Design | Decision | Reason |
| --- | --- | --- |
| `deep_freeze(Any) -> Any` | Rejected | Open accepted language and fallback behavior |
| `copy.deepcopy` at authority boundaries | Rejected | Invokes caller-controlled protocols and hides schema omissions |
| Reflect all dataclasses/enums | Rejected | Unregistered variants silently become authoritative |
| Frozen subclass of `dict`, `list`, or mutable domain class | Rejected | Base mutation/reinitialization bypass |
| `MappingProxyType` over caller storage | Rejected | Read-only view retains the caller alias |
| Set/frozenset as canonical protocol order | Rejected | Iteration order is not a canonical ABI |
| Public `to_scratch_*` conversion from committed authority state | Rejected | Creates a second mutable domain representation and makes non-escape a Python convention |
| Structural read protocol at an authority-core entry | Rejected | A mutable legacy builder can satisfy the protocol and cross the ownership boundary |
| Re-admit a mutable post-transition builder | Rejected | Duplicates validation and makes one transition depend on a mutation/copy-back window |
| Compatibility coercion at committed boundary | Rejected | Expands accepted language and creates encoding aliases |
| Rewrite whole core in Rust in these PRs | Deferred | Excess scope; thin boundary follows exact Python contract |
| Persistent map migration in these PRs | Deferred | Requires independent parity, benchmark, and dependency evidence |

## Implementation-agent authority

The implementation agent may choose local variable names and split small
helpers when complexity limits require it. It may not change:

- accepted source types;
- output types;
- rejection precedence or codes;
- bounds;
- canonical order;
- PR sequencing;
- public nonclaims;
- forbidden mechanisms;
- required tests and gates.

Any necessary deviation is returned as a written design question. Code must
not be used to answer the question implicitly.
