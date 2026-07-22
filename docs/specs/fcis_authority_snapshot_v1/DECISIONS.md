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
  -> typed reject
   | owned next state + canonical effect plan + receipt
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

### FCIS-D004: Three distinct representations

Each mutable subsystem has three explicit stages:

```text
SourceBuilder -> CommittedValue -> ScratchBuilder
```

`SourceBuilder` may be mutable and caller-owned. `CommittedValue` owns its
complete graph and exposes reads only. `ScratchBuilder` is a fresh local copy,
may mutate during one transition, never escapes, and is discarded on reject.

Rationale: using one inheritance hierarchy for mutable and committed values
left base-class mutation and reinitialization paths reachable.

### FCIS-D005: Composition for committed collections and tables

Committed enums, maps, sequences, balances, LP tables, nonce tables, pools,
intents, settlements, fills, and deltas must not inherit from mutable runtime
classes or built-in mutable containers. They use composition and read-only
protocols. Registered Python enum members are source values only; admission
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

Owned persistent maps/vectors with structural sharing are part of the official
plan after the correctness repair. Promotion requires benchmarks, dependency
and license review, canonical iteration/encoding parity, state-root parity,
nested immutability, memory bounds, and adversarial denial-of-service evidence.

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

State, effects, receipt, nonce/nullifier changes, roots, and outbox entries must
eventually commit at one expected-root compare-and-swap linearization point.
The snapshot PRs do not claim datastore linearizability or exactly-once
external delivery.

## Rejected designs

| Design | Decision | Reason |
| --- | --- | --- |
| `deep_freeze(Any) -> Any` | Rejected | Open accepted language and fallback behavior |
| `copy.deepcopy` at authority boundaries | Rejected | Invokes caller-controlled protocols and hides schema omissions |
| Reflect all dataclasses/enums | Rejected | Unregistered variants silently become authoritative |
| Frozen subclass of `dict`, `list`, or mutable domain class | Rejected | Base mutation/reinitialization bypass |
| `MappingProxyType` over caller storage | Rejected | Read-only view retains the caller alias |
| Set/frozenset as canonical protocol order | Rejected | Iteration order is not a canonical ABI |
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
