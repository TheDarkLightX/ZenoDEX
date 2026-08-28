---
name: zenodex-pattern-selector
description: >-
  Mandatory pattern and authority selector for ZenoDEX value-moving,
  state-carrying, proof-bearing, and transition code. Selects architecture from
  domain invariants, legal state space, authority level, ownership, and failure
  semantics rather than from syntax or familiar design-pattern names. Use
  before editing the functional core, proof projections, runtime bindings,
  settlement shells, or persisted protocol state in any language.
---

# ZenoDEX Pattern Selector

Use this skill before writing or refactoring any code that can affect:

- admission, authorization, ordering, replay, or freshness;
- balances, custody, liabilities, debt, collateral, fees, rewards, or supply;
- state roots, proof journals, witnesses, receipts, nullifiers, or effect plans;
- migration, shutdown, recovery, or atomic commit;
- a public assurance or production-authority claim.

The governing rule is:

> Select the pattern from the domain relationship and authority claim, not from
> whether the current implementation happens to be a class, dataclass, mapping,
> function, or Rust struct.

Two principles override every mechanical style rule:

1. **Semantic completeness precedes representational restriction.** Enumerate
   every legal state, ownership bucket, transition, and outcome before making
   illegal combinations unrepresentable. A rigid incomplete model is still
   wrong.
2. **Helper applicability is not profile authority, and profile authority is
   not commit authority.** A reusable arithmetic helper may accept a broader
   input language than a source-pinned proof profile. Narrow authority at an
   explicit wrapper or projection boundary. Do not silently change the helper's
   semantics and do not let the shell promote a helper result by proximity.

## Literature anchors

- Functional core, imperative shell:
  `https://functional-architecture.org/functional_core_imperative_shell/`
- Gary Bernhardt's boundaries discussion, summarized at:
  `https://www.andrewyao.me/Bernhardt-Boundaries/`
- Typed Design Patterns for the Functional Era:
  `https://arxiv.org/abs/2307.07069`

The useful interpretation for ZenoDEX is not merely "pure functions inside,
I/O outside." The core owns decisions. The shell owns acquisition and execution.
Boundary values explicitly bind the two.

---

## The authority pipeline

Every critical flow must expose these stages rather than collapsing them:

```text
raw external material
  -> parsed canonical domain values
  -> authenticated and freshness-bound facts
  -> pure deterministic decision or transition candidate
  -> profile-specific certificate or proof projection
  -> atomic compare-and-swap commit receipt
  -> asynchronous observation only
```

### Stage 1: Raw external material

Examples: JSON, transaction bytes, a database snapshot, oracle messages,
filesystem artifacts, network responses, wall-clock observations.

This stage has no economic authority.

### Stage 2: Authenticated facts

Examples: a finalized epoch permit, verified oracle snapshot, signer quorum,
policy root, source receipt, custody observation, proof-verifier result.

A fact must bind:

- its subject;
- exact state or source root;
- chain and profile;
- rule or protocol version;
- freshness window or finalized cursor;
- evidence or producer identity;
- intended consumer or command where substitution matters.

A caller-supplied Boolean such as `auth_ok`, `verified`, `fresh`, or
`maint_margin_ok` is not an authenticated fact.

### Stage 3: Pure decision or transition candidate

This stage owns all domain branching:

- eligibility;
- amounts and rounding;
- fee and liability ownership;
- mode and lifecycle transition;
- ordering and selection;
- complete effect plan;
- typed rejection set.

It performs no I/O and reads no hidden state.

### Stage 4: Profile-specific certificate or proof projection

This stage narrows a general result to one exact claim. It must validate every
profile dimension rather than assuming that a nearby proof or helper carries
that meaning.

Examples:

```text
generic DepositMint result
  -> exact Liquity V1 MCR = 11000
  -> mandatory prestate commitment
  -> exact policy and image identities
  -> authorized recursive mint row
```

The general helper remains general. The profile projection remains narrow.

### Stage 5: Atomic commit receipt

Only the commit boundary changes authoritative state. It atomically binds:

- expected pre-root or version;
- command and request identity;
- authenticated facts and policy root;
- post-state;
- complete typed effect plan;
- nonce, replay map, and nullifiers;
- receipt and outbox record.

A pure candidate, proof journal, effect preview, or self-hashed packet is not a
commit receipt.

---

## Three independent pattern axes

Do not force each artifact into one mutually exclusive category. Decide these
three properties separately.

### Axis 1: Authority

```text
Does this code decide or bind admission, authorization, amounts, ownership,
fees, order, replay, roots, proofs, or effects?
  -> authoritative pure core or pure profile projection

Does it acquire external material or execute an already-decided effect?
  -> imperative shell
```

The core never calls the shell. `src/core/**` must not import
`src/integration/**`.

The shell may have many dependencies, but it should have few semantic branches.
It branches on typed core outcomes, commit status, and operational failures. It
must not independently decide economic amounts, modes, or ownership.

### Axis 2: Lifetime and ownership

```text
Does the value escape, persist, hash, sign, cache, cross a thread/task boundary,
or enter a proof, receipt, or effect plan?
  -> transitively immutable value

Is it fresh, exclusively owned, function-local scratch space that is discarded
on rejection?
  -> honest mutable builder is permitted
```

Immutability means no retained mutable alias, not merely `frozen=True`.

### Axis 3: Failure semantics

```text
Expected protocol refusal?
  -> typed rejection or canonical violation vector

Operational I/O failure?
  -> shell error with explicit retry/idempotency policy

Impossible state after trusted construction?
  -> programmer-error exception or Rust panic at a non-attacker boundary
```

Do not catch every exception in the pure core and convert it into an ordinary
protocol rejection. That hides implementation defects, changes public error
semantics, and can make Python and Rust disagree.

---

## Boundary invariants

### 1. Capture external facts once

Read clock, environment, network, files, database rows, and verifier output in
the shell. Normalize and authenticate once, then pass immutable values inward.
The core never rereads or recomputes the external observation.

### 2. Parse into a legal domain, do not carry raw bags inward

Reject unknown fields, noncanonical encodings, Boolean/integer aliases, duplicate
keys, wrong units, malformed identifiers, and out-of-domain numbers before the
value becomes a trusted domain object.

Do not use `Dict[str, Any]`, `Mapping[str, Value]`, or arbitrary JSON as committed
or proof-bearing state.

### 3. Keep boundary directions one-way

```text
shell -> values -> core -> effect values -> shell
```

The core does not call databases, adapters, callbacks, loggers, or service
objects. A callback can smuggle I/O and nondeterminism into an apparently pure
function.

### 4. Represent effects as data

When the shell would otherwise contain domain logic, move that logic into a pure
plan:

```python
@dataclass(frozen=True, slots=True)
class TransferEffect:
    effect_id: EffectId
    asset: AssetId
    source: CustodyId
    destination: CustodyId
    amount_atoms: int
    liability_before: LiabilityId | None
    liability_after: LiabilityId | None
```

The shell executes this exact plan. It does not reconstruct amounts or choose a
fallback destination.

### 5. Test the communication boundary with real contracts

Pure core unit tests are necessary but insufficient. Mocks can match the test
interface while diverging from production encoding, transactionality, or retry
behavior.

For each critical boundary require:

- pure unit/property/formal tests for the core relation;
- contract tests against the actual adapter codec;
- integration tests for core-to-shell communication;
- reject-is-no-op tests;
- crash/retry tests around the commit boundary;
- golden cross-language vectors where Rust, Python, Tau, Lean, ESSO, or RISC0
  claim correspondence.

---

## Semantic completeness checklist

Before choosing typestate, sum types, immutable records, or proofs, enumerate:

1. Every legal lifecycle phase.
2. Every admitted command in each phase.
3. Every legal successor and stuttering transition.
4. Every asset and unit.
5. Every custody, liability, and ownership bucket.
6. Every rounding residue and dust destination.
7. Every rejection and whether independent failures must be retained together.
8. Every replay, retry, stale-state, and concurrency outcome.
9. Every migration and shutdown obligation.
10. Every proof or certificate claim and its explicit nonclaims.

The model is not complete merely because all current constructors are frozen or
all current transitions are proved.

### Legal-state representability test

For each adopted scenario, ask:

```text
Can this legal state be constructed without lying about ownership or units?
Can this legal transition be expressed without an imperative-shell special case?
Can the result retain every liability and residue?
```

If not, extend the model before restricting it.

---

## Authoritative state representation

### Transitive immutability

Python authoritative values should normally use:

```python
@dataclass(frozen=True, slots=True)
class State:
    ...
```

Allowed fields are immutable scalars, enums, tuples, frozensets where ordering
is irrelevant, persistent immutable maps, or other transitively immutable
values.

A frozen dataclass containing `dict`, `list`, a mutable mapping view, or a mutable
nested object is a frozen lie.

`MappingProxyType` is only a read-only view. It is not an immutable value if the
backing dictionary is retained elsewhere.

### Collections by semantics

| Domain meaning | Representation rule |
|---|---|
| Ordered sequence | Immutable tuple in protocol-defined order. Never sort unless the protocol says to. |
| Set | Explicit duplicate policy plus canonical cross-language order for encoding. |
| Dynamic map | Persistent map or privately owned map behind an immutable API; canonicalize bytes separately. |
| Large hot state | Preserve indexed lookup complexity. Do not replace a large map with an O(n) tuple scan without measurement. |
| Hash/signature input | One versioned canonical byte encoding independent of in-memory representation. |

### Exact runtime types

In Python, `bool` is an `int`. Critical constructors should normally require
`type(value) is int` rather than `isinstance(value, int)`.

Likewise, canonical string keys may need `type(key) is str` before set equality,
because equal-hashing subclasses can bypass a purely value-based key-surface
check.

### Checked arithmetic

Define one integer domain for each field and intermediate.

- Python arbitrary precision does not prove Rust overflow safety.
- Rust checked arithmetic does not prove the Python model enforces the same cap.
- Multiplication may require a wider intermediate domain than persisted values.
- Rounding mode and remainder ownership are part of semantics.

Every value-moving arithmetic path needs boundary, max, max-plus-one, and
intermediate-overflow tests.

---

## Typed rejection rules

Use a discriminated result, not Boolean success plus a message string.

```python
class RejectCode(Enum):
    STALE_PRESTATE = "stale_prestate"
    POLICY_MISMATCH = "policy_mismatch"
    LIABILITY_COVER_MISMATCH = "liability_cover_mismatch"

@dataclass(frozen=True, slots=True)
class StepReject:
    code: RejectCode
    details: RejectDetails
```

### Preserve independent violations

A first-error return is wrong when multiple obligations are independently
observable or required for recovery/audit.

Return a unique canonical tuple:

```python
violations: tuple[Violation, ...]
```

Dependent checks must not fabricate defaults when a prerequisite is missing.
Represent dependency-blocked obligations explicitly or omit them according to a
specified dependency graph.

### Rejection is a no-op

A rejected transition preserves:

- authoritative prestate;
- balances and custody;
- nonce and replay state;
- nullifiers;
- receipts and outbox;
- all external effects.

Local mutable builders are discarded.

---

## Witness and certificate rules

A proof-like value must bind what it proves.

Unsafe:

```rust
struct LiquidationEligible;
```

Safer shape:

```rust
struct EligibleLiquidationPlan {
    vault_id: VaultId,
    command_hash: CommandHash,
    pre_state_root: StateRoot,
    oracle_root: OracleRoot,
    policy_root: PolicyRoot,
    protocol_version: ProtocolVersion,
    evidence_root: EvidenceRoot,
    plan: LiquidationPlan,
}
```

Prefer ownership and consumption for one-use witnesses. In Python, a frozen
witness improves structure but is not unforgeable; only a private trusted
constructor or authoritative runtime revalidation may mint it.

An expected hash supplied in the same untrusted payload as the object being
checked proves self-consistency, not authenticity.

---

## Profile authority versus helper applicability

This rule is mandatory for formal and proof-backed code.

### Broad helper, narrow profile

A helper may support a family:

```text
mcr_bps > 10000
```

A profile may require one member:

```text
Liquity V1 minimum -> mcr_bps = 11000
```

Correct architecture:

```text
generic helper(input)
  -> generic journal
  -> validate exact profile dimensions
  -> profile certificate / authorized row
```

Incorrect repairs:

- changing the generic helper to 11000 and breaking legitimate nonbaseline use;
- accepting any helper result because a nonzero `policy_hash` is nearby;
- letting the shell decide whether the result is "close enough" to the profile;
- treating stronger numeric restrictions as semantically interchangeable.

A stronger rule is a different transition relation and proof identity unless a
formal dominance/refinement theorem says otherwise.

---

## Imperative shell rules

1. Acquire and authenticate external material.
2. Convert it to exact typed values.
3. Call one versioned pure transition or profile projection.
4. Exhaustively handle success and rejection.
5. Atomically commit the exact returned state and effects.
6. Return the committed receipt, not a prediction of success.
7. Make retries idempotent and request-identity bound.
8. Keep asynchronous proof generation, indexing, notification, and observation
   outside settlement authority.

### Shell branch budget

A shell branch is acceptable for:

- parse/authentication failure;
- typed core reject versus accept;
- CAS conflict;
- committed retry versus new request;
- operational retry/abort policy.

A shell branch is suspicious when it decides:

- a fee split;
- a liquidation branch;
- a dust owner;
- a fallback custody destination;
- which legal state is "really" intended;
- whether an incomplete proof is sufficient.

Move those branches into typed pure values.

---

## Rust guidance

- Use `BTreeMap` or an explicitly canonical map for hashed state. Do not rely on
  `HashMap` iteration order.
- Use checked arithmetic for every attacker-reachable or value-moving operation.
- Use `Result<T, E>` at trust boundaries; no `unwrap`, `expect`, or panic for
  attacker-controlled input.
- Add `#[must_use]` to transitions, plans, and certificates whose return value
  must not be ignored.
- Keep enum wire discriminants stable. Append variants or version the schema.
- Do not rely on Serde struct layout as a canonical commitment codec.
- Use typestate for small statically known pipelines such as
  `Raw -> Canonical -> Authenticated`. Use exhaustive tagged state plus a total
  transition function for persisted dynamic financial state.
- Interior mutability belongs only in local scratch builders or shell-managed
  operational state, never in authoritative economic state.

---

## Refactoring preflight

Record these before editing existing critical code:

1. Exact file, type, function, and line range.
2. Domain relation and adopted scenario IDs.
3. Current authority level: helper, profile projection, proof, or commit.
4. Full legal state and transition inventory affected.
5. Constructors, mutation sites, retained aliases, and escape points.
6. Every caller and API compatibility obligation.
7. Canonical encoding, state-root, signature, proof, and receipt consumers.
8. Python/Rust/Tau/Lean/ESSO/RISC0 parity consumers.
9. Units, bounds, rounding, duplicate, order, and rejection semantics.
10. Big-O and memory impact.
11. Schema version and migration path.
12. Evidence invalidation: image IDs, receipts, manifests, proofs, and release
    artifacts that become stale.
13. Counterexample and reject-is-no-op regression.
14. Explicit nonclaims after the change.

Representation-only changes and semantic changes should be separate patches.
Do not opportunistically refactor neighboring critical code.

See `reference/boundary-authority-checklist.md` for the review worksheet and
`reference/before-after-examples.md` for concrete templates.

---

## Stop signs

Stop and redesign when any of these appears:

- `@dataclass(frozen=True)` with a `dict` or `list` field;
- `Dict[str, Any]` as committed or proof-bearing state;
- `auth_ok: bool`, `verified: bool`, or a caller-provided verdict as authority;
- `except Exception` in a pure transition that turns bugs into protocol rejects;
- float arithmetic in consensus, custody, accounting, or proof paths;
- a shell recomputing economic amounts from a receipt;
- a proof journal omitting a value-moving observable;
- a profile accepting a general helper result without exact narrowing;
- a helper narrowed merely because one consumer is stricter;
- a hash compared only to another value from the same untrusted payload;
- an immutable API refactor that keeps a mutating method name while callers
  ignore the new return value;
- state persisted without the complete effect plan, replay record, and receipt;
- a proof or test called "verified" without the exact claim and nonclaims.

---

## Required critical-PR evidence

Every critical repair PR should contain:

1. A minimized counterexample.
2. The normative scenario or invariant IDs.
3. Root cause at the correct authority boundary.
4. The smallest pure semantic repair.
5. Boundary and commit changes, when mounted.
6. Typed negative tests and reject-is-no-op evidence.
7. Property, mutation, differential, model-checking, or theorem evidence
   proportional to the claim.
8. Exact commands and outcomes.
9. Evidence invalidation and rebuild requirements.
10. Explicit residual obligations and nonclaims.

A passing theorem about a supplied arithmetic value does not prove runtime
inventory completeness. Python/Rust parity does not prove correct economics. A
root match does not prove conservation. State the claim at the smallest level
that the evidence actually supports.
