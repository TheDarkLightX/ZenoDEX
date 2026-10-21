# FCIS Design-Pattern Audit

Status: **normative for PR #477 and PR #478; production claim blocked**

## Audit authority

This companion record extends the published ZenoDEX Audit V6 without modifying
its frozen artifact:

```text
audit URL: https://zenodex-oracle-audit-v4.jazzy-harp-9002.chatgpt.site/
snapshot schema: zenodex/audit-snapshot/v6
audit target commit: e2efd360921c6b1872710e77e300fb57fd6f2cc7
audit snapshot SHA-256:
  aeb96a452355860ef2e2fa116fec46f18a0dee4b7b7bd3dc3de9ba80c982c507
```

The V6 case, finding, and witness records do not currently carry design-pattern
fields. This file binds patterns to the exact V6 case and witness IDs. The next
generated audit snapshot should embed the fields defined below and preserve the
frozen V6 records unchanged.

## Required audit fields

Every repaired audit case or finding must carry, directly or through a
content-addressed pattern registry:

```text
pattern_id
pattern_version
selection_status
applicability
rationale
rejected_alternatives
mechanical_guarantees
explicit_non_guarantees
trusted_constructors_and_boundaries
counterexample_or_failure_family
python_enforcement
rust_or_proof_enforcement
serialization_replay_and_migration_impact
evidence_hooks
implementation_source_sha
pattern_record_sha256
review_status
```

`selection_status` is one of `SELECTED`, `EXPERIMENTAL`, `DEFERRED`, or
`REJECTED`. A selected pattern does not close an audit case. Closure also
requires a minimized pre-repair witness, exact-head implementation evidence,
canonical/root parity where applicable, and an independent review result.

## Pattern FCIS-PAT-CLOSED-ADMISSION-V1

**Name:** Closed deterministic admission algebra

**Selection:** SELECTED for PR #477 and inherited by PR #478
**Audit bindings:** `STATE-ALIAS-001` through `STATE-ALIAS-006` and
`IMMUTABILITY-ALIAS-01` through `IMMUTABILITY-ALIAS-06`

### Applicability and rationale

Use this pattern whenever an unowned or mutable value enters an authoritative
state, command, settlement, effect, receipt-data, or proof-input graph. The
accepted source language is finite, tagged, bounded, and exact. One total
interpreter returns one owned value or one stable typed rejection.

The production interpreter is profile-bound. Registry records remain
declarative, while one module-owned exhaustive resolver supplies trusted record
postconditions and versioned encoding. Keeping behavior out of the registry
prevents a caller-selected callback from redefining admission or byte limits.

This pattern was selected because the old open `deep_freeze(Any) -> Any` shape
could preserve behavior-bearing subclasses, invoke caller copy protocols,
silently admit new variants, and produce rejection order from host iteration.
Those behaviors violate the consensus boundary.

### Rejected alternatives

- `copy.deepcopy`: invokes caller-controlled protocols and has an open accepted
  language.
- Reflective dataclass or enum copying: silently expands authority when a new
  host type appears.
- Generic `Mapping`, `Sequence`, or `Iterable` traversal: executes caller
  behavior and leaves iteration semantics open.
- Normalization during committed admission: admits multiple spellings and can
  erase duplicate or collision evidence.
- One fallback branch for unknown objects: makes the language non-exhaustive.

### Mechanical guarantee and non-guarantees

The interpreter guarantees exact source-type admission, declared bounds,
canonical traversal order, stable rejection precedence, no partial result on
rejection, and construction only from fully admitted children. It does not
prove signature validity, economic correctness, database atomicity, or
cross-language refinement.

### Enforcement and evidence

Python uses exact frozen/slotted schema values, exhaustive `match` or exact-type
dispatch, `ValidatedAdmissionLimitsV1`, closed record/enum registries, and
`AdmitOk | AdmitReject`. A future Rust implementation should use a closed enum,
owned values, checked constructors, and an exhaustive match without trait-object
fallback. Required evidence includes hostile-hook tests, registry-drift tests,
BVA for all limits, rejection-permutation properties, AST checker mutation
tests, and canonical encoder parity.

## Pattern FCIS-PAT-COMPOSITION-OWNERSHIP-V1

**Name:** Composition-owned immutable aggregate

**Selection:** SELECTED for PR #477 and PR #478
**Audit bindings:** `STATE-ALIAS-001` through `STATE-ALIAS-006` and
`IMMUTABILITY-ALIAS-01` through `IMMUTABILITY-ALIAS-06`

### Applicability and rationale

Use this pattern for every committed collection or record whose source form is
mutable, subclassable, or behavior-bearing. The committed value owns a canonical
tuple of owned children and, when needed, a fresh private lookup index. It has no
mutable base class and exposes no backing container.

Composition removes the inherited mutator and initializer surface. It also
makes protocol fields separate from implementation caches and indexes. Python
enum singletons are treated as behavior-bearing source objects and copied into
composition-owned profile/member ordinals before they enter this graph.

### Rejected alternatives

- `FrozenDict(dict)` or `FrozenList(list)`: base-class mutators and initializers
  can bypass overridden methods.
- A frozen dataclass containing a list, dict, or mutable domain object: freezes
  only field rebinding.
- `MappingProxyType(caller_dict)`: creates a read-only view over storage that the
  caller may still mutate.
- A proxy around a mutable domain object: preserves mutable identity and
  behavior below the proxy.
- Trusting an already-owned-looking wrapper without revalidation: corrupted
  internal values can cross the boundary.

### Mechanical guarantee and non-guarantees

For accepted construction, later mutation of every retained source alias cannot
change canonical bytes, roots, lookup results, or behavior of the committed
value. The pattern does not prevent deliberate CPython memory corruption or a
trusted module from using `object.__setattr__`. Those remain TCB assumptions and
must be named.

Python enforcement uses final-by-convention frozen/slotted records, exact-type
admission, tuple children, private fresh dict indexes, no `__dict__`, no mutable
inheritance, and no public unowned insertion. Rust enforcement should own the
data behind immutable structs and persistent or standard owned collections.
Evidence includes retained-alias mutation, MRO/base-route attacks,
reinitialization, child-reference inspection, canonical-byte/root stability,
and corrupted-owned revalidation.

## Pattern FCIS-PAT-PERSISTENT-TRANSITION-V1

**Name:** One-way admission and persistent return-new transition

**Selection:** SELECTED for PR #477 and PR #478
**Audit bindings:** `STATE-ALIAS-001` through `STATE-ALIAS-006`

### Applicability and rationale

Use one-way admission at compatibility ingress and exact committed values
throughout the authority core:

```text
LegacySource
  -> closed exact admission
  -> CommittedValue

LeafStep(CommittedValue, TypedDelta, ExplicitContext)
  -> LeafReject(StableReason)
   | LeafOk(NewCommittedValue, CanonicalPatch)
```

This is the state-patch leaf relation for a domain with no protocol-defined
committed failure. It does not issue the aggregate receipt. The aggregate DEX
relation is the three-way `Decision` from `ERRATA.md` E10. Only aggregate
`Reject` is an unchanged-state no-op.

The pattern makes ownership transfer occur exactly once and removes a public
post-admission mutation window. Old committed versions remain valid for roots,
replay, proofs, and concurrent readers. Specialized persistent maps may share
unchanged structure; the initial Python repair may rebuild owned tuples while
preserving the same return-new semantics.

### Rejected alternatives

- Mutating a committed value in place.
- Public committed-to-mutable `to_scratch_*` conversion.
- Re-admitting a mutable post-transition domain builder.
- Structural read protocols that legacy mutable builders can satisfy.
- Catching immutability exceptions as normal control flow.
- Generic thaw or `deepcopy`.
- Sharing mutable children between legacy ingress and committed values.

### Mechanical guarantee and non-guarantees

Each accepted leaf transition returns a distinct immutable successor while the
pre-state remains byte- and behavior-stable. Leaf rejection returns no
candidate or effect. Aggregate rejection retains its canonical rejection
receipt while returning no successor or authoritative effect. The pattern does
not prove that transition logic is economically correct or that the imperative
shell commits the result atomically.

A leaf function may use a private builtin work buffer only when it cannot
escape and a differential test proves parity with the return-new reference.
Python cannot statically prove this non-escape property, so such a buffer is an
implementation optimization and never a domain representation or public API.

Evidence includes old-root stability throughout settlement, retained-source
alias inspection, rejected-transition no-output, pure-update/reference parity,
static rejection of public mutable projections, and mounted consumer tests.

Research basis:

- Functional Software Architecture defines the core as pure functions over
  immutable values and places stateful infrastructure in the shell:
  https://functional-architecture.org/functional_core_imperative_shell/
- Its illegal-state guidance places legacy conversion in an anti-corruption
  parse layer so downstream calculations receive the stronger value:
  https://functional-architecture.org/make_illegal_states_unrepresentable/
- Okasaki's persistence model preserves old versions and shares unchanged
  structure: https://doi.org/10.1017/CBO9780511530104
- Launchbury and Peyton Jones permit internal mutation behind a pure interface
  when a type system proves encapsulation. Python supplies no comparable
  parametricity guarantee:
  https://www.microsoft.com/en-us/research/publication/lazy-functional-state-threads/

## Pattern FCIS-PAT-TYPESTATE-AUTHORITY-V1

**Name:** Typestate authority pipeline with opaque verifier witnesses
**Selection:** SELECTED as a constraint on PR #478; broader implementation is a
separate contract
**Audit bindings:** `STATE-ALIAS-005` and `IMMUTABILITY-ALIAS-05`

### Applicability and rationale

Use distinct exact values for canonical bytes, parsed commands, owned commands,
authenticated commands, authorized commands, evaluated candidates, and
committed receipts. Each stage consumes only the exact predecessor and binds the
same canonical command identity/hash.

Stable owned data is necessary for authentication. It is not evidence that
authentication or authorization occurred. Opaque verifier-controlled witnesses
carry those facts.

### Rejected alternatives

- Treating a frozen or owned intent as an authentication witness.
- Passing raw dictionaries to value-moving functions.
- Reconstructing command meaning from a mutable builder after signature
  verification.
- Requiring Python object identity across wrappers instead of canonical
  identity/hash equality.
- Caller-constructible `auth_ok` flags as production authority.

### Mechanical guarantee and non-guarantees

The pattern prevents a later phase from accepting an earlier-phase value by
accident and prevents signed meaning from drifting through a mutable alias. PR
#478 implements ownership only. It does not claim parser replacement,
authentication-policy correctness, nonce commitment, receipt issuance, or
atomic commit.

Evidence includes phase-negative type tests, canonical command hash equality
across wrappers, mutable-builder mutation after signing, signed-envelope field
inventory, and mypy/static ABI checks.

## Pattern FCIS-PAT-SAME-CANDIDATE-EFFECT-V1

**Name:** Same-candidate owned effect plan

**Selection:** SELECTED for PR #478
**Audit bindings:** `STATE-ALIAS-006` and `IMMUTABILITY-ALIAS-06`

### Applicability and rationale

Use one owned evaluated candidate as the source of next-state data, settlement,
effects, totals, and future receipt data. `DexEffects` stores the exact owned
settlement value, and every nested fill, delta, included intent, event, and
metadata value is admitted before the effect exists.

This pattern closes the TOCTOU gap where a frozen outer effect retained a
mutable settlement graph or recomputed totals from a different representation.

### Rejected alternatives

- Freezing only `DexEffects`.
- Copying only the top-level settlement.
- Recomputing totals independently after effect construction.
- Retaining mutable event dictionaries or lists.
- Treating a hash computed before ownership as sufficient protection.

### Mechanical guarantee and non-guarantees

Post-construction mutation of every retained source alias cannot change effect
bytes, effect hash, totals, or the settlement presented to consumers. The
pattern does not prove external delivery, receipt commitment, outbox
idempotency, or database atomicity.

Evidence includes recursive retained-alias mutations, batch-reference mutation,
event/metadata mutation, total recomputation parity from the stored owned
settlement, canonical effect hash stability, and same-candidate integration
tests.

## Pattern FCIS-PAT-CHECKER-DERIVED-PROMOTION-V1

**Name:** Checker-derived evidence promotion

**Selection:** SELECTED for this packet and later release profiles
**Audit bindings:** process-level; no V6 defect receives fixed credit from this
pattern alone

### Applicability and rationale

Use a fail-closed checker to derive whether required pattern fields, audit
bindings, tests, source hashes, and review statuses are complete. Producer
self-claims and passing example tests cannot promote a repair.

The checker must reject an unknown audit ID, unknown pattern, uncovered
mandatory test, undeclared packet file, stale implementation head, or selected
pattern without rationale and explicit non-guarantees.

## Audit-row rendering rule

The next audit console should render a compact pattern summary beside each
affected case and finding:

| Field | Display |
|---|---|
| Pattern | ID, version, and selection status |
| Why | one-sentence applicability and rationale |
| Avoids | rejected alternatives relevant to the defect |
| Guarantees | exact mechanical property |
| Does not guarantee | residual nonclaims |
| Evidence | witness, exact source head, commands, and artifact hashes |
| Review | unreviewed, conditionally accepted, or independently accepted |

The downloadable JSON packet must include the complete pattern record or its
content hash. UI text is never the authority.

## Implementor handoff requirement

Every PR #477 and #478 handoff must report:

```text
Pattern IDs implemented:
Pattern deviations:
Why each deviation was necessary:
Rejected alternatives reintroduced: none | exact list
Mechanical guarantees evidenced:
Explicit non-guarantees retained:
Audit case and witness IDs exercised:
Exact implementation head:
Evidence artifact hashes:
Independent review status:
```

A pattern deviation is a design question. The implementation agent stops before
code expansion until the primary reviewer updates this packet.
