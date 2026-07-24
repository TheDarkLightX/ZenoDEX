# FCIS Authority Snapshot V1 Errata 1

Status: **normative; read before every other packet file**

This errata resolves contradictions found after the first packet assembly. It
narrows implementation authority. Where an older clause conflicts with this
file, this file controls.

## E1. Validated admission limits

Raw limit configuration is not an input to `Admit`. A trusted constructor first
builds an exact frozen/slotted `ValidatedAdmissionLimitsV1` or returns a
separate startup/configuration rejection. `Admit` accepts only the exact
validated type.

```text
BuildAdmissionLimitsV1(raw trusted configuration)
  -> LimitProfileReject(INVALID_LIMIT_PROFILE)
   | ValidatedAdmissionLimitsV1

Admit(schema_revision, schema_id, validated_limits, source)
  -> AdmitReject(code, path)
   | AdmitOk(owned_value)
```

Therefore `INVALID_LIMIT_PROFILE` is not an `AdmitCode`, and admission error
precedence begins with wrong exact top-level source type. A malformed limit
profile blocks startup or profile activation before any authority value is
processed.

`max_nodes` is one graph-wide budget. Count each visited scalar, record,
sequence, map, map key, and map value exactly once per occurrence in the
traversal. Shared acyclic values are counted at each occurrence. The final
canonical byte limit is checked against the trusted canonical encoder after
ownership construction; field string/bytes and collection limits bound work
before that final encoding.

## E2. Complete closed schema algebra

The sequence and tagged-record cases are explicit schema values:

```text
SequenceSourceKind = EXACT_LIST | EXACT_TUPLE

SequenceOf(
  accepted_source_kinds: nonempty tuple[SequenceSourceKind, ...],
  inner,
  minimum_items,
  maximum_items,
)

TaggedRecordOf(
  record_tag,
  discriminant_field,
  discriminant_enum_tag,
  variants: ordered tuple[(exact enum member, declared fields), ...],
)
```

`SequenceOf` returns an owned tuple. It admits only the exact built-in source
kinds declared by that schema. This resolves the JSON-list, owned-tuple, and
list-or-tuple batch edges without broad `Sequence` admission.

`TaggedRecordOf` first checks the exact registered source record type, then
reads the declared discriminant with `object.__getattribute__`, admits it as the
exact registered enum, and selects one exhaustive variant field tuple. Missing,
duplicate, or extra variant registry entries are `REGISTRY_DRIFT`. An unknown
exact enum member is `UNSUPPORTED_VARIANT`. There is no default variant.

`ExactString` may carry an `EXACT_LITERAL` string rule. A separate arbitrary
literal callback is forbidden.

## E3. Canonical keys are never normalized at committed admission

Committed admission accepts only already-canonical keys. It never transforms a
key spelling. Consequently two distinct admitted keys cannot collide after a
normalization that does not exist. `DUPLICATE_CANONICAL_KEY` is removed from
`AdmitCode` for this profile.

Raw JSON duplicate member names are rejected by the strict byte parser before
a `dict` exists. Noncanonical in-memory key spellings reject with
`NONCANONICAL_SCALAR`; last-write-wins behavior is never used.

## E4. PR #478 scope is ownership-only

PR #478 owns mounted intent, envelope payload, settlement, fill, delta, event,
and effect graphs. It does not claim to implement the canonical raw-byte parser,
authentication or authorization policy, committed receipts, nonce commitment,
outbox construction, or atomic commit.

Phase wrappers preserve the same canonical command identity/hash and canonical
bytes. Python object identity across wrappers is not required.

Before PR #478 implementation, freeze an exact mounted envelope inventory that
includes quote-receipt payloads, transaction sender/auth mode, the chain/domain
signature frame, and settlement proof/Oracle/certificate/grid payloads. Any
omitted mounted field blocks implementation.

## E5. Evidence and claims

The snapshot PRs may claim defensive ownership and exact baseline parity only
for the tested profile at the exact head. They cannot claim complete parser
refinement, full transition refinement, atomic shell correctness, or release
readiness.

Every mandatory test ID must bind to at least one requirement. The packet
checker must reject unbound tests and undeclared files rather than report
success with incomplete coverage.

## E6. Production admission is bound to one source-owned profile

The generic interpreter may accept registry and resolver arguments only through
an underscore-prefixed internal function used by focused tests and one mounted
profile facade. It is not the authority API.

The production relation retains the four-argument form:

```text
Admit(schema_revision, schema_id, validated_limits, source)
  -> AdmitReject(code, path)
   | AdmitOk(owned_value)
```

The mounted `state_admission_profile.py` facade binds all of the following:

- one immutable declarative registry;
- one exhaustive record-construction and postcondition resolver;
- one exhaustive versioned canonical-encoder resolver;
- the profile, schema, and algorithm revision used by receipts and evidence.

Registration records contain exact tags, exact source/owned types, schemas, and
schema IDs. They contain no `Callable`, lambda, closure, bound method, predicate,
constructor, or serializer field. Authority input cannot provide or select a
registry or resolver. Synthetic registries and resolvers are test-only and the
AST checker rejects their use from mounted authority modules.

This profile binding is part of the trusted computing base. Its source SHA and
registry inventory must be present in exact-head evidence. Python cannot prove
that trusted resolver code is pure, so production promotion also requires the
resolver to be an exhaustive source-reviewed match plus deterministic replay.

## E7. Enum ownership and bounded map preflight

Python `Enum` members are singleton objects with mutable reachable state.
`ExactEnum` therefore validates the exact registered source member and returns
a fresh `OwnedEnumV1(schema_revision, enum_tag_ordinal, member_ordinal)`.
Committed records and map keys never retain the source member or its `.value`.
An exact matching `OwnedEnumV1` is revalidated and reconstructed.

For exact source dictionaries, item limits are checked with the exact built-in
length operation before an entries tuple or sorted work list is allocated.
After exact key-shape admission, every string/bytes key component, including
components nested in exact pairs, is preflighted against its field limit and
the remaining graph-wide byte budget. Oversized individual or aggregate keys
return `BYTE_LIMIT` at the map path before sort-value derivation. Deterministic
key-error selection may then sort only bounded schema-derived built-in values.
This ordering is required so two noncanonical keys produce the same typed
rejection under every insertion permutation without allowing rejected input
size to control comparison work.

## E8. Exact record unions and independent string bounds

Two minimized counterexamples reopen the primitive checkpoint before domain
mounting:

1. The perps market map contains four distinct exact source classes and four
   distinct committed counterparts. `MapOf` has one value schema, while
   `TaggedRecordOf` has one source/owned class pair. The closed algebra therefore
   adds `RecordUnionOf`, an ordered nonempty tuple of `RecordOf` variants.
   Dispatch uses only unique registered exact source types. It does not inspect
   a discriminant, backtrack, or invoke caller behavior.
2. The mounted state boundary limits general strings to 4,096 characters.
   `ExactString(max_utf8_bytes=4096)` would instead impose a 4,096-byte limit
   and reject valid multibyte strings. `ExactString` therefore carries an
   independent optional character bound and a required UTF-8 work bound.

Both changes preserve stable `BYTE_LIMIT` and `WRONG_EXACT_TYPE` rejection
codes. They expand only the trusted closed schema language needed to express
the already-mounted state domain. Domain snapshot functions remain unmounted
until the production profile and its drift checker are green.

## E9. Persistent committed transitions replace domain scratch conversion

The earlier three-representation rule is withdrawn. The normative authority
path is now:

```text
LegacySource
  -> closed exact admission
  -> CommittedValue

LeafStep(CommittedValue, TypedDelta, ExplicitContext)
  -> LeafReject(StableReason)
   | LeafOk(NewCommittedValue, CanonicalPatch)
```

`LeafStep` is the state-patch transition shape used by this state-migration
packet. It applies only where the leaf has no protocol-defined
committed-failure transition. It does not independently issue the aggregate
receipt or authorize external effects. The aggregate DEX command boundary
derives its receipt and commit plan from the complete evaluated candidate and
is governed by E10.

There is no public `to_scratch_*` conversion, structural read protocol at an
authority-core entry, mutable domain-builder parameter, or mutable
post-transition value that is re-admitted into committed state. Existing
mutating callers must be converted to explicitly named return-new transition
functions.

A pure function may allocate a private builtin `dict` or `list` for a profiled
leaf calculation. The buffer is not a domain representation. It must be created
inside the function from admitted immutable values, remain unreachable from all
outputs and callbacks, be discarded on rejection, and match a return-new pure
reference under differential tests. The static checker rejects public mutable
projection APIs and mutable legacy constructors inside admission resolvers.

This change preserves the later persistent-collection plan. The immediate
Python implementation may rebuild an owned map in `O(n)` while keeping
persistent return-new semantics. Structural sharing is a later representation
optimization gated by canonical-byte/root parity and benchmarks.

## E10. Aggregate outcome and commit-bundle semantics

The [Formal Methods Philosophy FCIS tutorial](https://thedarklightx.github.io/Formal_Methods_Philosophy/tutorials/functional-core-imperative-shell-values-as-boundaries/)
is the semantic baseline for the aggregate core/shell contract. The specialized
ZenoDEX pattern reports and this migration packet refine that contract for
their narrower surfaces.

The aggregate command result is a closed three-way value:

```text
Decision
  = Accept(NewCommittedState, CommitPlan, Receipt)
  | Reject(RejectReason, Receipt)
  | CommittedFailure(FailureReason, NewCommittedState, CommitPlan, Receipt)
```

Only `Reject` has the unchanged-state and no-authoritative-effects law.
`CommittedFailure` is required whenever an unsuccessful requested operation
intentionally consumes a nonce, charges a fee, advances a breaker, records a
failed attempt, or otherwise changes authoritative state. A leaf domain with
no such transition may continue to expose the two-way `DomainStep` from E9.

The imperative shell atomically publishes one root-bound commit bundle. The
bundle includes the expected pre-root, next root or canonical patch, receipt,
replay/nullifier or nonce updates, authoritative protocol effects, and outbox
records. A root mismatch publishes none of them. External delivery happens
after commitment from those outbox records under receipt-derived idempotency
keys.

Internal balance, pool, LP, and nonce patches in PR #477 are deterministic
leaf transition values. Their exact per-cell preconditions do not replace the
aggregate expected-pre-root check, receipt binding, or atomic commit bundle.
Likewise, canonical encoding and protocol ordering are separate contracts;
byte ordering may implement protocol ordering only when an explicit law and
cross-language vectors establish their equivalence.

## E11. State ownership, authority ownership, and final mounting are separate review stages

The earlier two-PR landing order is withdrawn because it creates a circular
promotion obligation. PR #477 cannot mount an aggregate result whose effects,
receipt, settlement, and command graphs remain mutable, while PR #478 cannot
be reviewed against the final state boundary until the exact state substrate
exists.

The normative sequence is therefore:

```text
state-substrate review unit
  exact state admission, reads, leaf transitions, production execution context,
  exact settlement replay, roots, snapshots, and differential evidence

authority-graph review unit
  owned command, settlement, event, effect, receipt, and three-way Decision values

atomic-mount review unit
  one switch of all eight DexState fields and every mounted authority consumer
```

The first two units may be stacked review branches. They are not independent
production merge candidates. The atomic-mount unit is the first branch allowed
to claim that the repaired authority path is mounted. It must contain or depend
on the exact reviewed heads of both earlier units.

Until the atomic-mount evidence passes:

- the legacy implementation remains only as a pinned differential oracle;
- exact state candidates remain non-authorizing evidence values;
- the structural checker must report legacy mounted mechanisms when run in its
  final-mount profile;
- no `FCIS-477-*` or `FCIS-478-*` requirement is promoted merely because a leaf
  or shadow suite passes.

Deletion of `Frozen*`, `deep_freeze`, copy-based settlement application, seal
flags, and compatibility projections happens in the atomic-mount unit after
old/new parity is recorded. This preserves the comparison oracle without
allowing it to survive the promoted authority boundary.

## E12. Closed authority-graph algebra extensions

The state-substrate review established that four PR #478 field shapes cannot be
expressed by the original closed schema sum. They are added here before any
owned intent or settlement module is implemented. Domain adapters must not
replace these additions with hand-written validation.

### Bounded recursive JSON

The schema sum adds one exact `BoundedJsonValue` variant. It is interpreted by
the same admission engine and represents only:

```text
None
exact bool
exact int with magnitude bit length at most 256
exact canonical string with at most 4,096 characters and 16,384 UTF-8 bytes
exact list at decoded ingress or exact tuple at owned/builder revalidation
exact dict at decoded ingress or exact matching OwnedMapV1 at revalidation
```

Arrays become exact tuples. Objects become exact `OwnedMapV1` values whose
exact-string keys are ordered lexicographically after bounded key preflight.
Each container has the schema's item bound and also consumes the shared depth,
node, and byte budgets. Cycles reject. Unsupported objects reject before
iteration, hashing, formatting, or caller behavior.

The exact tuple input is compatibility for already-owned values and exact
in-memory builders. Strict raw-byte ingress still produces lists and dicts and
must separately reject duplicate keys, floats, negative-zero spelling, partial
consumption, and noncanonical re-encoding. `BoundedJsonValue` does not replace
that parser contract.

The 256-bit policy follows the existing bounded canonical JSON artifact
profile: `abs(value).bit_length() <= 256`. A narrower domain field declares a
narrower non-JSON schema.

### Optional exact keyed-map members

`ExactKeyedMap` adds:

```text
required_field_names: None | exact tuple[exact declared field name, ...]
```

`None` preserves the prior rule that every declared field is required. An
explicit tuple must be unique, be a subset of declared names, and follow
declared-field order. The accepted cardinality is between the number of
required fields and the number of declared fields. Unknown members reject in
canonical string order. Missing required members reject in required-field
order. Present values are admitted in declared-field order; absent optional
members are omitted. An explicit `None` is distinct from absence and succeeds
only when the field schema is `OptionalValue`.

### Canonical prefixed hexadecimal strings

`StringRuleV1` adds `LOWERCASE_0X_HEX`. It requires exact prefix `0x`, at least
one hexadecimal digit, and only lowercase `0-9a-f` digits after the prefix.
Fixed-width hashes and keys also declare their exact total UTF-8 byte length.

### Enum ownership controls

E7 remains controlling. `ExactEnum` accepts an exact registered source enum
member and returns a fresh `OwnedEnumV1`; it never stores or reconstructs the
source singleton. PR #478 phrases such as `exact IntentKind` and
`exact FillAction` mean:

```text
exact registered source member
  -> ExactEnum admission
  -> exact owned tag/member ordinals in the committed graph
```

Core code compares or renders those ordinals through source-owned exhaustive
helpers. It must not use `__getattribute__` masquerading, an enum-preserving
schema variant, or a property that reconstructs and retains a mutable enum
member.

These additions remain inside the one profile binding from E6. No authority
module may call `_admit_with_registry_v1` directly or build a second production
registry.

## E13. Tagged discriminants follow declared record order

`TaggedRecordOf.discriminant_field` names one declared field whose schema is
the matching `ExactEnum`. The discriminant may appear at any position in the
record's exact dataclass field order. Every variant must still declare every
record field exactly once and in that exact order.

This correction preserves the mounted `Intent` layout:

```text
module, version, kind, intent_id, sender_pubkey, deadline, salt, fields
```

The interpreter reads only the named discriminant to select the exhaustive
variant. It then admits all fields in declared dataclass order. Reordering the
source record to place `kind` first would be an unnecessary compatibility
change, while requiring the discriminant to be first would make the declared
closed schema unable to represent the mounted type.

## E14. Settlement event omission has one owned normal form

The mounted settlement encoder omits `events` when the source field is `None`
or an empty list. Authority admission must not retain both source spellings as
distinct owned values with identical canonical bytes.

The owned settlement normal form is:

```text
events = None
       | tuple[OwnedJsonObjectV1, ...] with 1..200,000 entries
```

An empty source list rejects at authority admission. Callers that mean absence
provide `None`. A present sequence is admitted through the closed bounded
owned-JSON schema and contains at least one event.

## E15. One record tag may declare an exact source-type union

Some mounted records have multiple exact source dataclass classes with the
same protocol fields and one owned normal form. Intent admission is the current
case: exact `Intent`, `SwapIntent`, `RouteIntent`, `CreatePoolIntent`, and
`ValidatedIntent` all have the same declared field order and produce exact
`OwnedIntentV1`.

`RecordRegistrationV1` therefore adds one declarative exact tuple:

```text
additional_source_types: tuple[type[object], ...] = ()
```

The primary and additional source classes must be exact dataclasses, unique
across the complete registry, distinct from every owned class, and have field
names identical to the primary source in identical order. Registry construction
rejects source-field drift. `RecordOf` and `TaggedRecordOf` dispatch only by
exact `type(source)` membership in this closed tuple or by the exact owned type.

The original source enters the interpreter. A wrapper, projection record,
manual type dispatch, or pre-projected batch is forbidden because it can erase
undeclared fields and change first-rejection precedence.
