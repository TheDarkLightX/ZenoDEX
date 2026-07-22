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

Step(CommittedValue, TypedCommand, ExplicitContext)
  -> Reject
   | Accept(NewCommittedValue, CanonicalEffects, Receipt)
```

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
