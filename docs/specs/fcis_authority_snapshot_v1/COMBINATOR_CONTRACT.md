# Closed Deterministic Combinator Contract

This file defines the implementation shape. It is deliberately more concrete
than an architectural essay. The implementation agent must preserve the type
language, error precedence, and construction phases below.

## 1. Total admission relation

The normative interface is data in, data out:

```text
Admit(schema_revision, schema_id, limits, source)
  -> AdmitReject(code, path)
   | AdmitOk(owned_value)
```

`AdmitReject` contains no partial output. The adapter used by a dataclass
constructor may translate it into one `StateAdmissionError`, but the pure
combinator itself returns a discriminated result.

Minimum Python shape:

```python
PathPart = str | int
FieldPath = tuple[PathPart, ...]

class AdmitCode(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    NONCANONICAL_SCALAR = "noncanonical_scalar"
    OUT_OF_RANGE = "out_of_range"
    WRONG_CONTAINER = "wrong_container"
    WRONG_KEY_TYPE = "wrong_key_type"
    UNKNOWN_FIELD = "unknown_field"
    MISSING_FIELD = "missing_field"
    UNSUPPORTED_VARIANT = "unsupported_variant"
    REGISTRY_DRIFT = "registry_drift"
    CYCLE = "cycle"
    DEPTH_LIMIT = "depth_limit"
    ITEM_LIMIT = "item_limit"
    BYTE_LIMIT = "byte_limit"
    DOMAIN_INVARIANT = "domain_invariant"

@dataclass(frozen=True, slots=True)
class AdmitReject:
    code: AdmitCode
    path: FieldPath

@dataclass(frozen=True, slots=True)
class AdmitOk(Generic[T]):
    value: T
```

Do not include the rejected object, its `repr`, its dynamic class name, or an
unordered key in the stable result. A separate non-consensus diagnostic may
include a trusted schema name and source location.

## 2. Schema values

The accepted schema language is a closed tagged sum interpreted by one pure
function. Do not implement an open class hierarchy whose subclasses can add
new admission behavior.

```text
Schema =
    ExactInt(minimum, maximum_or_none)
  | ExactBool
  | ExactString(string_rule, max_utf8_bytes, exact_literal_or_none,
                exact_utf8_bytes_or_none, max_characters_or_none)
  | ExactBytes(exact_length_or_none, max_length)
  | ExactEnum(enum_tag)
  | Optional(inner)
  | SequenceOf(accepted_source_kinds, inner, minimum_items, maximum_items)
  | ExactPair(left, right)
  | MapOf(key_schema, value_schema, maximum_items, map_schema_id)
  | ExactKeyedMap(declared_fields, map_schema_id)
  | RecordOf(record_tag, declared_fields)
  | RecordUnionOf(ordered_nonempty_record_variants)
  | TaggedRecordOf(record_tag, discriminant_field, discriminant_enum_tag,
                   variants)
```

Implementation requirements:

- each schema variant is an exact frozen/slotted value;
- `admit` dispatches with `type(schema) is Variant`, never broad
  `isinstance`;
- `enum_tag` and `record_tag` are closed enums interpreted by exhaustive
  `match` statements;
- schema data never carries an arbitrary constructor, callback, predicate,
  serializer, or user-provided callable;
- declarative registry records also carry no callable behavior;
- every record field is declared in one ordered tuple;
- every heterogeneous closed map uses `ExactKeyedMap`; its exact string keys,
  per-key schemas, and traversal order are declared in one ordered tuple;
- every registry has an import-time or test-time exact field-set drift check;
- `typing.Any` is forbidden in the combinator and committed-value modules.

### 2.1 Profile binding

The schema interpreter is reusable implementation machinery. Its registry-aware
entry is private. Exactly one mounted profile facade binds a declarative registry
to exhaustive trusted resolvers and exposes the normative four-argument
`Admit` relation.

```text
authority caller
  -> Admit(revision, schema_id, validated_limits, source)
  -> module-owned profile
  -> internal schema interpreter
```

The public caller never passes registry data, a constructor, an invariant
function, or an encoder. Record tags select construction and postconditions by
an exhaustive module-owned match. Schema IDs select a versioned encoder by an
exhaustive module-owned match. Test-only synthetic resolvers are never mounted.

The path-scoped checker permits the internal interpreter call only from
`src/state/state_admission_profile.py`. A production profile change requires a
registry-drift test, exact source hash, and replay evidence.

## 3. Scalar semantics

### ExactInt

1. Check `type(value) is int`.
2. Check the lower bound.
3. Check the upper bound when declared.
4. Return the same built-in integer.

No `int(value)`, arithmetic, comparison, formatting, or hashing occurs before
the exact-type check.

### ExactBool

Check `type(value) is bool`. Do not accept integers `0` or `1`.

### ExactString

1. Check `type(value) is str`.
2. When declared, enforce the semantic character limit using exact built-in
   `len` before UTF-8 traversal.
3. Enforce the declared UTF-8 byte work limit.
4. Enforce one declared rule such as fixed-width lowercase hex, canonical
   identifier, non-empty text, or exact literal.
5. Reject noncanonical spelling. Do not normalize at committed admission.

Character and UTF-8 bounds are separate policy values. The mounted generic
string limit remains 4,096 Unicode code points, while its conservative UTF-8
work bound is 16,384 bytes. Narrow ASCII and fixed-width fields declare tighter
bounds. A violation of either resource dimension returns `BYTE_LIMIT`; no
caller-controlled text enters the rejection.

Builder normalization is a separate decode-stage operation. An authority value
arriving at this boundary must already be canonical.

### ExactBytes

Check `type(value) is bytes`, then length. `bytearray`, `memoryview`, and bytes
subclasses reject.

### ExactEnum

Resolve the declared `enum_tag` to one trusted enum class and check
`type(value) is DeclaredEnum`. An exact matching `OwnedEnumV1` may be supplied
only for full revalidation. Do not accept strings, integers, `IntEnum` aliases,
or enum subclasses.

Successful admission returns a fresh composition-owned value:

```text
OwnedEnumV1(schema_revision, enum_tag_ordinal, member_ordinal)
```

It never returns or retains the Python `Enum` singleton. Python enum members
can contain mutable values and expose mutable instance storage, so retaining
the member would violate transitive ownership even when the enum class itself
is exact and closed. Tagged owned records and owned map keys store
`OwnedEnumV1` values. A non-authoritative presentation adapter may resolve an
owned ordinal through the same source-pinned registry; the functional core does
not reconstruct the mutable enum member.

## 4. Container semantics

### Source containers

Only exact built-in containers declared by the field schema are source values:

```text
tuple field -> exact tuple
map field   -> exact dict
JSON array  -> exact list at byte-decoder output, exact tuple once owned
```

An exact final `OwnedMap` may be reused only when its schema revision and schema
ID match. An owned record is accepted only through a separately registered
exact committed-source schema that fully revalidates every field. An untagged
owned record is never inferred from its class alone. Generic `Mapping`,
`Sequence`, `Iterable`, set, frozenset, iterator, generator, proxy, and subclass
inputs reject.

### Owned sequence

The owned output is a built-in tuple containing only owned child values. There
is no `FrozenList` compatibility class.

### Owned map

Use one composition-based final class:

```text
OwnedMapV1 {
  schema_id: exact string or closed enum
  entries: canonical tuple[(OwnedKey, OwnedValue), ...]
  private_index: read-only view over a fresh private builtin dict
}
```

Requirements:

- it does not inherit from `dict` or a mutable domain table;
- its constructor rejects a second initialization before changing any field;
- the backing dictionary is created fresh after keys and values are admitted;
- the backing dictionary never escapes;
- iteration follows `entries`, which is in the schema's canonical key order;
- lookup uses the private index;
- getters return only immutable child values;
- it has no mutator, update, setter, or in-place operator;
- no cache, seal, schema ID, or index enters canonical protocol fields;
- an exact `OwnedMapV1` subclass is never accepted;
- equality against arbitrary mappings is not part of authority admission.

### Deterministic map algorithm

For an exact source dict:

1. Check container item limit.
2. Scan keys only with the key schema's non-behavioral shape check.
3. If any key has the wrong exact type, return `WRONG_KEY_TYPE` at the map path.
   Do not include the offending key in the stable error.
4. Recursively preflight every string/bytes key component against its declared
   bound and the remaining graph-wide byte budget. Reject before sorting.
5. Preflight exact-integer ranges and owned-enum registry metadata recursively,
   replacing invalid or out-of-range raw magnitudes with bounded tagged sort
   sentinels. Raw attacker-sized integers never participate in comparison.
6. Derive the schema's non-behavioral bounded sort value for each key.
7. Sort those values, then verify key canonicality in that order.
8. Copy enum keys to `OwnedEnumV1` and recursively own pair keys.
9. Admit values in sorted-key order.
10. Construct `entries`, then the fresh private index.

Committed admission never normalizes keys. A noncanonical spelling rejects, so
there is no post-normalization collision class at this boundary. Raw JSON
duplicate names are rejected by the byte parser before a dictionary exists.

This avoids error precedence depending on insertion order. The preliminary
sort operates only on resource-bounded exact built-in scalars, registry
ordinals, and exact pairs of those values; it never sorts or formats arbitrary
objects. An `ExactInt` used anywhere inside a map-key schema must have finite
bounds no wider than 256 bits; registry construction rejects a wider or
unbounded key domain.

### Exact keyed-map algorithm

`ExactKeyedMap` is the closed heterogeneous-map form used for perps and
clearinghouse state dictionaries:

1. Require an exact builtin dictionary or matching exact `OwnedMapV1`.
2. Enforce the declared cardinality before field inspection.
3. Require every source key to have exact `str` type and preflight aggregate
   UTF-8 work before sorting.
4. Select unknown keys in canonical string order, then missing keys in declared
   order.
5. Admit every value with its declared per-key schema in declared order.
6. Construct an `OwnedMapV1` whose entries follow declared order.
7. On committed revalidation, reject noncanonical entry order or index drift
   instead of silently repairing it.

No domain adapter may duplicate this key-set or per-key admission loop.

## 5. Record semantics

For `RecordOf(record_tag, fields)`:

1. Resolve `record_tag` to one exact trusted source type and one exact owned
   output type.
2. Check `type(source) is ExactSourceType` before reading a field.
3. Compare the source dataclass field set with the declared field registry.
   Any drift returns `REGISTRY_DRIFT` in tests and blocks import/release.
4. Enter cycle tracking for the source record.
5. Read each declared field in declaration order with
   `object.__getattribute__`.
6. Admit the field with its declared schema and appended field path.
7. Construct the exact owned output through its named trusted constructor.
8. Run the named postcondition/invariant checker.
9. Leave cycle tracking.

No generic dataclass reflection decides whether a type is accepted. Dataclass
field inspection is used only by drift tests against a predeclared exact type.
No `object.__new__` bypass constructs a domain record.

For `RecordUnionOf(variants)`:

1. Require a nonempty exact tuple of exact `RecordOf` schema values.
2. Require unique record tags and unique registered source/owned classes.
3. Select a variant only when `type(source) is RegisteredSourceType`.
4. Delegate to that variant's `RecordOf` admission and construction.
5. Reject an unknown exact type, subclass, or lookalike as
   `WRONG_EXACT_TYPE` before reading any source field.

`RecordUnionOf` represents a heterogeneous container whose variants are
different exact record classes, such as the mounted perps market map.
`TaggedRecordOf` remains the schema for one exact record class whose declared
enum field selects an exhaustive field variant. Neither combinator backtracks,
consults caller behavior, or uses a default variant.

## 6. Budget and cycle semantics

The interpreter threads an immutable evaluation state through every recursive
result:

```text
AdmissionLimitsV1 {
  max_depth
  max_nodes
  max_canonical_bytes
  field-specific cardinality limits
}

AdmissionState {
  limits
  nodes_used
  canonical_bytes_used
  active_container_ids: tuple
}

AdmitProgress[T] {
  value: T
  next_state: AdmissionState
}
```

Rules:

- root depth is zero;
- reject before descending when `depth + 1 > max_depth`;
- count one node for each scalar, record, sequence, map, map key, and map value;
- reject before consuming a node beyond `max_nodes`;
- track only objects on the active recursion path so shared acyclic values are
  allowed and cycles reject;
- update byte usage from trusted exact strings/bytes and final canonical
  encoding; never ask an arbitrary object to serialize itself;
- check a field-specific container limit before iterating its children;
- limit failures return the first result under the fixed traversal order.
- no mutable counter object, mutable cycle set, or context builder is shared
  across recursive calls.

The implementation may use an iterative stack to avoid Python recursion. If it
uses recursion, the declared maximum depth must remain well below the
interpreter recursion limit and must reject before deeper calls.

## 7. Construction phases

Every domain admission function follows this exact order:

```text
exact top-level type
-> structural/container bounds
-> exact scalar and child-record admission
-> construct exact immutable committed candidate
-> pure semantic invariant check over that candidate
-> committed composition value
-> canonical projection and byte/root parity check in tests
```

The semantic check must not reconstruct a mutable legacy domain object. If an
existing invariant is coupled to a mutable class, extract a pure predicate over
the admitted fields and prove parity against the mounted behavior before using
it as authority. Admission never normalizes an admitted child or copies a value
back out of a mutable constructor.

## 8. Pure persistent transition

Authority-bearing transitions consume only exact committed values and return a
new exact committed value:

```text
Step(CommittedState, TypedCommand, ExplicitContext)
  -> StepReject(code, path)
   | StepOk(NewCommittedState, CanonicalEffects, Receipt)
```

Public `to_scratch_*` functions, mutable domain-builder parameters, and
structural read protocols at core entry points are forbidden. Domain updates
use explicitly named return-new functions such as `with_balance_delta` or
`apply_pool_patch`; an ignored return cannot resemble successful mutation.

An implementation may allocate a fresh private builtin `dict` or `list` inside
one pure function when profiling requires it. The buffer may contain only
admitted immutable values, cannot escape through a return, exception, closure,
global, cache, or callback, and must be discarded on rejection. A static check
and a differential property against the return-new reference are required.

## 9. Error precedence

For the same schema and semantic input, rejection selection is:

```text
1. wrong exact top-level source type
2. top-level byte/cardinality limit
3. wrong key/container shape
4. noncanonical key
5. declared record fields in declaration order
6. sequence elements in index order
7. map values in canonical key order
8. trusted constructor/domain invariant
9. final canonical byte limit
```

Limit-profile construction is a separate startup relation. `Admit` receives
only an exact `ValidatedAdmissionLimitsV1`; malformed raw limit configuration
cannot participate in admission-error precedence.

Tests must permute map insertion order and verify identical `(code, path)`.

## 10. Forbidden source patterns

The conformance checker must reject these patterns inside authority modules:

```text
from copy import copy or deepcopy
import copy followed by copy.copy/deepcopy
pickle, __reduce__, __reduce_ex__, copyreg
typing.Any
is_dataclass used for admission
isinstance(value, Mapping|Sequence|Iterable|int|str|bytes|Enum|record type)
dict(source), list(source), tuple(source) before exact source admission
set or frozenset in an authority schema
object.__new__ for a domain record
an else/fallback branch that preserves, copies, coerces, stringifies, or
  serializes an unsupported value
committed class inheriting from a mutable builder or container
public to_scratch_* conversion from a committed authority value
authority-core parameter typed as a structural read protocol or legacy builder
legacy mutable domain construction inside the admission resolver
```

`isinstance` remains acceptable in unrelated compatibility or rendering code.
The checker is path-scoped and must not rewrite unrelated inherited debt.

## 11. Mechanical guarantees and non-guarantees

This contract mechanically targets:

- closed accepted in-memory language;
- exact-type and bool/int separation;
- caller-alias detachment;
- stable traversal and rejection;
- cycle and resource rejection;
- immutable committed API under trusted CPython/repository code;
- pure return-new authority transitions;
- no public mutable post-admission representation;
- registry drift failure.

It does not prove:

- economic requirement completeness;
- canonical byte injectivity without the separate encoder tests;
- storage atomicity or crash recovery;
- cross-language refinement;
- protection from arbitrary trusted in-process memory mutation;
- appropriate economic upper bounds where no source-pinned bound exists.
