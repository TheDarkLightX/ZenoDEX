# Audit Findings at the Pinned Heads

Scope: PR #477 at `fc2f9150c1eacfdb7f6e4272f2a8efbd5fdafe85`
and PR #478 at `6dbb9b36237d982515777caae04a296d0ebac040`.

This is a design and source audit of the two snapshot PRs. It is not an
exhaustive audit of every ZenoDEX transition. `CONFIRMED` means the source
contains the described mechanism or admits the direct construction. Closure
still requires the named executable witness at the repaired exact head.

## Executive result

The scalar-subclass report was one member of a larger family. The two PRs
misimplemented five governing decisions:

1. an open generic copier replaced a closed schema;
2. mutable and committed values remained in shared inheritance hierarchies;
3. input ownership, semantic validation, and canonical projection were mixed;
4. resource and cycle bounds were absent from the recursive paths;
5. tests demonstrated selected aliases and did not characterize the full
   accepted language.

PR #477 and PR #478 are therefore **not ready to merge** at the pinned heads.

## PR #477 findings

### FCIS-477-001: Open `Any -> Any` authority helper

- Severity: P0 design blocker
- Status: CONFIRMED
- Source: `src/state/immutable_collections.py::deep_freeze`
- Defect: unsupported values fall through to `deepcopy(value)`. The protocol
  schema is whatever Python's copy machinery happens to accept.
- Required closure: remove `deep_freeze` from every authoritative path. Replace
  it with the finite combinators in `COMBINATOR_CONTRACT.md`.

### FCIS-477-002: Caller-controlled copy protocol executes during admission

- Severity: P0
- Status: CONFIRMED
- Source: `deepcopy` in `deep_freeze` and dataclass cloning
- Counterexample: a scalar or record subclass returns `self` from
  `__deepcopy__`, retains mutable fields, or mutates global state while being
  copied.
- Required closure: no `copy`, `deepcopy`, pickle, reduction, conversion, or
  serialization hook may be invoked to decide admission.

### FCIS-477-003: Broad container admission executes attacker iteration

- Severity: P0
- Status: CONFIRMED
- Source: `isinstance(value, Mapping)`, `isinstance(value, list)`, generic
  `Iterable` constructors
- Counterexample: a mapping or iterable subclass changes yielded entries
  between validation and copying or has side effects during iteration.
- Required closure: exact built-in container or exact owned-container checks at
  each declared field. No generic `Mapping`, `Sequence`, or `Iterable` source.

### FCIS-477-004: Arbitrary dataclasses and enums become authoritative

- Severity: P0
- Status: CONFIRMED
- Source: reflective `is_dataclass` handling; the attempted local correction
  also admitted arbitrary `Enum`
- Counterexample: an unregistered record or enum is inserted into optional
  module state and survives admission without a schema or canonical encoding.
- Required closure: exact record and exact enum registries. A new variant must
  fail registry-drift tests until every binding is declared.

### FCIS-477-005: Constructor and invariant bypass

- Severity: P0
- Status: CONFIRMED in the attempted generic correction; the pinned head uses
  `deepcopy` and then reflective field replacement
- Defect: reconstructing arbitrary records without a trusted exact constructor
  can preserve malformed states or omit `__post_init__` invariants.
- Required closure: explicit field prevalidation followed by a named trusted
  constructor for the declared record, then postconstruction invariant checks.
  `object.__new__` is forbidden for domain records.

### FCIS-477-006: Behavior-bearing scalar subclasses are admitted

- Severity: P0
- Status: CONFIRMED by GitHub review and minimized local witness
- Source: scalar fallthrough through `deepcopy`; many source constructors use
  `isinstance(int)` before the snapshot boundary
- Counterexample: an `int` subclass retains mutable multiplier state and
  overrides arithmetic while comparing equal to the admitted value.
- Required closure: `type(value) is int` or `type(value) is bool` at every
  declared scalar field before comparison, arithmetic, conversion, hashing, or
  constructor invocation.

### FCIS-477-007: Cycles and recursion depth are unhandled

- Severity: P0 availability and totality blocker
- Status: CONFIRMED
- Source: recursive `deep_freeze` without active-object tracking or depth limit
- Counterexample: `x = []; x.append(x)` produces interpreter recursion failure
  instead of a stable typed reject.
- Required closure: active-path cycle detection, depth budget, total-node
  canonical-byte budgets, and deterministic `CYCLE`, `DEPTH_LIMIT`,
  `ITEM_LIMIT`, or `BYTE_LIMIT` rejects.

### FCIS-477-008: Sets introduce unspecified protocol order

- Severity: P1
- Status: CONFIRMED
- Source: set and frozenset converted to frozenset
- Defect: no duplicate, ordering, or canonical encoding policy is declared.
- Required closure: sets are unsupported in these schemas. Any future set type
  needs an explicit canonical total order and duplicate policy.

### FCIS-477-009: Owned collection values can be reinitialized

- Severity: P0
- Status: SOURCE-CONFIRMED; permanent witness required
- Source: `FrozenDict.__init__` and `FrozenList.__init__` use
  `object.__setattr__` without rejecting a second initialization
- Counterexample shape:

  ```python
  FrozenDict.__init__(committed_map, {"replacement": 1})
  FrozenList.__init__(committed_list, ["replacement"])
  ```

- Required closure: exact owned collection types must be one-time initialized.
  Reinitialization must reject before changing any field.

### FCIS-477-010: Committed tables still inherit mutable tables

- Severity: P0
- Status: SOURCE-CONFIRMED; permanent witness required
- Source: `FrozenBalanceTable(BalanceTable)`, `FrozenLPTable(LPTable)`,
  `FrozenNonceTable(NonceTable)`, `FrozenPoolState(PoolState)`
- Counterexample shape: mutable base initialization or unbound base methods can
  reset seal state or reach mutable implementation details. In particular,
  `BalanceTable.__init__` and `LPTable.__init__` explicitly set the seal false.
- Required closure: distinct composition-based committed types plus pure
  return-new transition functions that accept only those exact committed types.

### FCIS-477-011: Previously frozen values are trusted without full validation

- Severity: P1
- Status: CONFIRMED
- Source: exact `FrozenDict`, `FrozenList`, and frozen table values are returned
  unchanged
- Defect: an object created by an older open helper, a partially initialized
  instance, or a reinitialized instance bypasses field-level validation.
- Required closure: exact owned types must have a closed constructor and
  one-time seal. Reuse is allowed only for that final type and still runs cheap
  invariant/provenance validation where corruption is representable.

### FCIS-477-012: Table snapshots run semantic methods before exact validation

- Severity: P0
- Status: CONFIRMED
- Source: table getters and mutable `set` methods are used to copy entries
- Defect: source internals can contain scalar subclasses because the mutable
  builders do not uniformly enforce exact types. Comparisons such as
  `amount < 0` execute before the snapshot rejects the scalar.
- Required closure: require exact source class and exact builtin internal
  dictionaries; read entries with trusted direct access; validate every key and
  scalar first; only then construct owned storage.

### FCIS-477-013: Pool copying executes validation on untrusted field values

- Severity: P0
- Status: CONFIRMED
- Source: `copy_pool_state(source)` precedes field-specific exact-type checks
- Defect: overloaded comparison, conversion, enum, or string behavior can run
  inside the mutable pool constructor.
- Required closure: extract exact fields from the exact `PoolState`, validate
  them with the pool schema, then call the trusted committed constructor.

### FCIS-477-014: Optional module admission is open-ended

- Severity: P0
- Status: CONFIRMED
- Source: `freeze_optional_module_state` sends every non-`None`, non-perps
  object through generic deep freeze
- Required closure: four explicit entry points only:
  `snapshot_vault`, `snapshot_oracle`, `snapshot_fee_accumulator`, and
  `snapshot_perps`. Unknown module values reject at the `DexState` field path.

### FCIS-477-015: Perps validation is incomplete and partly broad

- Severity: P0
- Status: CONFIRMED
- Source: `_validate_exact_perps_types`
- Defects:
  - `source.markets` is admitted through broad `Mapping`;
  - only selected nested record types are checked;
  - scalar fields and all global-state key/value rules are not checked before
    recursive copying;
  - trusted constructors normalize mutable dictionaries, so source, normalized,
    and committed meanings are not explicit stages.
- Required closure: exhaustive perps variant registry, exact builtin map source,
  exact scalar prevalidation, exact immutable candidate construction, pure
  postcondition check, and immediate sealing.

### FCIS-477-016: Error selection is not a stable protocol

- Severity: P1
- Status: CONFIRMED
- Source: heterogeneous `TypeError`, `ValueError`, `AssertionError`, recursion
  failure, and Python copy errors
- Required closure: stable admission code plus canonical field path and declared
  precedence. Do not include attacker `repr` or class name in consensus-facing
  diagnostics.

### FCIS-477-017: Resource policy is split across decoder and constructor

- Severity: P1, production blocker
- Status: CONFIRMED
- Source: `state_from_snapshot` is bounded; direct `DexState` construction and
  recursive freeze are not
- Required closure: reuse the mounted state limits in `FCIS-D009` at committed
  admission. Fields without a source-pinned numeric maximum remain named
  boundedness gaps rather than guessed policy.

### FCIS-477-018: Tests cover examples instead of the accepted language

- Severity: P0 evidence gap
- Status: CONFIRMED
- Missing families: scalar/enum/record subclasses, hostile copy and access
  hooks, reinitialization, arbitrary record variants, cycles, every limit plus
  one, registry drift, deterministic error ordering, and canonical/root parity.
- Required closure: complete `TEST_MATRIX.md` and retain every witness.

## PR #478 findings

### FCIS-478-001: The dependent PR inherits every shared-helper defect

- Severity: P0
- Status: CONFIRMED
- Source: #478 is based on an earlier #477 head and imports `deep_freeze`
- Required closure: rebase only after #477 is reviewed. No local fork of the
  shared combinator implementation.

### FCIS-478-002: `deep_thaw_json` is another open `Any -> Any` copier

- Severity: P0
- Status: CONFIRMED
- Source: `src/state/immutable_collections.py::deep_thaw_json`
- Defect: broad mappings/sequences and `deepcopy` are accepted while the
  canonical encoder is expected to validate later.
- Required closure: a projection function accepts only exact certified
  `OwnedJsonValue`; it contains no copy fallback and cannot accept source data.

### FCIS-478-003: Intent admission uses broad subtype and mapping checks

- Severity: P0
- Status: CONFIRMED
- Source: `freeze_intent` and `FrozenIntent.__post_init__`
- Defect: `isinstance(intent, Intent)` and generic `Mapping` admit
  behavior-bearing subclasses and arbitrary field containers.
- Required closure: explicit exact source-intent registry and one distinct
  `OwnedIntent` output record.

### FCIS-478-004: Authenticated intent remains a mutable-base subtype

- Severity: P0 design blocker
- Status: CONFIRMED
- Source: `FrozenIntent(Intent)`
- Required closure: composition-based `OwnedIntent`; parser builders and signed
  authority values are different types. No inherited `set_field` API exists.

### FCIS-478-005: Intent snapshot invokes caller copy behavior

- Severity: P0
- Status: CONFIRMED
- Source: `deepcopy(fields)` and generic deep freeze
- Required closure: kind-indexed exact field schemas and the bounded JSON
  combinator only where a field is intentionally a JSON carrier.

### FCIS-478-006: The admitted batch remains mutable

- Severity: P1
- Status: CONFIRMED
- Source: `freeze_intent_batch` returns `list[Intent]`
- Required closure: return `tuple[OwnedIntent, ...]` with a 256-item bound and
  pass the same tuple to nonce validation, settlement, effects, and receipts.

### FCIS-478-007: Intent field knowledge is duplicated

- Severity: P1 drift blocker
- Status: CONFIRMED
- Source: parser registries in `src/integration/operations.py` are separate from
  snapshot logic
- Required closure: move the kind/field schema to one leaf registry used by the
  parser, ownership boundary, canonical encoder, tests, and schema-drift gate.

### FCIS-478-008: Settlement snapshots inherit mutable settlement records

- Severity: P0 design blocker
- Status: CONFIRMED
- Source: `FrozenFill(Fill)`, frozen delta subclasses, and
  `FrozenSettlement(Settlement)`
- Required closure: distinct owned records and validators/application functions
  that consume the exact owned records and return immutable patches or a new
  committed candidate.

### FCIS-478-009: Seal metadata leaks into the dataclass schema

- Severity: P0 commitment/schema blocker
- Status: CONFIRMED at #478 head
- Source: `_snapshot_sealed` is declared with `dataclasses.field` on every
  frozen settlement record
- Impact: `fields()` and `asdict()` observe an implementation field that is not
  part of the protocol schema.
- Required closure: no seal or cache metadata may be a dataclass field or enter
  canonical bytes, hashes, proof input, receipt, or schema inventory.

### FCIS-478-010: Settlement copying runs caller hooks before validation

- Severity: P0
- Status: CONFIRMED
- Source: `deepcopy` on identifiers, reasons, events, and settlement fields
- Required closure: exact record and scalar validation before construction;
  no copy protocol.

### FCIS-478-011: Settlement events have no closed variant registry

- Severity: P0
- Status: CONFIRMED
- Source: `events: Optional[List[Dict[str, Any]]]` plus generic deep freeze
- Required closure: inventory mounted event shapes and define an exhaustive
  tagged event sum. If compatibility temporarily requires JSON events, admit
  only bounded canonical `OwnedJsonObject` and keep `EVENT-TYPING` blocked.

### FCIS-478-012: Fill and delta scalar fields lack exact schema admission

- Severity: P0
- Status: CONFIRMED
- Source: snapshot constructors copy fields directly; only later validators
  cover selected semantics
- Required closure: exact strings/enums/optional integers, explicit bounds,
  and record invariants before creating an owned fill or delta.

### FCIS-478-013: Existing frozen values are returned without revalidation

- Severity: P1
- Status: CONFIRMED
- Source: `freeze_settlement` and `freeze_intent` reuse exact frozen types
- Required closure: final owned types have closed one-time constructors and
  invariant checks. No value produced by the old helper is grandfathered.

### FCIS-478-014: Effect-plan validation begins with broad settlement type

- Severity: P0
- Status: CONFIRMED
- Source: `DexEffects.__post_init__` uses `isinstance(self.settlement, Settlement)`
- Required closure: accept exact `OwnedSettlement` throughout the authority
  core. Legacy mutable settlement admission ends at the outer conversion edge.
  Do not use subtype or structural-protocol admission.

### FCIS-478-015: Canonical JSON bounds are not bound to snapshots

- Severity: P1
- Status: CONFIRMED
- Source: freeze/thaw paths have no depth, item, string, or byte budget
- Required closure: use the existing canonical JSON depth/item limits and bind
  the exact limit profile/version to the resulting authority value.

### FCIS-478-016: Stack and evidence are stale

- Severity: P0 process blocker
- Status: CONFIRMED
- Source: #478 predates the latest #477 head and its schema-metadata repair
- Required closure: repaired #477 exact-head review, rebase #478, rerun every
  focused and broad gate, then obtain independent exact-head review.

## Wider pre-existing gaps exposed by this audit

These are not assigned to the snapshot implementation agent unless a touched
call site requires them. They remain in the backlog and prevent broad claims:

1. exact-type policy is not uniform across existing domain constructors and
   helpers such as integer guards;
2. several in-memory domain records still use raw `dict[str, Value]` after
   decode instead of named typed fields;
3. frozen Python dataclasses are not unforgeable capabilities;
4. canonical byte ingress, owned in-memory representation, and runtime parser
   refinement are not yet generated from one source grammar;
5. the atomic state/effect/receipt/nonce/outbox storage commit is not proved by
   these PRs;
6. state maps have mounted cardinality limits, while some economic integer
   fields still lack a source-pinned upper bound;
7. cross-language Python/Rust/proof-guest parity remains a separate obligation.

## Merge posture

```text
PR477Ready = false
PR478Ready = false
ProductionReleaseAllowed = false
```
The implementation agent closes findings only by mapping each ID to source,
negative evidence, positive evidence, and exact-head gate output in
`requirements.json`. Passing unrelated tests does not close a finding.
