# M5-P4B0 Legacy-to-FCIS Refinement Contract

## Purpose

Legacy DEX output and FCIS V1 output have different representations and
authority envelopes. Direct byte equality is therefore false for all current
P4A fixtures. The next checkpoint must decide whether FCIS V1 preserves the
shared legacy semantics while adding self-consistent exact-only outputs.

The relation is directional:

```text
RefinesV1(legacy, exact, fixed_policy)
```

It is not equality, an input-controlled allowlist, or permission to mount FCIS.

## Closed result algebra

```text
RefinementDecisionV1
  = RefinesV1(witness)
  | MismatchV1(code, path, legacy_value, exact_value)
  | InvalidEvidenceV1(code, path)
```

`RefinesV1` is returned only after every obligation below succeeds.
`MismatchV1` preserves the first deterministic semantic mismatch.
`InvalidEvidenceV1` covers malformed, stale, non-canonical, unbounded, or
unknown evidence. No variant contains partial authority.

## Input pipeline

```text
exact bytes
  -> strict canonical JSON parser
  -> closed snapshot-combinator schema
  -> exact owned observation values
  -> pure refinement decision
  -> canonical refinement artifact
```

### P4B0-001: source-bound inputs

Every observation binds the P4A baseline artifact hash, differential artifact
hash, reviewed start SHA, fixture ID, command bytes/hash, pre-state bytes/root,
and execution-context bytes/hash. Substitution at any one field is invalid.

### P4B0-002: canonical byte parser

Ingress starts from bytes. Reject duplicate keys, non-canonical whitespace or
key order, BOM, trailing bytes, floats, exponent notation, `NaN`, infinity,
negative zero, invalid Unicode, oversized input, and incomplete consumption.
Successful decode must re-encode to the exact input bytes.

### P4B0-003: closed combinator admission

Declare the evidence schema in a dedicated schema module. The admission module
must call the existing closed `admit(schema, value, path, context)` algebra.
Hand-written parallel map/list/type validation is forbidden. Authority input
cannot select constructors, registries, resolvers, policies, or encoders.

### P4B0-004: immutable exact values

Owned values are exact, final, frozen, slotted records containing only exact
owned children. No `Any`, mutable base class, subclass-based freeze, seal flag,
generic `deep_freeze`, `copy`, `deepcopy`, open `Mapping`, or caller-selected
behavior may enter the refinement core.

### P4B0-005: code-owned policy registry

The refinement policy is a closed, versioned registry in trusted source. It is
not read from the artifact. It contains only:

- the fixed legacy and FCIS algorithm/schema/codec/snapshot/support versions;
- the closed exact-only field set;
- explicit rejection-code and precedence mappings;
- explicit semantic projection versions.

Every policy entry must have a unique stable ID and source test. Unknown command
kinds, errors, fields, or versions fail closed.

### P4B0-006: same-input precondition

The relation is undefined until legacy and FCIS observations bind identical
command, pre-state, and execution context. Compare bytes and hashes. Hash-only
agreement is insufficient.

## Shared semantic obligations

### P4B0-007: result kind

Legacy and FCIS must agree on `accept` or `reject`. P4B0 does not treat an
accepted transition as a refinement of a rejection.

### P4B0-008: rejection refinement

For rejection:

- the fixed policy maps the legacy code and precedence to the exact typed code,
  phase, and path;
- public reason and embedded domain reason agree under the declared mapping;
- exact rejection exposes a receipt and no successor, patch, commit plan,
  effects, replay update, outbox, or bundle;
- unknown or many-to-one mappings remain mismatches unless the contract proves
  the lost distinction is non-authoritative.

### P4B0-009: accepted-state refinement

Decode both accepted successor representations into one typed semantic state
projection covering all eight committed state fields:

```text
balances, pools, LP state and duration metadata, nonces,
vault, Oracle, fee accumulator, perps
```

Semantic projections must be byte-identical. Do not compare only roots or the
three legacy spot tables.

### P4B0-010: economic outputs

Settlement, ordered fills/events, value movement, pool/reserve/LP changes,
total fees, fee allocation, dust, and nonce advancement must agree in their
shared semantic projection.

## Exact-only obligations

### P4B0-011: patch consistency

The exact patch is sorted, duplicate-free, preconditioned on the exact
pre-state, and applies to exactly the exact successor semantic state. Any stale
expected-old value or partial application is a mismatch.

### P4B0-012: receipt and bundle binding

Recompute receipt and bundle roots from canonical bytes. They must bind the
same command, pre-root, context, next state, patch, effects, replay, and outbox.
Cached roots do not substitute for recomputation.

### P4B0-013: replay and outbox consistency

Replay advances exactly the accepted intent nonces/nullifiers. Outbox records
derive from the same decision and use receipt-bound idempotency keys. Reorder,
delete, duplicate, or payload substitution is a mismatch.

### P4B0-014: fixed version deltas

Algorithm and representation deltas are accepted only through the closed
policy registry. The witness records both versions and the policy hash.
Input-supplied expected differences and wildcard field paths are forbidden.

## Totality and bounds

### P4B0-015: unknown fails closed

Every unknown enum, field, status, mapping, version, or observation shape
returns `InvalidEvidenceV1`. Broad exception recovery may not convert an
unknown case into refinement.

### P4B0-016: resource bounds

Declare exact limits for bytes, nesting, nodes, fixtures, observations,
collection length, field length, mismatch payload, and witness bytes. Reject
before expensive work where possible. The evaluator performs no I/O, clock,
randomness, environment read, or global mutation.

## Evidence and promotion

### P4B0-017: deterministic artifact

Generate a canonical artifact with one row per P4A fixture. Bind all source and
policy hashes. Two runs at one source head must be byte-identical.

### P4B0-018: mutation evidence

Kill every mutation in `TEST_MATRIX.md`. Hash mismatch alone is insufficient;
rehash adversarial artifacts before semantic validation.

### P4B0-019: no authority switch

`src/core/dex.py`, deployment configuration, mounted dispatch, verifier policy,
proof guest, Rust authority, and public claims remain byte-identical to the
required ancestor. New refinement modules remain unmounted.

### P4B0-020: fail-closed promotion gate

Normal validation accepts a structurally valid artifact containing mismatches.
`--require-all-refine` exits nonzero unless every fixture returns `RefinesV1`.
Even an all-refine result does not authorize P4B mount; it authorizes reviewer
consideration of the next checkpoint.
