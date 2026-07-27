# FCIS M5-P4B3: Closed Exact Route Binding and Replay

**Status:** semantically approved
**Prompt kind:** build
**Intended use:** an implementation agent working in an isolated ZenoDEX worktree
**Visibility:** repository-local
**Contract version:** `zenodex/fcis-m5-p4b3-route-binding/v1`
**Execution authorized:** yes, only within the file and checkpoint boundaries below
**Normative source:** this file is the only normative P4B3 prompt

## Intent mirror

### User's real job

Continue the ZenoDEX FCIS migration without repeating the generic-deep-freeze
or parallel-validation failures. Move the route command and replay substrate
onto closed typed values so the later exact strong-validator specialization can
disconnect the mixed legacy route module.

### Desired result

Produce an unmounted, independently reviewable route-binding checkpoint that:

1. admits route-leg and fingerprint structure through the existing closed
   deterministic combinator;
2. derives exact immutable route values with stable typed rejection;
3. replays only against exact committed pool values;
4. preserves the existing supported route semantics and rejection precedence;
5. migrates FCIS-only readers to the exact module;
6. leaves mounted legacy authority unchanged.

### Decision enabled

An accepted checkpoint lets the reviewer build the exact-only strong settlement
validator without importing the legacy `route_settlement.py` union.

### Non-goals

- Do not mount the FCIS evaluator.
- Do not edit `src/core/dex.py`, `src/integration/dex_engine.py`,
  `src/core/settlement_strong_validator.py`, or `src/core/route_settlement.py`.
- Do not remove legacy route behavior or tests.
- Do not implement the raw-byte authority parser, Rust parity, datastore commit,
  proof-guest parity, or external outbox delivery.
- Do not invent a new route wire codec in this checkpoint. The admitted
  `OwnedIntentV1` remains the canonical command carrier; route binding is a
  controlled derived value.
- Do not claim that the nine legacy route findings are closed. They remain
  reachable through the mixed validator until its later specialization.

### Decision authority

The architecture, result variants, rejection precedence, allowed file surface,
and checkpoint boundaries in this prompt are frozen. The implementor may choose
local private helper names and test-fixture organization. Stop and return
`BLOCKED` if the source contradicts a frozen requirement or if satisfying it
would require another production file, a public API change, a new dependency,
or a rejection-order change. Do not infer permission from a passing legacy
test, an existing permissive helper, or a similarly shaped module.

## Semantic traceability

| ID | Requirement or decision | Origin | Status | Consequence if wrong |
| --- | --- | --- | --- | --- |
| R1 | The existing closed combinator is the sole structural admission engine | user-stated | approved | A second parser can drift in shape, limits, and errors |
| R2 | Route values are exact, immutable, owned, and free of mutable base classes | user-stated | approved | Authority can change through aliases or subclasses |
| R3 | Route sequence order is semantic and must be preserved | source-derived | approved | Reordering changes replay and rejection behavior |
| R4 | Fingerprint map order is canonical and independent of input-map iteration | context-derived | approved | Equal commands can produce different bytes or reads |
| R5 | Legacy behavior remains a differential oracle during this checkpoint | context-derived | approved | The agent could erase evidence before proving refinement |
| R6 | No authority switch occurs before Python/Rust/verifier parity | user-stated | approved | Python could outrun the reviewed promotion profile |
| R7 | The P4B2 checkpoint at the exact start SHA is immutable input | source-derived | approved | Evidence and reviewer baselines become untrustworthy |

## Exact starting state

Start from this exact commit:

```text
9c7da554480f26c0466b1dae3757ff5fa2ba243a
```

Create a separate worktree and branch. Recommended names:

```text
worktree: /tmp/zenodex-fcis-m5-p4b3-route-20260727
branch:   agent/fcis-m5-p4b3-route-binding-20260727
```

Before editing, prove:

```bash
git rev-parse HEAD
git status --short
git merge-base --is-ancestor 9c7da554480f26c0466b1dae3757ff5fa2ba243a HEAD
git diff --exit-code 9c7da554480f26c0466b1dae3757ff5fa2ba243a -- \
  src/core/dex.py \
  src/integration/dex_engine.py \
  src/core/settlement_strong_validator.py \
  src/core/route_settlement.py
```

Stop if the start SHA is wrong or the worktree is dirty.

## Frozen architecture

The required route is:

```text
known Intent source
  -> INTENT_SCHEMA_V1
  -> closed route child schemas
  -> OwnedIntentV1
  -> derive_exact_route_binding_v1
  -> RouteBindingOkV1 | RouteBindingRejectV1
  -> replay_exact_route_v1(exact committed pools)
  -> RouteReplayOkV1 | RouteReplayRejectV1
```

Structural shape belongs to the closed combinator. Cross-field relationships
belong to a pure verifier over the already-admitted values. Exact replay accepts
only the verified exact binding and exact committed pool map.

### Required closed child schemas

Define route schemas using existing combinator constructors:

```text
ROUTE_LEG_SCHEMA_V1
  ExactKeyedMap {
    pool_id:   TEXT_256_V1
    asset_in:  TEXT_256_V1
    asset_out: TEXT_256_V1
    amount_in: ExactInt(1, DEX_SWAP_AMOUNT_MAX)
    amount_out: ExactInt(1, DEX_SWAP_AMOUNT_MAX)
  }
  required fields = all five

ROUTE_LEGS_SCHEMA_V1
  SequenceOf(EXACT_LIST | EXACT_TUPLE,
             ROUTE_LEG_SCHEMA_V1,
             min=1,
             max=256)

ROUTE_POOL_FINGERPRINTS_SCHEMA_V1
  MapOf(TEXT_256_V1,
        HASH_32_V1,
        max=256,
        versioned schema id)
```

Replace the two `JSON_VALUE_SCHEMA_V1` route-field registrations in
`intent_schema.py` with these schemas. Do not create an alternate admission
function that manually walks a raw mapping or list.

The schemas must return only existing owned primitives: tuples and
`OwnedMapV1`. Do not add behavior-bearing subclasses or route objects to the
combinator registry.

### Acyclic schema dependency

`fcis_route_binding_schema.py` owns the route-specific primitive and child
schemas. It may import only `domain_limits.py` and
`snapshot_combinators.py`. It must not import `intent_schema.py`,
`intent_snapshots.py`, `intents.py`, or any route runtime module.

Define the route-specific text and hash primitives directly in that leaf
schema module with the same frozen rules as the current intent primitives:

```text
ROUTE_TEXT_256_V1
  NON_EMPTY, max 256 characters, max 1,024 UTF-8 bytes

ROUTE_HASH_32_V1
  LOWERCASE_0X_HEX, exactly 66 characters and 66 UTF-8 bytes
```

`intent_schema.py` imports the two exported route-field schemas. Dependency
direction is therefore:

```text
snapshot_combinators + domain_limits
  -> fcis_route_binding_schema
  -> intent_schema
```

Add a test asserting that the route-specific primitive rules remain equal to
the corresponding current intent-field rules. Do not solve the dependency by
duplicating route child schemas in `intent_schema.py`, by importing
`intent_schema.py` from the leaf module, or by adding a runtime factory whose
arguments can be selected by authority input.

### Exact values

Create final, frozen, slotted values with exact fields:

```text
RouteKindV1 = EXACT_IN | EXACT_OUT

RouteLegBindingV1 {
  pool_id: str
  asset_in: str
  asset_out: str
  amount_in: int
  amount_out: int
}

RouteBindingV1 {
  kind: RouteKindV1
  asset_in: str
  asset_out: str
  total_amount_in: int
  total_amount_out: int
  legs: tuple[RouteLegBindingV1, ...]
  pool_fingerprints: OwnedMapV1[str, str]
}
```

Construction must be controlled by the derivation module. Caller construction
of an authority-bearing `RouteBindingV1` must fail. Decoded or projected claims
remain non-authoritative.

Use a closed result algebra:

```text
RouteBindingResultV1
  = RouteBindingOkV1(binding)
  | RouteBindingRejectV1(code, path)

RouteReplayLegV1 {
  pool_id: str
  asset_in: str
  asset_out: str
  amount_in: int
  amount_out: int
  fee_paid: int
  new_reserve0: int
  new_reserve1: int
}

RouteReplayOkV1 {
  legs: tuple[RouteReplayLegV1, ...]
  total_amount_in: int
  total_amount_out: int
  total_fee_paid: int
}

RouteReplayResultV1
  = RouteReplayOkV1
  | RouteReplayRejectV1(code)
```

Do not use `ok: bool`, optional error fields, raw strings outside a closed enum,
or a result whose valid field combinations depend on comments.

`RouteReplayRejectCodeV1` uses closed enum members whose serialized values are
the existing stable public route rejection strings. The exact module must
recursively revalidate `RouteBindingV1` and every nested child before reading
pools. Hostile in-process `object.__setattr__` corruption returns the closed
invalid-binding rejection with no pool read and no partial replay value.

### Cross-field derivation order

After structural admission, verify in this exact order:

1. exact route intent kind;
2. distinct route endpoint assets;
3. `leg_indices == tuple(range(len(legs)))`;
4. every leg uses the route endpoint assets;
5. fingerprint keys equal the set of leg pool IDs;
6. sum leg input and output amounts with checked bounded integer arithmetic;
7. exact-in: signed total input equals the leg sum, and minimum output is not
   greater than the leg output sum;
8. exact-out: signed total output equals the leg sum, and maximum input is not
   less than the leg input sum.

The first failure wins. Define a closed `RouteBindingRejectCodeV1` enum whose
members correspond one-to-one with these checks. Bind tests to the enum and
field path. Input data must never select the registry, constructor, or error
precedence.

### Replay order

Exact replay consumes `RouteBindingV1` and
`OwnedMapV1[str, CommittedPoolStateV1]` only. Preserve this order:

1. preflight unique fingerprint pool IDs in canonical key order;
2. missing pool;
3. inactive pool;
4. fingerprint drift;
5. replay legs in their original semantic sequence while threading per-pool
   reserves;
6. invalid asset orientation;
7. quote mismatch;
8. derive exact leg outputs, totals, and fee total.

Repeated pool IDs across multiple legs are valid. They must share the threaded
scratch reserves. Scratch dictionaries or lists may exist only as local,
non-escaping builders and must freeze once into the returned value.

The exact module must expose observed-read variants for the existing FCIS trace
consumer:

```text
route_binding_pins_exact_snapshot_observed_v1(binding, pools)
  -> (bool, tuple[pool_id, ...])

replay_exact_route_observed_v1(binding, pools)
  -> (RouteReplayResultV1, tuple[pool_id, ...])
```

The observed tuple records lookups at their actual sites. It includes canonical
fingerprint preflight reads and subsequent semantic leg reads, including a
repeated pool ID when the route reads that pool again. Non-observed convenience
wrappers, if retained, must be projections of these functions rather than a
second replay implementation.

### Canonical behavior

- Route leg order is preserved exactly.
- Fingerprint map storage and traversal use canonical key order.
- No `set` iteration may affect an observable output.
- No float, wall clock, randomness, environment, I/O, global mutable state, or
  broad exception catch may enter the exact module.
- Bounds: at most 256 legs and 256 unique fingerprint entries.
- Bool is rejected wherever an integer is required.

## Required file surface

New files:

```text
src/core/fcis_route_binding_values.py
src/core/fcis_route_binding.py
src/state/fcis_route_binding_schema.py
tests/core/test_fcis_route_binding.py
tests/core/test_fcis_route_binding_parity.py
tests/state/test_fcis_route_binding_schema.py
docs/research/FCIS_M5_P4B3_IMPLEMENTOR_REPORT_20260727.md
```

Permitted modifications:

```text
src/state/intent_schema.py
src/state/fcis_route_support_v5.py
src/core/fcis_traced_reads_v5.py
src/core/fcis_support_profile_v5.py
tools/check_fcis_authority_snapshot_contract.py
tests/tools/test_check_fcis_authority_snapshot_contract.py
```

Any additional file requires reviewer approval before editing. Do not update an
older generated artifact, P4A/P4B0/P4B1/P4B2 report, baseline, receipt, or source
hash.

## Required migration boundary

Migrate FCIS-only readers so they consume `RouteBindingV1` and exact replay:

```text
fcis_route_support_v5.py
fcis_traced_reads_v5.py
fcis_support_profile_v5.py
```

Keep the mixed strong validator unchanged. Keep `route_settlement.py` unchanged.
The exact route module may call shared AMM kernels and committed pool
fingerprinting functions. It must not import `route_settlement.py`, `Intent`,
`PoolState`, `Mapping`, or a legacy route binding class.

The checker must:

- include the new exact files in the appropriate authority profiles;
- reject `Any`, `object` authority fields, `Mapping`, mutable base classes,
  generic JSON route schemas, `copy`, `deepcopy`, seal flags, and broad catches;
- reject imports from `route_settlement.py` in the new exact files and migrated
  FCIS-only readers;
- verify controlled construction sites for exact binding and replay results;
- preserve the existing legacy route path in the final-mount inventory until
  the exact strong-validator checkpoint disconnects it.

## Forbidden mechanisms

Automatic NO-GO:

- `JSON_VALUE_SCHEMA_V1` or `BoundedJsonValue` for either route authority field;
- hand-written structural parsing of raw `dict`, `list`, `Mapping`, or `Any`;
- `deep_freeze`, `copy.copy`, `copy.deepcopy`, pickle, JSON round-trip copying,
  mutable subclassing, `_snapshot_sealed`, or `object.__setattr__` in production;
- public constructor token/capability;
- behavior-bearing values selected by input data;
- `isinstance` on the exact path;
- bool flags encoding result variants;
- coercive `str()`, `int()`, `tuple()`, `dict()`, or `list()` at authority
  admission;
- sorting route legs;
- replacing rejection enums with strings supplied by callers;
- changing tests, checkers, or fixtures to accept a new divergence;
- editing mounted or immutable-input files named above;
- claiming authority, production, Rust, verifier, proof, or datastore parity.

## Required evidence

### Closed schema tests

At minimum:

1. valid exact-in and exact-out route fields admit;
2. list and tuple source forms produce equal owned tuples;
3. caller mutation after admission cannot change the owned route graph;
4. empty and 257-leg sequences reject with stable code/path;
5. missing, extra, misspelled, or duplicated semantic fields reject;
6. bool amounts reject;
7. malformed pool IDs, assets, and fingerprints reject according to the frozen
   field schemas;
8. non-route intents cannot carry reserved route fields;
9. generic JSON substitution in either schema is killed by a checker mutation.

### Cross-field tests

Cover each ordered rejection check, plus:

- repeated pool IDs across legs;
- fingerprint key insertion-order permutations;
- reversed leg order changes the binding and replay when semantically relevant;
- same semantic map with different insertion order yields equal
  `RouteBindingV1` values and identical ordered fingerprint entries;
- object-level corruption of an owned child is detected before replay;
- exact derivation is deterministic across repeated calls.

### Replay and parity tests

Use the existing legacy route implementation only as a differential oracle.
For the supported single-hop split-route corpus, compare:

```text
accept/reject
first rejection code
observed pool-read order
per-leg result order and values
threaded post-reserves
total input
total output
total fee
```

Include missing, inactive, drifted, invalid-orientation, quote-mismatch,
repeated-pool, exact-in, and exact-out cases. A versioned divergence must be
explicitly classified and must block promotion unless this prompt already
authorizes it. This prompt authorizes no divergence.

### Structural mutation tests

The checker suite must kill at least these mutations:

1. restore `JSON_VALUE_SCHEMA_V1` for `route_legs`;
2. restore `JSON_VALUE_SCHEMA_V1` for fingerprints;
3. add `Mapping` to the exact binding module;
4. make a binding constructor public;
5. import `route_settlement.py` from an FCIS-only reader;
6. replace the closed replay union with `ok: bool`;
7. sort legs before replay;
8. accept a raw mapping at the exact replay API;
9. add a broad `except Exception`;
10. omit the 256-item bound.

Each mutation test must recompute any outer hash or artifact field before
calling a checker. A stale checksum does not count as semantic mutation
evidence.

## Mandatory gates

Run narrow gates after each checkpoint:

```bash
python3 -m py_compile <changed Python files>
python3 -m ruff check <changed Python files>
python3 -m ruff format --check <changed Python files>
python3 -m mypy \
  src/core/fcis_route_binding_values.py \
  src/core/fcis_route_binding.py \
  src/state/fcis_route_binding_schema.py
python3 -m pytest -q \
  tests/state/test_fcis_route_binding_schema.py \
  tests/core/test_fcis_route_binding.py \
  tests/core/test_fcis_route_binding_parity.py \
  tests/core/test_exact_route_replay_parity.py \
  tests/core/test_fcis_support_profile_v5.py \
  tests/tools/test_check_fcis_authority_snapshot_contract.py
python3 tools/check_fcis_authority_snapshot_contract.py --profile state-substrate --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile authority-graph --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-replay --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-consumers --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile final-mount --json
python3 docs/specs/fcis_authority_snapshot_v1/check_packet.py
git diff --check
```

Expected profile result:

```text
pre-mount profiles: ok=true
final-mount: honest fail-closed
final-mount count: at least the existing 64 until the mixed validator is replaced
```

Do not lower the count by deleting a checker path while a mounted or exact
caller can still reach the legacy module.

## Checkpoint and terminal condition

Use three reviewable commits:

```text
P4B3-A  closed route child schemas and schema tests
P4B3-B  controlled exact values, cross-field derivation, replay, and parity
P4B3-C  FCIS-only consumer migration, checker mutations, and report
```

The task is complete only when:

- all required files exist;
- mounted and immutable-input files are byte-identical to the start SHA;
- every required gate has the expected result;
- valid legacy fixtures retain exact parity;
- final-mount remains honestly blocked;
- the worktree is clean after the three commits;
- the report lists exact start/end SHAs, commands, outcomes, nonclaims, and
  residual risk.

Stop after P4B3-C. Do not begin the exact strong-validator specialization.

## Reviewer attacks

The reviewer will independently attempt:

1. raw mapping, list, subclass, and lookalike objects at every exact API;
2. post-admission caller mutation;
3. `object.__setattr__` corruption of nested owned values;
4. extra or missing route-leg fields;
5. bool-as-int values;
6. empty and over-budget graphs;
7. duplicate and missing fingerprint coverage;
8. repeated-pool reserve threading;
9. leg-order reversal;
10. map insertion-order permutations;
11. each rejection-precedence neighbor;
12. exact/legacy parity on every supported route failure;
13. reintroduction of a legacy import;
14. public or reflective constructor access;
15. semantic checker mutations with recomputed outer hashes.

Any mounted-file edit, immutable-input edit, forbidden mechanism, unclassified
parity divergence, or false authority claim is an automatic NO-GO.

## Implementor handoff format

Return:

```text
Result:
- Outcome: M5_P4B3_COMPLETE_UNMOUNTED | BLOCKED
- Exact start head:
- Exact end head:
- Branch and worktree:
- Three commits:

Changed:
- file-by-file purpose

Invariant/authority impact:
- exact laws established
- explicit nonclaims

Evidence:
- command and exact result
- profile counts
- parity corpus and result

Commands not run:
- exact list and reason

Residual risk:
- remaining route, validator, mount, cross-language, and datastore gaps

Next safest step:
- return to reviewer; no mount and no P4B4 work
```

Do not push unless the user or reviewer separately authorizes it.
