# Implement FCIS M5-P4B4: exact strong-settlement specialization

**Status:** frozen

**Prompt kind:** build

**Contract version:** `zenodex/fcis-m5-p4b4-exact-strong-validator/v1`

**Required reviewed ancestor:** `99da842b6606e6f10ce8ab6b2c94c2d36f2e169f`

**Authority posture:** unmounted evidence only

## Objective

Create one exact-only strong-settlement validator that consumes admitted,
immutable FCIS values and returns one typed candidate or one typed rejection
together with the exact state-read trace.

The checkpoint must preserve the current mixed validator byte-for-byte as its
differential oracle. It must not change mounted DEX behavior.

The target relation is:

```text
ExactStrongSettlementV1(
    OwnedSettlementV1,
    tuple[OwnedIntentV1, ...],
    ExactSpotPreStateV1,
    StrongSettlementContextV1,
)
  -> ExactStrongSettlementObservedV1(
       ExactStrongSettlementCandidateV1
       | ExactStrongSettlementRejectV1,
       FCISStateReadTraceV5,
     )
```

The result must be total over the admitted profile and bounded by source-owned
limits. An ordinary rejection carries no successor state or patch.

## Why this checkpoint exists

`src/core/settlement_strong_validator.py` currently combines:

- legacy mutable command and settlement classes;
- exact owned command and settlement values;
- legacy adapters and differential admission;
- exact committed state;
- route parsing through the legacy route module;
- pure economic replay;
- exact candidate construction;
- public compatibility rendering.

That mixed module contributes 26 of the 64 current `final-mount` violations.
P4B4 creates an exact semantic owner. A later atomic mount checkpoint may
switch the exact evaluator to it and demote the mixed module. P4B4 itself does
not change reachability, so the expected `final-mount` count remains 64.

## Required reading

Read completely before editing:

1. The root `AGENTS.md` supplied for this checkout.
2. `.agents/coding-style.md` from the primary checkout.
3. `docs/specs/fcis_authority_snapshot_v1/CONTEXT_DRIFT_PROTOCOL.md`.
4. `docs/specs/fcis_authority_snapshot_v1/COMBINATOR_CONTRACT.md`.
5. `docs/specs/fcis_authority_snapshot_v1/DECISIONS.md`.
6. `docs/research/FCIS_M5_P4B3_IMPLEMENTOR_REPORT_20260727.md`.
7. `src/core/settlement_strong_validator.py`.
8. `src/core/fcis_step_evaluator.py`.
9. `src/core/fcis_route_binding.py`.
10. `src/core/fcis_traced_reads_v5.py`.
11. `src/state/spot_state_transitions.py`.
12. `src/state/state_transitions.py`.
13. `src/state/settlement_snapshots.py` if present; otherwise
    `src/core/settlement_snapshots.py`.
14. Exact pool-creation, LP-duration, balance, pool, LP, fee, and nonce
    transition modules reached by the current evaluator.
15. Existing strong-validator, route parity, FCIS evaluator, and structural
    checker tests.

Record the exact start SHA and interpreter. Run the style classifier before
source edits.

## Protected immutable inputs

P4B4 must leave these paths byte-identical to the reviewed ancestor:

```text
src/core/dex.py
src/integration/dex_engine.py
src/core/settlement_strong_validator.py
src/core/route_settlement.py
src/core/fcis_step_evaluator.py
src/state/legacy_state_snapshots.py
docs/research/FCIS_M5_P4A_LEGACY_BASELINE_V1.json
docs/research/FCIS_M5_P4A_DIFFERENTIAL_REPLAY_V1.json
docs/research/FCIS_M5_P4A_MOUNT_CALL_GRAPH_V1.json
docs/research/FCIS_M5_P4A_CROSS_LANGUAGE_MATRIX_V1.json
docs/research/FCIS_M5_P4A_READINESS_RECEIPT_V1.json
docs/research/FCIS_M5_P4B0_REFINEMENT_V1.json
```

Changing any protected path is an automatic `NO-GO`.

## Required source surface

Use these names unless an existing exact type makes one redundant:

```text
src/core/fcis_settlement_strong_values.py
src/core/fcis_settlement_strong_validator.py
tests/core/test_fcis_settlement_strong_values.py
tests/core/test_fcis_settlement_strong_validator.py
tests/core/test_fcis_settlement_strong_parity.py
tools/check_fcis_authority_snapshot_contract.py
tests/tools/test_check_fcis_authority_snapshot_contract.py
docs/research/FCIS_M5_P4B4_IMPLEMENTOR_REPORT_20260727.md
```

Do not add a second schema interpreter. Reuse existing exact admitted values
and source-owned enums or limits.

## Frozen design

### P4B4-D01: exact values

Define final, frozen, slotted values for:

```text
StrongSettlementContextV1
ExactSpotPreStateV1
ExactStrongSettlementCandidateV1
ExactStrongSettlementRejectV1
ExactStrongSettlementObservedV1
```

Requirements:

`StrongSettlementContextV1` composes the existing exact
`FCISSettlementExecutionContextV1` plus the exact LP-duration policy. Do not
create another settlement-mode enum or flatten the admitted settlement context
back into loose scalar arguments.

- exact type checks in `__post_init__`;
- no caller-supplied constructor, registry, resolver, encoder, hash, root, or
  callback;
- no `Any`, `object`, raw mapping, raw list, or legacy mutable class in an
  authority-bearing field;
- validation mode comes from the existing closed FCIS settlement context;
- fee recipient presence is structurally compatible with the fee-share rule;
- rejection contains a stable public reason and no candidate fields;
- candidate owns exact successor balances, pools, LP positions, and canonical
  patches;
- observed result owns exactly one result and one exact trace.

Do not encode validation-only success as a public third result. P4B4 evaluates
an authority candidate or rejects.

### P4B4-D02: one exact composition kernel

The exact validator must perform these phases in this order:

```text
1. Revalidate exact graph identity at the public boundary.
2. Validate source-owned context and resource bounds.
3. Build one exact settlement index.
4. Enforce canonical intent/fill coverage and rejection precedence.
5. Derive and verify route bindings through the P4B3 command-bound API.
6. Replay each accepted intent against one immutable exact pre-state plus
   private local scratch.
7. Recompute canonical balance, reserve, LP, event, and fee projections.
8. Require exact equality with the supplied settlement certificate.
9. Check batch conservation.
10. Build one all-or-none exact spot candidate and require it to equal the
    sequential replay state.
11. Return the candidate or the first stable typed rejection with the exact
    read prefix observed before rejection.
```

The composition kernel coordinates domain machines. Arithmetic and state
mutation semantics remain owned by existing exact leaf transitions and kernels.
Do not duplicate AMM, liquidity, pool-creation, LP-duration, balance, pool, or
LP accounting formulas in the orchestrator.

New or materially touched critical functions should target 60 lines, five
branches, and two indentation levels. Split by semantic phase or intent kind.

### P4B4-D03: exact route behavior

All route handling must use:

```text
OwnedIntentV1
  -> derive RouteBindingV1
  -> validate exact committed pool graph
  -> replay exact ordered legs
```

Forbidden route behavior:

- importing `src/core/route_settlement.py`;
- parsing route fields from a raw mapping;
- accepting a caller-supplied binding without rederivation from the command;
- normalizing the observed read tuple with `set`, `sorted(set(...))`, or a
  second order;
- counting private scratch lookup as another committed-state read.

Observed route reads equal the canonical unique committed pool preflight reads
from P4B3. Repeated legs may reuse private scratch reserves.

### P4B4-D04: exact command and settlement access

Only exact owned command/settlement accessors may be used.

Forbidden:

- `_Replay*` union aliases;
- `Intent`, `Settlement`, `Fill`, `BalanceDelta`, `ReserveDelta`, `LPDelta`,
  `BalanceTable`, `LPTable`, `PoolState`, or legacy snapshot imports;
- `isinstance` admission;
- `int(...)`, `str(...)`, truthiness, `value or 0`, or `.get(..., default)` as
  authority coercion;
- dictionary/list reconstruction;
- JSON round-trip copy;
- generic freeze, `copy`, `deepcopy`, mutable inheritance, or seal flags;
- broad exception catches around the exact core.

Exact optional fields must be matched by the declared command/fill variant.
Missing, extra, or wrong-variant fields reject through stable precedence.

### P4B4-D05: deterministic settlement index

The exact index must prove:

- intent IDs are unique;
- every fill names one admitted intent;
- every admitted intent has exactly one included action;
- an included `FILL` action has exactly one detailed fill row;
- an included `REJECT` action has no detailed fill row;
- fill order and route intent order obey the current protocol rule;
- CoW pairing is complete and symmetric when enabled;
- duplicate or ambiguous pairings reject before economic replay;
- settlement delta/event sequences preserve their protocol-defined order;
- unordered domains are normalized once by the declared protocol key.

The index must be an owned immutable value. A caller cannot mutate it or supply
it as authority.

### P4B4-D06: rejection and observation parity

For every supported differential fixture:

```text
kind(exact) = kind(legacy)

Reject(exact)
  -> public_reason(exact) = public_reason(legacy)
  -> observed_reads(exact) = observed_reads(legacy)
  -> no successor or patch

Accept(exact)
  -> exact successor state = legacy-oracle successor state
  -> exact canonical patches = legacy-oracle canonical patches
  -> observed_reads(exact) = observed_reads(legacy)
```

Compare tuples directly. No projection may sort, deduplicate, omit, default, or
otherwise weaken either side.

If a genuine versioned semantic difference is discovered, stop with
`M5_P4B4_BLOCKED_PARITY`. Do not add an input-controlled allowlist or rewrite
the oracle.

### P4B4-D07: resource determinism

Bind work to existing source-owned admission limits. At minimum cover:

```text
intent count
fill count
balance/reserve/LP delta counts
event count and event bytes
route leg and fingerprint counts
integer domain bounds
state-read trace size
candidate patch operation count
```

Admission or context validation must reject before unbounded work. Do not add a
caller-selectable budget. If the existing admitted types do not expose a
bounded profile for one dimension, stop with
`M5_P4B4_BLOCKED_RESOURCE_BOUND`.

### P4B4-D08: structural checker

Register both new source modules in the `authority-graph`, `exact-replay`, and
`exact-consumers` profiles.

The checker must fail on:

- any protected-file drift;
- any legacy type or legacy module import;
- open authority fields or `_Replay*` unions;
- generic `Any`/`object` authority storage;
- `isinstance` admission or numeric/string coercion;
- raw dictionary/list/JSON reconstruction;
- generic freeze/copy/deepcopy/seal mechanisms;
- broad exception catches;
- caller-supplied bindings, encoders, hashes, roots, callbacks, or registries;
- imports from shell, integration, filesystem, network, clock, randomness,
  environment, locale, or timezone modules;
- route read normalization;
- exact values constructed outside the controlled derivation module and
  explicitly reviewed tests;
- a public exact entry that skips recursive revalidation;
- an admitted private sink imported by any module other than the future exact
  evaluator allowlist;
- a new command or fill variant without parity coverage.

Add mutation tests that preserve syntax and outer artifact hashes while
changing the forbidden mechanism. The test must prove the intended checker
rule killed the mutant.

### P4B4-D09: mount isolation

Prove:

```text
protected paths are byte-identical
new exact validator has no mounted importer
legacy mixed validator remains reachable only as before
final-mount violation count remains exactly 64
```

A reduction in the count during P4B4 indicates an unauthorized reachability or
checker change. An increase indicates new authority debt. Either is a
`NO-GO`.

## Required test matrix

### Exact values

- wrong exact type at every field;
- bool where integer is required;
- fee share at `0`, `1`, `9999`, `10000`, and invalid neighbors;
- fee recipient absent/present combinations;
- hostile nested mutation with `object.__setattr__`;
- pickle/reconstruction or direct-constructor bypass where locally relevant;
- rejection proves no candidate attributes or committable output.

### Coverage and precedence

Cover at least:

- `CREATE_POOL`;
- route exact-in and route exact-out;
- single-pool `SWAP_EXACT_IN` and `SWAP_EXACT_OUT`;
- CoW accepted and rejected forms;
- `ADD_LIQUIDITY`;
- `REMOVE_LIQUIDITY`;
- ordinary `REJECT` fill;
- proof-carrying reserve witness mode;
- snapshot-bound quote binding;
- protocol fee disabled/enabled;
- sender distinct from recipient;
- duplicate, missing, unknown, reordered, and wrong-action fills;
- malformed or command-substituted route binding;
- missing, inactive, drifted, misoriented, and repeated route pools;
- canonical delta and event mismatch;
- balance, reserve, LP, and conservation failure;
- overflow and domain-bound neighbors.

### Properties and metamorphic tests

- same admitted inputs produce equal result and trace;
- exact public revalidation and private admitted sink agree;
- accepted replay candidate equals application of its canonical patches;
- rejection leaves the pre-state graph byte-identical and returns no patch;
- event/delta reorder, deletion, duplication, or payload mutation rejects;
- command, pre-state, context, fee policy, or pool substitution changes result
  or rejects;
- route repeated-pool scratch behavior preserves exact direct read parity;
- adding an unsupported enum member fails the coverage gate.

### Differential corpus

Use source-owned fixtures or generated in-test values. Do not mutate historical
artifacts.

For each row bind:

```text
fixture ID
canonical command/settlement bytes
pre-state root
context and policy
legacy result projection
exact result projection
exact direct observed-read tuple
legacy direct observed-read tuple
first mismatch path or REFINE
source SHA and algorithm versions
```

The checker must reject a fabricated all-refine artifact even after its outer
hash is recomputed.

## Mandatory independent attacks

Before declaring complete, demonstrate failure for:

1. replace one exact intent with a legacy `Intent`;
2. import one helper from `route_settlement.py`;
3. replace exact field matching with `int(value or 0)`;
4. accept a binding derived from command A with command B;
5. compare read traces through `sorted(set(...))`;
6. remove one fill from exact index coverage;
7. reorder two rejection checks;
8. mutate a nested exact pool after construction;
9. fabricate all-refine evidence and recompute its outer hash;
10. add an unbounded event or route collection;
11. catch `Exception` around the exact core;
12. import the private admitted sink from an unauthorized module.

## Gates

Run the narrowest gates first:

```text
python3 -m py_compile <changed Python files>
python3 -m ruff check <changed Python files>
python3 -m ruff format --check <changed Python files>
python3 -m mypy <changed source modules>
pytest -q <P4B4 focused tests>
pytest -q tests/core/test_settlement_strong_validator.py
pytest -q tests/tools/test_check_fcis_authority_snapshot_contract.py
```

Then run:

```text
python3 tools/check_fcis_authority_snapshot_contract.py --profile state-substrate
python3 tools/check_fcis_authority_snapshot_contract.py --profile authority-graph
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-replay
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-consumers
python3 tools/check_fcis_authority_snapshot_contract.py --profile final-mount
python3 docs/specs/fcis_authority_snapshot_v1/check_packet.py
bash tools/run_critical_quality_gate.sh
python3 tools/check_production_boundary.py --json
python3 tools/permissionless_assurance.py status
```

Run security red flags and design metrics on the new source/checker paths.

## Stop conditions

Stop without mounting when:

- any protected input changes;
- complete parity cannot be established;
- rejection precedence differs;
- a required bound is absent;
- the implementation needs a new economic rule;
- the exact composition kernel would duplicate an existing leaf formula;
- a checker mutant survives;
- any pre-mount profile fails;
- `final-mount` differs from exactly 64;
- a required tool returns unknown/error and no stronger local evidence exists.

## Report

Write:

```text
docs/research/FCIS_M5_P4B4_IMPLEMENTOR_REPORT_20260727.md
```

Include:

```text
Result
Exact start and end heads
Changed paths
Invariant and authority impact
Parity fixture coverage
Direct rejection and read-trace parity
Resource bounds
Mutation kills
Profile counts
Exact commands and outcomes
Commands not run
Residual risk
Next safest step
```

Allowed completion claim:

```text
P4B4 provides an unmounted exact strong-settlement specialization with direct
observable parity over the declared supported corpus.
```

Forbidden claims:

```text
M5 is complete
the FCIS path is mounted
the datastore commit is linearizable
Python equals Rust/Tau/proof guest
the functional core is bug-free
M6 may begin
```
