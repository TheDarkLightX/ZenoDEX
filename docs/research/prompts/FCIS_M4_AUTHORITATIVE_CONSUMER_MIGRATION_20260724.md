# Implement FCIS M4 Exact Authoritative Consumers

**Status:** candidate execution prompt derived from the normative FCIS packet
**Prompt kind:** build
**Intended use:** one implementation agent, followed by an independent read-only reviewer
**Visibility:** repository-local
**Contract version:** `zenodex/fcis-m4-exact-consumers/v1`
**Source intent:** finish exact owned command consumption without mounting DexState
**Execution authorized:** yes, only within the M4 scope below

Read `FCIS_M4_M5_SHARED_CONTEXT_20260724.md` completely before this file.

## Intent mirror

### User's real job

Complete the remaining exact consumer migration so the already-owned command,
settlement, and state values flow through nonce validation, settlement replay,
fee derivation, support-root derivation, and candidate evidence without a
legacy mutable command path.

### Desired result

One unmounted M4 candidate in which every promoted consumer accepts exact owned
types, returns the same accepted/rejected result and bytes as the pinned legacy
oracle on the valid compatibility corpus, and fails closed on every legacy,
subclassed, corrupted, rebound, or mutated command graph.

### Non-goals

- Do not switch `DexState` fields.
- Do not mount `src/core/dex.py::step` on the new candidate.
- Do not delete legacy differential-oracle functions yet.
- Do not implement the final effect, receipt, outbox, or datastore commit.
- Do not begin M5 or M6.
- Do not add persistent collections, Rust ownership, or parallel execution.

## Required starting state

The exact M3 implementation commit
`0763a39de9daad13a3e189fa8ab3a9f6a1e3589c` must be an ancestor. Rerun:

```bash
bash tools/run_critical_quality_gate.sh
```

Stop if M3 is not green at the exact starting head. Preserve all M3 negative
tests and the `exact-replay` checker profile.

## Required implementation slices

Implement these slices in order. Commit or checkpoint after each green slice.

### M4.1 Exact command admission in the FCIS evaluator

Target: `src/core/fcis_step_evaluator.py`.

Replace the promoted use of `_admit_legacy_command_shape_v1` with one exact
command admission path that:

1. accepts only exact `OwnedSettlementV1` and exact tuple
   `OwnedIntentV1` at the exact evaluator boundary;
2. fully revalidates them through `snapshot_settlement` and
   `admit_intent_batch`;
3. binds each admitted value exactly once;
4. returns the exact pair or one `FCISStepEvaluationRejectV1`;
5. preserves the current command-admission phase, public rejection order, and
   public reason strings where their semantics are unchanged;
6. never returns or retains the raw input after successful admission.

The public boundary may keep `object` annotations only when needed to produce a
typed runtime rejection. Every private consumer after admission has exact
owned annotations. A separate explicitly named legacy differential wrapper may
remain, but the exact evaluator must not call it.

Add negative tests for:

- legacy `Settlement`;
- legacy list of `Intent`;
- tuple containing one legacy `Intent`;
- `OwnedSettlementV1` subclass/lookalike;
- list instead of exact tuple;
- corrupted already-owned settlement and intent;
- exact admission followed by raw replacement, rebinding, or
  `object.__setattr__` mutation.

### M4.2 Exact settlement replay consumer

Change these private consumers together:

```text
_evaluate_spot_v1
_spot_candidate_v1
evaluate_fcis_step_candidate_v1
evaluate_fcis_spot_candidate_v1 or its exact replacement
```

The exact path must call `evaluate_settlement_strong_committed_v1` with the same
revalidated `OwnedSettlementV1` and tuple `OwnedIntentV1`. It must not call
`evaluate_settlement_strong_legacy_committed_for_differential_v1`, reconstruct
legacy `Settlement`/`Intent`, or re-admit a mutable post-transition builder.

Keep the legacy evaluator only behind an explicit test/differential entry. Add
a monkeypatch test that makes every legacy behavior callback raise and proves
the exact path still succeeds.

### M4.3 Exact rejected-intent and route consumers

Any rejected-intent scan, route binding, route settlement, and intent-field
reader reached by the exact evaluator must consume the exact owned graph.

Use the closed readers in `src/state/intent_snapshots.py` and the declared
intent registries. Do not use `Intent.get_field`, `vars`, `__dict__`, a broad
mapping protocol, or a projection to mutable `Intent`.

Preserve exact route behavior for:

```text
single-pool exact-in
single-pool exact-out
multi-leg exact-in
multi-leg exact-out
canonical winner and tie-break
nonascending route order rejection
forged totals or legs
quote receipt binding and leg coverage
```

Any mixed legacy/exact helper must be split into an exact helper and a clearly
named legacy oracle unless its closed union is exhaustively checked and the
exact caller cannot reach the legacy branch. Do not enlarge the compatibility
allowlist.

### M4.4 Exact nonce consumer

Target: `src/core/nonce_batch_transition.py`.

Change `validate_and_apply_intent_nonce_batch_committed_v1` so its promoted
input is exactly `tuple[OwnedIntentV1, ...]`. The exact implementation:

1. revalidates the tuple or receives it only from the exact command admission;
2. reads `nonce` and sender from exact owned fields;
3. uses exact integer and exact canonical sender rules;
4. preserves missing/mixed/duplicate/sequence rejection precedence and public
   messages;
5. builds one canonical nonce patch and one return-new committed nonce state;
6. returns no patch or successor on rejection.

Move the current list/dict/`Intent.fields` logic behind an explicitly named
legacy differential oracle. Do not leave `list | tuple`, `dict`, or `Intent` in
the exact function signature or body.

Required nonce cases:

```text
empty batch
nonce-free allowed
nonce-free required
mixed presence
zero and MAX_U32 neighbors
bool and integer subclass
invalid sender
duplicate nonce
gap, reordering, and valid consecutive sequence
multiple senders
replay against advanced state
legacy/exact accept-reject and reason parity
```

### M4.5 Exact fee derivation

Targets in `src/core/fcis_step_evaluator.py`:

```text
_total_settlement_fees_v1
_fee_candidate_v1
```

Consume exact `OwnedSettlementV1` and exact owned fills. Derive the total from
the same settlement instance used by strong replay. Reject invalid/corrupted
owned fee fields before effect allocation. Preserve exact integer addition,
overflow/domain rules, fill order, dust carry, allocation, and public rejection
semantics.

Add a same-candidate test: modifying or substituting any raw settlement after
admission cannot change fees, state, evidence, or rejection.

### M4.6 Exact support-root consumer

Target: `src/state/support_root.py` and direct callers.

The exact committed batch-support and support-root functions must accept:

```text
tuple[OwnedIntentV1, ...]
OwnedMapV1[str, CommittedPoolStateV1]
CommittedBalanceTableV1
CommittedLPTableV1
CommittedNonceTableV1
```

Build a distinct exact support derivation. It uses exact owned intent readers
and exact committed pool readers. It must not call `Intent.get_field`, accept
`Sequence[Intent]`, accept a broad `Mapping`, construct a mutable `PoolState`,
or route through the legacy support helper.

Retain the legacy support relation only as a differential oracle. Prove
byte-for-byte support-root parity for all mounted intent kinds, every optional
field that changes support, create-pool followed by same-batch use, routes,
nonce keys, LP recipients, malformed/rejected commands, and canonical order.

The exact support-root reader must be independent evidence, rather than a
wrapper that delegates to the mixed legacy helper.

### M4.7 Candidate evidence and provenance

Change `_candidate_evidence_v1` and its callers so support roots and every
command-dependent evidence value consume the exact admitted intent tuple.

Bind at least:

```text
algorithm ID and version
execution-context bytes and hash
pre-state root and preimage
post-state root and preimage
canonical snapshot bytes and commitment
support root
```

No evidence value may be recomputed from raw legacy command input after
admission. Add a mutation test that changes every retained legacy source alias
and proves the evidence is unchanged.

### M4.8 Structural gate for exact consumers

Extend `tools/check_fcis_authority_snapshot_contract.py` with a distinct M4
review profile, for example `exact-consumers`, covering at minimum:

```text
src/core/fcis_step_evaluator.py
src/core/nonce_batch_transition.py
src/core/route_settlement.py
src/core/settlement_strong_validator.py
src/state/support_root.py
```

The checker must use AST/dataflow rules, not grep counts. It must prove:

- exact entry annotations or exact runtime-admission assignments;
- one permitted binding for each protected admitted value;
- no alternate return or replay call using raw values;
- no exact call to the legacy differential evaluator;
- no `Intent.get_field`, legacy `Settlement`/`Intent` construction, mutable
  projection, generic copy, or post-admission mutation on the exact path;
- no new unallowlisted broad-admission finding;
- exact nonce, fee, and support-root consumers receive the protected exact
  values.

Mutation tests must inject and kill at least:

```text
ignored admission result
raw and exact path coexistence
rebind after admission
same-line rebind
object/type attribute mutation
legacy differential call after an exact call
raw fee input after exact replay
raw intents passed only to support-root evidence
legacy Intent.get_field hidden behind an alias
```

## Required semantic evidence

Run exact-versus-legacy differential tests over:

- all five mounted spot actions;
- valid, malformed, rejected, route, CoW, create-pool, add/remove liquidity,
  fee, and quote-binding cases;
- nonce sequences and retries;
- stateful quote, settle, reject, retry, and replay sequences;
- canonical snapshot bytes, state root, support root, post-state fields, patch
  bytes, and public errors.

Equality includes acceptance/rejection, rejection precedence, successor values,
roots, canonical bytes, fees, rounding, dust, and output order.

## Acceptance relation

M4 is complete only when:

```text
exact admitted command
-> exact nonce consumer
-> exact settlement consumer
-> exact fee consumer
-> exact support-root/evidence consumer
```

contains no legacy command object or legacy behavior callback, all differential
evidence passes, the exact-consumer structural profile is green, the M3 profiles
remain green, and independent review returns `PASS FOR STACK PROGRESSION`.

## Required commands

At minimum run:

```bash
python3 -m pytest -q \
  tests/core/test_fcis_step_evaluator.py \
  tests/state/test_nonce_batch_transition.py \
  tests/core/test_settlement_strong_validator.py \
  tests/core/test_route_settlement.py \
  tests/core/test_support_root.py \
  tests/integration/test_dex_engine_route_settlement.py \
  tests/integration/test_fcis_spot_shadow.py
python3 tools/check_fcis_authority_snapshot_contract.py --profile state-substrate --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile authority-graph --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-replay --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-consumers --json
bash tools/run_critical_quality_gate.sh
python3 tools/check_production_boundary.py --json
```

Discover renamed test files with `rg --files tests` rather than deleting a
required case. Do not lower a coverage floor.

## Deliverables

- normal source and test commits;
- `docs/research/FCIS_M4_COMPLETION_RECEIPT_V1.json`;
- exact command list and results;
- canonical/state/support-root parity artifact hashes;
- static-checker mutation results;
- independent read-only drift review;
- exact head and GitHub check status;
- explicit M5 blockers and nonclaims.

## Stop conditions

Stop and report a design question if:

- exact and legacy behavior differ on the declared canonical corpus;
- preserving public rejection precedence would require accepting a forbidden
  type or mechanism;
- an owned field needed by a consumer is missing from the frozen schema;
- the authority graph requires a new record, enum, intent kind, or callable
  registry behavior;
- a root or canonical byte changes without a source-pinned migration decision;
- M3 ancestry or a required structural profile is not green.

Do not begin M5. Return exactly:

```text
Exact M4 head:
Required M3 ancestor:
Base and merge base:
Packet receipt SHA-256:
Changed files and symbols:
Requirements satisfied:
Requirements still open:
Negative witnesses retained:
Exact commands and results:
Canonical/state/support-root parity hashes:
Independent review verdict:
GitHub checks at exact head:
Known unrelated failures:
Nonclaims:
Design questions or deviations: none | exact list
```
