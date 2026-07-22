# Paint-by-Number Implementation Runbook

This runbook is written for a lower-cost implementation agent. Follow the
steps in order. Do not combine #477 and #478. Do not make a design choice when
the specification is silent; stop and return a design question with the exact
file, field, caller, and counterexample.

## 0. Start conditions

1. Work in a clean clone or worktree. Do not use the dirty primary checkout.
2. Read every applicable `AGENTS.md`.
3. Read `ERRATA.md` first. Copy this complete folder into the branch unchanged.
4. Confirm the intended branch and print:

   ```text
   git status --short
   git rev-parse HEAD
   git merge-base HEAD <stack-base>
   ```

5. Run the style map, trust-surface scan, red flags, and design metrics on the
   files listed below.
6. Run the current focused tests once and save the baseline. Existing failures
   are evidence; do not edit tests to erase them.
7. Do not add or modify a GitHub workflow until source and local tests pass.
8. Do not use base64 patches, self-modifying workflows, or CI that pushes code.

## 1. Fixed file layout

### Shared state ownership files

```text
src/state/snapshot_combinators.py
src/state/owned_collections.py
src/state/state_snapshot_values.py
src/state/state_snapshot_schema.py
src/state/state_admission_profile.py
src/state/state_snapshots.py
src/state/state_transitions.py
tools/check_fcis_authority_snapshot_contract.py
tests/state/test_snapshot_combinators.py
tests/state/test_state_admission_profile.py
tests/state/test_state_snapshot_schema_drift.py
tests/core/test_dex_state_immutability.py
tests/tools/test_check_fcis_authority_snapshot_contract.py
```

Remove authoritative imports of `src/state/immutable_collections.py`. Delete
`deep_freeze`, `deep_thaw_json`, `FrozenDict`, and `FrozenList` after all callers
are migrated. If an unrelated non-authoritative caller remains, report it;
do not preserve a dangerous helper for compatibility.

### PR #478 files

```text
src/state/owned_json.py
src/state/intent_schema.py
src/state/intent_snapshots.py
src/core/settlement_schema.py
src/core/settlement_snapshots.py
tests/core/test_authority_snapshot_immutability.py
tests/state/test_owned_json.py
tests/state/test_intent_schema_drift.py
tests/core/test_settlement_schema_drift.py
```

Use existing parser, canonical encoder, DEX core, and integration files only
for the minimal call-site changes required by these types.

## 2. PR #477 implementation sequence

### 2.1 Add failing evidence

Before implementation, add the #477 tests from `TEST_MATRIX.md`. Confirm that
the pinned implementation fails the expected tests. The first commit contains
tests/spec only and is allowed to be red locally.

Required first witnesses:

```text
scalar subclass survives
arbitrary dataclass survives
arbitrary enum survives
hostile deepcopy executes
cycle raises RecursionError
FrozenDict can be reinitialized
FrozenList can be reinitialized
BalanceTable base initializer changes a frozen balance snapshot
LPTable base initializer changes a frozen LP snapshot
perps nested subclass or raw mapping survives
```

Do not add only one representative test. Each mechanism has its own retained
regression.

### 2.2 Implement admission results and limits

Create `snapshot_combinators.py` with only:

- the exact `AdmitCode` enum;
- `AdmitReject` and `AdmitOk`;
- the closed schema tagged sum;
- the limit/context values;
- the exhaustive pure interpreter;
- path formatting for trusted diagnostics.

No domain imports belong in this file except closed enum-tag definitions. Keep
each function under the repository complexity limits. There is no fallback
branch that accepts an unknown schema or value.

### 2.3 Implement owned collections

Create `owned_collections.py`:

- `OwnedEnumV1` and `OwnedMapV1` by composition;
- enum admission copies registry/member ordinals and retains no Python enum;
- built-in tuple for owned sequences;
- one-time constructor/reinitialization guard;
- canonical entries and fresh private index;
- read-only lookup/iteration methods;
- no mutable base class;
- no generic source constructor exposed to authority callers.

Run the collection tests before continuing.

### 2.4 Implement exact committed values

Create the distinct frozen/slotted committed values from
`PR477_STATE_SCHEMA.md`. Authority-bearing readers and transitions accept those
exact types. Do not add a structural protocol that a legacy mutable builder can
satisfy.

### 2.5 Implement balance, LP, nonce, and pool snapshots

In `state_snapshot_schema.py`, declare the exact field schemas and drift
registries. In `state_snapshots.py`, implement:

```text
snapshot_balance_table
snapshot_lp_table
snapshot_nonce_table
snapshot_pool
snapshot_pool_map
```

Delete the old `Frozen*` subclasses. Validate exact internals before calling a
source getter or mutable setter. Do not construct a legacy mutable domain value
inside the admission resolver. Run focused table/pool tests.

### 2.6 Implement optional module snapshots

Implement four explicit functions:

```text
snapshot_vault
snapshot_oracle
snapshot_fee_accumulator
snapshot_perps
```

There is no `snapshot_optional(object)` helper. Implement the complete perps
variant registry and its drift tests before wiring `snapshot_perps` into
`DexState`.

### 2.7 Mount the one production admission profile

Create `state_admission_profile.py` only after every #477 schema and exact
source/owned type binding is declared. It owns:

- the one immutable declarative registry;
- the exhaustive record-construction and semantic-postcondition resolver;
- the exhaustive schema-ID canonical-encoder resolver;
- the exact four-argument `admit(schema_revision, schema_id,
  validated_limits, source)` facade.

The resolver receives only the record tag and an ordered tuple of already
admitted fields. It constructs the named exact owned record, checks its domain
postcondition, and returns that record or raises for a typed
`DOMAIN_INVARIANT` rejection. It cannot normalize or replace an admitted
child. Callers never pass registry or resolver behavior.

Run checker mutation tests proving that a fifth public argument, a
caller-selected binding, an empty registry inventory, a second private-engine
call site, or executable behavior in a registry record all fail closed. Domain
snapshot functions may be mounted only after this facade is green.

### 2.8 Wire DexState atomically

Build all field candidates into local single-assignment bindings. Assign them
to `DexState` only after all admissions and aggregate checks succeed. Keep
field order identical to the normative order in the schema.

Add tests proving a late-field rejection exposes no state and does not mutate
any source builder.

### 2.9 Migrate readers and transitions

Use `rg` to enumerate every call to table mutators, pool field assignment,
`dataclasses.replace`, and old copy helpers.

- authority readers receive exact committed classes;
- mutating paths become pure return-new functions in `state_transitions.py`;
- no public `to_scratch_*` conversion or mutable domain-builder parameter is
  added;
- no caller mutates a committed value and catches the error as control flow;
- an optional private builtin work buffer stays inside one function and has a
  differential test against the return-new reference;
- no compatibility inheritance is reintroduced.

Run focused tests after each subsystem migration rather than changing all
callers at once.

### 2.10 Canonical/root parity

Capture golden canonical snapshots and state/support roots from canonical valid
fixtures at the pinned base. Run the repaired implementation over the same
fixtures and require byte-for-byte/root equality.

The parity fixture must include every optional module and perps market variant,
not only an empty state.

### 2.11 Add the static contract checker

`tools/check_fcis_authority_snapshot_contract.py` must:

1. parse the authority modules with `ast`;
2. reject imports/calls for copy, deepcopy, pickle, reflective dataclass
   admission, and forbidden broad admission;
3. reject `typing.Any` in the authority modules;
4. reject committed classes with mutable bases;
5. verify the known schema/record/enum/variant registry IDs;
6. verify every requirement marked for #477 maps to at least one test;
7. emit deterministic JSON and a nonzero exit on violation.

It must also scan every Python file under `src/` for escape calls/imports of
the private interpreter, registry builder, construction tokens, and owned-map
factory. Checking only the newly added modules is insufficient.

Tests mutate fixtures or temporary source files to prove every checker rule is
live. A grep-only checker is insufficient.

### 2.12 Stop and review #477

Do not begin #478. Commit normal source and tests. Run the gates in section 4,
publish the exact head, and request independent review against every
`FCIS-477-*` item.

## 3. PR #478 implementation sequence

### 3.1 Rebase

Rebase or rebuild #478 on the reviewed final #477 head. Confirm no copy of the
old helper survives. Re-run #477's complete focused suite before changing
#478.

### 3.2 Add failing evidence

Add all #478 tests from `TEST_MATRIX.md` and confirm current failures. Include
intent, signed envelope, candidate settlement, accepted effect, JSON, schema
metadata, bounds, and canonical parity.

### 3.3 Implement owned JSON

Implement only the grammar in `PR478_AUTHORITY_EFFECT_SCHEMA.md`. Reuse the
shared closed combinator interpreter and limits. Add raw-byte duplicate-key and
canonical re-encoding tests at the existing strict decoder edge.

Delete `deep_thaw_json`. Canonical encoders accept owned JSON or explicit fresh
projections only.

### 3.4 Centralize the intent schema

Move common/kind field knowledge from `operations.py` into
`src/state/intent_schema.py`. Parser and snapshot import the same constants and
validators. The parser remains responsible for byte/JSON normalization;
committed admission requires canonical values and does not normalize.

### 3.5 Implement OwnedIntentV1

Delete `FrozenIntent(Intent)`. Implement the distinct owned record, exact source
registry, kind-indexed admission, tuple batch output, and signed-message
encoding. Update signer, relayer, nonce validator, DEX core, and integration
consumers to use the same exact owned value.

### 3.6 Implement owned settlement records

Delete all `Frozen*(mutable base)` settlement classes. Implement exact owned
records and pure candidate/effect construction. Ensure no seal field enters the
dataclass schema and no mutable settlement projection enters the core.

Inventory current event producers. Preserve event payload semantics through
bounded owned JSON and record `EVENT-TYPING-001` as open. Do not invent event
tags in this PR.

### 3.7 Implement OwnedDexEffectsV1

Construct effects from the exact owned settlement used by validation and state
application. Derive/check total fee consistency. Update `DexStepResult` to use
the exact effect type and preserve reject-is-no-output.

### 3.8 Parity and integration

Run signed-message, canonical settlement, effect-plan, state-root, nonce, and
mounted DEX integration parity. Include all intent kinds and a settlement with
every optional fill field/delta/event family.

### 3.9 Stop and review #478

Run all gates. Publish an exact-head review packet. Do not call the PR ready
until #477 and #478 requirements are independently marked `SATISFIED` and all
GitHub checks at that exact head are green or explicitly classified unrelated.

## 4. Required commands

Use the repository environment selected by the branch. At minimum:

```bash
python3 .claude/skills/zenodex-style-map/scripts/which_style.py \
  src/state/snapshot_combinators.py \
  src/state/owned_collections.py \
  src/state/state_snapshots.py \
  src/state/intent_snapshots.py \
  src/core/settlement_snapshots.py

python3 .claude/skills/zenodex-security-analysis/scripts/trust_surface.py
python3 .claude/skills/zenodex-security-analysis/scripts/redflags.py \
  src/state/snapshot_combinators.py \
  src/state/owned_collections.py \
  src/state/state_snapshots.py \
  src/state/intent_snapshots.py \
  src/core/settlement_snapshots.py

python3 .claude/skills/zenodex-refactoring/scripts/design_metrics.py \
  src/state/snapshot_combinators.py \
  src/state/state_snapshots.py \
  src/state/intent_snapshots.py \
  src/core/settlement_snapshots.py --top 20 --coupling

python3 tools/check_fcis_authority_snapshot_contract.py --json
python3 -m ruff check <every changed Python file>
python3 -m ruff format --check <every changed Python file>
python3 -m mypy <focused changed modules>
python3 -m pytest -q \
  tests/state/test_snapshot_combinators.py \
  tests/state/test_state_snapshot_schema_drift.py \
  tests/core/test_dex_state_immutability.py \
  tests/tools/test_check_fcis_authority_snapshot_contract.py
```

For #478 add:

```bash
python3 -m pytest -q \
  tests/state/test_owned_json.py \
  tests/state/test_intent_schema_drift.py \
  tests/core/test_settlement_schema_drift.py \
  tests/core/test_authority_snapshot_immutability.py
```

Then run mounted consumers and the critical gate:

```bash
python3 -m pytest -q \
  tests/core/test_batch_clearing.py \
  tests/core/test_dex_step.py \
  tests/integration/test_dex_engine_helpers.py \
  tests/integration/test_perp_engine.py

bash tools/run_critical_quality_gate.sh
python3 tools/check_production_boundary.py --json
```

If a named test file differs on the branch, locate the exact equivalent and
record the replacement. Do not silently omit a semantic lane.

## 5. Mandatory stop conditions

Stop implementation and report instead of guessing when:

- a current canonical valid fixture violates the frozen schema;
- a field lacks a source-pinned semantic bound and the code change would invent
  one;
- a consumer requires a mutator on a committed value;
- canonical bytes or roots change for canonical valid input;
- parser, runtime, proof guest, or generated reference disagree;
- a new intent/event/perps variant is found outside the registry;
- a required call site cannot be converted without changing economics,
  ordering, rounding, rejection, or authority;
- an unrelated existing test failure blocks evidence classification;
- a context refresh, rebase, branch switch, or manual reconstruction occurs
  without running `CONTEXT_DRIFT_PROTOCOL.md`.

## 6. Implementation handoff report

Return exactly:

```text
Exact head:
Base head:
Changed files:
Requirement IDs implemented:
Requirement IDs still open:
Counterexamples observed failing before repair:
Exact commands and results:
Canonical/root parity artifacts:
GitHub checks:
Known unrelated failures:
Nonclaims:
Design questions or deviations: none | listed with IDs
```

Do not use “all good”, “should work”, or “merge ready” without the exact-head
evidence above.
