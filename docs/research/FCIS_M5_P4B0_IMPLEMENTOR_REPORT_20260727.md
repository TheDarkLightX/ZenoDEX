# FCIS M5-P4B0 Implementor Report

## Result

```text
outcome: M5_P4B0_REFINEMENT_EVIDENCE_ONLY
promotion verdict: BLOCKED
mounted authority changed: no
```

This checkpoint replaces the rejected P4B0 attempts with a directional,
source-bound refinement decision over the 24 frozen P4A fixtures. It does not
authorize P4B, P5, or M6 mounting.

Checkpoint ancestry:

```text
required ancestor: 09bd121f3c0194f0bead2eb8b1230657b74e2ae6
P4B0-A: cb8748c8f  close refinement admission and policy
P4B0-B: adc3eb4481c9c219b75f14943474269d7db23719
P4B0-C: the commit containing this report and generated artifact
```

## Changed

P4B0-A defines:

- exact final frozen evidence values;
- one strict canonical JSON parser engine with code-owned byte profiles;
- closed combinator schemas, including `ExactProduct` for fixed heterogeneous
  values;
- exact bytes-to-owned admission;
- source-owned command, rejection, state-projection, exact-only-field, and
  version-delta registries.

P4B0-B defines:

- the total `RefinesV1 | MismatchV1 | InvalidEvidenceV1` evaluator;
- same-command, same-pre-state, and same-context checks before comparison;
- explicit rejection mapping and rejection-receipt checks;
- comparison of all eight semantic state fields;
- settlement, fee, dust, nonce, replay, effects, patch, receipt, bundle, and
  outbox consistency checks;
- recomputation of state, patch, plan, receipt, bundle, nonce-table, effect
  identity, and idempotency roots or hashes;
- fail-closed cross-candidate and hostile nested-mutation handling.

P4B0-C defines:

- deterministic artifact generation from the frozen P4A differential input;
- a fail-closed checker that independently rebuilds every decision;
- normal and `--require-all-refine` promotion modes;
- 24 named mutation families and 33 independently rehashed artifact mutants;
- no-mount and source-manifest tests.

## Invariant and authority impact

The new modules are unmounted evidence code. `src/core/dex.py` is unchanged and
does not import the refinement evaluator.

Ingress is:

```text
canonical bytes
  -> duplicate-aware bounded parser
  -> closed combinator schema
  -> exact owned observation pair
  -> pure refinement decision
  -> canonical source-pinned artifact
```

The aggregate P4A evidence file has a separate fixed 2,000,000-byte limit. It
uses the same parser implementation as authority observations. Callers cannot
select a parser, constructor, schema registry, policy, or limit.

The generated artifact binds these seven source files:

```text
src/core/fcis_legacy_refinement.py
src/core/fcis_legacy_refinement_admission.py
src/core/fcis_legacy_refinement_policy.py
src/core/fcis_legacy_refinement_schema.py
src/core/fcis_legacy_refinement_values.py
tools/build_fcis_m5_p4b0_refinement.py
tools/check_fcis_m5_p4b0_refinement.py
```

Artifact identifiers:

```text
artifact_sha256:
  0x46011b77c0114f2dd1246056333e9224fc27aa01e03b53182b67155279103b87
policy_hash:
  0x8abf8cda4d86a5fb7807ae5f4aac887ec66843fdababba9de80c173d554f32cc
```

## Refinement result

```text
fixtures:          24
RefinesV1:         21
MismatchV1:         3
InvalidEvidenceV1:  0
```

The three genuine mismatches are:

```text
add_liquidity_boundary_valid
add_liquidity_smallest_accepted
create_pool_smallest_accepted
```

Each mismatch has:

```text
code: state_field_mismatch
path: next_state.lp_balances
```

The artifact preserves these mismatches. Normal validation accepts the honest
`BLOCKED` artifact. `--require-all-refine` exits nonzero.

## Evidence

Focused executable evidence:

```text
386 passed in 85.49s
```

This includes admission/parser boundaries, all 24 fixture decisions, rejection
mapping, eight-field state mutations, economics, patch atomicity, receipt and
bundle recomputation, replay and outbox attacks, 33 rehashed semantic artifact
mutants, promotion gates, no-mount checks, and the structural checker mutation
suite.

Additional evidence:

- Ruff: passed on the P4B0 source, tools, and tests.
- mypy: passed on the P4B0 source, tools, and tests.
- `state-substrate`: `ok=true`, zero violations.
- `authority-graph`: `ok=true`, zero violations.
- `exact-replay`: `ok=true`, compatibility findings only.
- `exact-consumers`: `ok=true`, compatibility findings only.
- production-boundary audit: `ok=true`.
- security red-flag scan: zero findings across 10 changed files.
- frozen P4A input diff: empty.
- all 33 required packet test IDs occur in executable tests.
- artifact generation repeated byte-identically.
- `git diff --check`: passed.

The `final-mount` profile correctly remains closed with 79 inherited
violations:

```text
BROAD_ADMISSION             50
SNAPSHOT_SEAL_FLAG          12
OPEN_AUTHORITY_TYPE          5
MUTABLE_BASE                 4
FORBIDDEN_RECONSTRUCTION     4
GENERIC_DEEP_FREEZE          3
COERCIVE_CONTAINER_COPY      1
```

## Why the implementation is large

P4B0 covers a cross-product of 24 fixtures, seven command variants, accepted
and rejected outcomes, eight state fields, and every candidate output. The
majority of source is declarative closed schema, exact projection, and
independent recomputation logic. Compact generic mechanisms such as `Any`,
`deepcopy`, generic deep-freeze, input-selected constructors, or permissive
mapping admission are prohibited because they previously allowed parallel
authority systems to drift.

The design-metrics tool flags the schema, admission, and evaluator modules as
large. This is retained as a review risk. Splitting them is safe only when each
new module preserves one schema registry, one parser engine, and one source-owned
policy. File size is not being reduced by moving validation into hidden generic
helpers.

## Commands not run

The critical quality gate did not start because the environment lacks
`pytest_cov`:

```text
error: missing python module 'pytest_cov'
```

The full release gate, Rust parity, Tau, Lean, ESSO, RISC0, datastore
linearizability, crash recovery, and external-delivery lanes were not promoted
by this checkpoint.

## Residual risk

- Three LP-state mismatches prohibit refinement promotion.
- The frozen spot fixture profile requires `vault`, `oracle`, and `perps` to be
  null. Their non-null forms fail admission here; populated-module refinement
  needs a later profile with source-pinned fixtures and schemas.
- The reference evidence checker establishes deterministic Python refinement.
  It is not Python/Rust byte-parity evidence.
- The three large authority modules remain review hotspots.
- The 79 final-mount violations remain the explicit migration surface for the
  later authority-switch checkpoint.

## Next safest step

Independently review this exact checkpoint and reproduce the mandatory attacks.
Then repair the three LP semantics mismatches in a separate unmounted
checkpoint. Do not switch authority until every frozen fixture refines and the
final-mount, cross-language, verifier, and datastore gates are ready.
