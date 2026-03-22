# ZenoDEX Phase 2 Ratchet Backlog

This document begins after the current ShapeForge candidate targets are green.

It is not a new shape-discovery note.
It is a ratchet plan: freeze the achieved audited-domain shape, make regressions hard, and shift research budget toward witness-carrying decisions, bounded liveness, cross-layer parity, and adversarial stress.

Current baseline:

- `shape_pp_candidate_v1`: `10/10`, `blocked=0`
- `dex_kernel_candidate_v1`: `6/6`, `blocked=0`
- `runtime_boundary_candidate_v1`: `5/5`, `blocked=0`

Authoritative sources:

- `docs/zenodex/shapeforge_promoted/zenodex_target_shapes.seed.json`
- `docs/zenodex/shapeforge_promoted/zenodex_world_model.seed.json`
- `docs/zenodex/shapeforge_promoted/zenodex_negative_knowledge.seed.json`
- `docs/zenodex/SHAPEFORGE_TARGET_SHAPES.md`

Non-goals for this phase:

- do not silently widen the public claim beyond the audited domain
- do not mutate `src/core/` exact-out selection policy before witness, parity, and shadow gates are clean
- do not replace negative knowledge with optimism; narrow it only when a stronger scoped replacement is actually replayable

## Workstreams

## 1. Release Governance

### RG-1. Freeze `SHAPE_V1`

Deliverable:

- `docs/zenodex/SHAPE_V1.md`

Required contents:

- audited-domain statement of scope
- one clause row per `Shape++` requirement
- proving artifact
- checker command
- replay artifact
- release gate
- domain-of-validity note

Acceptance:

- every `Shape++` clause has a concrete artifact reference
- every artifact is replayable or checkable by command
- public claim explicitly says `audited domain D_v1`, not “global” or “fully solved”

### RG-2. CI ratchet gate

Deliverable:

- release CI job that fails if any of these regress:
  - `python3 tools/shapeforge_validate.py docs/zenodex/shapeforge_promoted/zenodex_target_shapes.seed.json`
  - `python3 tools/shapeforge_target_shape_eval.py docs/zenodex/shapeforge_promoted/zenodex_target_shapes.seed.json`

Acceptance:

- any drop from `10/10`, `6/6`, or `5/5` fails CI
- any new blocker on the candidate target shapes fails CI

### RG-3. Negative-knowledge ratchet policy

Deliverable:

- rule text in docs plus CI lint if needed

Rule:

- every narrowed or retired blocker must name:
  - the stronger scoped replacement claim
  - the replay pointer
  - the exact domain that remains excluded

Acceptance:

- blocker edits cannot remove falsifier history without replacement claim text

## 2. Certificates

### C-1. `DecisionWitness` schema

Deliverable:

- one shared witness schema for:
  - exact-in winners
  - exact-out winners
  - batch winners
  - settlement steps

Minimum fields:

- state binding
- request binding
- quote and epoch binding
- expiry
- feasibility payload
- canonical key
- accounting receipt
- optional proof payload

Normal form:

```text
solver(input, state) -> (decision, witness)
checker(input, state, decision, witness) -> accept | reject
```

Acceptance:

- checker is smaller and more stable than solver
- witness schema is replayable at the integration boundary
- settlement trusts the checker plus witness, not the search procedure

### C-2. Exact-in witness adapter

Deliverable:

- adapter from exact-in canonical winner surfaces into `DecisionWitness`

Status:

- not yet promoted on clean `main`
- current clean tree still lacks `src/integration/decision_witness.py`
- current clean tree still lacks `tests/integration/test_decision_witness_adapters.py`

Acceptance:

- witness checker replays the current exact-in route-key winner relation

### C-3. Exact-out witness adapter

Deliverable:

- adapter from repaired exact-out bounded winner surfaces into `DecisionWitness`

Status:

- not yet promoted on clean `main`
- current clean tree still lacks `src/integration/decision_witness.py`
- current clean tree still lacks `tests/integration/test_decision_witness_adapters.py`

Acceptance:

- witness checker replays the repaired bounded exact-out winner relation
- default runtime remains shadow-only until parity and stress gates are clean

### C-4. Settlement witness adapter

Deliverable:

- settlement end-to-end certificate packet mapped into `DecisionWitness`

Status:

- not yet promoted on clean `main`
- current clean tree still lacks `src/integration/decision_witness.py`
- current clean tree still lacks `tests/integration/test_decision_witness_adapters.py`

Acceptance:

- witness carries canonical deltas, full-price-rails result, and value-lane result

## 3. Liveness

### L-1. Audited-bounds liveness Tau contract

Deliverable:

- `src/tau_specs/recommended/optimizer_audited_bounds_liveness_v1.tau`
- `src/tau_specs/recommended/optimizer_audited_bounds_liveness_v2.tau`
- `src/kernels/dex/optimizer_audited_bounds_liveness_v2.yaml`
- `src/integration/exact_out_route_certificate.py` (`ExactOutManyPoolAdaptiveLivenessPacket`)

Starting substrate:

- `src/kernels/dex/spec_quality_assessment_v1.yaml`

Bounded claims to encode:

```text
FeasibleUnderBounds(req, σ) -> ◇ Returned(req)
```

```text
ValidWitness(w, σ) ∧ BeforeExpiry(w) -> ◇ Settled(w) ∨ ◇ RejectedWithReason(w)
```

```text
ContinuouslyEnabled(req) ∧ FairScheduling -> ◇ Accepted(req)
```

```text
OracleHealthyAgain -> ◇ RiskyOpsReenabled
```

Acceptance:

- fail-closed bounded contract exists
- replay harness can produce pass or reject-with-reason outcomes
- scope stays audited and bounded

Status note:

- clean `main` does not yet ship the dedicated audited-bounds liveness Tau/ESSO carriers listed above
- clean `main` also does not yet ship the settlement witness lifecycle carrier
- the current clean release posture is still bounded certificate replay on the promoted exact-out and settlement surfaces, not a dedicated liveness contract with accept-or-reject outcomes

### L-2. No-spurious-failure replay checks

Deliverable:

- replay checks on the audited routing surfaces for “feasible under bounds but returned nothing”

Acceptance:

- no spurious failures on the claimed audited domain

Status note:

- the opt-in adaptive exact-out lane is implemented
- the bounded three-pool, four-pool, and five-pool supported-family receipts are replayable from the new adaptive benchmark surface
- the remaining gap is no longer the audited benchmark gate; it is broader liveness theory outside this bounded exact-out lane

## 4. Parity

### P-1. `PARITY_V1` release gate

Deliverable:

- parity gate requiring:

```text
same input + same state + same witness
-> same admissibility
∧ same winner
∧ same accounting
∧ same post-state
```

Layers:

- Python runtime
- Tau gate
- proof-side checker
- replay harness

Replay classes:

- golden traces
- adversarial traces
- upgrade-diff traces

Acceptance:

- release fails on any parity mismatch in promoted lanes

## 5. Stress

### S-1. Canonical plateau pack

Targets:

- tied winners
- plateau minimizers
- equal-output routes with different leg patterns

Goal:

- prove or falsify whether canonicality is semantic, not merely procedural

### S-2. Dust-and-carry pack

Targets:

- rounding boundaries
- tiny exact-in and exact-out requests
- fee dust accumulation
- LP mint and burn edges

Goal:

- stress exact accounting at the smallest scales

### S-3. Oracle-divergence pack

Targets:

- stale-but-close prices
- lag asymmetry
- pending versus active mismatch
- cross-module disagreement

Goal:

- turn current oracle safety contracts into stronger replay stress

### S-4. Liquidation-cascade pack

Targets:

- mark shocks
- liquidation waves
- AMM depth erosion
- second-wave liquidations

Goal:

- make systemic containment a scenario object, not only a local guard

### S-5. Batch-welfare pack

Targets:

- batch versus continuous processing
- welfare
- fairness
- ordering sensitivity

Goal:

- create the first benchmark-relative welfare floor scenario

### S-6. Curve-admission pack

Targets:

- every new curve family before canonical-router admission

Goal:

- curve extensibility remains fail-closed

## 6. Parameter Synthesis

### PS-1. `ParameterSynthesisReceipt`

Deliverable:

- `src/integration/optimizer_parameter_synthesis_receipt.py`

Receipt contents:

- chosen knobs
- admissible search bounds
- benchmark reference
- evidence digest
- replay metadata

Acceptance:

- any suggested parameter move is evidence-carrying and replayable

## Sequencing

Recommended order:

1. `RG-1` Freeze `SHAPE_V1`
2. `RG-2` CI ratchet gate
3. `C-1` `DecisionWitness` schema
4. `L-1` audited-bounds liveness Tau contract
5. `P-1` `PARITY_V1`
6. `S-1` and `S-2`
7. `S-3` and `S-4`
8. `S-5`
9. `PS-1`

## Stop conditions

Stop and reassess if any of the following occur:

- target-shape support drops below the current baseline
- a new blocker appears on the promoted candidate target shapes
- a witness checker becomes more complex than the solver path it is supposed to certify
- liveness claims require widening the audited-domain scope without new evidence

## Phase 2 thesis

The question is no longer:

```text
What shape should the DEX have?
```

It is now:

```text
How do we make the achieved audited-domain shape hard to silently lose?
```
