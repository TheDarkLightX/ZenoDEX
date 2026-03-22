# ShapeForge Target Shapes

This note records candidate target shapes for ZenoDex.

These are useful because ShapeForge is not only a baseline world model. It is
also a reasoning substrate for asking:

- what shape does the current evidence suggest
- what stronger shape would be worth steering toward
- which clauses are already supported
- which clauses are only partially supported
- which clauses are blocked by missing proofs, missing certificates, or missing
  runtime promotion

Use `docs/zenodex/SHAPEFORGE_META_NOTATION.md` for the formal notation of
support, gaps, blocked promotions, target refinement, and scenario deltas.

Target shapes are therefore aspirational by default.

They are not required truths unless every clause is supported by the current
baseline at the claimed evidence level.

## 1. Baseline vs Target

Use the following distinction:

```text
BaselineShape(W)
```

means:

```text
the current machine-readable world model supports these clauses now
```

while:

```text
TargetShape(T, W, E)
```

means:

```text
T is a candidate ideal shape for the system,
typed against the current world model W and evidence posture E
```

The useful outputs are:

```text
SupportedClauses(T, W, E)
GapClauses(T, W, E)
BlockedPromotions(T, W, E)
```

## 2. Candidate Set

ShapeForge should not reason from one target shape only.

The machine-readable target-shape artifact now carries at least three candidate
ideals:

- `Shape++`: broad aspirational compression of canonicality, accounting,
  settlement, oracle boundaries, and replay parity.
- `DEX Kernel Assurance`: narrower target focused on optimizer canonicality,
  exact accounting, anti-fragmentation, and proof-carrying DEX boundaries.
- `Runtime Boundary Assurance`: narrower target focused on settlement, oracle
  synchronization, replay parity, and public certificate surfaces.

This matters because different next steps may improve different targets by
different amounts. ShapeForge should therefore be able to compare:

```text
Eval(W, T1)
Eval(W, T2)
T1 ⪯ T2
T1 ⟂ T2
```

instead of asking only whether one favored slogan is already true.

## 3. Candidate: Shape++

One strong candidate target shape is:

```text
Shape++
:=
  CBCValidity
  ∧ UniqueCanonicalWinnerEverywhere
  ∧ ExactFeeAwareAccounting
  ∧ ValueAwareSettlementSafety
  ∧ ProofCarryingOptimizerCertificates
  ∧ AntiFragmentationByTheorem
  ∧ NonCommutativityQuarantine
  ∧ OracleDivergenceSafety
  ∧ LiquidationSpiralContainment
  ∧ CrossLayerReplayParity
```

This is a good target shape because it compresses several recurring ZenoDex
themes:

- invalid states should be hard to represent
- optimizers should produce unique canonical winners
- exact accounting should win over approximate folklore when the claim is exact
- settlement should be guarded by replayable certificates
- cross-module and cross-layer drift should be explicit and fail-closed

But `Shape++` is not a current baseline theorem.

It is a target candidate with mixed clause status.

## 4. Other Candidate Targets

Two narrower candidates are useful for planning:

```text
DEXKernelAssurance
:=
  CBCValidity
  ∧ UniqueCanonicalWinnerEverywhere
  ∧ ExactFeeAwareAccounting
  ∧ ProofCarryingOptimizerCertificates
  ∧ AntiFragmentationByTheorem
  ∧ NonCommutativityQuarantine
```

```text
RuntimeBoundaryAssurance
:=
  ValueAwareSettlementSafety
  ∧ ProofCarryingOptimizerCertificates
  ∧ OracleDivergenceSafety
  ∧ CrossLayerReplayParity
  ∧ NonCommutativityQuarantine
```

These are useful because:

- `DEXKernelAssurance` tells us whether optimizer and accounting work are
  cohering.
- `RuntimeBoundaryAssurance` tells us whether certificates, settlement,
  oracles, and replay parity are cohering.
- `Shape++` remains the broader attractor that may refine both.

## 5. Current Reading

The current repo supports the following reading:

- `CBCValidity`: supported for the batch `ValidOutcome` surface, not yet a
  system-wide CBC theorem.
- `UniqueCanonicalWinnerEverywhere`: partially supported. Batch is proved,
  exact-in routing is proof-backed on its emitted-domain candidate surface, and
  exact-out is proved on the repaired bounded audited lane, but broader
  all-optimizer generalization remains open.
- `ExactFeeAwareAccounting`: partially supported. Exact fee carry,
  fee-aware same-pool dominance, and fee-aware exact batch K-gap accounting are
  all proved, but they are not yet one universal theorem across every execution
  layer.
- `ValueAwareSettlementSafety`: partially supported through settlement
  contract/certificate surfaces.
- `ProofCarryingOptimizerCertificates`: partially supported. Exact-in and
  exact-out certificate lanes are proof-backed on their promoted bounded
  surfaces, but they are not universal optimizer acceptance gates.
- `AntiFragmentationByTheorem`: supported on both zero-fee and fee-aware
  same-pool same-direction proved domains; broader cross-pool or
  heterogeneous-rate fragmentation claims remain open.
- `NonCommutativityQuarantine`: supported as a negative guardrail.
- `OracleDivergenceSafety`: partially supported. Pending-vs-committed mismatch
  and cross-module sync barriers both exist, but not as one fully promoted
  theorem.
- `LiquidationSpiralContainment`: too broad as stated. The current proved shape
  is closer to bounded-move solvency and deterministic liquidation posture.
- `CrossLayerReplayParity`: partially supported as an assurance discipline over
  active Tau specs, not as a direct economic invariant.

## 6. Why Keep It

The point of `Shape++` is not to force the repo into one slogan.

The point is to give ShapeForge one plausible attractor:

```text
If we kept strengthening the DEX in the same direction,
what shape would we be moving toward?
```

That is a good use of ShapeForge because shape is not obtained only from
deduction. It is also discovered from:

- repeated counterexamples
- blocked promotions
- pattern recurrence across proofs and code
- analogies between modules
- compression of many local design decisions into a smaller set of laws

## 7. Current Best Use

Treat `Shape++` as:

- a candidate target shape
- a comparison point against the current baseline
- a backlog generator for the next promotion steps

Do not treat it as:

- a current theorem
- a required contract for every module today
- a license to overclaim unsupported clauses

## 8. Immediate ShapeForge Uses

Under the current baseline, `Shape++` mainly points to the following next work:

1. Widen the now proved exact-out full-allocation lane from the audited selected-domain CPMM surface into broader runtime/certificate packaging and generator-completeness coverage.
2. Keep widening proof-carrying optimizer certificate surfaces.
3. Strengthen settlement from opt-in contract posture toward a more complete
   default proof/certificate posture.
4. Raise active Tau replay parity from review-packet completeness toward
   semantic-contract completeness.
5. Keep cross-module oracle divergence explicit when modules share economic
   assumptions.

## 9. Matrix-Derived Theorem/Contract Backlog

The matrix-derived `Shape++` reading is slightly coarser than the ten-clause
candidate above.

It compresses `CBCValidity`, `AntiFragmentationByTheorem`, and
`NonCommutativityQuarantine` into broader promotion lanes.

The goal here is not to relabel the current baseline.

The goal is to assign each stronger clause one concrete repo object that can
carry the next promotion without overclaiming current proof scope.

### 9.1 Clause-to-object map

| Matrix clause | Lane | Repo object | Posture | Why this object |
| --- | --- | --- | --- | --- |
| Universal canonicality | Lean theorem | `lean-mathlib/Proofs/ZenoDEXExactOutCanonicalMinimizer.lean` (`exists_unique_canonical`) | Current, scoped | Strongest current uniqueness theorem for a finite emitted candidate set under an explicit total key; the generalization target is to reuse this shape across every optimizer surface. |
| Exact fee-aware accounting | Lean theorem family | `lean-mathlib/Proofs/FeeAwareBatchKGap.lean` (`feeBatch_K_gap_sum`) plus `lean-mathlib/Proofs/FeeAwareAntiFragmentation.lean` (`fee_aware_anti_fragmentation`) | Current, stronger but still scoped | Current best proof pair: fee-aware same-pool dominance plus exact fee-in-pool batch K-gap telescoping. The remaining gap is still one promoted cross-layer runtime object, not the absence of any fee-aware theorem. |
| Settlement that is structurally safe and economically meaningful | Runtime receipt type | `src/integration/settlement_strong_certificate.py` (`SettlementStrongCertificate`) | Current, partial | Canonical delta commitments, proof/binding flags, and the optional price-history packet already live in one fail-closed boundary object. |
| Optimizer outputs become proof-carrying objects | Tau contract | `src/tau_specs/recommended/argmin_stream_certificate_v1.tau` | Current | Most reusable public certificate surface for “winner is the canonical argmin over emitted candidates”; it is the right shell to widen before widening heuristics. |
| Stronger oracle safety | Runtime receipt type | `src/integration/zusd_oracle_contracts.py` (`ZUSDCrossModuleOracleSyncContract`) | Current, partial | Best current carrier for composed-oracle safety because it binds divergence, epoch lag, and the fail-closed Tau witness into one packet. |
| Systemic containment | Tau contract | `src/tau_specs/recommended/perp_risk_envelope_proof_gate_v1.tau` | Current, partial | Closest current public containment object: bounded mark/oracle gaps, open-interest cap, funding cap, liquidation-penalty cap, insurance floor, and proof/binding gates are checked together. |
| Cross-layer parity | Runtime receipt type | `tools/build_tau_active_semantic_parity_contract.py` (`TauActiveSemanticParityContract`) | Current, assurance-only | This packet already records whether active Tau specs meet the declared semantic source rank, which is the concrete carrier for parity claims. |
| Safer curve extensibility | Tau contract | `src/tau_specs/recommended/service_proof_registry_v1.tau` | Current, partial | Best current extensibility anchor because new service or curve proof lanes can be admitted only through a whitelisted verifier registry instead of implicit trust. |

These anchors are intentionally the strongest current carriers.

They are not claims that the whole matrix clause is already proved end-to-end.

Additional promoted helper theorems now exist but remain staged rather than
counted as direct target-shape support:

- `lean-mathlib/Proofs/GaloisSplitCertificate.lean`
  Useful for future bounded split-routing certificates when the objective can
  be shown discretely concave.
- `lean-mathlib/Proofs/RoundingErrorBound.lean`
  Useful for route-quality envelopes and quote-budget reasoning, not yet exact
  route optimality.
- `lean-mathlib/Proofs/ArbitrageCertificate.lean`
  Useful for future weighted route-graph or cross-venue potential packets, but
  not yet attached to a current ZenoDEX runtime graph surface.

### 9.2 Missing gaps that still need first-class objects

The following backlog objects are either current bounded carriers for still-open
gaps or proposed targets where the carrier is still missing.

| Missing gap | Lane | Backlog object | Posture | Why a new object is needed |
| --- | --- | --- | --- | --- |
| Liveness under audited bounds | Tau contract + ESSO shell + runtime contract | `src/tau_specs/recommended/optimizer_audited_bounds_liveness_v1.tau`; `src/kernels/dex/optimizer_audited_bounds_liveness_v1.yaml`; `src/tau_specs/recommended/optimizer_audited_bounds_liveness_v2.tau`; `src/kernels/dex/optimizer_audited_bounds_liveness_v2.yaml`; `src/integration/exact_out_route_certificate.py` (`ExactOutManyPoolAuditedBoundsContract`, `ExactOutManyPoolAdaptiveLivenessPacket`) | Proposed | Clean `main` does not yet ship the dedicated audited-bounds liveness carriers listed here. The current promoted exact-out and settlement surfaces provide bounded certificate replay, but not a dedicated liveness contract with total accept-or-reject outcomes on the audited domain. |
| Benchmark-relative welfare floors | Replay scenario | `docs/zenodex/shapeforge_promoted/scenario_corpus.seed.json` (`scenario_benchmark_relative_welfare_floor_v1`) | Proposed | A scenario is the safest first artifact because the floor claim is comparative and should be framed against explicit benchmark policies before it becomes a hard contract. |
| Parameter synthesis | Runtime receipt type | `src/integration/optimizer_parameter_synthesis_receipt.py` (`ParameterSynthesisReceipt`) | Proposed | The missing object is a replayable packet that binds chosen knobs, admissible search bounds, benchmark reference, and evidence digest for any suggested parameter move. |

### 9.3 Highest-value proposed scenario pack

If only one replay pack is added next, it should live under
`docs/zenodex/shapeforge_promoted/scenario_corpus.seed.json` and contain:

- `scenario_exact_out_many_pool_generator_gap_v1`
- `scenario_settlement_compact_bundle_scope_gap_v1`
- `scenario_cross_module_oracle_split_brain_v1`
- `scenario_perp_risk_envelope_containment_v1`
- `scenario_curve_registry_fail_closed_v1`

This pack is the highest-value first addition because it exercises the largest
remaining evidence boundaries:

- emitted-candidate canonicality versus generator completeness
- compact settlement receipts versus full price-rail semantics
- local oracle validity versus shared-world oracle sync
- bounded perps containment versus broad spiral claims
- extensibility by explicit registry versus implicit service trust

## 10. Tooling

The machine-readable comparison surface lives in:

- `docs/zenodex/shapeforge_promoted/zenodex_target_shapes.seed.json`
- `tools/shapeforge_target_shape_eval.py`
- `tools/shapeforge_target_shape_compare.py`

So the practical workflow is:

```text
Eval(W, T)
Compare(T1, T2)
choose next improvement by the shape delta it buys
```
