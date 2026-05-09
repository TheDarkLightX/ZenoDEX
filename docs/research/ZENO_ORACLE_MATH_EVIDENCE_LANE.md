# ZenoOracle Math Evidence Lane

Status: first replayable math-witness lane, not a production proof package.

The first Julia witness sweep is:

```bash
julia tools/zeno_oracle_math_witness_sweep.jl
```

Current expected receipt:

```text
schema = zenodex.oracle.math_witness_sweep.v1
case_count = 43
failed_count = 0
status = accepted
```

The sweep covers integer witnesses for median deviation boundaries,
zero-scale and equal-value median sanity cases, a bounded grid decomposition
of median deviation into low/high side obligations, monotonic acceptance under
a widened deviation bound, source-cartel concentration, zero-bond dispute
griefing, reward-pool conservation, overpay rejection, reward-cap rejection,
live-economics escrow floor, timelock receipt checks, settlement-execution
receipt-dependency chain acceptance/rejection, receipt-chain chronology
acceptance/rejection for live economics and the production-network release
path, settlement-execution
total matching, drift rejection, component dominance by the computed settlement
grand total, the rule that a budget covering the grand total caps every
component, and preservation of component caps under a larger budget,
cross-module split-brain divergence, epoch-lag rejection, epoch-lag symmetry,
and bounded O5 independence-witness acceptance/rejection. It also checks
settlement-execution receipt admission/rejection for query, totals, asset, and
contract obligations.
Bounded O3 action binding is checked across terminal DAG closure, runtime
binding, and sync-window acceptance, plus rejection witnesses for duplicate
terminal receipts and stale sync windows, rejection witnesses for missing value
binding and wrong consumer action, a bounded witness that widening an accepted
sync window preserves O3 action-binding acceptance, and a witness that composing
accepted sync windows preserves O3 action binding. It also checks a bounded
sync-window composition grid: if source-to-bridge and bridge-to-target epoch
windows are accepted, then the composed source-to-target window is accepted
with the summed lag bound.

The Lean tree already has adjacent checked anchors:

- `lean-mathlib/Proofs/OracleSyncGateSoundness.lean`
- `lean-mathlib/Proofs/OracleBenefitAccounting.lean`
- `lean-mathlib/Proofs/OracleBenefitRiskClasses.lean`
- `lean-mathlib/Proofs/ZenoOracleMathWitness.lean`

`ZenoOracleMathWitness.lean` now includes restricted general arithmetic anchors for
zero-scale and equal-value median deviation, median-deviation decomposition
into low/high side bounds, an iff characterization of sorted
median-deviation acceptance by the two side bounds, monotonic acceptance under
a widened deviation bound, low/high side rejection lemmas, self-divergence,
epoch-lag symmetry, reward-pool bounds, bonded-slash
conservation, live-economics escrow floor arithmetic, timelock execution
obligations, settlement-execution total arithmetic, component dominance by the
settlement total, budget-to-component cap transfer, monotone budget widening,
settlement-execution receipt iff decomposition, and totals/asset/contract drift
rejection, plus receipt-position transitivity/asymmetry, live-economics and
production-network receipt-order acceptance/rejection anchors, and
live-economics receipt-dependency chain projection/rejection anchors. It also
includes Prop-level bridge
anchors for live-economics receipt bundles, terminal DAG closure, runtime
binding, sync-window symmetry/rejection, O3 action binding from
DAG/runtime/sync obligations, iff decompositions for terminal DAG, runtime
binding, and O3 action-binding obligations, direct O3 value-binding and
same-consumer-action projections, rejection of missing DAG dependencies,
content-hash drift, registry-root drift, runtime-state drift, missing value
binding, or wrong consumer action, sync-window widening preservation for O3
action binding, and O3 preservation through sync-window composition. It also
proves epoch-lag triangle composition and Oracle sync-window composition with
summed lag bounds. The O4/O5 Oracle-use
rule now has iff decompositions for O4/O5 bridge obligations and full O5 use:
accepted O3 receipt, ZenoProof acceptance, same query/value/window, same
consumer action, primary O5 claim, distinct verifiers, distinct proof kinds,
shared input/output roots, and DAG closure.
Missing ZenoProof acceptance, same query/value/window binding, distinct
verifiers, distinct proof kinds, shared input/output roots, or DAG closure
contradicts O5 use.

The next proof ladder should turn the remaining Julia cases into restricted Lean
theorems for median/deviation boundaries, budget conservation, executable DAG
closure, typed binding, and production sync-gate use in the live typed
adapters. The current public workflow status lane is documented in
`docs/research/ZENO_ORACLE_WORKFLOW_EVIDENCE_STATUS.md`. ZenoProof now has
public replay profiles for this Julia sweep, the Lean anchor, and the bounded
ESSO/TLA/LTLf Oracle recovery models through
`tools/zenoproof_public_replay_verifier.py`. Deeper Morph, external ESSO/TLC,
and PopperPad evidence should remain internal until each lane has a public
replay command and a stable claim boundary.
