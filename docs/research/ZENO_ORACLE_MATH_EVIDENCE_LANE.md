# ZenoOracle Math Evidence Lane

Status: first replayable math-witness lane, not a production proof package.

The first Julia witness sweep is:

```bash
julia tools/zeno_oracle_math_witness_sweep.jl
```

Current expected receipt:

```text
schema = zenodex.oracle.math_witness_sweep.v1
case_count = 23
failed_count = 0
status = accepted
```

The sweep covers first-shell integer witnesses for median deviation boundaries,
zero-scale and equal-value median sanity cases, source-cartel concentration,
zero-bond dispute griefing, reward-pool conservation, overpay rejection,
reward-cap rejection, live-economics escrow floor, timelock receipt checks,
settlement-execution total matching and drift rejection, cross-module
split-brain divergence, epoch-lag rejection, epoch-lag symmetry, and bounded
O5 independence-witness acceptance/rejection. It also now checks bounded O3
action binding across terminal DAG closure, runtime binding, and sync-window
acceptance, plus rejection witnesses for duplicate terminal receipts and stale
sync windows.

The Lean tree already has adjacent checked anchors:

- `lean-mathlib/Proofs/OracleSyncGateSoundness.lean`
- `lean-mathlib/Proofs/OracleBenefitAccounting.lean`
- `lean-mathlib/Proofs/OracleBenefitRiskClasses.lean`
- `lean-mathlib/Proofs/ZenoOracleMathWitness.lean`

`ZenoOracleMathWitness.lean` now includes small general arithmetic anchors for
zero-scale and equal-value median deviation, self-divergence, epoch-lag
symmetry, reward-pool bounds, bonded-slash conservation, live-economics escrow
floor arithmetic, timelock execution obligations, settlement-execution total
arithmetic, and settlement-execution receipt projections. It also includes
Prop-level bridge anchors for live-economics receipt bundles, terminal DAG
closure, runtime binding, sync-window symmetry/rejection, O3 action binding
from DAG/runtime/sync obligations, and the O4/O5 Oracle-use rule: O4/O5 use
projects to accepted O3 receipt binding and same consumer action, and O5 use
projects to an independence witness with distinct verifiers and DAG closure.
Missing distinct verifiers or missing DAG closure contradicts O5 use.

The next proof ladder should turn the Julia cases into restricted Lean
theorems for median/deviation boundaries, budget conservation, executable DAG
closure, typed binding, and production sync-gate composition. The current public workflow status lane is documented in
`docs/research/ZENO_ORACLE_WORKFLOW_EVIDENCE_STATUS.md`. ZenoProof now has
public replay profiles for this Julia sweep and Lean anchor through
`tools/zenoproof_public_replay_verifier.py`; deeper Morph, ESSO, TLA/LTLf,
and PopperPad evidence should remain internal until each lane has a public
replay command and a stable claim boundary.
