# ZenoOracle Math Evidence Lane

Status: first replayable math-witness lane, not a production proof package.

The first Julia witness sweep is:

```bash
julia tools/zeno_oracle_math_witness_sweep.jl
```

Current expected receipt:

```text
schema = zenodex.oracle.math_witness_sweep.v1
case_count = 10
failed_count = 0
status = accepted
```

The sweep covers first-shell integer witnesses for median deviation boundaries,
source-cartel concentration, zero-bond dispute griefing, reward-pool
conservation and overpay rejection, cross-module split-brain divergence and
epoch-lag rejection, and bounded O5 independence-witness acceptance/rejection.

The Lean tree already has adjacent checked anchors:

- `lean-mathlib/Proofs/OracleSyncGateSoundness.lean`
- `lean-mathlib/Proofs/OracleBenefitAccounting.lean`
- `lean-mathlib/Proofs/OracleBenefitRiskClasses.lean`
- `lean-mathlib/Proofs/ZenoOracleMathWitness.lean`

`ZenoOracleMathWitness.lean` now also includes a small Prop-level bridge for
the O4/O5 Oracle-use rule: O4/O5 use projects to accepted O3 receipt binding
and same consumer action, and O5 use projects to an independence witness with
distinct verifiers and DAG closure. Missing distinct verifiers or missing DAG
closure contradicts O5 use.

The next proof ladder should turn the Julia cases into restricted Lean
theorems for median/deviation boundaries, budget conservation, executable DAG
closure, typed binding, and sync-gate composition. The current public workflow status lane is documented in
`docs/research/ZENO_ORACLE_WORKFLOW_EVIDENCE_STATUS.md`. ZenoProof now has
public replay profiles for this Julia sweep and Lean anchor through
`tools/zenoproof_public_replay_verifier.py`; deeper Morph, ESSO, TLA/LTLf,
and private campaign evidence should remain internal until each lane has a public
replay command and a stable claim boundary.
