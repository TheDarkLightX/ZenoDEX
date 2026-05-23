# ZenoDEX Review Reconciliation, 2026-05-18

This note reconciles the pasted A- review with the current local checkout.

Run context:

- Date: 2026-05-18
- Git HEAD at evidence run: `263cb670eff12beefa31c735949a012775bd79a0`
- Working tree status: dirty. This is local checkout evidence, not a clean
  release tag claim.
- Public-testnet gate artifacts: `/tmp/zenodex-public-testnet-gate-263cb670`

## Current Deltas From The Pasted Review

The pasted review is directionally useful, but two blocker descriptions are
stale for this checkout.

1. Python hash-pinned dependency closure is green locally.

   ```bash
   python3 tools/check_python_hash_locks.py --json
   pytest -q tests/test_check_python_hash_locks.py
   python3 tools/check_proof_toolchain_lock.py --json
   ```

   Observed result:

   - `check_python_hash_locks.py`: `ok: true`
   - `requirements-core.lock.txt`: 13 packages, 387 hashes
   - `requirements-agents.lock.txt`: 40 packages, 668 hashes
   - `requirements-dev.lock.txt`: 107 packages, 1531 hashes
   - `tests/test_check_python_hash_locks.py`: `9 passed in 0.61s`
   - `check_proof_toolchain_lock.py`: `ok: true`, `status: accepted`
   - proof toolchain lock hash:
     `0x1b0bfa596c4ea8f2a8ec22fcf43cf87ce5e3a7711c7967223a554ddb232d3a0a`

   Residual limit: `tools/check_dependency_change_approval.py` could not
   evaluate this checkout against `origin/main` or `main` because this local
   branch has no merge base. That is a local git ancestry limitation, not a
   hash-lock checker failure.

2. UPBA v2 is stronger than a deterministic partial-fill certificate.

   ```bash
   pytest -q tests/core/test_uniform_batch_optimality.py \
     -k 'v2_bounded_grid or partial_fill_winner or omitted_better or fill_vector'
   pytest -q tests/integration/test_dex_engine_uniform_batch_certificate.py \
     -k 'v2_bounded_grid or strict_upba_posture_accepts_v2 or partial_certificate'
   (cd lean-mathlib && lake env lean Proofs/UniformBatchOptimality.lean)
   ```

   Observed result:

   - core UPBA v2 focused tests: `8 passed, 29 deselected in 0.29s`
   - integration UPBA v2 focused tests: `3 passed, 38 deselected in 0.97s`
   - Lean bridge replay: passed

   Current checkout includes a v2 bounded-grid partial-fill verifier surface,
   fill-vector/candidate-root binding, omitted-better-candidate rejection tests,
   strict posture coverage, and a Lean bridge in
   `lean-mathlib/Proofs/UniformBatchOptimality.lean`.

   Residual limit: economic sufficiency and rational-grid production-policy
   claims still need careful wording and gate coverage. The current result is a
   bounded-grid optimality lane, not a claim that every possible market design
   question has been closed.

## Aristotle Boundary Proof Batch

Three Aristotle proof-search packets were promoted into tracked Lean modules and
replayed locally.

Promoted modules:

- `lean-mathlib/Proofs/UPBAV2ScoreOrder.lean`
- `lean-mathlib/Proofs/ZenoEnergyAdvisoryBoundary.lean`
- `lean-mathlib/Proofs/ZenoCoverReserveArithmetic.lean`

Receipt:

- `lean-mathlib/proof_receipts/aristotle_boundary_batch_20260518.md`

Focused wrapper:

- `tests/formal/test_lean_aristotle_boundary_packets.py`

Replay commands:

```bash
(cd lean-mathlib && lake env lean Proofs/UPBAV2ScoreOrder.lean)
(cd lean-mathlib && lake env lean Proofs/ZenoEnergyAdvisoryBoundary.lean)
(cd lean-mathlib && lake env lean Proofs/ZenoCoverReserveArithmetic.lean)
(cd lean-mathlib && lake build Proofs.UPBAV2ScoreOrder \
  Proofs.ZenoEnergyAdvisoryBoundary Proofs.ZenoCoverReserveArithmetic
)
(cd lean-mathlib && lake env lean Proofs.lean)
pytest -q tests/formal/test_lean_aristotle_boundary_packets.py
```

Observed result:

- all three promoted Lean files replayed
- aggregate build replayed
- `Proofs.lean` replayed
- focused pytest wrapper: `3 passed in 31.58s`
- local placeholder scan found no `sorry`, `admit`, `axiom`, `unsafe`, or
  `sorryAx` in the promoted files

## Fresh Public-Testnet Candidate Gate

Command:

```bash
GATE_OUT_DIR=/tmp/zenodex-public-testnet-gate-263cb670 \
  bash tools/run_public_testnet_candidate_gate.sh
```

Observed result:

- syntax checks passed
- Tau promotion metadata passed for:
  - `settlement_admission_envelope_v1`
  - `settlement_admission_envelope_temporal_v1`
- generated Tau trace report passed: 9 cases
- local two-node public-network smoke accepted
- regression lane: `14 passed, 1 warning in 381.93s`
- final gate line: `ok: public testnet candidate gate passed`

Smoke report:

```json
{
  "schema": "zenodex.zeno_ledger.public_network_smoke_report.v0",
  "status": "accepted",
  "ok": true,
  "network_id": "zeno-ledger-public-testnet-gate",
  "chain_id": "zeno-ledger-public-testnet-gate",
  "final_common_height": 12,
  "final_peer_check_ok": true,
  "final_peer_height_relation": "same_height",
  "node_a_watcher_count": 2,
  "node_b_watcher_count": 2,
  "source_feature_count": 10,
  "sync_a_feature_count": 10,
  "sync_b_feature_count": 10
}
```

This is fresh local public-testnet candidate evidence for the current checkout.
It does not replace physical two-machine evidence from separate hosts.

## Current Grade Implication

The pasted A- grade is still a reasonable conservative public summary, but the
local evidence is stronger than two of its listed blockers. A current internal
score should treat dependency hash locks and UPBA v2 bounded-grid evidence as
green for this checkout, subject to the residual limits above.

Mainnet/live-value claims still need additional evidence for physical
multi-machine rehearsal on latest main, validator/P2P/fork-choice hardening,
and complete spot-block proof-of-execution coverage.
