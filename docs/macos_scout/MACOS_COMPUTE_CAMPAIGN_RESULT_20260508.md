# MacOS Compute Campaign Result - 2026-05-08

This note distills the local Mac compute pass without committing raw campaign
directories. Raw receipts, logs, and minimized witnesses remain under
`internal/`.

## Derivatives Scout

- Default campaign:
  - command: `JULIA_NUM_THREADS=auto CAMPAIGN_ID=20260508_compute_max_codex_default bash tools/macos_scout/run_compute_campaign.sh`
  - runs: 7
  - screened candidates: 700,256
  - accepted regression gates: 7
  - accepted witness receipts: 7
  - total counterexamples: 0
  - campaign reachable witnesses: 0
  - campaign witness receipt hash: `sha256:3714ca54a0a4393adfdceb925548ec53312e54c37c5443d6bb7ca3b0cb7f4f36`
- Dedicated soak:
  - command: `RUN_SMOKE=0 SCOUT_SEEDS='' DEEP_SEEDS='' RUN_SOAK=1 JULIA_NUM_THREADS=auto CAMPAIGN_ID=20260508_compute_max_codex_soak bash tools/macos_scout/run_compute_campaign.sh`
  - runs: 1
  - screened candidates: 1,000,000
  - accepted regression gates: 1
  - accepted witness receipts: 1
  - total counterexamples: 0
  - campaign reachable witnesses: 0
  - campaign witness receipt hash: `sha256:3cf55a9dc31294e707c0e219d335ebf258ad42d77670ef67862052a85f5e8d5a`

The campaign summarizer was hardened after the first run showed it was dropping
current `stable_receipt_hash` receipts and reporting accepted witness receipts
as zero.

## Stateful Disaster Campaign

- command: `python3 tools/acceptance_tcb_fuzz_campaign.py --gate-lane deep --stateful-exploration --format json`
- interpreter: `/Library/Developer/CommandLineTools/usr/bin/python3`
- result: accepted
- gate tests: 73 passed, 1 warning
- minimized bounded witnesses archived under `internal/fuzz_campaigns/deep/20260508T230740Z_acceptance-tcb-fuzz`
- witness count: 12
- stateful surface status counts:
  - witnessed: 7
  - reached_no_witness: 1
  - harnessed_unreached: 1
  - unharnessed: 1

Python 3.9 compatibility hardening was required before this gate could execute:
the first deep campaign stopped during collection on runtime evaluation of
newer annotation syntax.

## Proof-Market Checks

- command: `python3.11 -m pytest -q tests/core/test_proof_mining_manager.py tests/core/test_proof_mining_claimability_gate.py tests/tools/test_permissionless_solver_proof_mining_claim.py tests/integration/test_proof_mining_claimability.py tests/integration/test_proof_verifier.py tests/test_zenoproof_reward_payout_replay.py`
- result: 67 passed, 1 skipped, 1 warning

The proof-mining CLI path now imports under the default system `python3`, so the
test that shells out to `python3 tools/permissionless_solver_proof_mining_claim.py`
can exercise the claim emission boundary instead of failing in package imports.

## Blocked Follow-Through

- Metal prefilter: blocked because `Metal.jl` is not installed in the
  `tools/macos_scout` Julia environment. CPU Julia remains the authoritative
  evidence path.
- Lean formal checks: blocked before theorem checking because
  `lean-mathlib/../external/mathlib4` is missing.

## Public Hardening Promoted

- Compute campaign summaries now recognize both legacy `receipt_hash` receipts
  and current `stable_receipt_hash` receipts.
- Campaign summaries now surface the combined witness receipt status, hash, and
  reachable-witness count.
- Default `python3` compatibility was restored for the stateful fuzz gate and
  proof-mining CLI import path.
