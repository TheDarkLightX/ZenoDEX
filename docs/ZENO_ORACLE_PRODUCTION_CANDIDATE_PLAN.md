# ZenoOracle Production Candidate Plan

Status: active goal plan, not a production certification.

This document turns the current ZenoOracle goal into concrete deliverables and
gates. The immediate branch target is a single integration branch that keeps
the public devnet/docs work from `origin/main` and the typed runtime
`OracleAuthorization` checks from `codex/zeno-oracle-mvp-hardening`.

The current prompt-to-artifact completion audit is tracked in
`docs/ZENO_ORACLE_GOAL_COMPLETION_AUDIT.md`.

## Success Criteria

ZenoOracle reaches production-candidate O3 status only when all of these are
true:

- critical ZenoDEX consumers reject raw oracle values and accept only
  action-bound O3-or-better receipts;
- the O3 path replays from feed registry through terminal action receipt;
- reporter economics are live in the replay model: bonds, rewards, disputes,
  slashing, withdrawals, and fee splits;
- the disaster corpus has a checked obligation-antichain certificate;
- public claims are promoted only when their command gates are replayable from a
  clean checkout;
- O4/O5 evidence has a ZenoProof v0 design with explicit verifier and registry
  boundaries.

## Current Branch Facts

The active workspace now has:

- typed runtime Oracle authorization in
  `src/integration/zeno_oracle_authorization.py`;
- trigger, routing, settlement, zUSD, and perps authorization hooks/tests on
  this branch;
- the public receipt-bundle verifier API in `tools/zenodex_oracle.py`,
  including `verify_bundle`, `sample_bundle`, and receipt content hashing;
- devnet feed, signed-report, admission, aggregate, aggregate-read,
  aggregate-adapter, consumer-adapter, service, disaster-harness, and package
  shells from `origin/main`;
- runtime `oracle_adapter_bridge` compatibility hooks for perps settlement,
  standalone perps liquidation, zUSD mint/liquidation, guarded routing, and
  trigger execution, plus typed critical-settlement authorization;
- the critical-action map now reports `7` catalog profiles, `7`
  runtime-wired profiles, and `0` design-only backlog profiles;
- a local reporter/validator bundle builder in
  `tools/build_zenodex_oracle_release.py`;
- a deterministic end-to-end O3 receipt-flow replay at
  `tools/zeno_oracle_o3_receipt_flow_replay.py`, covering feed registry,
  reporter lifecycle, signed reports, report admission, admitted median3,
  accepted read, action adapter, and terminal DAG replay with `8/8` accepted
  stages;
- the Oracle whitepaper under
  `docs/papers/zeno-oracle-whitepaper/ZenoOracleWhitepaper.pdf`;
- an Oracle-specific disaster-obligation manifest at
  `tools/zeno_oracle_disaster_obligation_certificate_manifest.json`.
- a ZenoProof v0 local verifier shell at `tools/zenoproof_verify.py` with a
  public sample verifier manifest at `tools/zenoproof_registry_manifest.json`;
  the shell now checks Oracle O5 bridges with an independence witness requiring
  distinct verifier IDs, distinct proof kinds, shared Oracle input/output
  roots, and claim-DAG dependency closure.
- ZenoProof public replay verifier roots at
  `tools/zenoproof_public_replay_verifier.py` for workflow-evidence status,
  Julia witness-sweep, Lean witness-anchor, deterministic bounded TLA Oracle
  recovery, deterministic bounded LTLf Oracle recovery, deterministic bounded
  ESSO zUSD Oracle recovery, Morph oracle-clamp, and SMT Oracle freshness
  profiles.
- a bounded ZenoProof reward-payout replay bridge at
  `tools/zenoproof_reward_payout_replay.py`, which takes an accepted local
  reward gate through proof-mining claim construction, manager execution, and
  claimability checks.
- a devnet RC package validator at `tools/check_zeno_oracle_rc_package.py`,
  which checks the package manifest, launcher, docs, whitepaper, branding,
  receipt, and devnet integrity signature.
- a local reporter economics replay verifier at
  `tools/zenodex_oracle_reporter_economics_replay.py` for rewards, disputes,
  slashing, withdrawals, and fee splits.
- a public named disaster-class corpus at
  `tools/zeno_oracle_disaster_class_corpus.py` for source cartel, dispute
  griefing, registry drift, verifier spoofing, O5 independence spoofing,
  proof-timeout fail-closed behavior, replay integrity, and cross-module
  split-brain first-shell checks.
- a first Julia witness sweep at
  `tools/zeno_oracle_math_witness_sweep.jl` for median
  deviation, source cartel, dispute griefing, reward-pool conservation,
  live-economics settlement-execution total matching/drift rejection, and
  split-brain boundary cases, plus O5 independence-witness acceptance and
  missing-distinct-verifier rejection.
- a first Lean witness anchor at
  `lean-mathlib/Proofs/ZenoOracleMathWitness.lean` for the same bounded
  median/deviation, reward-pool, live-economics settlement-execution total,
  source-cartel, and split-brain arithmetic, plus Prop-level live-economics
  receipt, O4/O5 Oracle-use binding, O4/O5 iff decomposition, and full O5
  independence-witness obligation decomposition.
- a public workflow evidence status checker at
  `tools/zeno_oracle_workflow_evidence_status.py` for the first TLA, LTLf,
  ESSO, Morph smoke, and PopperPad smoke lanes. The ESSO, TLA, and LTLf lanes
  have deterministic bounded public replay at
  `tools/zeno_oracle_esso_zusd_recovery_replay.py`,
  `tools/zeno_oracle_tla_recovery_replay.py` and
  `tools/zeno_oracle_ltlf_recovery_replay.py`.
- a production-candidate network config receipt gate at
  `tools/check_zeno_oracle_production_network_config.py` that validates local
  reporter-registry deployment, feed-governance deployment, feed-governance
  approval/execution, signed release artifact, signed-release transparency-log
  root binding, and runtime-control attestation receipts while keeping live
  chain and public soak verification outside the claim.
- a production-candidate live economics policy gate at
  `tools/check_zeno_oracle_live_economics_policy.py` that binds reporter
  economics replay to token, escrow, governance approval/execution, escrow
  funding, and settlement execution receipts while keeping live chain
  settlement outside the claim.

Current public gate evidence:

```bash
bash scripts/check_zeno_oracle_mvp.sh
python3 tools/check_zeno_oracle_critical_action_map.py
python3 tools/zeno_oracle_o3_receipt_flow_replay.py --format text
pytest -q tests/test_zenodex_oracle_devnet_service.py tests/test_zenodex_oracle_devnet_disaster_harness.py
python3 tools/zenodex_oracle_devnet_disaster_harness.py --format text
python3 tools/zenodex_oracle_devnet_alpha_audit.py
python3 tools/check_claims_registry.py
python3 tools/zenoproof_verify.py self-test --registry tools/zenoproof_registry_manifest.json
python3 tools/zenoproof_reward_payout_replay.py --format text
bash scripts/package_zeno_oracle_rc.sh zeno-oracle-devnet-alpha-rc1
python3 tools/check_zeno_oracle_rc_package.py --package-dir dist/zeno-oracle-devnet-alpha-rc1 --receipt dist/zeno-oracle-devnet-alpha-rc1.receipt.json --sig dist/zeno-oracle-devnet-alpha-rc1.sig
python3 tools/zenodex_oracle_reporter_economics_replay.py self-test
python3 tools/check_zeno_oracle_live_economics_policy.py --format text
python3 tools/zeno_oracle_disaster_class_corpus.py --format text
python3 tools/check_disaster_obligation_certificate.py --manifest tools/zeno_oracle_disaster_obligation_certificate_manifest.json
julia tools/zeno_oracle_math_witness_sweep.jl
cd lean-mathlib && lake env lean Proofs/ZenoOracleMathWitness.lean
python3 tools/zeno_oracle_workflow_evidence_status.py --format text
```

The gate evidence is devnet evidence. It does not claim production oracle truth,
on-chain feed governance, or production code signing.

## Remaining Gaps

The current branch is stronger than the first MVP shell, but the full goal is
still open. The remaining completion work is:

- connect the local reporter economics replay to production token settlement
  and on-chain governance once those surfaces exist;
- deepen the current SMT, TLA, ESSO, Lean, Julia, and Morph ZenoProof roots
  beyond bounded witness anchors;
- promote the bounded local ZenoProof reward-payout replay to live proof-mining
  token settlement once that settlement surface exists;
- add deterministic Julia witnesses for quorum, median deviation, slash
  economics, and any new oracle benefit/search cases beyond the first witness
  sweep;
- add Lean/TLA/LTLf gates for median/deviation laws, action binding,
  receipt-borrowing exclusion, terminal DAG closure, budget inequalities, and
  cross-module sync;
- keep extending the disaster-obligation antichain and named-class corpus when
  new axes are found;
- build a production package with on-chain feed governance, production signing,
  and replay health checks.

## Work Packages

### 1. Branch Integration

Create a fresh branch from `origin/main`, then integrate this branch's stricter
typed authorization path.

Acceptance evidence:

```bash
git ls-tree -r --name-only HEAD | rg 'ZENO_ORACLE|zenodex_oracle|zeno_oracle'
pytest -q tests/integration/test_oracle_authorization_semantic_binding.py
```

Required result: the public devnet shell and the typed runtime gate both exist.

### 2. O3 Receipt Flow

The production O3 chain is:

```text
feed registry
  -> reporter lifecycle
  -> signed report
  -> report admission
  -> admitted aggregate
  -> accepted read
  -> action adapter
  -> terminal DAG replay
```

Every edge must bind content hash, query semantics, registry roots, freshness,
evidence class, uncertainty, dispute state, and consumer action facts.

Acceptance evidence:

```bash
python3 tools/zeno_oracle_o3_receipt_flow_replay.py --format text
pytest -q tests/test_zeno_oracle_o3_receipt_flow_replay.py
bash scripts/check_zeno_oracle_mvp.sh
bash scripts/check_zeno_oracle_devnet_alpha.sh
```

The standalone replay is the focused local O3 chain check. The gate scripts
remain broader devnet checks after the `origin/main` Oracle shell is
integrated.

### 3. Critical Consumers

Critical consumers must all call one typed predicate equivalent to:

```text
OracleUseOK(action, authorization, runtime_facts)
```

Required surfaces:

- zUSD bootstrap, report, commit, mint, liquidation;
- perps settlement and standalone liquidation;
- protected routing and protected swap;
- trigger execution;
- critical settlement packets.

Acceptance evidence:

```bash
pytest -q \
  tests/integration/test_oracle_authorization_semantic_binding.py \
  tests/integration/test_zusd_oracle_contracts.py \
  tests/integration/test_perp_engine_oracle_authorization.py \
  tests/integration/test_dex_engine_protected_swap_oracle_authorization.py \
  tests/integration/test_dex_engine_critical_settlement_oracle_authorization.py \
  tests/integration/test_zeno_oracle_trigger_authorization.py
```

### 4. Reporter Economics

Reporter economics are part of O3 because critical reads need economic margin
in addition to syntactic receipts.

Required laws:

```text
RewardPaid <= QueryBudgetRemaining
SlashPaid <= ReporterBondAvailable
DisputeRewardPaid <= DisputeBudgetAvailable
ReporterShare + TreasuryShare + BurnShare <= FeePaid
```

The first target is now implemented as deterministic replay over local event
streams:

```bash
python3 tools/zenodex_oracle_reporter_economics_replay.py self-test
pytest -q tests/test_zenodex_oracle_reporter_economics_replay.py
python3 tools/check_zeno_oracle_live_economics_policy.py --format text
pytest -q tests/test_check_zeno_oracle_live_economics_policy.py
```

The production-candidate policy gate binds the replay to local governance
approval/execution, escrow funding, and settlement execution receipts. Live
token settlement can follow once governance, signing, deployment, and on-chain
receipt replay surfaces are stable.

### 5. Disaster-State Antichain

The Oracle disaster corpus starts with the checked manifest:

```bash
python3 tools/check_disaster_obligation_certificate.py \
  --manifest tools/zeno_oracle_disaster_obligation_certificate_manifest.json
```

Current manifest scope:

- `24` Oracle disaster axes;
- `21` quotient classes;
- `16` antichain representatives;
- `10` selected guard families;
- private-obligation witnesses for every selected guard.

New axes must be classified as existing, dominated, incomparable, dominating,
or requiring a new obligation atom.

The current public named-class replay corpus is:

```bash
python3 tools/zeno_oracle_disaster_class_corpus.py --format text
pytest -q tests/test_zeno_oracle_disaster_class_corpus.py
```

It closes the first-shell source-cartel, dispute-griefing, registry-drift,
verifier-spoofing, O5 independence-spoofing, proof-timeout, replay-integrity,
and cross-module split-brain families against the current local checkers. It
is bounded replay evidence, and broader Julia, Morph, ESSO, TLA/LTLf, and
Lean discovery/proof work remains open.

### 6. Math And Evidence Lanes

Julia lane:

- first witness sweep:

```bash
julia tools/zeno_oracle_math_witness_sweep.jl
```

- next parameter sweeps for quorum, slash economics, oracle benefit, and attack
  margin;
- minimized integer witnesses for new source-collusion, reward-griefing, and
  cross-module split-brain variants found by Morph or fuzzing.

Lean lane:

- first bounded witness anchor:

```bash
cd lean-mathlib && lake env lean Proofs/ZenoOracleMathWitness.lean
```

- median and deviation laws;
- action binding and receipt-borrowing exclusion;
- terminal DAG closure;
- economic budget and deterrence inequalities;
- cross-module sync including epoch-lag composition beyond the current local
  theorem scope.

Workflow lane:

- Morph and fuzzers search for witnesses;
- ESSO/TLA/LTLf check finite-state safety and liveness;
- PopperPad records internal evidence;
- `docs/claims_registry.yaml` receives only stable, public replay commands.

The first public status checker is:

```bash
python3 tools/zeno_oracle_workflow_evidence_status.py --format text
pytest -q tests/test_zeno_oracle_workflow_evidence_status.py
```

It checks the presence and replay boundaries for the Oracle recovery TLA/LTLf
lanes, the ESSO zUSD oracle recovery lane, a Morph oracle-clamp smoke check,
and a temporary PopperPad append-only smoke. The ESSO/TLA/LTLf lanes replay the
bounded Oracle recovery models locally. Broader Morph campaigns, external
TLC/ESSO synthesis, and private PopperPad ledgers remain internal until
promoted through public replay commands.

### 7. Public Claim Promotion

Promotion requires:

```bash
python3 tools/check_claims_registry.py
pytest -q tests/test_claims_registry.py
```

Claims must state what is proved, what is bounded evidence, and what remains an
external assumption.

### 8. Devnet Alpha Package

The devnet alpha package must include:

- executable launcher or native binary path;
- docs and whitepaper;
- replay verifier;
- event store replay;
- CI gate;
- explicit non-claims.

The package is a devnet artifact until public reporter economics, dispute
governance, verifier registry, and replay health are stable.

## Completion Audit Checklist

Before marking the goal complete, audit each item below against real artifacts:

- branch contains both `origin/main` Oracle devnet files and typed
  `OracleAuthorization`;
- O3 receipt replay path covers every edge listed above;
- all critical consumers are wired and tested;
- reporter economics have positive and negative replay tests;
- Oracle disaster antichain certificate passes;
- named disaster-class corpus passes for the current first-shell named classes;
- Julia witness sweep passes, and Morph witnesses are captured as deterministic
  tests or artifacts as they are promoted;
- Lean/TLA/LTLf gates pass for promoted formal claims;
- workflow evidence status checker passes for promoted public workflow lanes;
- public claims registry validates;
- ZenoProof v0 design, verifier shell, registry manifest, Oracle O4 bridge,
  and Oracle O5 independence-witness bridge
  sample pass replay, including the workflow-evidence, Julia, Lean,
  deterministic bounded TLA, deterministic bounded LTLf, deterministic bounded
  ESSO, Morph, and SMT public replay verifiers and the local proof-mining
  reward gate plus bounded reward-payout replay;
- devnet alpha package builds and validates its manifest, launcher, docs,
  replay, whitepaper, branding, receipt, integrity signature, and non-claims.
