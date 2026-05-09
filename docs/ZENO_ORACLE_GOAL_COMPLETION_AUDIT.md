# ZenoOracle Goal Completion Audit

Status: active audit, goal still open.

Last checked: 2026-05-06.

This audit maps the active ZenoOracle/ZenoProof goal to concrete workspace
evidence. It is intentionally conservative: an item is complete only when the
repo has a replayable public artifact, verifier, test, or package gate for the
specific requirement.

The machine-readable audit is:

```bash
python3 tools/check_zeno_oracle_goal_completion_audit.py --format json
```

By default this command exits nonzero while the production-candidate goal is
blocked. Use `--expect-blocked` when testing the current expected state.

## Objective

Finish ZenoOracle as a production-candidate O3 oracle for ZenoDEX critical
actions, minimize ZenoOracle/ZenoDEX disaster states with replayable
obligation-antichain evidence, and design ZenoProof v0 as the proof
registry/verifier layer for O4/O5 claims.

## Current Evidence

| Requirement | Current evidence | Status |
| --- | --- | --- |
| One Oracle integration branch | The PR-capable integration branch is `codex/zeno-oracle-main-integration`, with draft PR `#204` opened against `main`. Public devnet/docs artifacts and typed `OracleAuthorization` code are present in the branch. | Integrated branch |
| O3 receipt flow | `tools/zeno_oracle_o3_receipt_flow_replay.py` replays the focused local path from feed registry through reporter lifecycle, signed report, admission, admitted median3, accepted read, action adapter, and terminal DAG replay with `8/8` accepted stages. Devnet service tools and `bash scripts/check_zeno_oracle_devnet_alpha.sh` provide broader shell coverage. `tools/check_zeno_oracle_production_network_config.py` adds a fail-closed production-candidate network config gate, including typed isolated perps settlement authorization plus a local receipt bundle for reporter-registry deployment, feed-governance deployment, feed-governance approval/execution, signed release artifacts, signed-release transparency-log root binding, and runtime-control attestation. Live chain receipt verification and public soak remain open. | Devnet complete plus config gate |
| Critical consumers | `tools/check_zeno_oracle_critical_action_map.py` reports `catalog_profile_count = 7`, `runtime_wired_count = 7`, and `design_only_backlog_count = 0`, covering zUSD, perps settlement/liquidation, routing, triggers, and critical settlement. | Devnet complete |
| Reporter economics | `tools/zenodex_oracle_reporter_economics_replay.py` and tests cover bonds, rewards, disputes, slashing, withdrawals, fee splits, and budget rejection. `tools/check_zeno_oracle_live_economics_policy.py` binds that replay to a production-candidate token, escrow, governance receipt, fee-split, dispute-bond, slash-cap, and withdrawal-delay policy. The same checker now verifies a local receipt bundle for governance approval, governance execution, escrow funding against the replay-derived escrow floor, and settlement execution totals against the replay. Live chain receipt replay, on-chain funded escrow verification, and on-chain settlement execution remain open. | Replay plus policy gate |
| Disaster corpus | `tools/zenodex_oracle_devnet_disaster_harness.py` reports 17 selected states unreachable; `tools/zeno_oracle_disaster_class_corpus.py` reports 9 named families closed, including settlement-execution total drift, O5 independence-spoofing, and proof-timeout fail-closed behavior. `tools/check_zeno_oracle_disaster_frontier.py` tracks 29 production-candidate disaster families: 24 closed by public/devnet evidence and 5 left as explicit blocker/backlog families. `tools/check_zeno_oracle_perps_snapshot_gate.py` adds bounded replay evidence for usable perps oracle snapshots, including stale pre-drift action-ID rejection after snapshot price drift and clearinghouse 2p/3p action binding. `tools/check_zeno_oracle_cross_domain_finality_gate.py` adds local receipt-bundle replay for source finality checkpoint and target adapter acceptance binding, including source finality receipt block chronology against the finalized source block. `tools/check_zeno_oracle_reporter_soak_gate.py` adds local reporter-soak observation replay for operator-diversity and source-diversity thresholds. `tools/check_zeno_oracle_compositional_disaster_regressions.py` records sanitized private-campaign summaries and accepts seven public branch-local regressions with no deferred projection among the selected private witnesses. | First shell plus frontier gate |
| Obligation antichain | `tools/check_disaster_obligation_certificate.py` validates `tools/zeno_oracle_disaster_obligation_certificate_manifest.json`; the current certificate compresses 24 axes into 16 antichain classes and includes `proof_independence` and `cross_domain_finality` as required obligation atoms. `tools/check_zeno_oracle_frontier_obligation_projection.py` projects all 29 current frontier families onto manifest quotient classes with zero unprojected families. `lean-mathlib/Proofs/DisasterAntichainBasis.lean` and `lean-mathlib/proof_receipts/disaster_antichain_basis_v1.json` add generic checked lift theorems for covered antichain-basis rejection plus private-witness guard lower bounds. The Python certificate instantiates the current manifest and frontier projection only, and it must expand with any newly promoted frontier axis. | Accepted |
| Julia math lane | `tools/zeno_oracle_math_witness_sweep.jl` checks 41 bounded witnesses for median deviation, zero-scale/equal-value sanity, bounded median-deviation side-obligation decomposition, monotone acceptance under widened deviation bounds, source cartel, dispute griefing, reward conservation/caps, live-economics escrow floor and timelock receipts, live-economics and production-network receipt-chain chronology acceptance/rejection, settlement-execution total matching/drift rejection, settlement component dominance by the computed grand total, budget-to-component cap transfer, preservation under budget widening, settlement-execution receipt totals/asset/contract drift rejection, split-brain, epoch-lag symmetry, O5 independence-witness cases, O5 proof/window/proof-kind/root drift rejection, O3 action-binding DAG/runtime/sync-window cases, missing value-binding and wrong consumer-action rejection, sync-window widening preservation, and bounded sync-window composition with summed lag bounds plus O3 composition preservation. | Bounded witness plus theorem pressure |
| Lean math lane | `lean-mathlib/Proofs/ZenoOracleMathWitness.lean` provides bounded arithmetic anchors plus restricted general lemmas for zero-scale/equal-value deviation, median-deviation side-obligation decomposition, the iff relation between sorted median-deviation acceptance and its two side bounds, monotone acceptance under widened deviation bounds, low/high side rejection, epoch lag, reward/slash conservation, live-economics escrow floor, timelock receipt-bundle obligations, receipt-position transitivity/asymmetry, live-economics and production-network receipt-chain chronology acceptance/rejection, settlement-execution component dominance, budget-to-component cap transfer, monotone budget widening, receipt iff decomposition, and totals/asset/contract drift rejection, terminal DAG closure projections, runtime binding projections, iff decompositions for terminal DAG/runtime binding/O3 action-binding/O4-or-O5 bridge/O5 independence/O5 use obligations, direct O3 value-binding and same-consumer-action projections/rejections, rejection of missing DAG dependencies, content-hash drift, registry-root drift, and runtime-state drift, sync-window symmetry/rejection/monotonicity, epoch-lag triangle composition, Oracle sync-window composition with summed lag bounds, O3 action-binding projections, O3 sync-window widening and composition preservation, and Prop-level O4/O5/O5-independence projections and rejections for missing proof, window, proof-kind, input/output-root, and DAG obligations. Complete generalized oracle math, production economics, executable DAG closure, live typed production sync use, and typed binding theorems remain open. | Restricted theorem packet |
| ESSO/TLA/LTLf/Morph/PopperPad | `tools/zeno_oracle_workflow_evidence_status.py` reports 5 accepted first-shell lanes. `tools/zeno_oracle_esso_zusd_recovery_replay.py`, `tools/zeno_oracle_tla_recovery_replay.py`, and `tools/zeno_oracle_ltlf_recovery_replay.py` give the bounded ESSO/TLA/LTLf Oracle recovery profiles deterministic public replay commands. Private PopperPad content, external TLC/ESSO toolchains, and deeper Morph campaigns remain outside public claims. | First shell complete |
| Public claims registry | `docs/claims_registry.yaml` validates with `python3 tools/check_claims_registry.py` and `pytest -q tests/test_claims_registry.py`. | Complete for promoted claims |
| ZenoProof v0 | `tools/zenoproof_verify.py` validates artifacts, registry DAGs, public replay profiles, O4 bridge, O5 independence witness bridge, reward gate, and bounded payout replay. The self-test now accepts all registered public replay profiles locally, including workflow, Julia, Lean, ESSO, TLA, LTLf, Morph, and SMT. Public replay input/output roots bind declared source/spec file digests, and skipped or missing public replay toolchains become rejected profile results instead of accepted evidence or a traceback. `tools/check_zenoproof_production_governance_policy.py` adds a production-candidate governance policy gate that quarantines local static verifiers, disables executable path lookup for production public replay verifiers, checks verifier sandbox/code-signing/revocation/O4/O5/reward-settlement controls, and verifies a local receipt bundle for governance execution, revocation drill/list, code signing, verifier-release manifest binding, verifier-release transparency-log root binding, and sandbox attestation. It still rejects `--require-live` while live proof-network blockers remain. | Local v0 plus governance gate |
| Devnet alpha package | `scripts/package_zeno_oracle_rc.sh` and `tools/check_zeno_oracle_rc_package.py` build and validate the devnet alpha package, docs, whitepaper, branding, manifest, receipt, and devnet integrity signature. | Devnet complete |
| Goal completion audit | `tools/check_zeno_oracle_goal_completion_audit.py` maps all 10 prompt items to evidence and blocks completion on production network, live economics, broader disaster-search, generalized math, and ZenoProof production-governance gaps. | Blocking audit |

## Latest Replay Commands

```bash
bash scripts/check_zeno_oracle_devnet_alpha.sh
python3 tools/check_zeno_oracle_critical_action_map.py
python3 tools/zeno_oracle_o3_receipt_flow_replay.py --format text
python3 tools/zeno_oracle_disaster_class_corpus.py --format text
python3 tools/check_disaster_obligation_certificate.py --manifest tools/zeno_oracle_disaster_obligation_certificate_manifest.json
python3 tools/check_zeno_oracle_frontier_obligation_projection.py --format text
python3 tools/zeno_oracle_workflow_evidence_status.py --format text
python3 tools/zeno_oracle_esso_zusd_recovery_replay.py --format text
python3 tools/zeno_oracle_tla_recovery_replay.py --format text
python3 tools/zeno_oracle_ltlf_recovery_replay.py --format text
python3 tools/zenoproof_verify.py self-test --registry tools/zenoproof_registry_manifest.json
python3 tools/zenoproof_reward_payout_replay.py --format text --registry tools/zenoproof_registry_manifest.json
python3 tools/check_claims_registry.py
python3 tools/check_zeno_oracle_goal_completion_audit.py --format text --expect-blocked
python3 tools/check_zeno_oracle_production_network_config.py --format text
python3 tools/check_zeno_oracle_live_economics_policy.py --format text
python3 tools/check_zeno_oracle_disaster_frontier.py --format text
python3 tools/check_zeno_oracle_cross_domain_finality_gate.py --format text
python3 tools/check_zeno_oracle_reporter_soak_gate.py --format text
python3 tools/check_zeno_oracle_compositional_disaster_regressions.py --format text
julia tools/zeno_oracle_math_witness_sweep.jl
pytest -q tests/test_zeno_oracle_math_witness_sweep.py
cd lean-mathlib && lake env lean Proofs/ZenoOracleMathWitness.lean
cd lean-mathlib && lake build Proofs.DisasterAntichainBasis
python3 tools/check_zenoproof_production_governance_policy.py --format text
```

## Remaining Work Before Goal Closure

1. Land the integration PR after review and any required CI/branch-protection
   checks.
2. Production network: replace local/devnet-only assumptions with production
   reporter operations, production signing, production code signing, on-chain
   feed governance, public soak evidence, and live settlement policy. The
   current production-candidate config checker rejects malformed configs and
   missing local deployment/signing receipts, but it does not prove that the
   network is deployed or live.
3. Live economics: promote the production-candidate economics policy into live
   token settlement with on-chain escrow funding, governance execution,
   settlement execution receipt replay, and public reporting soak evidence.
4. Broader disaster search: close the five explicit frontier blockers currently
   reported by `tools/check_zeno_oracle_disaster_frontier.py`, then keep the
   frontier catalog aligned with every newly promoted disaster family. The
   cross-domain finality gate is local receipt replay; live finality adapter
   receipts and public soak evidence remain required. The selected
   compositional private campaign witnesses now have public branch-local
   regression projections, including confidential live-admission replay.
5. General formal math: continue lifting current Julia/Lean witnesses into
   complete generalized theorem families for median/deviation, economics, DAG
   closure, synchronization, and typed Oracle binding. The current packet now
   has restricted Lean theorems and 41 Julia witnesses, but full production
   theorem coverage remains open.
6. Deeper proof lanes: strengthen ESSO/TLA/LTLf/Morph evidence beyond current
   bounded anchors. The ESSO, TLA, and LTLf lanes now have deterministic
   bounded public replay; external TLC/ESSO model checking and Morph campaign
   evidence still need stable public replay boundaries before broader claims
   can be promoted.
7. ZenoProof productionization: close the production governance gate blockers:
   on-chain governance execution, production verifier code signing, sandbox
   deployment, live revocation drill, public proof-network soak, and live
   proof-mining token settlement.

## Completion Decision

The active goal is not complete. The workspace now has strong devnet and local
v0 evidence, including O5 independence-witness checking, a
production-candidate live economics policy gate, an explicit
production-disaster frontier catalog, and a generic Lean basis theorem for the
current obligation-antichain certificate. Production network, live settlement,
broader disaster search, generalized formal proofs, and final branch integration
remain open.
