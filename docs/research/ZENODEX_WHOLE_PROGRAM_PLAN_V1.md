# ZenoDEX Whole-Program Production-Readiness Plan V1

Status: `TRACKED_PLAN_RESEARCH_ONLY`

Claim authority: `NONE`

Production authority: `NONE`

This document restores the six-phase Modular Whole-Economy Zeno Recursive Proof
Fabric program of 2026-08-05 as a tracked plan with exact task identifiers and
live statuses. The machine-readable source of truth is
`docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V1.json`. The tables below are
generated from that file; edit the JSON and regenerate, never the tables.

The plan records what exists and what is open. It promotes nothing. Every
authority field is a closed constant enforced by
`tools/check_whole_program_plan_v1.py`, which also pins the checker hash of
every live gate, re-executes the gates on demand, rejects dependency cycles,
requires pinned evidence for closed tasks, and requires a RIPR counterexample
plus a mutation killer for any task that claims a VM-gate improvement.

## Program shape

The stable boundary is `GlobalSettlementABI V1`. Every enabled lane is a module
behind that ABI, and the settlement flow is:

```text
Authenticated command
  -> module leaf proofs
  -> lane coordinator proof
  -> governed route-composer proof
  -> ordered epoch recursion proof
  -> release-selected root verification
  -> one atomic ZenoLedger commit
  -> external-only outbox delivery
```

Gate dependencies follow the steering packet:

```text
VM-01 -> VM-09 -> VM-12
VM-02 + VM-03 + VM-04 -> VM-05 -> VM-06 -> VM-07
VM-01 + VM-02 + VM-05 + VM-06 + VM-07 -> VM-08 -> VM-09 -> VM-10 -> VM-11
VM-01..VM-11 -> VM-12
```

Tasks are ordered by dependency inside each phase (the checker rejects any
`depends_on` edge whose dependency sorts after the dependent task id), and the
`depends_on` edges form the integration order: sink closure, then ABI and
effects, then lane lifecycles, then composition and refinement, then proof and
verifier, then publisher, then recovery and migration, then release evidence
(`P6-T09` evidence portfolio), then the claim certificate (`P6-T10`).

## Progress report at the recorded subject

Three separate dimensions are reported, following the progress scale:

1. Implementation maturity: the typed ABI, bounded lane modules, tokenomics and
   perps SHADOW cores, proof workspaces, durable journals, crash tests, and
   legacy donor modules support an architectural implementation estimate of
   roughly 35 to 45 percent. This is not a release probability.
2. Deterministic release-gate closure: 0 of 12 value-movement gates are closed
   (7 `PARTIAL`, 5 `GAP`); 103 capability rows, 27 writer-coverage rows, and
   19 classified Python sinks remain release-blocking.
3. Authority: `production_authority=NONE`, `production_ready=false`.

Base-gate defects found by the re-audit at `21fa295a4` are registered as
`B-01` through `B-05` and mapped to phase-1 repair tasks so that later
checkpoints never inherit a silently failing gate; the checker rejects a
narrative range that ends before the highest registered `B-` finding.

## Regeneration procedure

```bash
python3 tools/check_whole_program_plan_v1.py --json              # structural check
python3 tools/check_whole_program_plan_v1.py --execute --json    # re-run live gates
python3 tools/check_whole_program_plan_v1.py --refresh --observed-at YYYY-MM-DD \
  [--repin-evidence TASK_ID ...]                                  # regenerate observations
python3 tools/check_whole_program_plan_v1.py --render            # regenerate tables
python3 -m pytest -q tests/test_check_whole_program_plan_v1.py
```

`--refresh` re-executes every live gate and rebinds the subject: the program
base commit (an ancestor of, or equal to, HEAD) and a source-snapshot digest
of HEAD's committed tree entries except these two plan artifacts. Cleanliness
is recomputed from git status and required before structural success and
before any gate executes; the recorded Boolean is never trusted. Every
ordinary check and every `--execute` uses full scope: the whole worktree,
including both plan artifacts, must match the committed subject. Only the
`--refresh`/`--render` phase, which rewrites those two files, ignores exactly
those two paths, and it cannot be combined with `--execute`. A commit cannot
contain its own identifier, so the candidate SHA is never recorded; a fresh
detached checkout of the candidate reproduces the digest exactly, a
superseded provisional commit fails lineage, and any edit after regeneration
is reported as dirty or drifted. The regeneration order is therefore: commit
sources, run `--refresh`, amend the same single commit with the regenerated
artifacts, then run the focused suite and `--execute` on the committed
subject. `--refresh` never re-pins task evidence hashes unless the task is
named explicitly, so a stale evidence pin remains a visible blocker until
someone states why the artifact changed.

An ordinary invocation reads both exact `HEAD:path` blobs before opening the
worktree artifacts, captures the JSON and Markdown in held write-sealed
descriptors, requires byte equality with those committed blobs, and decodes or
renders only the held bytes. Both artifact digests remain attached to the
invocation and every planned live-gate effect. `ExecutionContextV1` and
`LiveGateEffectV1` are caller-constructible same-process conventions. They are
not unforgeable capabilities, and code already executing inside the checker
process remains trusted.

## Evidence rules for closing a task

- `DONE` requires every dependency `DONE`, at least one evidence row, a pinned
  hash for every file-kind evidence row, and nonclaims.
- `DONE_BOUNDED` is the same with dependencies allowed at `DONE_BOUNDED` and
  a mandatory statement of the bound in `nonclaims`.
- `claims_vm_improvement=true` additionally requires a named VM gate, a RIPR
  counterexample (reach, infect, propagate, reveal), and at least one mutation
  killer of the form `tests/<file>.py::test_<name>` that exists.
- A finding may move to `CLOSED` only when a closed task with a mutation killer
  references it.
- A VM gate may become `PASS` only when every mapped task is `DONE`, and the
  authority ceiling still forbids any production claim.

<!-- BEGIN GENERATED PLAN TABLES: regenerate with python3 tools/check_whole_program_plan_v1.py --render -->

Subject: base `21fa295a42d455ced130a50ae66c84b3c1b32afa` on `codex/fable-whole-program-20260825-r3`, source snapshot `23cc8d166b81a504288c8d71dbdfb0daf8162d607e44381036f31f141969da61` (5790 files, plan artifacts excluded), observed 2026-08-25.

Authority ceiling: `claim_authority="NONE"`, `production_authority="NONE"`, `production_ready=false`, `release_ready=false`.

### Phases

| Phase | Original plan section | Title |
| --- | --- | --- |
| P1 | 1 | Freeze a trustworthy candidate |
| P2 | 2 | Promote the global contract: closed requirements and complete mediation |
| P3 | 3 | Build the stable functional core and publisher |
| P4 | 4 | Complete modular M6 cores and terminal lifecycles |
| P5 | 5 | Implement the recursive proof fabric |
| P6 | 6 | Mount, migrate, and cut over |

### Tasks

| Task | Status | Title | Depends on | VM gates | Findings | Claims VM improvement |
| --- | --- | --- | --- | --- | --- | --- |
| P1-T01 | DONE | Isolate the clean implementation worktree at the exact subject | - | - | - | no |
| P1-T02 | DONE_BOUNDED | Record donor provenance manifests for the ZRPF, M6/FCIS, and dirty primary checkouts | P1-T01 | - | - | no |
| P1-T03 | DONE_BOUNDED | Register heavy gates that require RunPod and record the host disk posture | P1-T01 | - | - | no |
| P1-T04 | DONE | Re-audit every deterministic gate at the exact subject and record live statuses | P1-T01 | - | B-01, B-02, B-03, B-04, B-05, H5 | no |
| P1-T05 | OPEN | Repair the research-boundary regression without weakening the checker | P1-T04 | VM-01 | B-01 | no |
| P1-T06 | OPEN | Re-pin the V1 object-nullifier quarantine byte manifest with provenance | P1-T04 | - | B-02 | no |
| P1-T07 | OPEN | Enforce a deterministic nesting bound in the shared canonical-JSON decoder | P1-T04 | VM-02 | B-03 | no |
| P1-T08 | OPEN | Regenerate the closure ledger against the current candidate through the source-pinned procedure | P1-T05, P1-T06, P1-T07 | VM-12 | H5 | no |
| P1-T09 | BLOCKED_EXTERNAL | Classify the historical ATDD/Luna contract pins and their re-pin procedure | P1-T04 | - | B-04 | no |
| P1-T10 | OPEN | Make every live gate dependency-declared and path-hook-free: no user-site packages and no ignored-directory sitecustomize insertion | P1-T04 | VM-12 | B-05 | no |
| P2-T01 | OPEN | Extend operation-derived value-sink discovery to mounted tools, Path.replace, and file-write sinks | P1-T05 | VM-01 | F-03, H3, H4, I1 | no |
| P2-T02 | OPEN | Register the mounted node writers in the writer inventory with lane and workflow coverage rows | P1-T05 | VM-01 | F-03, F-04, F-05, I1 | no |
| P2-T03 | OPEN | Scan mounted tools for unsafe configuration literals and classify node settlement reachability | P2-T02 | VM-01 | F-03, H3 | no |
| P2-T04 | OPEN | Prove novel-writer and dynamically imported writer mutants block release | P2-T01 | VM-01, VM-09 | H4 | no |
| P2-T05 | OPEN | Add cross-language and deployment sink inventories (Rust, Tau, shell, generated code, deployment wiring) | P2-T01 | VM-01 | F-03, H4 | no |
| P2-T06 | OPEN | Quarantine private-key-over-HTTP ingress; accept signatures or locally signed envelopes only | P1-T04 | VM-01 | F-02, H1 | no |
| P2-T07 | OPEN | Freeze consensus policy and authority identities into committed state instead of process environment | P1-T04 | VM-01, VM-07 | F-01, H2, I1 | no |
| P2-T08 | OPEN | Map every capability-manifest row to command, transition, effects, route, terminal path, adapter, and evidence status | P1-T04 | VM-01, VM-04 | I2 | no |
| P2-T09 | OPEN | Wire the release gate so a reachable command without a complete release row fails CI | P2-T02 | VM-01, VM-12 | - | no |
| P2-T10 | OPEN | Produce a proved-no-writer certificate for zUSD emergency shutdown | P2-T01 | VM-04 | F-10 | no |
| P2-T11 | DEFERRED_SEMANTIC_DECISION | Record the faucet asset-exclusion divergence as a semantic question and add a parity witness | P1-T04 | VM-04 | F-05 | no |
| P2-T12 | DEFERRED_SEMANTIC_DECISION | Record the Tau buyback supply-floor specifications against the hyperdeflation anchor | P1-T04 | VM-07 | F-15 | no |
| P3-T01 | OPEN | Close the ABI ownership table: one owner, width, unit, order, authorization source, and reject behavior per field | P2-T08 | VM-02 | I2 | no |
| P3-T02 | OPEN | Establish complete Python/Rust/guest/verifier/durable codec and root parity for GlobalEconomicStateV1 | P3-T01 | VM-02, VM-07 | - | no |
| P3-T03 | OPEN | Complete the global effect algebra: authorization grant, claimant, residue, terminal, and external-delivery rows | P3-T01 | VM-03 | - | no |
| P3-T04 | OPEN | Retire the node treasury-balance buy-and-burn sidecar in favor of a typed governed route with one header write | P2-T02 | VM-09 | F-04 | no |
| P3-T05 | OPEN | Model the proof-reward reserve as an accounting location with occurrence rows | P3-T03 | VM-03, VM-04 | F-11 | no |
| P3-T06 | OPEN | Replace catch-all exception rejection on mounted apply paths with typed rejection | P2-T07 | VM-07 | F-12 | no |
| P3-T07 | OPEN | Introduce root and amount newtypes in the ABI with a Python mirror and regenerated goldens | P3-T01 | VM-02 | - | no |
| P3-T08 | OPEN | Apply deterministic depth and byte bounds to every canonical decoder on authoritative paths | P1-T07 | VM-02 | B-03 | no |
| P3-T09 | DONE_BOUNDED | Retain the crash-tested durable activation, epoch, authority, anchor, and verifier-owned publisher shells | P1-T04 | VM-10 | - | no |
| P4-T01 | IN_PROGRESS | Complete the ASSET_TRANSFER lane lifecycle: fee policy envelope, asset registration, and supply terminal policy | P3-T03 | VM-04 | - | no |
| P4-T02 | OPEN | Refine legacy Spot settlement and liquidity into the SPOT_LIQUIDITY lane with pool close and residue disposition | P3-T03 | VM-04 | - | no |
| P4-T03 | OPEN | Implement the FARM_INCENTIVES lane lifecycle behind a versioned profile | P3-T03 | VM-04 | - | no |
| P4-T04 | IN_PROGRESS | Complete the ZDEX_TOKENOMICS lane: hosting-compensation claims, staking claims, reserve lifecycle, and terminal disposition | P3-T03 | VM-04 | - | no |
| P4-T05 | OPEN | Refine zUSD into one complete ZUSD_MONETARY lifecycle with Stability Pool, liquidation, recovery, and terminal claims | P3-T03 | VM-04 | - | no |
| P4-T06 | IN_PROGRESS | Extend the SHADOW perps margin core to the selected PERPS_MARKET profile: funding, liquidation, insurance, ADL, bankruptcy, closeout | P3-T03 | VM-04 | - | no |
| P4-T07 | OPEN | Implement the ORACLE_MARKET lifecycle: query, tip, bond, report, finality, reward, dispute, clawback, slash, terminal drain | P3-T03 | VM-04 | - | no |
| P4-T08 | OPEN | Implement the SEALED_AUCTION lane with bond custody, reveal, clearing, payment, inventory, refund, slash, cancel, and expiry | P3-T03 | VM-04 | - | no |
| P4-T09 | OPEN | Implement the STRATEGY_ESCROW lane: reservation, activation, trigger, replacement, cancellation, expiry, recovery | P3-T03 | VM-04 | - | no |
| P4-T10 | OPEN | Implement the PROOF_REWARDS lane: reserve, verified-result binding, claimant, nullifier, payout, terminal task state | P3-T05 | VM-04 | F-11 | no |
| P4-T11 | OPEN | Prove EXTERNAL_CUSTODY has no writer while the registry stays empty | P2-T01 | VM-01, VM-04 | - | no |
| P4-T12 | OPEN | Implement the GOVERNANCE_MIGRATION lane: registry change, parameter change, release activation, treasury action, schema migration, writer-epoch rotation, command submission | P3-T03 | VM-04 | F-14 | no |
| P4-T13 | IN_PROGRESS | Implement the four required cross-lane routes as governed route composers | P4-T02, P4-T04, P4-T05, P4-T06, P4-T09 | VM-05 | - | no |
| P4-T14 | IN_PROGRESS | Complete lane coordinators and route composers with exact port pairing, release coexistence, and field ownership | P3-T03 | VM-05 | - | no |
| P4-T15 | OPEN | Add the perps slice Python/Rust rejection corpus, Python delta bound, and boundary twin tests | P1-T04 | VM-07 | F-06 | no |
| P5-T01 | IN_PROGRESS | Split the shared proof code into a stable ABI crate plus independently versioned module guest crates | P3-T02 | VM-06 | - | no |
| P5-T02 | OPEN | Bind child image IDs, verifier-set roots, profiles, and statement hashes into lane composition journals | P5-T01 | VM-06 | F-06 | no |
| P5-T03 | OPEN | Remove environment-selected dev-mode admission from proof verifiers | P1-T04 | VM-06, VM-08 | F-07 | no |
| P5-T04 | OPEN | Replace third-party receipt serialization with an owned envelope digest and check journal bounds before decoding | P5-T01 | VM-06 | F-08 | no |
| P5-T05 | BLOCKED_EXTERNAL | Generate and replay real pinned-image receipts for every module family and mixed-lane epochs | P5-T01, P5-T02 | VM-06 | F-09 | no |
| P5-T06 | OPEN | Add direct-versus-proof parity vectors across Python, Rust, and guest for every command | P3-T02 | VM-07 | - | no |
| P5-T07 | OPEN | Replace the quarantined risc0 1.2 state_proof crate on 3.0.x and bind proof journal hash plus signature set in live headers | P5-T01 | VM-06, VM-09 | F-09 | no |
| P5-T08 | OPEN | Record Tau policy applicability per lane and add Tau-versus-runtime parity where applicable | P2-T12 | VM-07 | - | no |
| P5-T09 | IN_PROGRESS | Real-receipt proof BVA: epochs accept 1, 8, 9, and 64 occurrences and reject 0 and 65; routes accept 1 and 8 modules and reject 0 and 9; missing, extra, reordered, duplicate, wrong-image, wrong-profile, wrong-control-root, conditional, fake, development-mode, and mutated receipts reject before publication | P5-T02, P5-T05 | VM-06 | - | no |
| P6-T01 | OPEN | Seal verification behind a release-selected measured verifier with commit-lock reselection and an isolation boundary | P2-T01, P3-T02, P4-T14, P5-T06 | VM-08 | I3 | no |
| P6-T02 | OPEN | Route every API, UI, Tau bridge, and recovery operation through the command registry and status model | P2-T08 | VM-01, VM-09 | - | no |
| P6-T03 | OPEN | Dual-run legacy execution and ZRPF in shadow mode and convert every divergence into minimized negative evidence | P6-T02 | VM-07 | - | no |
| P6-T04 | OPEN | Mount one sole atomic publisher and mechanically fence every other writer | P2-T04, P6-T01 | VM-09 | I3 | no |
| P6-T05 | OPEN | Deploy a concrete authenticated finality/anchor service and complete the persistence-boundary fault matrix and outbox reconciliation | P3-T09 | VM-10 | - | no |
| P6-T06 | OPEN | Prove migration totality, atomic profile and writer-epoch rotation, and shared-asset coexistence or issuance disablement | P6-T04 | VM-11 | - | no |
| P6-T07 | OPEN | Retire legacy writers after cutover | P3-T04, P6-T06 | VM-09, VM-11 | - | no |
| P6-T08 | OPEN | Regenerate release evidence on the clean candidate and obtain independent security, proof, lifecycle, and authority reviews | P1-T08, P2-T09, P6-T07 | VM-12 | - | no |
| P6-T09 | OPEN | Release-blocking evidence portfolio: preserve all 81 M6 scenarios plus 11 expansions with profile shutdown exclusions; per-actor happy, rejection, authorization, cancellation, recovery, and terminal BDD; BVA; stateful, property, and differential evidence; migration, CAS, and outbox histories; independent security, proof, economic-lifecycle, and authority reviews | P1-T09, P4-T13, P4-T14, P6-T06, P6-T08 | VM-04, VM-06, VM-07, VM-10, VM-11, VM-12 | B-04 | no |
| P6-T10 | OPEN | Emit the whole-value-movement claim certificate only from the checker that binds every conjunct | P6-T08, P6-T09 | VM-12 | - | no |

### VM gate status

| Gate | Status | Decisive remaining condition | Tasks |
| --- | --- | --- | --- |
| VM-01 | PARTIAL | Operation-derived, cross-language, deployment-aware sink reachability and release bindings. | P1-T05, P2-T01, P2-T02, P2-T03, P2-T04, P2-T05, P2-T06, P2-T07, P2-T08, P2-T09, P4-T11, P6-T02 |
| VM-02 | PARTIAL | Complete Python/Rust/guest/verifier/durable codec and root parity with deterministic resource bounds. | P1-T07, P3-T01, P3-T02, P3-T07, P3-T08 |
| VM-03 | PARTIAL | Authorization, claimant, residue, terminal, and external-delivery effect coverage. | P3-T03, P3-T05 |
| VM-04 | GAP | Total enabled-lane lifecycles with recovery and terminal drain; excluded lanes proved writer-free. | P2-T08, P2-T10, P2-T11, P3-T05, P4-T01, P4-T02, P4-T03, P4-T04, P4-T05, P4-T06, P4-T07, P4-T08, P4-T09, P4-T10, P4-T11, P4-T12, P6-T09 |
| VM-05 | GAP | Governed mixed-lane routes and exact port/effect/release composition. | P4-T13, P4-T14 |
| VM-06 | PARTIAL | Whole-economy execution in real pinned-image recursive proofs and replay. | P5-T01, P5-T02, P5-T03, P5-T04, P5-T05, P5-T07, P5-T09, P6-T09 |
| VM-07 | GAP | Decision, reject precedence, state, effects, roots, replay, and outbox refinement across every authoritative implementation. | P2-T07, P2-T12, P3-T02, P3-T06, P4-T15, P5-T06, P5-T08, P6-T03, P6-T09 |
| VM-08 | PARTIAL | Measured isolated backend, committed release selection, exact replay, revocation, and lock-time reselection. | P5-T03, P6-T01 |
| VM-09 | GAP | One mounted atomic publisher and mechanically fenced legacy writers. | P2-T04, P3-T04, P5-T07, P6-T02, P6-T04, P6-T07 |
| VM-10 | PARTIAL | Concrete finality/anchor service, all persistence-boundary faults, delivery and acknowledgment reconciliation. | P3-T09, P6-T05, P6-T09 |
| VM-11 | PARTIAL | Proved migration semantics, atomic authority rotation, total classification, terminal/payable validity, coexistence. | P6-T06, P6-T07, P6-T09 |
| VM-12 | GAP | Clean exact-subject reproducible evidence after all preceding gates close. | P1-T08, P1-T10, P2-T09, P6-T08, P6-T09, P6-T10 |

### Live gates

| Gate | Command | Exit | Observed |
| --- | --- | --- | --- |
| m6_asset_precision_policy | `python3 tools/check_m6_asset_precision_policy_v1.py` | 0 | `{"atoms_per_display_unit":100000000,"decimal_places":8,"ok":true,"policy_root":"0xacfbd1be88e823fcdd1b094b8d2f0c8ee1bf19c826004e89752f27fd22aa49dd"}` |
| m6_atdd_contract | `python3 tools/check_m6_global_economic_core_atdd_v1.py` | 1 | `{"contract_status":"RESEARCH_ONLY_DRAFT","errors#len":26}` |
| m6_capability_manifest | `python3 tools/check_m6_capability_manifest_v1.py` | 0 | `{"lane_count":12,"manifest_complete":false,"manifest_root":"0x21efc162df198e40a0aa942fcb69b7a5f5cc0f93907b11a3c6b25359e4a464bb","ok":true,"open_capability_count":103,"production_authority":"NONE","release_eligible":false}` |
| m6_luna_completeness_review | `python3 tools/check_m6_global_economic_core_luna_review_v1.py` | 1 | `{"errors#len":5}` |
| m6_research_boundary | `python3 tools/check_m6_research_boundary.py --json` | 1 | `{"checked_file_count":636,"findings[].path":["src/core/economic_initial_state_v1.py","src/core/economic_initial_state_v1.py","src/core/global_settlement_abi_v1.py","src/core/global_settlement_abi_v1.py","src/core/global_settlement_abi_v1.py","src/core/lane_module_receipt_verification_v1.py","src/core/perps_market_policy_v1.py"],"findings[].rule_id":["research_module_import","research_module_import","research_module_import","research_module_import","research_module_import","research_module_import","research_module_import"],"m6_production_mounted":false,"ok":false}` |
| m6_risc0_semantic_surface | `python3 tools/check_m6_risc0_semantic_surface_v1.py` | 1 | `{"activation_eligible":false,"canonical_state_codec_match":false,"errors#len":8,"ok":false,"risc0_guest_transition_reachable":false,"status":"BLOCKED_SEMANTIC_SURFACE"}` |
| m6_value_sinks | `python3 tools/check_m6_value_sinks_v1.py --json` | 0 | `{"classified_identity_count":20,"observed_occurrence_count":29,"ok":true,"release_gaps#len":19,"release_ready":false}` |
| m6_writer_inventory | `python3 tools/check_m6_writer_inventory.py --json` | 0 | `{"coverage_row_count":27,"findings#len":0,"ok":true,"open_coverage_count":27,"release_gate_status":"BLOCKED_OPEN_COVERAGE","release_ready":false,"unmounted_entrypoint_count":18}` |
| permissionless_assurance_status | `python3 tools/permissionless_assurance.py status` | 0 | `{}` |
| production_boundary | `python3 tools/check_production_boundary.py --json` | 1 | `{"checks[].check_id":["production_boundary_audit_execution_complete"],"checks[].ok":[false],"ok":false}` |
| value_movement_closure_status | `python3 tools/check_value_movement_closure_status_v1.py` | 1 | `{"findings#len":15,"gate_count":12,"ok":false,"production_authority":"NONE","subject_commit":"69ff811b785a80eec91ee3512f856e6fd33e4a3a"}` |

### Heavy gates requiring RunPod or external capacity

| Gate | Workspace | Command | Reason | Last recorded evidence |
| --- | --- | --- | --- | --- |
| HG-01 | zk/global_settlement_abi_v1 | `cargo test --locked --offline --manifest-path zk/global_settlement_abi_v1/Cargo.toml && cargo clippy --locked --offline --manifest-path zk/global_settlement_abi_v1/Cargo.toml --all-targets -- -D warnings` | Pure Rust crate; affordable locally only with an explicit scratch CARGO_TARGET_DIR while root free space stays near 9 GiB; not run in this checkpoint. | docs/research/GLOBAL_SETTLEMENT_ABI_V1_REFERENCE_20260805.md evidence commands (historical); F-06 notes a Rust boundary test without a Python twin. |
| HG-02 | zk/asset_transfer_module_risc0 | `cargo test --locked -p zenodex-asset-transfer-module-risc0-host --test real_proof real_asset_transfer_transition_proves_the_exact_module_journal -- --ignored --nocapture` | RISC0 3.0.6 guest build and Succinct proving; multi-gigabyte target and long proving time. | Historical image root 0x226651d0ba0e014c84331a521d78de508a5ede995990a7745d7ae61d93c22e24, 569.75 s local proof (reference doc); not reproduced at this subject. |
| HG-03 | zk/asset_lane_coordinator_risc0 | `cargo test --locked -p zenodex-asset-lane-coordinator-risc0-host --test real_composition real_module_receipt_composes_into_the_exact_lane_journal -- --ignored --nocapture` | Recursive child verification proof; multi-gigabyte target and long proving time. | Historical coordinator image root 0xdba71555eb4790fd0146032e88f7c4720b343f08a1de785982b3c4faf14cfa61, 1443.67 s recursive run; release-aware replay interrupted (exit 130). |
| HG-04 | zk/global_economic_epoch_risc0 | `cargo test --locked -p zenodex-global-economic-epoch-risc0-host --test real_composition -- --ignored --nocapture && cargo test --locked -p zenodex-global-economic-epoch-risc0-host --test real_aggregation_nine -- --ignored --nocapture` | Bounded epoch recursion with real Succinct children; heavy. | Historical three-receipt direct/aggregation branch and 12-receipt nine-command tree (reference doc); no 64-command replay exists. |
| HG-05 | zk/economic_initial_state_risc0 | `cargo test --locked --workspace -- --ignored --nocapture` | Initialization guest never built; no ELF, image ID, cycle measurement, proof, or receipt replay exists (closure ledger). | None; source-only slice with static max-review passes. |
| HG-06 | zk/perps_margin_module_risc0 | `RISC0_SKIP_BUILD=1 cargo test --locked --workspace && cargo test --locked --workspace -- --ignored --nocapture` | Perps margin module guest build and Succinct proof. | README records a RunPod Succinct replay dated 2026-08-25; not reproduced here (prior audit nonclaim). |
| HG-07 | zk/perps_margin_lane_coordinator_risc0 | `RISC0_SKIP_BUILD=1 cargo test --locked --workspace && cargo test --locked --workspace -- --ignored --nocapture` | Single-child recursive perps lane proof; includes the ignored pin-equality test (F-06). | README records a RunPod Succinct replay and a CUDA benchmark (commit ea8e3c164); not reproduced here. |
| HG-08 | zk/perps_margin_route_composer_risc0 | `RISC0_SKIP_BUILD=1 cargo test --locked --workspace && cargo test --locked --workspace -- --ignored --nocapture` | Shadow route recursion seam (commit 21fa295a4); unbuilt on this host. | Unknown at this subject; source only. |
| HG-09 | zk/zdex_fee_allocation_risc0 | `RISC0_SKIP_BUILD=1 cargo test --locked --workspace && cargo test --locked --workspace -- --ignored --nocapture` | ZDEX allocation guest; unbuilt on this host. | Unknown at this subject; prior audit did not read this workspace. |
| HG-10 | zk/zdex_hyperdeflation_burn_risc0 | `RISC0_SKIP_BUILD=1 cargo test --locked --workspace && cargo test --locked --workspace -- --ignored --nocapture` | ZDEX burn guest; unbuilt on this host. | Unknown at this subject; prior audit did not read this workspace. |
| HG-11 | zk/zdex_tokenomics_lane_coordinator_risc0 | `RISC0_SKIP_BUILD=1 cargo test --locked --workspace && cargo test --locked --workspace -- --ignored --nocapture` | ZDEX lane coordinator guest; unbuilt on this host. | Unknown at this subject; prior audit did not read this workspace. |
| HG-12 | zk/state_proof_risc0 | `cd zk/state_proof_risc0 && cargo test --all && cargo clippy --all -- -D warnings` | Quarantined risc0 1.2.6 crate (GHSA-jqq4-c7wq-36h7); cannot support production proof claims (F-09). | Quarantine README; authority NONE. |
| HG-13 | external/ESSO | `PYTHONPATH=external/ESSO python3 -m ESSO verify-multi <model.yaml> --solvers z3,cvc5` | external/ESSO is absent on this host; kernel, spot, derivatives, and perps evidence lanes report MISSING. | permissionless_assurance status: lane readiness 1/7. |
| HG-14 | tau | `python3 tools/check_tau_supported_runtime_subset.py && pytest -q tests/tau/test_tau_spec_assurance.py` | tau-binary is absent on this host; Tau upstream requires requalification (closure ledger tau_upstream). | Closure ledger tau_upstream: requalification_required=true. |
| HG-15 | lean-mathlib | `cd lean-mathlib && lake build` | Mathlib-backed Lean build is multi-gigabyte and thermally heavy on this workstation. | Not run at this subject. |
| HG-16 | release | `bash tools/run_release_gate.sh` | Full release gate requires Tau, proof, evidence, and audit lanes that are absent locally. | permissionless_assurance status: release lane MISSING (external/ESSO, tau-binary). |

### Unresolved policy inputs

| Policy | Statement | Source | Implementation rule |
| --- | --- | --- | --- |
| UP-01 | Fee allocation percentages among purchase-and-burn, hosting compensation, staking, treasury, reserves, and any carried residue. | SEMANTIC_DECISION_BOUNDARY.md item 1 | Typed governed parameters with fail-closed envelopes only; production values stay profile-owned, canonically committed, and unselected. |
| UP-02 | Hosting claimant eligibility, measurement period, proof of service, replacement, slashing, and terminal disposition. | SEMANTIC_DECISION_BOUNDARY.md item 2 | Hosting compensation stays a separately named claimant obligation; no PulseX percentage is inferred. |
| UP-03 | Farm activation, emission schedule, cancellation, and terminal drain. | SEMANTIC_DECISION_BOUNDARY.md item 3 | Lane structure may exist; the release stays SHADOW until values and evidence are selected. |
| UP-04 | zUSD collateral assets, collateral ratios, fees, Oracle thresholds, liquidation/recovery rules, Stability Pool economics, and coexistence rule. | SEMANTIC_DECISION_BOUNDARY.md item 4 | Shared zUSD issuance stays disabled across releases unless a coexistence theorem exists. |
| UP-05 | Complete perps market profile, funding cadence, margin and liquidation thresholds, insurance priority, ADL ordering, bankruptcy allocation, and terminal closeout. | SEMANTIC_DECISION_BOUNDARY.md item 5 | The SHADOW margin core stays bounded to deposit, withdraw, and close; wider incompatible choices are recorded, not chosen. |
| UP-06 | Oracle query, tip, bond, reward, dispute, clawback, and slash values and the finality rule. | SEMANTIC_DECISION_BOUNDARY.md item 6 | Route-bound occurrence authority stays structural; reporter economics remain unmounted. |
| UP-07 | Auction bond, reveal window, clearing tie-break, inventory disposition, cancellation, slash, refund, and expiry rules. | SEMANTIC_DECISION_BOUNDARY.md item 7 | Existing clearing fixtures do not decide the profile. |
| UP-08 | Strategy escrow trigger authority, replacement, expiry, recovery, and route permissions. | SEMANTIC_DECISION_BOUNDARY.md item 8 | No escrow writer is added before the policy is selected. |
| UP-09 | Proof-reward funding, claimant eligibility, nullifier scope, payout, and task terminal semantics. | SEMANTIC_DECISION_BOUNDARY.md item 9 | The reserve becomes an accounting location; funding rules stay profile inputs. |
| UP-10 | Autonomous-governance quorum, timelock, parameter envelopes, emergency procedure, treasury authority, and upgrade constraints. | SEMANTIC_DECISION_BOUNDARY.md item 10 | Prior 24/48/72 hour examples and fixed quorums remain candidates. |
| UP-11 | Tau-origin asset registration and finality semantics once the Tau runtime exposes a stable authoritative interface. | SEMANTIC_DECISION_BOUNDARY.md item 11 | Testnet adapters keep explicit options; no final ABI is assumed. |
| UP-12 | Spot and LP curve selection, fee tiers, routing, slippage, pool admission and closure, LP rounding, dust, and residue disposition. | SEMANTIC_DECISION_BOUNDARY.md item 12 | Legacy batch clearing remains a donor; normative behavior is preserved where it already exists. |
| UP-13 | Generic-transfer fees, asset registration, managed-issuance authority, and asset-supply terminal policy. | SEMANTIC_DECISION_BOUNDARY.md item 13 | The transfer module keeps a profile-owned flat fee without a chosen production value. |
| UP-14 | Exact retained-supply parameters, per-epoch burn limits, minimum purchase and burn atoms, and zero-output handling. | SEMANTIC_DECISION_BOUNDARY.md item 14 | Bind R(S)=ceil(p*S/q) with 0<p<q and burn<=S-R(S) structurally; p and q stay profile inputs. |
| UP-15 | ZDEX future issuance policy, reserve lifecycle, staking claims, and terminal disposition. | SEMANTIC_DECISION_BOUNDARY.md item 15 | No issuance route is added; hyperdeflation remains the intended long-run policy. |
| UP-16 | Transaction ordering, authorization grants, replay domains, and consensus-time rules not already fixed by the stable ABI. | SEMANTIC_DECISION_BOUNDARY.md item 16 | Only rules already fixed by GlobalSettlementABI V1 are implemented. |
| UP-17 | Price, ratio, funding, and collateral fixed-point scales beyond eight-decimal asset amounts. | SEMANTIC_DECISION_BOUNDARY.md item 17 | Eight decimals applies to asset amounts and does not silently select every other scale. |
| UP-18 | Deployment profile for the node's locally synthesized settlement: whether any allow_missing_settlement=True testnet helper may remain and how production proves it unreachable. | Encountered during the 21fa295a4 re-audit (HOTSPOT_TARGETS H3, audit F-03) | The production-boundary scan is extended to tools; a helper survives only with a reachability proof, never by default. |
| UP-19 | Faucet asset-exclusion policy: the node excludes only the protocol token while the Tau plugin also excludes canonical zUSD. | Encountered during the 21fa295a4 re-audit (audit F-05) | Two artifacts disagree; both are preserved as provenance and neither is silently chosen. |
| UP-20 | Tau buyback supply-floor specifications versus the retained-supply hyperdeflation anchor. | Encountered during the 21fa295a4 re-audit (audit F-15, docs/TAU_SPECS_PRODUCTION.md) | The anchor governs the selected profile; the Tau floor specs are historical drift and cannot be mounted under it. |

### Finding registry

| Finding | Severity | Status | Title | Source |
| --- | --- | --- | --- | --- |
| F-01 | High | OPEN | Consensus-path policy and authority identities read from os.environ inside the Tau transition | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-02 | High | OPEN | HTTP APIs accept raw private keys in request bodies and sign server-side | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-03 | High | OPEN | Mediation checkers scan src only while the deployed node holds unregistered writers, sinks, and the forbidden literal | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-04 | Medium-High | OPEN | Node buy-and-burn is a treasury-balance shortcut with post-hoc rewrite of written block artifacts | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-05 | Medium | OPEN | Two faucet writers with divergent policy; the node faucet can mint canonical zUSD | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-06 | Medium | OPEN | Perps slice Python/Rust rejection-class divergence, missing Python boundary twin, lane journal lacks child binding | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-07 | Medium | OPEN | Proof verifiers read RISC0_DEV_MODE from the process environment | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-08 | Medium | OPEN | Receipt canonical form is third-party serialization decoded before journal bounds | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-09 | Medium | OPEN | Spot proof crate quarantined on risc0 1.2; live blocks are unproven, unsigned, and DA-less | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-10 | Medium | OPEN | zUSD shutdown writer exists while the manifest requires a proved no-writer certificate | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-11 | Medium | OPEN | Proof-reward reserve is a key-controlled account re-based to the observed chain balance | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-12 | Medium | OPEN | Catch-all exception handling produces deterministic-looking rejects and shallow immutability | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-13 | Low | OPEN | Wall-clock fallbacks in node time_ms and API previews | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-14 | Low | OPEN | AutoGovNext records economic parameters that nothing consumes | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| F-15 | Low | OPEN | Tau specs encode a supply-floor buyback policy that drifts from the hyperdeflation anchor | Fable FCIS audit 2026-08-25 at ea8e3c16 |
| H1 | High | OPEN | Raw signing material at network ingress | HOTSPOT_TARGETS.md at 21fa295a4 |
| H2 | High | OPEN | Environment-selected economic or authority policy | HOTSPOT_TARGETS.md at 21fa295a4 |
| H3 | High | OPEN | Mounted node permits locally synthesized settlement | HOTSPOT_TARGETS.md at 21fa295a4 |
| H4 | High | OPEN | Multiple durable writer families | HOTSPOT_TARGETS.md at 21fa295a4 |
| H5 | Medium | OPEN | Stale closure-ledger evidence on a continuous 49-commit lineage | HOTSPOT_TARGETS.md at 21fa295a4 |
| I1 | High | OPEN | Deployed writer/sink mediation incomplete; environment- or caller-selected authority remains | STATE.md open issue |
| I2 | High | OPEN | Enabled M6 lane lifecycles, cross-lane effects, terminal paths, and cross-implementation parity incomplete | STATE.md open issue |
| I3 | High | OPEN | No measured release-selected verifier, sole atomic publisher, proved migration/cutover, or legacy retirement | STATE.md open issue |
| B-01 | Medium | OPEN | M6 research-boundary gate fails at the subject: ABI policy-binding modules carry the research m6_ prefix and are package-imported | Fable re-audit at 21fa295a4 (this plan) |
| B-02 | Low | OPEN | V1 object-nullifier quarantine byte pin is stale after perps route-binding test changes | Fable re-audit at 21fa295a4 (this plan) |
| B-03 | Low | OPEN | Canonical JSON decoders reject deep nesting only through the interpreter recursion limit | Fable re-audit at 21fa295a4 (this plan) |
| B-04 | Info | HISTORICAL | M6 ATDD and Luna completeness contracts remain pinned to historical base 12bde5263 | Fable re-audit at 21fa295a4 (this plan) |
| B-05 | Medium | OPEN | Live gates depend on operator-local ambient state: the production-boundary gate resolves py_ecc only from the user site, and the tracked root sitecustomize.py inserts the ignored external/ESSO directory into child sys.path whenever it exists | Fable re-audit at 21fa295a4 (this plan; explicit gate environment) |

### Test execution receipt

`python3 -m pytest -q -p no:cacheprovider tests/core/test_global_settlement_abi_v1.py tests/core/test_global_settlement_abi_v1_parity.py tests/core/test_economic_*.py tests/core/test_global_economic_*.py tests/integration/test_global_economic_*.py tests/core/test_zdex_*.py tests/core/test_perps_margin_*.py tests/core/test_asset_*.py tests/core/test_managed_asset_*.py tests/core/test_lane_module_release_route_binding_v1.py tests/core/test_receipt_backed_*.py tests/integration/test_m6_*.py tests/core/test_m6_*.py tests/core/test_global_oracle_occurrence_authority_v1.py tests/test_check_m6_writer_inventory.py tests/test_check_m6_value_sinks_v1.py tests/test_check_m6_research_boundary.py tests/test_check_production_boundary.py tests/test_check_m6_capability_manifest_v1.py tests/test_check_m6_asset_precision_policy_v1.py tests/test_check_value_movement_closure_status_v1.py tests/core/test_perps_market_policy_binding_v1.py tests/core/test_global_oracle_price_occurrence_v1.py` at `21fa295a42d455ced130a50ae66c84b3c1b32afa`: 1573 passed, 4 failed in 1526 s (Python 3.12.3, pytest 7.4.4, Linux x86_64; LOCAL_EXECUTION_RECORD_UNATTESTED).
- FAILED `tests/core/test_global_economic_object_nullifier_reference_v2_isolation.py::test_reference_v2_leaves_v1_quarantine_artifacts_byte_identical`
- FAILED `tests/integration/test_global_economic_authority_journal_v1.py::test_decoder_normalizes_hostile_json_nesting_to_typed_rejection`
- FAILED `tests/test_check_m6_research_boundary.py::test_current_m6_research_boundary_is_unmounted_and_clean`
- FAILED `tests/test_check_value_movement_closure_status_v1.py::test_current_value_movement_closure_status_is_exact_and_fail_closed`

<!-- END GENERATED PLAN TABLES -->

## Nonclaims

- No production readiness, production authority, settlement authority, writer
  rotation, mount, or value-moving authority is claimed by this plan.
- Recorded live-gate observations are local unattested execution records.
- Historical RunPod proof replays are not reproduced by this plan.
- The whole-value-movement formal safety claim remains `UNPROVED`.
