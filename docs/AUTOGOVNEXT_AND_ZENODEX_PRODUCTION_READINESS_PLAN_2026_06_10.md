# AutoGovNEXT And ZenoDEX Production Readiness Plan (2026-06-10)

## Status

Goal: bring ZenoDEX to production readiness by completing AutoGovNEXT first,
wiring it into a real ZenoLedger node path, then closing the remaining DEX
production lanes with reproducible evidence.

Current checkout facts from local exploration:

- Branch: `codex/zeno-ledger-public-testnet-20260514`.
- Git posture: ahead of origin by 28 commits and behind by 12 commits.
- Worktree posture: `tools/permissionless_assurance.py status` reported 6,498
  dirty paths. Production release work requires a clean candidate tree before
  final promotion.
- Public assurance posture: `python3 tools/permissionless_assurance.py status`
  reported lane readiness `8/8`, with the assurance snapshot dated
  2026-04-06.
- Production-boundary posture:
  `python3 tools/check_production_boundary.py --json` passed.
- Adopted local review discipline from the ZenoDEX Claude skills:
  path-first style routing, consensus-aware red-flag scanning, churn by
  complexity prioritization, evidence-tiered findings, and version-bump caution
  for rounding, dust, ordering, nonce semantics, kernel observables, and
  canonical roots. These scripts are preflight and triage aids; the release
  gates and manifest checkers remain authoritative.
- AutoGov current code posture:
  `src/integration/autonomous_governance_q_policy.py` has deterministic policy
  evaluation, verified-surface evaluation, and a commit/no-op step.
- Initial AutoGovNEXT gap: before Phase 1 work, no `AutoGovNEXT` symbol, no
  `sample_autonomous_governance_next_policy_v1`, and no
  `admit_autonomous_governance_surface_request_v1` request boundary were found
  under `docs`, `src`, `tools`, `tests`, `lean-mathlib`, or `.github`. The
  local request boundary is now implemented in this working tree.
- Initial node wiring gap: before Phase 2 work, `tools/zeno_ledger_node.py`
  could append DEX transactions, faucet mints, and tokenomics reward claims,
  but had no first-class autonomous governance admission transaction path. This
  working tree now has a tested `append-autogov-next`/HTTP node path for
  deterministic admission receipts. Accepted admissions now commit a
  node-owned governance app-root lane and trajectory accumulator. PR CI and
  release-integrity run the focused governance lane gate. A committed public
  manifest checker, Lean bounded-drift artifact, and explicit no-auto-reset
  trajectory policy now exist. The browser proof client now requires pinned
  checkpoint trust anchors, and its ZK proof-status parser can fail closed on
  caller-pinned verifier/circuit/image artifact hashes. A future
  governance-authority reset transaction remains outside this lane.

This plan is an execution contract. It is pre-promotion planning material.
Promotion requires the evidence commands in this document to pass on a clean,
pinned release candidate.

## Implementation Progress

### 2026-06-10 Phase 1 Local Front Door

Implemented in this working tree:

- `sample_autonomous_governance_next_policy_v1`
- `admit_autonomous_governance_surface_request_v1`
- CLI `sample --surface --next`
- CLI `admit`
- fast authority-boundary tests for valid admission, receipt-rejected no-op,
  bad expected policy hash, direct result-field injection, unknown request
  fields, and CLI bypass rejection

Evidence from this pass:

```bash
python3 -m py_compile src/integration/autonomous_governance_q_policy.py tools/autonomous_governance_q_policy.py tests/integration/test_autonomous_governance_q_policy.py
python3 -m pytest -q tests/integration/test_autonomous_governance_q_policy.py -k 'autogovnext'
# 8 passed, 28 deselected
python3 -m pytest -q tests/integration/test_autonomous_governance_q_policy.py
# 36 passed
python3 tools/autonomous_governance_q_policy.py sample --surface --next --output /tmp/autogovnext-bundle.json
python3 tools/autonomous_governance_q_policy.py admit /tmp/autogovnext-bundle.json
python3 tools/check_production_boundary.py --json
# ok: true
python3 tools/permissionless_assurance.py status
# lane readiness: 8/8, dirty tree: 6479 paths
```

This is local-front-door evidence only. It does not prove node replay, release
gate coverage, or production readiness.

### 2026-06-10 Phase 2 Node Admission And Replay

Implemented in this working tree:

- `ZENODEX_AUTOGOVNEXT_ADMISSION` node transaction kind.
- `append_autogovnext_admission_v1` writer append function.
- CLI `tools/zeno_ledger_node.py append-autogov-next`.
- HTTP `POST /api/governance/autogov-next`, behind existing write-auth and
  testnet-intake controls.
- Generic HTTP `POST /tx` dispatch for
  `ZENODEX_AUTOGOVNEXT_ADMISSION`, routed through the same deterministic
  `append_autogovnext_admission_v1` path as the dedicated governance endpoint.
- Follower replay support in `pull_live_from_peer_v0`.
- Node tests for:
  - valid writer append plus follower replay to the same header hash and
    governance state;
  - node-owned governance state binding for the next update;
  - duplicate `tx_id` idempotency returning the prior append report;
  - tampered live body rejection without follower tip mutation;
  - gate-rejected no-op receipt with unchanged state root;
  - direct result-field bypass rejected before tip mutation;
  - authority-parameter policy attempts committed only as rejected no-op
    receipts;
  - automatic trajectory reset policy rejected fail-closed;
  - HTTP valid admission;
  - HTTP write-auth enforcement;
  - HTTP policy rejection committed as a no-op receipt.
  - generic `/tx` AutoGovNEXT admission routing;
  - generic `/tx` tx-id mismatch rejection without tip mutation.
  - generic `/tx` missing or non-string outer `tx_id` rejection without tip
    mutation.
- Imported and current-grounded
  `docs/AUTOGOVNEXT_GAME_THEORY_AND_MECHANISM_DESIGN.md` from
  `claude/autogov-trajectory-runner`. Its current correction is that the node
  now owns and persists the governance state and trajectory accumulator. The
  Lean bounded-drift artifact proves the carried-accumulator arithmetic. The
  node state pins a no-auto-reset policy; any future reset must be a separate
  governance-authority action.
- AutoGovNEXT policy normalization now has an explicit authority-parameter
  denylist for verifier/image IDs, signer sets, policy registries, deployment
  profiles, config/module digests, and related authority roots. Such parameters
  are rejected before they can enter the autonomous surface, and the node commits
  the attempt only as a rejected no-op receipt.
- `tools/dex-ui/src/sdk/zenoProofClient.js` and the synced
  `packages/zeno-proof-client` package now require caller-pinned checkpoint
  trust anchors (`trusted_prev_header_hash` and signer-registry hash) and expose
  expected proof-artifact hash pinning for strict ZK proof status. This closes
  the browser-side "accept whatever the bundle declares" gap for these local
  SDK paths. RISC0 receipt consumers still need to pass the expected artifact or
  image hash into the parser before making a proof-client production claim.
- PR CI and release-integrity now run the focused AutoGovNEXT governance lane
  gate over app-root, ledger-root, local admission, node append, HTTP, and
  writer/follower replay tests.
- `tools/autogovnext_governance_lane_assurance_manifest.json` now hash-pins the
  source, tests, workflows, Lean bounded-drift artifact, and run/check scripts
  for the focused gate. It keeps `production_security_claim=false` and records
  the absence of a governance-authority reset transaction as an explicit
  non-claim.

Evidence from this pass:

```bash
python3 -m py_compile tools/zeno_ledger_node.py tests/integration/test_zeno_ledger_node_autogovnext.py
python3 -m pytest -q tests/integration/test_zeno_ledger_node_autogovnext.py
# 12 passed
python3 -m pytest -q tests/integration/test_autonomous_governance_q_policy.py tests/integration/test_zeno_ledger_node_autogovnext.py
# 48 passed
python3 -m pytest -q tests/state/test_app_root.py tests/integration/test_zeno_ledger_v0.py tests/integration/test_autonomous_governance_q_policy.py tests/integration/test_zeno_ledger_node_autogovnext.py
# 103 passed
git diff --check -- src/state/app_root.py src/integration/zeno_ledger_v0.py src/integration/autonomous_governance_q_policy.py tools/autonomous_governance_q_policy.py tools/zeno_ledger_node.py tests/state/test_app_root.py tests/integration/test_zeno_ledger_v0.py tests/integration/test_autonomous_governance_q_policy.py tests/integration/test_zeno_ledger_node_autogovnext.py docs/AUTOGOVNEXT_AND_ZENODEX_PRODUCTION_READINESS_PLAN_2026_06_10.md docs/AUTOGOVNEXT_GAME_THEORY_AND_MECHANISM_DESIGN.md
cd lean-mathlib && lake env lean Proofs/AutogovNextTrajectoryBudget.lean
npm --prefix tools/dex-ui run test:sdk
cd packages/zeno-proof-client && npm test
python3 -m pytest -q tests/integration/test_zeno_proof_client_package.py -q
bash tools/sync_zeno_proof_client_package.sh --check
python3 tools/check_production_boundary.py --json
python3 tools/permissionless_assurance.py status
python3 tools/check_autogovnext_governance_lane_assurance_manifest.py --json
python3 -m pytest -q tests/test_check_autogovnext_governance_lane_assurance_manifest.py
bash tools/run_autogovnext_governance_lane_assurance_gate.sh
# ok
```

This is real-node test evidence for request admission and deterministic receipt
replay. Accepted admissions commit an autonomous-governance state lane into the
canonical app root. Rejected policy decisions remain explicit no-op receipts.
This path is now included in PR CI and release-integrity as a focused replay
gate and a committed public manifest checker. The carried-accumulator
bounded-drift arithmetic is backed by
`lean-mathlib/Proofs/AutogovNextTrajectoryBudget.lean`. The node state pins
`no_auto_reset_governance_authority_only_v1`, so budget reset is not automatic;
a future governance-authority reset transaction remains out of scope for this
increment.

Latest local confirmation: the focused AutoGovNEXT governance-lane assurance
gate (`bash tools/run_autogovnext_governance_lane_assurance_gate.sh`) exited
successfully after adding generic `/tx` AutoGovNEXT routing. A later defensive
boundary hardening pass made the generic `/tx` envelope require a string outer
`tx_id` equal to the inner request `tx_id`, with missing and non-string ID
regressions covered at the live HTTP route. That gate executes the
manifest-pinned compile, Lean bounded-drift, policy/node pytest, UI SDK,
proof-client package, package-sync, and manifest checks while keeping
`production_security_claim=false`.

Latest release-gate confirmation: `bash tools/run_release_gate.sh` now reaches
the production-promotion evidence gate. Earlier local blockers in
`src/state/state_root.py` acceptance-TCB branch coverage and UPBA v2 zero-fill
integration semantics were cleared with focused tests. The release gate still
exits nonzero at the production-promotion evidence bundle because five external
artifact lanes are intentionally absent: `oracle_authority`, `hardware_wallet`,
`zk_wrapping`, `autotrader`, and `confidential_runtime`. `app_root_jmt` is
auto-built from fresh local replay evidence by
`tools/run_production_promotion_evidence_gate.sh`.

Latest perps mechanism-design follow-up: PR 364 adds Lean-side FUNDED-LIQ
analysis for funded liquidation. The live isolated-perps enforcement point is
market-parameter admission (`create_market` and `set_market_params`), where
unfunded combinations are now rejected. The corresponding perps-v2 predicate is
kept advisory rather than registered in the per-step invariant registry, because
the registry runs after every kernel transition and would freeze legacy
parameter markets on unrelated operations.

## Authority Contract

The existing governance architecture is the right starting point:

```text
QPolicy(context) -> candidate_action
GovernanceGates(context, candidate_action) -> admissible
Commit(context, candidate_action) -> proposed_state if admissible else context.state
```

The policy ranks or proposes. The deterministic gates and node admission path
decide. Learned layers may improve search order, but they must not authorize
governance, settlement, upgrades, custody, or state roots.

Production AutoGovNEXT must preserve these boundaries:

- Runtime uses frozen, hash-pinned policy artifacts only.
- Julia, EBRM, and other optimizers stay offline.
- Every accepted autonomous governance update has a deterministic receipt.
- A policy hash mismatch rejects before state mutation.
- A forged result field, precomputed receipt, or model score cannot bypass live
  gate recomputation.
- Node replay from body plus pre-state reaches the same post-state and root.

## Mechanism Surface

### Game Surface

Players:

- Policy publisher: freezes a policy artifact and policy hash.
- Node writer: submits governance update transactions.
- Follower node: replays blocks and recomputes acceptance.
- Governance authority: validates threshold, timelock, evidence, and upgrade
  authority where required.
- Adversary: may submit stale observations, tampered policy hashes, forged
  receipts, repeated tx IDs, boundary states, or candidate actions near caps.

Actions:

- Publish policy artifact.
- Submit AutoGovNEXT observation plus expected policy hash.
- Evaluate candidate action.
- Recompute governance surface gates.
- Admit or reject a node transaction.
- Apply approved governance state or no-op on rejection.

Timing:

1. Policy artifact is frozen and reviewed.
2. Node receives an AutoGovNEXT request.
3. Node recomputes policy hash and candidate result.
4. Node recomputes deterministic gates against committed state.
5. Accepted request becomes a block operation.
6. Follower replay recomputes the same receipt, state, and root.

Payoff:

- Honest operator: deterministic approved updates inside the governance envelope.
- Adversary: profit only if a bad update enters committed node state or a
  follower accepts a different root.

### Attack Query

The main profitable-deviation query:

```text
exists request:
  NodeAccepts(request) and GateRejects(request)
```

There must be no request where the live node accepts an autonomous governance
transition that the deterministic gate suite rejects.

The replay query:

```text
exists body:
  WriterAccepts(body) and FollowerReplay(body) != WriterPostState(body)
```

There must be no accepted governance body whose follower replay diverges from
the writer's post-state or root.

### Bounded Model

Start with the existing bounded governance surface:

- `fee_bps`
- `buyburn_bps`
- `stakers_bps`
- `reserve_bps`
- `hosts_bps`
- `mcr_bps`
- `ccr_bps`
- `staker_bps`
- `funding_cap_bps`

Use the existing observation fields:

- `observed_price_bps`
- `target_price_bps`
- `deviation_bps`
- `volatility_bps`
- `divergence_bps`
- `freshness_lag_epochs`
- `liquidity_depth_bps`

Bound request fields before node admission:

- `policy_hash`: 64 lowercase hex characters.
- `tx_id`: canonical string, bounded length, unique for append idempotency.
- `current_epoch`, `proposal_epoch`, `time_ms`: nonnegative strict ints.
- `surface_state`: exact known field set, strict ints.
- `observation`: exact known field set, strict ints.
- `trajectory_budget`, `trajectory_used`, `previous_approved_deltas`: bounded
  maps over known parameter names.

### Evidence Lane

Required evidence for AutoGovNEXT promotion:

- Unit tests for policy hash, gate recomputation, request admission, and no-op
  rejection.
- Mutation-style regressions where a bad hash, forged approved flag, stale
  observation, unsafe surface delta, duplicated tx ID, and tampered node body
  all fail.
- Node tests where a writer appends an AutoGovNEXT transaction and a follower
  replays it to the same state root.
- CLI smoke tests for sample, admit, append, run, pull-live, and preflight.
- Policy-factory replay with full profile, not only a smoke profile, before
  any promotion claim.
- Lean, ESSO, or Tau artifacts for the safety envelope once the command ABI is
  stable.
- Release-gate inclusion so AutoGovNEXT cannot drift outside PR and release CI.

### Promotion Boundary

AutoGovNEXT can claim:

- Frozen policy artifacts are hash-pinned.
- Runtime candidate selection is deterministic.
- The node recomputes live governance gates before accepting a governance
  transition.
- Accepted governance node blocks replay to the same post-state and root across
  writer and follower.
- The autonomous action vocabulary is confined to the bounded economic surface;
  authority-changing keys, registries, digests, signer sets, and verifier IDs
  are denied in the AutoGovNEXT lane.

AutoGovNEXT cannot claim until separate evidence exists:

- Oracle truth.
- Global economic optimality.
- Safety of arbitrary future action vocabularies.
- Production custody safety.
- Settlement authorization.
- Upgrade-key correctness unless the governance authority and client pinning
  lanes are also complete.

## Phase 0: Release Hygiene Before Promotion

Purpose: make later evidence meaningful.

Tasks:

1. Create a clean implementation branch or worktree for AutoGovNEXT.
2. Rebase or merge the 12 missing upstream commits deliberately.
3. Preserve unrelated dirty work. Do not stage or revert unrelated files.
4. Record the exact base commit for every production-readiness claim.
5. Add a plan-entry or issue for dirty-tree cleanup before release candidate
   tagging.

Acceptance:

- `git status --short --branch` is clean or contains only reviewed,
  intentionally staged AutoGovNEXT changes before final promotion.
- The plan and evidence name the commit hash being promoted.

## Phase 1: Complete AutoGovNEXT Local Boundary

Purpose: create the deterministic front door before node wiring.

Tasks:

1. Add `sample_autonomous_governance_next_policy_v1` as a strict next-generation
   sample policy.
2. Add `admit_autonomous_governance_surface_request_v1`.
3. Make the request boundary validate schema, policy hash, observation,
   surface state, epochs, trajectory fields, and previous deltas.
4. Recompute the policy result internally. Ignore caller-provided `approved`,
   `receipt`, `proposed`, `scores`, and `action_id` as authority inputs.
5. Return a deterministic admission receipt with a stable hash.
6. Extend `tools/autonomous_governance_q_policy.py` with:
   - `sample --surface --next`
   - `admit`
7. Keep the existing `evaluate` and `step` behavior backward compatible.

Acceptance tests:

- Valid sample request admits.
- Policy hash mismatch rejects.
- Caller-forged approved result rejects or is ignored.
- Stale oracle observation rejects before commit.
- Surface gate rejection is a deterministic no-op.
- Unknown fields reject at the request boundary where consensus meaning would
  be ambiguous.
- Policy cannot authorize settlement or enter state roots without node
  admission.

Primary files:

- `src/integration/autonomous_governance_q_policy.py`
- `tools/autonomous_governance_q_policy.py`
- `tests/integration/test_autonomous_governance_q_policy.py`

## Phase 2: Wire AutoGovNEXT Into A Real Node Path

Purpose: make autonomous governance replayable by writer and follower nodes.

Add a first-class transaction operation:

```text
governance.autogov_next_admit_v1
```

Command ABI:

- `tx_id`
- `sender_pubkey` or governance submitter identity
- `expected_policy_hash`
- `policy`
- `surface_state`
- `observation`
- `current_epoch`
- `proposal_epoch`
- `last_update_epoch`
- `previous_approved_deltas`
- `trajectory_budget`
- `trajectory_used`

Effect ABI:

- `governance.autogov_next_admitted_v1`
- `governance.autogov_next_rejected_v1`

State ownership:

- Governance module owns the autonomous governance surface state.
- Ledger and settlement modules do not read model outputs.
- The node appends only the deterministic receipt and resulting state update.

Node tasks:

1. Add an append function parallel to `append_dex_transaction_v0`, or extend the
   block operation dispatcher with a typed governance operation while preserving
   existing DEX transaction behavior.
2. Add CLI command:
   - `tools/zeno_ledger_node.py append-autogov-next`
3. Add HTTP endpoint behind the same write-auth and intake controls:
   - `POST /api/governance/autogov-next`
4. Ensure `/tx` can carry the operation only through the same deterministic
   admission path.
5. Store append reports and receipt hashes exactly like other node append
   reports.
6. Add follower replay tests using `pull-live` or a direct replay harness.

Acceptance tests:

- Writer accepts a valid AutoGovNEXT transaction.
- Follower replays the block to the same `app_hash`.
- Duplicate `tx_id` returns the prior append report without reapplying.
- Tampered policy hash rejects with no state mutation.
- Tampered body fails replay.
- Missing write auth rejects before evaluation.
- Public-operator preflight rejects any public unauthenticated mutation path.

Primary files:

- `tools/zeno_ledger_node.py`
- `src/integration/autonomous_governance_q_policy.py`
- `src/integration/zeno_governance_authority.py`
- `tests/integration/test_zeno_ledger_node_autogovnext.py`
- `tests/integration/test_autonomous_governance_q_policy.py`

## Phase 3: Governance Authority And Upgrade Pinning

Purpose: keep AutoGovNEXT from becoming an upgrade oracle.

Tasks:

1. Bind AutoGovNEXT to `evaluate_governance_authority_v0` for any action that
   changes production authority, verifier keys, image IDs, policy registries,
   threshold signer sets, or deployment profiles.
   - Current status: AutoGovNEXT rejects these fields outright through
     `AUTOGOVNEXT_FORBIDDEN_AUTHORITY_PARAMETERS_V1`; authority-changing
     actions remain outside the autonomous vocabulary and must use the
     governance-authority lane.
2. Require timelock and threshold evidence for authority-changing governance
   actions.
3. Add client-side expected image ID and verifier-key pinning where proof
   clients consume governed headers.
   - Current status: browser checkpoint clients now require caller-pinned
     checkpoint trust anchors, and strict ZK proof-status parsing supports
     caller-pinned verifier/circuit/image artifact hashes. Each concrete RISC0
     receipt consumer must still supply the expected artifact identity.
4. Add rejection tests for committee-signed headers that change verifier
   meaning without a client-pinned expected identity.
5. Keep policy ranking outside the authority path. The authority function must
   not import model or residual-ranker modules.

Acceptance:

- Governance parameter updates can be autonomous only inside the bounded surface.
- Verifier identity, custody, signer registry, and upgrade actions require the
  production governance authority gate.
- Browser and CLI proof clients fail closed on image ID mismatch.

## Phase 4: Formal And Receipt Evidence

Purpose: prevent a config-only or receipt-only change from weakening the claim.

Tasks:

1. Add a Lean, ESSO, or Tau safety-envelope artifact for:

   ```text
   Admit(request) -> GatesAccept(request) and CommitIsNoopOnReject(request)
   ```

   The accept decision is the hypothesis. The safety property is the
   conclusion.

2. Maintain the committed public manifest for the AutoGovNEXT artifact.
3. Hash-pin:
   - source files
   - policy sample
   - formal artifact
   - tests
   - required commands
4. Add tamper tests for dropping an action, weakening a verdict, changing a
   command path, and editing only receipt metadata.
5. Keep the focused AutoGovNEXT replay gate in PR CI and release-integrity.
   Keep the manifest checker's tamper and downgrade regressions green.

Acceptance:

- A source change that bypasses gate recomputation fails CI.
- A receipt-only weakening fails CI.
- A policy-only action vocabulary change fails unless all action gate
  diagnostics and node replay tests pass.

## Phase 5: DEX Production Closure After AutoGovNEXT

Purpose: finish the rest of the DEX under the same evidence standard.

Current gate state:

- `bash tools/run_critical_quality_gate.sh` passes locally.
- `bash tools/run_acceptance_tcb_gate.sh` passes locally;
  `src/state/state_root.py` branch coverage is 98.7% against a 77.0% floor after
  adding LP metadata, nonce, and preimage type-check regressions.
- The UPBA bounded-grid release slice passes locally:

  ```bash
  cd lean-mathlib && lake env lean Proofs/UniformBatchOptimality.lean
  python3 -m pytest -q tests/core/test_uniform_batch_optimality.py tests/integration/test_dex_engine_uniform_batch_certificate.py
  # 79 passed
  ```

- `bash tools/run_release_gate.sh` progresses through the release sections up to
  `== release: production promotion evidence ==`, then fails closed on missing
  real-world production artifacts. This is expected until the external evidence
  lanes below are supplied.

Production-promotion evidence lanes still blocking the full release gate:

| Lane | Required external artifact class | Current status |
|---|---|---|
| `oracle_authority` | Public-testnet bounded oracle authority exercise with broadcast and settlement block references plus authority attestation | Missing |
| `hardware_wallet` | Hardware wallet attestation, OS prompt capture hash, and device approval transaction signature | Missing |
| `zk_wrapping` | Live proof-wrapper status with verified proof, audited circuit/verifier/source hashes, and sample accepted proof receipt | Missing |
| `autotrader` | 24h+ unattended supervisor evidence, crash recovery checkpoint, multi-signer approvals, and budget compliance | Missing |
| `confidential_runtime` | Approved TEE measurement, verifier binding, operator status hash, and redacted private execution receipt | Missing |

These lanes must be filled with real artifacts through
`tools/production_promotion_evidence_manifest.json` and validated by
`tools/run_production_promotion_evidence_gate.sh`. They must not be replaced by
fixture receipts or local-only smoke output.

Current checker hardening in this workstream:

- `app_root_jmt` can be auto-filled by the shell gate from live-root replay
  evidence and still does not clear the five external lanes.
- `zk_wrapping` rejects hand-made live-wrapper JSON unless it has the expected
  wrapper schema, proof/verifier/artifact configuration, no wrapper error, and
  matching sample proof request and receipt hashes. The lane also binds the
  captured live wrapper verifier/circuit artifact metadata and artifact-binding
  hash back to the evidence body so a sidecar from one circuit or verifier
  cannot clear another circuit's production-promotion evidence. The surface
  must also match the independently configured production surface.
- `hardware_wallet` rejects stale device approvals rehashed with a fresh
  `issued_at`; the prompt and approval must remain close in time, and the
  approval itself must be fresh relative to evidence issuance. The lane also
  verifies the device attestation and approval signatures over canonical
  ZenoDEX custody messages, and the attested pubkey must match the independently
  configured expected device pubkey. Correctly shaped hex signatures are not
  sufficient.
- `autotrader` rejects an internally coherent but stale 24h run rehashed with a
  fresh `issued_at`; the latest supervisor heartbeat must be fresh relative to
  the evidence issuance time. Each production approval must also carry a valid
  signer Ed25519 signature over the canonical run approval message. The run
  must match the independently configured chain ID and production budget caps.
- `confidential_runtime` rejects private execution receipts whose
  `result_code` is not `ok`, binds the approved-measurements digest to the
  active allowlist, requires the extension ID to match the independently
  configured production extension, and recomputes the canonical confidential
  runtime receipt hash from the redacted receipt fields plus the active
  operator/verifier bindings.
- `oracle_authority` rejects localhost, private, or non-routable explorer URLs
  for public-testnet evidence, and verifies the authority attestation as an
  Ed25519 signature over the canonical public-testnet exercise statement. The
  chain ID and signer pubkey must also match the independently configured
  production chain and oracle authority signer key in the promotion manifest.

Adopted preflight for any production-readiness edit:

```bash
python3 .claude/skills/zenodex-style-map/scripts/which_style.py <changed-paths>
python3 .claude/skills/zenodex-security-analysis/scripts/redflags.py <changed-paths>
python3 .claude/skills/zenodex-refactoring/scripts/design_metrics.py <changed-paths> --top 20
```

Use these to focus review attention. A clean preflight does not promote any
claim. Findings require the normal focused test, manifest, or release-gate
evidence before they can change readiness posture.

Operator collection sequence for the five external production-promotion lanes:

```bash
PYTHON=.venv/bin/python bash tools/run_production_promotion_evidence_gate.sh \
  tools/production_promotion_evidence_manifest.json \
  --explain-missing \
  --include-runbook
```

The command above is the operator entrypoint for the source-of-truth runbook
renderer. It delegates to the manifest checker, auto-fills fresh `app_root_jmt`
replay evidence where allowed, and reports the current lane requirements and
producer command templates. The example below shows the shape of the expected
operator flow.

```bash
mkdir -p runs/production_promotion/latest

python3 tools/build_oracle_authority_evidence.py \
  --bounded-oracle-exercise-status runs/production_promotion/latest/bounded_oracle_exercise_status.json \
  --out runs/production_promotion/latest/oracle_authority.json \
  --authority-id ORACLE_AUTHORITY_ID \
  --target-network public_testnet \
  --public-broadcast-block-hash PUBLIC_BROADCAST_BLOCK_HASH \
  --public-settlement-block-hash PUBLIC_SETTLEMENT_BLOCK_HASH \
  --public-broadcast-explorer-url PUBLIC_BROADCAST_EXPLORER_URL \
  --public-settlement-explorer-url PUBLIC_SETTLEMENT_EXPLORER_URL \
  --authority-attestation-signature AUTHORITY_ATTESTATION_SIGNATURE \
  --authority-attestation-signer-pubkey AUTHORITY_ATTESTATION_SIGNER_PUBKEY \
  --expected-chain-id EXPECTED_CHAIN_ID \
  --expected-authority-signer-pubkey EXPECTED_ORACLE_AUTHORITY_SIGNER_PUBKEY \
  --check

python3 tools/build_hardware_wallet_evidence.py \
  --out runs/production_promotion/latest/hardware_wallet.json \
  --device-id DEVICE_ID \
  --device-model DEVICE_MODEL \
  --device-firmware-version DEVICE_FIRMWARE_VERSION \
  --device-pubkey DEVICE_PUBKEY \
  --attestation-challenge ATTESTATION_CHALLENGE \
  --attestation-signature ATTESTATION_SIGNATURE \
  --prompt-kind PROMPT_KIND \
  --prompt-hash PROMPT_HASH \
  --prompt-captured-at PROMPT_CAPTURED_AT \
  --approval-tx-payload-hash APPROVAL_TX_PAYLOAD_HASH \
  --approval-signature APPROVAL_SIGNATURE \
  --approval-captured-at APPROVAL_CAPTURED_AT \
  --wallet-authority-profile-hash WALLET_AUTHORITY_PROFILE_HASH \
  --expected-device-pubkey EXPECTED_DEVICE_PUBKEY \
  --check

python3 tools/build_zk_wrapping_evidence_from_risc0_bundle.py \
  --risc0-surface-bundle runs/production_promotion/latest/risc0_surface_bundle.json \
  --out runs/production_promotion/latest/zk_wrapping.json \
  --live-wrapper-out runs/production_promotion/latest/live_proof_wrapper_status.json \
  --surface EXPECTED_SURFACE \
  --expected-surface EXPECTED_SURFACE \
  --verifier-cmd-json VERIFIER_CMD_JSON \
  --live-wrapper-status runs/production_promotion/input/live_proof_wrapper_status.json \
  --audit-id AUDIT_ID \
  --audit-report-hash AUDIT_REPORT_HASH \
  --auditor AUDITOR \
  --audited-at AUDITED_AT \
  --check

python3 tools/build_autotrader_evidence.py \
  --out runs/production_promotion/latest/autotrader.json \
  --supervisor-id SUPERVISOR_ID \
  --chain-id EXPECTED_CHAIN_ID \
  --profile-supervisor-hash SUPERVISOR_PROFILE_HASH \
  --started-at STARTED_AT \
  --last-heartbeat-at LAST_HEARTBEAT_AT \
  --duration-seconds DURATION_SECONDS \
  --ticks-executed TICKS_EXECUTED \
  --ticks-failed TICKS_FAILED \
  --ticks-throttled TICKS_THROTTLED \
  --heartbeat-timestamps-file runs/production_promotion/latest/autotrader_heartbeats.json \
  --crash-recovery-file runs/production_promotion/latest/autotrader_crash_recovery.json \
  --multi-signer-approvals-file runs/production_promotion/latest/autotrader_multisig_approvals.json \
  --expected-approval-signer-pubkeys-file runs/production_promotion/latest/autotrader_expected_approvers.json \
  --max-actions-per-tick-observed MAX_ACTIONS_PER_TICK_OBSERVED \
  --max-runs-per-process-observed MAX_RUNS_PER_PROCESS_OBSERVED \
  --config-max-actions-per-tick CONFIG_MAX_ACTIONS_PER_TICK \
  --config-max-runs-per-process CONFIG_MAX_RUNS_PER_PROCESS \
  --expected-chain-id EXPECTED_CHAIN_ID \
  --check

python3 tools/build_confidential_runtime_evidence.py \
  --out runs/production_promotion/latest/confidential_runtime.json \
  --extension-id EXPECTED_EXTENSION_ID \
  --provider-id PROVIDER_ID \
  --tee-kind TEE_KIND \
  --raw-attestation-hash RAW_ATTESTATION_HASH \
  --measurement APPROVED_MEASUREMENT \
  --measurement-in-allowlist \
  --platform-pubkey PLATFORM_PUBKEY \
  --attestation-signature ATTESTATION_SIGNATURE \
  --tee-verified-at TEE_VERIFIED_AT \
  --operator-status-hash OPERATOR_STATUS_HASH \
  --external-verifier-binding-hash EXTERNAL_VERIFIER_BINDING_HASH \
  --runtime-receipt-hash RUNTIME_RECEIPT_HASH \
  --attestation-receipt-hash ATTESTATION_RECEIPT_HASH \
  --request-id REQUEST_ID \
  --execution-id EXECUTION_ID \
  --execution-kind EXECUTION_KIND \
  --result-code RESULT_CODE \
  --result-redacted \
  --attestation-epoch ATTESTATION_EPOCH \
  --current-epoch CURRENT_EPOCH \
  --units-charged UNITS_CHARGED \
  --public-effect-digest PUBLIC_EFFECT_DIGEST \
  --approved-measurement APPROVED_MEASUREMENT \
  --expected-extension-id EXPECTED_EXTENSION_ID \
  --check

python3 tools/build_production_promotion_evidence_manifest.py \
  --out runs/production_promotion/latest/production_promotion_evidence_manifest.json \
  --oracle-authority runs/production_promotion/latest/oracle_authority.json \
  --hardware-wallet runs/production_promotion/latest/hardware_wallet.json \
  --zk-wrapping runs/production_promotion/latest/zk_wrapping.json \
  --autotrader runs/production_promotion/latest/autotrader.json \
  --confidential-runtime runs/production_promotion/latest/confidential_runtime.json \
  --bounded-oracle-exercise-status runs/production_promotion/latest/bounded_oracle_exercise_status.json \
  --wallet-authority-profile-hash WALLET_AUTHORITY_PROFILE_HASH \
  --live-proof-wrapper-status runs/production_promotion/latest/live_proof_wrapper_status.json \
  --supervisor-profile-hash SUPERVISOR_PROFILE_HASH \
  --config-max-actions-per-tick CONFIG_MAX_ACTIONS_PER_TICK \
  --config-max-runs-per-process CONFIG_MAX_RUNS_PER_PROCESS \
  --approved-measurement APPROVED_MEASUREMENT \
  --operator-status-hash OPERATOR_STATUS_HASH \
  --external-verifier-binding-hash EXTERNAL_VERIFIER_BINDING_HASH \
  --expected-chain-id EXPECTED_CHAIN_ID \
  --expected-oracle-authority-signer-pubkey EXPECTED_ORACLE_AUTHORITY_SIGNER_PUBKEY \
  --expected-surface EXPECTED_SURFACE \
  --expected-extension-id EXPECTED_EXTENSION_ID \
  --expected-device-pubkey EXPECTED_DEVICE_PUBKEY \
  --check \
  --explain-missing

PYTHON=.venv/bin/python bash tools/run_production_promotion_evidence_gate.sh \
  runs/production_promotion/latest/production_promotion_evidence_manifest.json \
  --explain-missing
```

The placeholder values above must come from public-testnet, hardware-device,
auditor, live-wrapper, supervisor, and TEE/operator artifacts. The manifest
builder recomputes lane hashes and sidecar-relative paths; it does not
synthesize the external evidence.

### Persistent Authoritative State Performance Milestone

Schedule this as a dedicated future PR after PRs #459 and #460 close
transitive ownership for committed state, signed commands, and accepted
effects. Complete it before parallel value-moving execution depends on
structural sharing for throughput. This is a representation and performance
refinement. It does not replace the current security closures or raise the
production posture by itself.

Target owned persistent maps and vectors that path-copy changed nodes and
share unchanged immutable structure. A persistent balanced map should target
logarithmic lookup, update, and new-node allocation per changed key. Initial
conversion and full canonical serialization remain linear in state size
unless a separately verified incremental-root design is introduced.

Construction rules:

1. Keep authoritative state in the persistent representation across the
   transition chain. Rebuilding it from ordinary dictionaries at every
   boundary would retain the current linear-copy cost.
2. Own every node and nested value. A read-only view over a caller-owned
   mutable container does not satisfy transitive immutability.
3. Define canonical iteration and encoding independently of tree shape,
   insertion history, hash seed, object identity, process, and library
   implementation details.
4. Require observable parity with the current sequential reference:

   ~~~text
   PersistentStepV1(pre_state, commands, execution_context)
     =
   SequentialStepV1(pre_state, commands, execution_context)
   ~~~

   Equality covers acceptance or rejection and precedence, post-state,
   canonical roots, effects, receipts, nonces, fees, rounding, and residue.
5. Permit mutable builders only when they are fresh, exclusive, local to one
   transition, non-escaping, and discarded completely on rejection.
6. Treat incremental Merkle hashing as a separate refinement boundary. A
   persistent container alone does not establish an incremental-root proof.
7. Version migration and canonical representation. Reject mixed-version
   states unless an exact migration and rollback path is specified and tested.

Required evidence:

- retained-alias, base-class bypass, getter, and nested-value mutation tests;
- byte-for-byte canonical encoding and state-root parity with the reference;
- stateful and differential insert, update, delete, retry, reject, migrate,
  rollback, and replay tests;
- BVA for empty, singleton, maximum-size, key-order, collision, and
  pathologically concentrated update cases;
- benchmarks for construction, lookup, update, iteration, canonical encoding,
  root computation, memory, and retained historical versions;
- dependency review covering determinism, license, maintenance, transitive
  size, version pinning, denial-of-service behavior, and a removal path;
- Python, Rust, and proof-guest golden vectors where the representation crosses
  a language or proof boundary.

Promote the representation only when realistic workloads show a measurable
improvement and all consensus-visible outputs remain identical.

### Deterministic-By-Construction Parallel Execution Milestone

Position this milestone after committed-state, signed-command, and accepted-
effect transitive immutability close, currently tracked by PRs #459 and #460,
and after execution-context/consensus binding is available. It must close
before throughput scaling or production promotion can rely on parallel
value-moving execution.

Keep the sequential functional core as the normative executable reference.
For every supported worker count and deterministic partition profile, require:

```text
ParallelStepV1(pre_state, command_batch, execution_context, worker_profile)
  =
SequentialStepV1(pre_state, command_batch, execution_context)
```

Equality covers:

- accepted versus rejected outcome and canonical reject class;
- post-state value and canonical state root;
- canonical effect-plan bytes and effect-plan hash;
- nonce, replay key, receipt, and outbox contents;
- overflow, rounding, dust, fee, ordering, and claimant semantics.

Construction rules:

1. Bind every worker to the same immutable pre-state root, command-set root,
   execution-context hash, policy hash, and module-version digest.
2. Partition work by a canonical committed key or range. Host scheduling,
   work stealing, completion order, thread count, and process layout cannot
   change protocol observables.
3. Permit workers to return data-only candidates. Workers cannot mutate shared
   committed state or execute external effects.
4. Use a fixed, versioned reduction tree when arithmetic is not proven
   associative and commutative under the exact integer and rounding rules.
5. Resolve duplicate keys, conflicting writes, and multiple rejections by a
   canonical total order declared in the protocol.
6. Join all worker outputs into one owned immutable post-state and effect plan.
   Any worker failure, missing result, duplicate result, context mismatch, or
   join violation rejects with no candidate state and no effects.
7. Commit state, effects, replay identity, receipt, and outbox atomically using
   compare-and-swap against the expected pre-state root.

Adoption order:

1. Parallelize proof generation and read-only validation first.
2. Parallelize disjoint state-root and certificate lanes with fixed joins.
3. Admit parallel value-moving transitions only after sequential/parallel
   observational equivalence is a required release gate.

Required evidence:

- differential replay across worker counts `1, 2, 4, 8` and multiple host
  schedules;
- property and stateful tests for permutation, retry, crash, timeout, worker
  loss, duplicate result, and rejected-transition no-op;
- cross-platform determinism over Python/Rust and supported operating systems;
- canonical state/effect/receipt golden vectors;
- bounded ESSO, SMT, Tau, or Lean evidence for partition coverage, unique
  ownership, fixed joins, and reduction arithmetic;
- recursive-proof checks that every child binds the same block context, or an
  exact ordered contiguous block range when aggregating across blocks;
- benchmarks with committed resource limits. Performance measurements do not
  promote safety or refinement claims.

Progressive cooldown, exponential backoff, local clocks, random scheduling,
and unordered reductions remain outside consensus semantics. Retry backoff may
exist in the imperative shell, where it cannot alter accepted state or effects.

Workstreams in dependency order:

1. State root and canonical root:
   - complete canonical multi-lane root or JMT keystone;
   - close transitive ownership of committed state, signed commands, and
     accepted effects before parallel execution;
   - bind field-level encoding to live encoders;
   - prove membership and non-membership paths needed by escape and light
     clients.
2. ZK to consensus binding:
   - prove RISC0 guests execute the live transition, not a parallel statement;
   - bind journals to canonical `post_state_root`;
   - add client refuse-by-default proof verification.
3. Deterministic parallel execution:
   - preserve the sequential functional core as the executable reference;
   - implement canonical partition, fixed join, exact-no-op failure, and atomic
     commit boundaries;
   - gate every parallel profile on state, effect, receipt, and root equality.
4. Spot and settlement:
   - finish exact-out settlement path and split-routing settlement binding;
   - keep direct pure-core helpers unexposed;
   - retain strong proof-carrying validation.
5. Balances and nonces:
   - close proof-to-live-transition binding;
   - keep per-change proof receipts CI-gated;
   - bind replay authority to the live admission path.
6. Perps and zUSD:
   - close funding, liquidation, breaker, and wallet-state surfacing;
   - add guest-to-Python differentials for all value-moving guest actions;
   - require proof coverage for production profiles.
7. Oracle:
   - replace single-source trust with quorum, staleness bounds, divergence
     limits, and production evidence receipts;
   - add adversarial stale and divergent report tests.
8. Runtime and UI:
   - remove timer-based finality;
   - poll receipt/finality endpoints;
   - remove or gate fake safety badges;
   - ensure production configs cannot expose fixture keys or unsigned mutation
     paths.
9. Release evidence:
   - run full release gate from a clean commit;
   - produce two-machine and multi-validator evidence;
   - include Docker, Trivy, dependency audit, Rust parity, proof receipts,
     coverage, mutation tests, and chaos reports.

## Phase 6: Release Candidate Definition Of Done

ZenoDEX is production-ready only when all of these are true on a clean,
pinned candidate commit:

1. AutoGovNEXT node writer and follower tests pass.
2. AutoGovNEXT public receipt checker passes and has tamper regressions.
3. Governance authority and upgrade pinning fail closed in CLI and browser
   clients.
4. Every value-moving production path uses fail-closed validation or a stronger
   proof/replay profile.
5. Unsupported or unproved transition families reject under proof-required
   profiles.
6. ZK proof journals bind to canonical state roots, and clients refuse unproven
   responses by default.
7. State-root, balances, nonces, spot, perps, zUSD, oracle, and proof-market
   lanes have current evidence artifacts.
8. Every production parallel-execution profile is observationally equal to the
   sequential reference across supported worker counts and schedules, with
   canonical joins and exact-no-op failure.
9. `production_security_claim` flips only after the full evidence bundle passes
   and is reviewed.
10. Full release gate passes without local-only hidden toolchain assumptions.
11. Two independent nodes replay to the same root under realistic network
    conditions.

## Initial Verification Commands

Run these after Phase 1:

```bash
python3 -m pytest -q tests/integration/test_autonomous_governance_q_policy.py
python3 tools/autonomous_governance_q_policy.py sample --surface --next --output /tmp/autogov_next_bundle.json
python3 tools/autonomous_governance_q_policy.py admit /tmp/autogov_next_bundle.json
python3 tools/check_production_boundary.py --json
```

Run these after Phase 2:

```bash
python3 -m pytest -q tests/integration/test_zeno_ledger_node_autogovnext.py
python3 tools/zeno_ledger_make_public_testnet_bundle.py --out-dir /tmp/zenodex-autogov-bundle
python3 tools/zeno_ledger_node.py run --bundle-root /tmp/zenodex-autogov-bundle --node-id writer --data-dir /tmp/zenodex-autogov-writer
python3 tools/zeno_ledger_node.py append-autogov-next --data-dir /tmp/zenodex-autogov-writer --request /tmp/autogov_next_request.json
python3 tools/zeno_ledger_node.py pull-live --data-dir /tmp/zenodex-autogov-follower --peer-url http://127.0.0.1:8787
```

Run these before any promotion claim:

```bash
python3 tools/permissionless_assurance.py status
python3 tools/check_production_boundary.py --json
python3 tools/autonomous_governance_policy_factory.py --out-dir runs/autonomous_governance_policy_factory/latest
python3 tools/autonomous_governance_policy_factory.py --check-policy runs/autonomous_governance_policy_factory/latest/optimized_policy.frozen.json --training-corpus runs/autonomous_governance_policy_factory/latest/ebr_training_corpus.json --optimizer-report runs/autonomous_governance_policy_factory/latest/optimizer_report.json --factory-report runs/autonomous_governance_policy_factory/latest/policy_factory_report.json --report-output runs/autonomous_governance_policy_factory/latest/policy_artifact_check.json
bash tools/run_release_gate.sh
bash tools/prod_gate.sh
```

## First Implementation Sprint

Sprint objective: land AutoGovNEXT local request admission and node wiring
without changing unrelated DEX behavior.

Atomic commits:

1. Add AutoGovNEXT request boundary and CLI admission command.
2. Add request-boundary tests and mutation regressions.
3. Add node operation ABI and append command.
4. Add writer/follower node replay tests.
5. Add receipt checker or release-gate hook.
6. Update docs and evidence command list.

Do not flip production claims in these commits. The first acceptable claim is:
AutoGovNEXT is deterministic, hash-pinned, and node-replayable under the tested
public-testnet path.

## Open Blockers

- Current checkout is dirty and branch-diverged.
- AutoGovNEXT local admission, node append/replay, app-root commitment, no-op
  rejection, authority-parameter confinement, and the committed public manifest
  gate exist in this working tree; they still need clean-candidate review and
  promotion from a non-diverged branch.
- Governance-authority reset remains a separate future lane. AutoGovNEXT v1
  pins `no_auto_reset_governance_authority_only_v1`.
- Browser and package proof-client pinning are covered for the local checkpoint
  and strict ZK proof-status parser paths, but every concrete RISC0 receipt
  consumer still has to pass the expected artifact identity before a
  proof-client production claim is justified.
- The focused AutoGovNEXT governance-lane gate passed locally. The full release
  gate has not been run in this session.
- Production readiness still depends on ZK-to-consensus binding, client
  refuse-by-default verification, state-root root-of-roots, oracle de-trust,
  perps/zUSD closure, and multi-node replay evidence.
