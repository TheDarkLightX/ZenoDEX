# Production Promotion Evidence Requirements

ZenoDEX production promotion is blocked until the six production-evidence lanes
in `tools/production_promotion_evidence_manifest.json` evaluate to
`production_ready: true`.

Run the gate with an explanation payload:

```bash
bash tools/run_production_promotion_evidence_gate.sh --explain-missing
```

The explanation payload includes each lane's `producer_tool`, required manifest
config, required evidence fields, external artifacts, and validator function.
Those entries are generated from the same checker that blocks promotion, so
operators should treat the JSON as the live contract.

Build a manifest from lane evidence JSON bodies and attach the correct
lane-specific `evidence_hash` values:

```bash
mkdir -p /tmp/zenodex-promotion-evidence
cp /path/to/oracle_authority.json /tmp/zenodex-promotion-evidence/oracle_authority.json
cp /path/to/app_root_jmt.json /tmp/zenodex-promotion-evidence/app_root_jmt.json
cp /path/to/bounded_oracle_exercise.json /tmp/zenodex-promotion-evidence/bounded_oracle_exercise.json

python3 tools/build_production_promotion_evidence_manifest.py \
  --out /tmp/zenodex-promotion-evidence/production_promotion_manifest.json \
  --oracle-authority /tmp/zenodex-promotion-evidence/oracle_authority.json \
  --app-root-jmt /tmp/zenodex-promotion-evidence/app_root_jmt.json \
  --bounded-oracle-exercise-status /tmp/zenodex-promotion-evidence/bounded_oracle_exercise.json \
  --expected-chain-id tau-test-prod \
  --now <unix-seconds> \
  --check-lane oracle_authority
```

The full release gate also runs this check:

```bash
bash tools/run_release_gate.sh
```

For a real promotion run, point the release gate at the generated manifest:

```bash
PRODUCTION_PROMOTION_EVIDENCE_MANIFEST=/tmp/zenodex-promotion-evidence/production_promotion_manifest.json \
  bash tools/run_release_gate.sh
```

The checker is intentionally fail-closed. Missing evidence, malformed JSON,
unknown fields, stale timestamps, mismatched hashes, and unbound sidecar status
files keep the promotion blocked.

For reproducible archived bundles, pass explicit `--issued-at`, `--accepted-at`,
`--now`, and `--check-now` values rather than relying on wall-clock defaults.

Sidecar paths in manifest config, such as `bounded_oracle_exercise_status_path`
and `live_proof_wrapper_status_path`, must be relative, must point to existing
files under the manifest directory, and are resolved from the manifest file's
directory. Put the manifest and all sidecars in one evidence directory so the
directory can be archived, moved, and checked from any current working
directory. Absolute sidecar paths and `../` escapes are rejected because they
would make the promotion depend on operator-local workspace layout.

The shell wrapper auto-builds fresh `app_root_jmt` evidence for full-scope
checks and for `--lane app_root_jmt`. Selected external-lane checks, for example
`--lane oracle_authority`, stay scoped to that lane and do not run unrelated
app-root replay tooling.

## App-Root / JMT

Purpose: prove live and release-replayed roots use the typed all-lane app-root
JMT rather than a spot-only root or fixture evidence.

Build the evidence body from the replayable root paths:

```bash
python3 tools/build_app_root_jmt_evidence.py \
  --out /tmp/app_root_jmt_evidence.json \
  --now <unix-seconds>
```

Required evidence fields:

- `schema`
- `evidence_kind`
- `root_system`
- `required_lane_kinds`
- `live_root_checks`
- `negative_checks`
- `issued_at`
- `evidence_hash`

Required positive checks:

- plain Dex snapshot live-root replay;
- local block pre-snapshot header root replay.

The historical Tau app-state wrapper remains research-oracle material. Current
Tau integration requires the versioned ingress adapter selected by the
whole-program plan before it can supply a new live-root replay mode.

Required negative check:

- lane-tamper rejection.

The evidence must cover `spot`, `oracle`, `vault`, `perps`, `zusd`, `clob`,
and `proof_mining`. Evidence marked fixture, synthetic, demo, or echo remains
blocked.

Validator: `evaluate_production_app_root_jmt_evidence_v2`.

## Oracle Authority

Purpose: prove the production oracle authority exercised the public-testnet
path.

Build the evidence body from a bounded oracle exercise status plus public block
references and attestation material:

```bash
python3 tools/build_oracle_authority_evidence.py \
  --bounded-oracle-exercise-status /path/to/bounded_oracle_exercise.json \
  --out /tmp/oracle_authority_evidence.json \
  --authority-id zeno-oracle-prod \
  --public-broadcast-block-hash <64-hex-broadcast-block-hash> \
  --public-settlement-block-hash <64-hex-settlement-block-hash> \
  --public-broadcast-explorer-url <broadcast-block-url> \
  --public-settlement-explorer-url <settlement-block-url> \
  --authority-attestation-signature <128-hex-signature> \
  --authority-attestation-signer-pubkey <64-hex-pubkey> \
  --expected-chain-id tau-test-prod \
  --expected-authority-signer-pubkey <64-hex-pubkey> \
  --issued-at <unix-seconds> \
  --check-now <unix-seconds> \
  --check
```

Required manifest config:

- `bounded_oracle_exercise_status_path`
- `expected_chain_id`
- `expected_oracle_authority_signer_pubkey`

Required evidence fields:

- `schema`
- `authority_id`
- `chain_id`
- `target_network`
- `exercise_hash`
- `profile_authority_hash`
- `public_broadcast_height`
- `public_settlement_height`
- `public_broadcast_block_hash`
- `public_settlement_block_hash`
- `public_broadcast_explorer_url`
- `public_settlement_explorer_url`
- `authority_attestation_signature`
- `authority_attestation_signer_pubkey`
- `issued_at`
- `evidence_hash`

External artifacts:

- bounded oracle exercise JSON with `authority_exercised=true`
- public testnet broadcast and settlement block references
- oracle authority attestation signature from the manifest-configured signer
  pubkey

Validator: `evaluate_production_oracle_authority_evidence_v1`.

## Hardware Wallet

Purpose: prove the active wallet authority is bound to a real hardware-device
approval.

Build the evidence body from hardware-device attestation, prompt capture, and
approval transaction material:

```bash
python3 tools/build_hardware_wallet_evidence.py \
  --out /tmp/hardware_wallet_evidence.json \
  --device-id ledger-x-prod-01 \
  --device-model ledger-nano-x \
  --device-firmware-version 2.4.0 \
  --device-pubkey <64-hex-device-pubkey> \
  --attestation-challenge <64-hex-challenge> \
  --attestation-signature <128-hex-attestation-signature> \
  --prompt-kind screenshot_hash \
  --prompt-hash <64-hex-prompt-capture-hash> \
  --prompt-captured-at <unix-seconds> \
  --approval-tx-payload-hash <64-hex-approval-payload-hash> \
  --approval-signature <128-hex-approval-signature> \
  --approval-captured-at <unix-seconds> \
  --wallet-authority-profile-hash <active-wallet-authority-profile-hash> \
  --expected-device-pubkey <64-hex-device-pubkey> \
  --issued-at <unix-seconds> \
  --check-now <unix-seconds> \
  --check
```

Required manifest config:

- `wallet_authority_profile_hash`
- `expected_device_pubkey`

Required evidence fields:

- `schema`
- `device_id`
- `device_model`
- `device_firmware_version`
- `device_attestation`
- `os_prompt_capture`
- `device_approval_tx`
- `profile_wallet_authority_hash`
- `issued_at`
- `evidence_hash`

External artifacts:

- hardware wallet attestation pubkey, challenge, and signature
- OS prompt capture hash
- device approval transaction payload hash and signature

Validator: `evaluate_production_hardware_wallet_evidence_v1`.

## ZK Wrapping

Purpose: prove the live proof wrapper is bound to an audited verifier/circuit
artifact.

Build the evidence body from a validated RISC0 surface bundle and an externally
captured live-wrapper status. The live-wrapper status must come from
`verify_live_proof_wrapper`; this builder does not fabricate a verified sidecar.
For local preflight only, pass `--candidate-only` without `--check`; candidate
output cannot clear the production lane.

```bash
python3 tools/build_zk_wrapping_evidence_from_risc0_bundle.py \
  --risc0-surface-bundle /path/to/risc0_surface_bundle.json \
  --out /tmp/zk_wrapping_evidence.json \
  --live-wrapper-status /path/to/live_proof_wrapper_status.json \
  --live-wrapper-out /tmp/live_proof_wrapper_status.json \
  --surface risc0.zenodex_public_surfaces.v1 \
  --expected-surface risc0.zenodex_public_surfaces.v1 \
  --verifier-cmd-json '["r0vm","verify"]' \
  --audit-id audit-risc0-surfaces-1 \
  --audit-report-hash <64-hex-audit-report-hash> \
  --auditor <auditor-id> \
  --audited-at <unix-seconds> \
  --accepted-at <unix-seconds> \
  --issued-at <unix-seconds> \
  --check-now <unix-seconds> \
  --check
```

Required manifest config:

- `live_proof_wrapper_status_path`
- `expected_surface`

Required evidence fields:

- `schema`
- `surface`
- `circuit_artifact`
- `soundness_audit`
- `verifier_binding`
- `sample_proof_acceptance`
- `issued_at`
- `evidence_hash`

External artifacts:

- live proof wrapper status with `zk_proof_verified=true`
- circuit artifact, source, verification-key, and reproducible-build hashes
- soundness audit report hash
- sample accepted proof request and receipt hashes

Validator: `evaluate_production_zk_wrapping_evidence_v1`.

## AutoTrader

Purpose: prove the AutoTrader supervisor ran unattended within configured
production limits.

Required manifest config:

- `supervisor_profile_hash`
- `config_max_actions_per_tick`
- `config_max_runs_per_process`
- `expected_chain_id`
- `expected_autotrader_approval_signer_pubkeys`

Required evidence fields:

- `schema`
- `supervisor_id`
- `chain_id`
- `profile_supervisor_hash`
- `run_window`
- `crash_recovery`
- `multi_signer_approvals`
- `budget_compliance`
- `issued_at`
- `evidence_hash`

External artifacts:

- 24h or longer unattended supervisor run window with heartbeat timestamps
- crash recovery checkpoint evidence
- multi-signer approvals from the configured production approver set
- budget compliance observations

Builder:

```bash
python3 tools/build_autotrader_evidence.py \
  --out /tmp/autotrader_evidence.json \
  --supervisor-id autotrader-prod-1 \
  --chain-id tau-test-prod \
  --profile-supervisor-hash <supervisor-profile-hash> \
  --started-at <unix-seconds> \
  --last-heartbeat-at <unix-seconds> \
  --duration-seconds <seconds> \
  --ticks-executed <count> \
  --ticks-failed <count> \
  --ticks-throttled <count> \
  --heartbeat-timestamps-file /path/to/heartbeats.json \
  --crash-recovery-file /path/to/crash_recovery.json \
  --multi-signer-approvals-file /path/to/multi_signer_approvals.json \
  --expected-approval-signer-pubkeys-file /path/to/expected_approvers.json \
  --max-actions-per-tick-observed <count> \
  --max-runs-per-process-observed <count> \
  --config-max-actions-per-tick <count> \
  --config-max-runs-per-process <count> \
  --expected-chain-id tau-test-prod \
  --issued-at <unix-seconds> \
  --check-now <unix-seconds> \
  --check
```

Validator: `evaluate_production_autotrader_evidence_v1`.

## Confidential Runtime

Purpose: prove confidential runtime receipts are bound to an approved
TEE/operator/verifier posture.

Required manifest config:

- `approved_measurements`
- `operator_status_hash`
- `external_verifier_binding_hash`
- `expected_extension_id`

Required evidence fields:

- `schema`
- `extension_id`
- `provider_id`
- `tee_attestation`
- `approved_measurements_hash`
- `external_verifier_binding_hash`
- `operator_status_hash`
- `private_execution_receipt`
- `issued_at`
- `evidence_hash`

External artifacts:

- TEE attestation with approved measurement
- approved-measurement digest and verifier binding
- redacted private execution receipt with public effect digest
- operator status hash from the deployed confidential runtime

Builder:

```bash
python3 tools/build_confidential_runtime_evidence.py \
  --out /tmp/confidential_runtime_evidence.json \
  --extension-id confidential-ext-prod \
  --provider-id nitro-prod-1 \
  --tee-kind nitro \
  --raw-attestation-hash <64-hex> \
  --measurement <approved-tee-measurement> \
  --measurement-in-allowlist \
  --platform-pubkey <64-hex> \
  --attestation-signature <128-hex> \
  --tee-verified-at <unix-seconds> \
  --operator-status-hash <64-hex> \
  --external-verifier-binding-hash <64-hex> \
  --runtime-receipt-hash <64-hex> \
  --attestation-receipt-hash <64-hex> \
  --request-id <safe-token> \
  --execution-id <safe-token> \
  --execution-kind redacted_compute \
  --result-code ok \
  --result-redacted \
  --attestation-epoch <u32> \
  --current-epoch <u32> \
  --units-charged <u32> \
  --public-effect-digest <64-hex> \
  --approved-measurement <approved-tee-measurement> \
  --expected-extension-id confidential-ext-prod \
  --issued-at <unix-seconds> \
  --check-now <unix-seconds> \
  --check
```

The builder derives `approved_measurements_hash` from the supplied
`--approved-measurement` values. Pass `--approved-measurements-hash <64-hex>`
only when binding to a precomputed allowlist artifact.

Validator: `evaluate_production_confidential_runtime_evidence_v1`.
