# FIRE Registry

This directory contains pinned FIRE publication artifacts.

Current snapshot:

- `devnet_v1/`

The `devnet_v1` snapshot is a signed registry index plus three bundled FIRE objects:

- `BurnBoostCall`
- `FeeNote`
- `LPLossCover`

Each bundle now carries a stronger canonical package surface:

- `object_manifest.json` for the canonical FIRE template/object semantics
- `instance_manifest.json` for the canonical concrete parameter instance bound to that object
- `object_lock.json` for the hash-pinned dependency lock
- `certificate.json` for the attached FIRE evidence
- `compile_receipt.json` for the compiler-origin bundle receipt derived from the canonical object instance
- `kernel_receipt.json` for the admitted ref-kernel provenance receipt derived from the canonical object and instance
- `kernel_eval_receipt.json` for the concrete kernel-origin compile/eval receipt derived from running the admitted ref-kernel on the canonical instance
- `kernel_replay_receipt.json` for the concrete kernel-origin replay transcript receipt derived from the admitted compile and settlement commands plus the canonical replay inputs
- `kernel_settlement_receipt.json` for the concrete kernel-origin settlement receipt derived from running the admitted ref-kernel against the canonical replay inputs
- `proof_tree_certificate.json` for an optional non-authoritative draft CAL-style proof-tree cert
- `replay_input.json` for the canonical bundle-local replay settlement inputs
- `object_card.txt` for human-readable explanation only

For the current `devnet_v1` release lane, every published bundle is required to carry:

- `replay_input.json`
- `compile_receipt.json`
- `kernel_receipt.json`
- `kernel_eval_receipt.json`
- `kernel_replay_receipt.json`
- `kernel_settlement_receipt.json`
- `proof_tree_certificate.json`

The repo now also has a source-of-truth FIRE spec tree under `src/fire/spec/` with concrete JSON Schemas for:

- `fire-ir.schema.json`
- `fire-instance.schema.json`
- `fire-cert.schema.json`
- `fire-compile-receipt.schema.json`
- `fire-kernel-receipt.schema.json`
- `fire-kernel-eval-receipt.schema.json`
- `fire-kernel-replay-receipt.schema.json`
- `fire-kernel-settlement-receipt.schema.json`
- `fire-cert-rules.schema.json`
- `fire-lock.schema.json`
- `fire-replay-input.schema.json`
- `object-package.schema.json`

For the admitted FIRE kernel lane, maintainers can run the private ESSO admission check over the current three models:

```bash
python3 tools/check_fire_esso_kernels.py \
  --output-dir internal/release_artifacts/fire_esso \
  --pretty
```

Plain English: this validates and cross-solves the admitted FIRE ESSO kernels for `BurnBoostCall`, `FeeNote`, and `LPLossCover`, writes the raw `validate` and `verify-multi` JSON per model, and fails closed on any non-`VERIFIED` result, solver disagreement, nondeterminism, or inconclusive query.

This is a maintainer-only lane. ESSO is a private tool, so the public GitHub release workflow does not require this command. Public release checks should verify emitted package, replay, and settlement artifacts without depending on the ESSO toolchain itself.

For a schema-aware object-package check over a persisted bundle, use:

```bash
python3 tools/check_fire_object_package.py \
  --bundle-dir docs/fire_registry/devnet_v1/burn_boost_call_v1 \
  --require-replay-input \
  --require-compile-receipt \
  --require-kernel-receipt \
  --require-kernel-eval-receipt \
  --require-kernel-replay-receipt \
  --require-kernel-settlement-receipt \
  --pretty
```

Plain English: this runs the current fail-closed bundle verifier and also validates the raw manifest, instance, lock, certificate, and bundle manifest JSON against the canonical schema files in `src/fire/spec/`.
With `--require-replay-input`, it also fails closed if `replay_input.json` is missing, then validates it against the canonical replay-input schema and checks that it binds to the same object and instance hashes.
With `--require-compile-receipt`, it also fails closed if `compile_receipt.json` is missing, validates it against the canonical compile-receipt schema, recompiles the object from the canonical instance parameters, and checks that the receipt matches that compiler output exactly.
With `--require-kernel-receipt`, it also fails closed if `kernel_receipt.json` is missing, validates it against the canonical kernel-receipt schema, reloads the canonical admitted ref-kernel surface for that object family, and checks that the receipt matches the current kernel-origin provenance exactly.
With `--require-kernel-eval-receipt`, it also fails closed if `kernel_eval_receipt.json` is missing, validates it against the canonical kernel-eval schema, reruns the canonical admitted compile command against the canonical instance parameters, and checks that the receipt matches that concrete kernel execution exactly.
With `--require-kernel-replay-receipt`, it also fails closed if `kernel_replay_receipt.json` is missing, validates it against the canonical kernel-replay schema, reruns the canonical admitted compile and settlement commands against the canonical instance parameters plus `replay_input.json`, and checks that the receipt matches that concrete replay transcript exactly.
With `--require-kernel-settlement-receipt`, it also fails closed if `kernel_settlement_receipt.json` is missing, validates it against the canonical kernel-settlement schema, reruns the canonical admitted settlement command against `replay_input.json`, and checks that the receipt matches that concrete kernel settlement execution exactly.

For a direct compile-receipt check without the full package gate, use:

```bash
python3 tools/check_fire_compile_receipt.py \
  --receipt-file docs/fire_registry/devnet_v1/burn_boost_call_v1/compile_receipt.json \
  --object-manifest-file docs/fire_registry/devnet_v1/burn_boost_call_v1/object_manifest.json \
  --instance-manifest-file docs/fire_registry/devnet_v1/burn_boost_call_v1/instance_manifest.json \
  --pretty
```

Plain English: this validates `compile_receipt.json` against the canonical schema, reloads the canonical object and instance artifacts, recompiles the object from the instance parameters, and rejects any drift between the receipt and that recomputed compiler result.

For a direct kernel-receipt check without the full package gate, use:

```bash
python3 tools/check_fire_kernel_receipt.py \
  --receipt-file docs/fire_registry/devnet_v1/burn_boost_call_v1/kernel_receipt.json \
  --object-manifest-file docs/fire_registry/devnet_v1/burn_boost_call_v1/object_manifest.json \
  --instance-manifest-file docs/fire_registry/devnet_v1/burn_boost_call_v1/instance_manifest.json \
  --pretty
```

Plain English: this validates `kernel_receipt.json` against the canonical schema, reloads the canonical object and instance artifacts, reloads the admitted `src/fire/kernel/fire_*_ref.py` module for that object family, and rejects any drift in model id, IR hash, phase symbols, command tags, or ref-file hash provenance.

For a direct kernel-eval receipt check without the full package gate, use:

```bash
python3 tools/check_fire_kernel_eval_receipt.py \
  --receipt-file docs/fire_registry/devnet_v1/burn_boost_call_v1/kernel_eval_receipt.json \
  --object-manifest-file docs/fire_registry/devnet_v1/burn_boost_call_v1/object_manifest.json \
  --instance-manifest-file docs/fire_registry/devnet_v1/burn_boost_call_v1/instance_manifest.json \
  --kernel-receipt-file docs/fire_registry/devnet_v1/burn_boost_call_v1/kernel_receipt.json \
  --pretty
```

Plain English: this validates `kernel_eval_receipt.json` against the canonical schema, reloads the canonical object and instance artifacts, reruns the admitted ref-kernel compile command for that family, and rejects any drift in the concrete compiled state or emitted compile effects.

For a direct kernel-settlement receipt check without the full package gate, use:

```bash
python3 tools/check_fire_kernel_settlement_receipt.py \
  --receipt-file docs/fire_registry/devnet_v1/burn_boost_call_v1/kernel_settlement_receipt.json \
  --object-manifest-file docs/fire_registry/devnet_v1/burn_boost_call_v1/object_manifest.json \
  --instance-manifest-file docs/fire_registry/devnet_v1/burn_boost_call_v1/instance_manifest.json \
  --replay-input-file docs/fire_registry/devnet_v1/burn_boost_call_v1/replay_input.json \
  --kernel-receipt-file docs/fire_registry/devnet_v1/burn_boost_call_v1/kernel_receipt.json \
  --kernel-eval-receipt-file docs/fire_registry/devnet_v1/burn_boost_call_v1/kernel_eval_receipt.json \
  --pretty
```

Plain English: this validates `kernel_settlement_receipt.json` against the canonical schema, reloads the canonical object and instance artifacts plus `replay_input.json`, reruns the admitted ref-kernel settlement command for that family, and rejects any drift in the concrete settlement state or emitted settlement effects.

For a direct kernel-replay receipt check without the full package gate, use:

```bash
python3 tools/check_fire_kernel_replay_receipt.py \
  --receipt-file docs/fire_registry/devnet_v1/burn_boost_call_v1/kernel_replay_receipt.json \
  --object-manifest-file docs/fire_registry/devnet_v1/burn_boost_call_v1/object_manifest.json \
  --instance-manifest-file docs/fire_registry/devnet_v1/burn_boost_call_v1/instance_manifest.json \
  --replay-input-file docs/fire_registry/devnet_v1/burn_boost_call_v1/replay_input.json \
  --compile-receipt-file docs/fire_registry/devnet_v1/burn_boost_call_v1/compile_receipt.json \
  --kernel-receipt-file docs/fire_registry/devnet_v1/burn_boost_call_v1/kernel_receipt.json \
  --kernel-eval-receipt-file docs/fire_registry/devnet_v1/burn_boost_call_v1/kernel_eval_receipt.json \
  --kernel-settlement-receipt-file docs/fire_registry/devnet_v1/burn_boost_call_v1/kernel_settlement_receipt.json \
  --pretty
```

Plain English: this validates `kernel_replay_receipt.json` against the canonical schema, reloads the canonical object and instance artifacts plus `replay_input.json`, reruns the admitted ref-kernel compile and settlement commands for that family, and rejects any drift in the replay transcript hash, emitted settlement hashes, or bound delta surface.

To require the optional draft proof-tree cert sidecar too:

```bash
python3 tools/check_fire_object_package.py \
  --bundle-dir docs/fire_registry/devnet_v1/burn_boost_call_v1 \
  --require-replay-input \
  --require-compile-receipt \
  --require-kernel-receipt \
  --require-kernel-eval-receipt \
  --require-kernel-replay-receipt \
  --require-kernel-settlement-receipt \
  --require-proof-tree-cert \
  --pretty
```

Plain English: this still does not make the proof-tree cert settlement authority. It only requires that, if the package claims to carry that draft CAL-style sidecar, the sidecar is present, schema-valid, bound to the same object and instance hashes, bound to the same `certificate.json` by `certificate_sha256`, carries a `runtime_certificate_summary` consistent with the live interval certificate, and stays consistent with the canonical verifier-rule ids, rule-to-predicate shapes, declared input predicates, the current `replay_input.json` plus its `sha256`, the concrete `compile_receipt.json` artifact via its `sha256`, the concrete `kernel_receipt.json` artifact via its `sha256`, the concrete `kernel_eval_receipt.json` artifact via its `sha256`, the concrete `kernel_replay_receipt.json` artifact via its `sha256` plus replay transcript hashes, the concrete `kernel_settlement_receipt.json` artifact via its `sha256`, the concrete bundle `contract_receipts` surface for witness/import provenance, and manifest/instance policy summaries for witness, parameter, authorization, nonce, maturity, and settlement-window claims.
The current `devnet_v1` release lane now uses this stronger package gate.

For the whole pinned snapshot, use:

```bash
python3 tools/check_fire_snapshot_packages.py \
  --snapshot-dir docs/fire_registry/devnet_v1 \
  --require-replay-input \
  --require-compile-receipt \
  --require-kernel-receipt \
  --require-kernel-eval-receipt \
  --require-kernel-replay-receipt \
  --require-kernel-settlement-receipt \
  --pretty
```

Plain English: every persisted bundle in the snapshot must pass the schema-aware object-package check, and current release lanes can require every bundle to carry canonical replay inputs before release or replay gates should trust the snapshot.

To require the optional draft proof-tree cert sidecar across the whole snapshot:

```bash
python3 tools/check_fire_snapshot_packages.py \
  --snapshot-dir docs/fire_registry/devnet_v1 \
  --require-replay-input \
  --require-compile-receipt \
  --require-kernel-receipt \
  --require-kernel-eval-receipt \
  --require-kernel-replay-receipt \
  --require-kernel-settlement-receipt \
  --require-proof-tree-cert \
  --pretty
```

Plain English: every bundle in the snapshot must still pass the ordinary package checks, and now each one must also carry a schema-valid `proof_tree_certificate.json` sidecar bound to the same object and instance hashes, the same runtime certificate hash, the same dependency lock surface, the same `compile_receipt.json` compiler-origin evidence surface, the same `kernel_receipt.json` kernel-origin evidence surface, the same `kernel_eval_receipt.json` concrete kernel-execution evidence surface, the same `kernel_replay_receipt.json` concrete replay-transcript evidence surface, the same `kernel_settlement_receipt.json` concrete kernel-settlement evidence surface, the same concrete bundle `contract_receipts` witness/import provenance surface, the same runtime certificate summary, and the same required claim evidences. This remains package evidence only, not settlement authority.
The public `release-integrity` workflow now uses this stronger snapshot package gate for `docs/fire_registry/devnet_v1`, and the publish step emits proof-tree sidecars plus kernel receipts for the release snapshot it produces under `internal/release_artifacts/fire_registry`.

The certificate now also carries first-class instance-gate claim labels for:

- `ParamOK`
- `AuthorizationOK`
- `NonceOK`
- `MaturityOK`
- `WindowOK`

Plain English: the evidence lane now names the instance-admissibility claims directly, instead of only surfacing derived gate summaries in bundle and snapshot reports.

The human-readable `object_card.txt` now mirrors those same labels in an `Instance gate claim evidence` section. That card remains explanatory only; settlement still binds to the machine-readable manifest, instance, lock, and certificate artifacts.
The bundle build/check CLIs now also echo that rendered card text as a noncanonical `object_card_text` field, so CI and review tooling can surface the same explanation without reopening bundle files by hand.

The bundle build CLI can also emit a non-authoritative draft proof-tree cert sidecar:

```bash
python3 tools/build_fire_registry_bundle.py \
  burn_boost_call_v1 \
  --bundle-dir /tmp/burn_bundle \
  --n-notional 10 \
  --strike-index 4 \
  --cap-index 3 \
  --source-upper 9 \
  --emit-proof-tree-cert \
  --pretty
```

Plain English: this writes `proof_tree_certificate.json` as a draft CAL-style sidecar derived from the current manifest, instance, dependency lock, runtime cert, replay input, and kernel-origin receipts. It is package evidence only, not settlement authority.
The same bundle build path also emits `compile_receipt.json`, `kernel_receipt.json`, `kernel_eval_receipt.json`, `kernel_replay_receipt.json`, and `kernel_settlement_receipt.json` for the current release lane.

The canonical template manifest now carries:

- parameter admissibility bounds and units
- instance policy for required party roles
- nonce / maturity / settlement-window requirements

Future naming note:

- the planned non-authoritative FIRE refinement subsystem is `FIRE Refiner`
- the technical name is `ORE` (`Object Refinement Engine`)
- `Morph` is reserved for the separate private toolchain and is not the FIRE component name

The instance checker now makes these verifier gates explicit:

```text
ParamOK ∧ AuthorizationOK ∧ NonceOK ∧ MaturityOK ∧ WindowOK
```

Plain English: the concrete instance must match the template’s declared parameter bounds and instance policy.

The persisted-bundle native settlement adapters now fail closed on a verifier receipt and carry that same receipt forward in a noncanonical settlement handoff:

- `verifier_receipt` in drained adapter effects
- `settlement_packet` in drained adapter effects

Plain English: the adapter will not emit settlement effects for a persisted bundle unless the receipt matches the exact object hash, instance hash, cert hash, bundle hash, and computed deltas.

Downstream callers should consume the adapter handoff through:

```python
from src.fire.verifier.settlement_v1 import extract_verified_fire_settlement_packet
```

That helper verifies the drained `settlement_packet` against the embedded receipt and rejects mismatched `firev_accept`, `payoff_out`, or receipt payloads.

For a funds-moving balance update helper inside the current repo, use:

```python
from src.fire.kernel.ledger_adapter_v1 import apply_verified_fire_settlement_effects
```

That helper refuses to mutate balances unless it can extract and verify the receipt-bound settlement packet first.

The ledger helper now also emits a noncanonical apply receipt for the balance transition itself:

- `apply_receipt.packet_hash = settlement_packet.packet_hash`
- `apply_receipt.holder_balance_after = holder_balance_before + holder_delta`
- `apply_receipt.writer_balance_after = writer_balance_before + writer_delta`

Plain English: the packet authorizes the delta set, and the apply receipt records the exact balance mutation that was carried out under that packet.

For a single in-repo entry point that loads a persisted bundle, runs verifier-backed settlement, executes the native adapter, and applies balances only through that verified packet path, use:

```bash
python3 tools/apply_fire_settlement.py \
  --bundle-dir docs/fire_registry/devnet_v1/burn_boost_call_v1 \
  --holder-posted 0 \
  --writer-posted 30 \
  --holder-balance 100 \
  --writer-balance 250 \
  --witness-final 7 \
  --pretty
```

That CLI is non-authoritative orchestration around the same rule:

```text
ApplyDeltas -> require VerifiedSettlementPacket
```

Plain English: the tool may drive the flow, but it still cannot mutate balances unless the bundle, verifier receipt, settlement packet, and delta binding all check.

Replay-check the emitted apply report:

```bash
python3 tools/check_fire_settlement_apply_report.py \
  --report-file /tmp/fire_apply_report.json \
  --bundle-dir docs/fire_registry/devnet_v1/burn_boost_call_v1 \
  --pretty
```

Plain English: downstream orchestration can now verify the full applied artifact off-line and, when given `--bundle-dir`, prove that the report matches a concrete persisted bundle on disk.

The apply report is now hash-addressed:

- `report_hash = H(canonical_apply_report_without_report_hash)`

Plain English: the checker rejects any top-level edit unless the report is re-canonicalized and re-hashed, so the apply report itself can be pinned as a concrete replay artifact.

To emit both the apply report and a pinned artifact receipt in one command:

```bash
python3 tools/apply_fire_settlement.py \
  --bundle-dir docs/fire_registry/devnet_v1/burn_boost_call_v1 \
  --holder-posted 0 \
  --writer-posted 30 \
  --holder-balance 100 \
  --writer-balance 250 \
  --witness-final 7 \
  --output-report-file /tmp/fire_apply_report.json \
  --output-artifact-receipt-file /tmp/fire_apply_artifact_receipt.json \
  --pretty
```

Plain English: the settlement command can now write the replayable apply report and immediately pin it with a receipt that binds the report hash, bundle hash, object hash, instance hash, certificate hash, settlement packet hash, and apply receipt hash.

Replay-check that pinned artifact receipt:

```bash
python3 tools/check_fire_settlement_apply_artifact_receipt.py \
  --receipt-file /tmp/fire_apply_artifact_receipt.json \
  --expected-bundle-dir docs/fire_registry/devnet_v1/burn_boost_call_v1 \
  --expected-object-hash sha256:... \
  --expected-instance-hash sha256:... \
  --expected-report-hash sha256:... \
  --pretty
```

Plain English: downstream orchestration can now accept one pinned artifact that proves both of these claims:

```text
VerifiedApplyReport ∧ VerifiedBundleMatch -> AppliedArtifactMatchesConcreteBundle
```

Plain English: the checked artifact still points back to the concrete bundle on disk, so a valid-looking report cannot be replayed against the wrong bundle.

When `--expected-bundle-dir` is provided, the checker now verifies that bundle and derives these pins automatically:

- `bundle_hash`
- `object_hash`
- `instance_hash`
- `cert_sha256`

The artifact checker can now also enforce caller-supplied identity pins:

- `--expected-bundle-dir`
- `--expected-bundle-hash`
- `--expected-object-hash`
- `--expected-instance-hash`
- `--expected-cert-sha256`
- `--expected-report-hash`

Plain English: the orchestrator does not have to trust the receipt's own self-description. It can require that the receipt match the exact bundle and object identity it expected ahead of time.

For a single CI/orchestrator command over the pinned devnet bundles, use:

```bash
python3 tools/check_fire_settlement_replay_gate.py \
  --snapshot-dir docs/fire_registry/devnet_v1 \
  --output-dir internal/release_artifacts/fire_settlement_replay_gate \
  --require-bundle-replay-input \
  --pretty
```

Plain English: this gate replays the pinned FIRE settlement cases for `burn_boost_call_v1`, `fee_note_v1`, and `lp_loss_cover_v1`, requires canonical `replay_input.json` in every current bundle, emits apply reports plus artifact receipts, and accepts only if each receipt verifies against its expected bundle directory.

Settlement and replay checks should bind to the machine-readable package artifacts, not the object card prose.

Build the snapshot again:

```bash
python3 tools/build_fire_registry_snapshot.py --output-dir docs/fire_registry/devnet_v1 --pretty
```

Emit draft proof-tree cert sidecars while building the snapshot:

```bash
python3 tools/build_fire_registry_snapshot.py \
  --output-dir docs/fire_registry/devnet_v1 \
  --emit-proof-tree-cert \
  --pretty
```

Publish a release snapshot with a CI or shell-provided signer:

```bash
export FIRE_REGISTRY_SIGNER_PRIVKEY=...
export FIRE_REGISTRY_EXPECTED_SIGNER_PUBKEY=...
python3 tools/publish_fire_registry_snapshot.py --output-dir internal/release_artifacts/fire_registry --snapshot-name release_v1 --pretty
```

Or publish a snapshot that also emits the optional draft proof-tree cert sidecars:

```bash
export FIRE_REGISTRY_SIGNER_PRIVKEY=...
export FIRE_REGISTRY_EXPECTED_SIGNER_PUBKEY=...
python3 tools/publish_fire_registry_snapshot.py \
  --output-dir internal/release_artifacts/fire_registry \
  --snapshot-name release_v1 \
  --emit-proof-tree-cert \
  --pretty
```

The publish path rejects the demo signer key unless `--allow-demo-signer` is set, and it fails closed if the derived signer pubkey does not match `FIRE_REGISTRY_EXPECTED_SIGNER_PUBKEY`.

To make signer policy explicit and auditable, publish can also consume a deployment contract:

```bash
python3 tools/build_fire_registry_deployment_contract.py \
  --output internal/release_artifacts/fire_registry/deployment_contract.json \
  --snapshot-name release_v1 \
  --required-signer-pubkey "$FIRE_REGISTRY_EXPECTED_SIGNER_PUBKEY" \
  --release-metadata-file internal/release_artifacts/fire_registry/release_metadata.json \
  --pretty

python3 tools/publish_fire_registry_snapshot.py \
  --output-dir internal/release_artifacts/fire_registry \
  --snapshot-name release_v1 \
  --deployment-contract-file internal/release_artifacts/fire_registry/deployment_contract.json \
  --pretty
```

When a deployment contract is provided, publish emits `deployment_receipt.json` beside `release_metadata.json`.
The publish report now exposes both the published snapshot contract set and the deployment contract's expected contract set, so CI logs can show the exact policy pin without opening the JSON artifacts by hand.

Replay-check the pinned snapshot through release metadata:

```bash
python3 tools/check_fire_registry_snapshot.py --metadata-file docs/fire_registry/devnet_v1/release_metadata.json --expected-snapshot-name devnet_v1 --pretty
```

The snapshot check now reports the aggregated contract identities carried by the signed index and pinned release metadata, so the published set can be audited by contract name without opening each bundle separately.
It also reports the aggregated instance gate summary, so `ParamOK`, `AuthorizationOK`, `NonceOK`, `MaturityOK`, and `WindowOK` are visible at snapshot scope instead of only inside each bundle.
It now also reports the aggregated certificate instance-gate claim summary, so the snapshot says not only whether those gates passed, but what evidence label currently backs each claim.

Replay-check the pinned deployment receipt:

```bash
python3 tools/check_fire_registry_deployment_receipt.py --receipt-file docs/fire_registry/devnet_v1/deployment_receipt.json --require-current --pretty
```

The deployment contract can now pin the exact expected aggregated contract set from `release_metadata.json`, and the deployment receipt mirrors that same summary. That makes the policy lane fail closed on signer drift or contract-set drift, instead of inheriting contract identity only transitively through the snapshot metadata.

The release metadata pins:

```text
snapshot_name = devnet_v1
index_path = fire_registry_index.json
signer_pubkey = 0x8e0b26637a9bc464c5a9ac490f6e673a0fb6279d7918c46a870307cf1f96109abf975d8453dc77273f9aba47c8eb68c2
contracts = {burn_contract, fee_contract, hodl_contract, lpv_contract}
instance_gate_summary = {entry_count = 3, all_ok = true}
certificate_instance_gate_summary = {
  entry_count = 3,
  param_ok = implemented,
  authorization_ok = implemented,
  nonce_ok = implemented,
  maturity_ok = implemented,
  window_ok = implemented
}
```

The snapshot is a deterministic publication surface, not a claim that the whole future FIRE stack is bug-free.
