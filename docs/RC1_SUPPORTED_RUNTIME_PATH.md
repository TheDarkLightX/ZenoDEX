---
title: RC2_SUPPORTED_RUNTIME_PATH
type: note
permalink: autonomous-tau-dex-review/docs/rc1-supported-runtime-path
---

# RC2 Candidate Supported Runtime And Signing Path

<!-- Generated from tools/rc1_scope_manifest.json. -->

Historical release baseline: `RC1` already shipped. This file keeps the `RC1_*` path for compatibility, but the live candidate label is `RC2`.

```text
RuntimePathOK := ReadOnlyHTTPBounded ∧ SpotAdmissionPinned ∧ WalletTransportPinned
```

Standard reading: the conservative RC2 runtime claim is only about a narrow HTTP subset, one pinned spot admission/signing path, and the narrow zUSD wallet transport path.

Practical consequence: this document does not promote the entire integration shell into RC2 authority.

## 1. Read-only HTTP subset

- Entrypoint: `src/integration/api_server.py`
- Supported routes:
  - `/health`
  - `/version`
  - `/api/dex/quote`
  - `/api/dex/verify_quote_receipt`
  - `/api/dex/build_settlement_end_to_end_certificate_packet`
  - `/api/dex/verify_settlement_end_to_end_certificate_packet`
- Notes:
  - This subset is read-only or certificate-packet oriented.
  - It avoids claiming the entire api_server surface as candidate-backed.

## 2. Spot intent admission and signing path

- Entrypoint: `src/integration/dex_engine.py:apply_ops`
- Signing contract: `docs/INTENT_SIGNATURES.md`
- Auth-message builder: `src/core/dex_intent_auth_message.py`
- Nonce and sequence state: `src/state/nonces.py`

```text
IntentAccepted -> CanonicalSigningPayloadVerified ∧ NonceBatchAccepted ∧ PreconditionsHold
```

Standard reading: spot admission accepts an intent batch only after canonical signing payload verification, nonce-batch validation, and ordinary precondition checks succeed.

Practical consequence: RC2 should describe one exact signing and nonce path, not a mix of alternative ingress behaviors.

- Replay command:
  - `python3 tools/permissionless_assurance.py replay public`
- Coverage tests:
  - `tests/integration/test_intent_signatures.py`
  - `tests/integration/test_dex_engine.py`
  - `tests/integration/test_replay_protection.py`
  - `tests/integration/test_dex_engine_helpers.py`
- Notes:
  - Intent signing payloads are canonical JSON bytes under the dex_intent_sig domain separator.
  - Nonce and sequence handling are enforced in the functional core before state transition.
  - The supported Tau runtime subset for this path is replayed through the public assurance lane and the dedicated Tau runtime subset checker.

## 3. zUSD Tau wallet transport

- Doc: `docs/ZUSD_TAU_WALLET.md`
- CLI: `tools/zusd_tau_wallet.py`
- Replay command:
  - `python3 tools/permissionless_assurance.py replay zusd`
- Coverage tests:
  - `tests/integration/test_zusd_tau_wallet_cli.py`
- Notes:
  - This path covers Tau-native token transport for transfer, mint, and burn.
  - It is narrower than a generic wallet or broad HTTP product claim.

## Release Hooks

- `python3 tools/check_tau_supported_runtime_subset.py`
- `python3 tools/check_production_boundary.py`
- `python3 tools/render_rc1_supported_runtime_path.py --check`
- `python3 tools/rc1_readiness.py --check`
- `python3 tools/rc1_candidate.py --plan`

