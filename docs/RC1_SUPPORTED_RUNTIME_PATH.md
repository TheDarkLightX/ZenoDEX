---
title: RC1_SUPPORTED_RUNTIME_PATH
type: note
permalink: autonomous-tau-dex-review/docs/rc1-supported-runtime-path
---

# RC1 Supported Runtime And Signing Path

<!-- Conservative RC1 runtime-path note. -->

```text
RuntimePathOK := ReadOnlyHTTPBounded ∧ SpotAdmissionPinned
```

Reading: the conservative RC1 runtime claim is only about a narrow HTTP subset and one pinned spot admission/signing path.

Practical consequence: this document does not promote the entire integration shell into RC1 authority, and it does not advertise unpublished wallet transport lanes as RC1-backed.

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
  - It avoids claiming the entire api_server surface as RC1-backed.

## 2. Spot intent admission and signing path

- Entrypoint: `src/integration/dex_engine.py:apply_ops`
- Signing contract: `docs/INTENT_SIGNATURES.md`
- Auth-message builder: `src/core/dex_intent_auth_message.py`
- Nonce and sequence state: `src/state/nonces.py`

```text
IntentAccepted -> CanonicalSigningPayloadVerified ∧ NonceBatchAccepted ∧ PreconditionsHold
```

Reading: spot admission accepts an intent batch only after canonical signing payload verification, nonce-batch validation, and ordinary precondition checks succeed.

Practical consequence: RC1 should describe one exact signing and nonce path, not a mix of alternative ingress behaviors.

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

## 3. zUSD Tau wallet transport

- Status: not part of the current public RC1 replay contract
- Notes:
  - the repo still contains design and review material for a zUSD Tau wallet transport lane
  - the runnable wallet CLI and its full assurance gate family are not yet published in the committed public slice
  - until that slice is published coherently, this path must not be described as RC1-backed or as a public replay lane

## Release Hooks

- `python3 tools/permissionless_assurance.py status`
- `python3 tools/permissionless_assurance.py replay critical`
- `python3 tools/permissionless_assurance.py replay full`

