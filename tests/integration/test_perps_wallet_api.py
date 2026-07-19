from __future__ import annotations

import json
import sys
from dataclasses import replace
from typing import Mapping

import pytest
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat

import src.integration.perps_wallet_api as perps_wallet_api
from src.core.dex import DexState
from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.perp_engine import (
    PerpEngineConfig,
    _kernel_initial_global_state,
    apply_perp_ops,
)
from src.integration.perps_wallet_authority import (
    PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
    PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_SCHEMA_V1,
    PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND,
    PERPS_WALLET_RECOVERY_EXERCISE_SCHEMA_V1,
    PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND,
    PERPS_WALLET_ROTATION_EXERCISE_SCHEMA_V1,
    PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_SCHEMA_V1,
    PERPS_WALLET_SIGNER_PROMPT_CAPTURE_SCHEMA_V1,
    build_perps_wallet_authority_profile_v1,
    build_perps_wallet_device_approval_environment_policy_v1,
    build_perps_wallet_device_approval_exercise_v1,
    build_perps_wallet_device_approval_use_policy_v1,
    build_perps_wallet_signer_device_integration_v1,
    build_perps_wallet_signer_execution_exercise_v1,
    build_perps_wallet_signer_prompt_capture_v1,
    evaluate_perps_wallet_authority_profile_v1,
    evaluate_perps_wallet_device_approval_exercise_v1,
    evaluate_perps_wallet_hardware_custody_v1,
    evaluate_perps_wallet_recovery_exercise_v1,
    evaluate_perps_wallet_rotation_exercise_v1,
    evaluate_perps_wallet_signer_ceremony_v1,
    evaluate_perps_wallet_signer_device_integration_v1,
    evaluate_perps_wallet_signer_execution_exercise_v1,
    evaluate_perps_wallet_signer_prompt_capture_v1,
    perps_wallet_device_approval_exercise_hash_v1,
    perps_wallet_recovery_exercise_hash_v1,
    perps_wallet_rotation_exercise_hash_v1,
    perps_wallet_signer_device_integration_hash_v1,
    perps_wallet_signer_execution_exercise_hash_v1,
    perps_wallet_signer_prompt_capture_hash_v1,
)
from src.integration.production_promotion_evidence import (
    HARDWARE_WALLET_EVIDENCE_SCHEMA_V1,
    attach_production_hardware_wallet_hash_v1,
    evaluate_production_hardware_wallet_evidence_v1,
    production_hardware_wallet_approval_message_v1,
    production_hardware_wallet_attestation_challenge_v1,
    production_hardware_wallet_attestation_message_v1,
)
from src.integration.tau_net_client import (
    TauNetRpcError,
    bls_pubkey_hex_from_privkey,
    build_signed_tau_transaction,
    sign_perp_op_for_engine,
)
from src.integration.zeno_key_manager import (
    KEY_ENVIRONMENT_LOCAL_PROCESS,
    KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
    KeyExecutionEnvironment,
    KeyRef,
    RecoveryGuardian,
    SocialRecoveryPolicy,
    ZenoKeyManager,
)
from src.integration.zeno_key_manager_v0 import (
    BACKEND_HARDWARE_WALLET,
    BACKEND_HARDWARE_WALLET_PLACEHOLDER,
    BACKEND_OS_KEYCHAIN,
    KeyBackendDescriptor,
)
from src.integration.zeno_ledger_signature import (
    build_bls_signed_artifact_envelope_v0,
    infer_artifact_hash_v0,
)
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zeno_oracle_authority import (
    ORACLE_AUTHORITY_PAYLOAD_KIND,
    build_oracle_authority_profile_v1,
)
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from src.state import BalanceTable, LPTable
from src.state.balances import copy_balance_table
from tests.support.perps_oracle_bridge_fixture import build_perps_oracle_bridge_fixture
from tools.zenodex_oracle_aggregate_adapter import (
    verify_aggregate_adapter_bridge as verify_test_oracle_aggregate_adapter_bridge,
)

CHAIN_ID = "tau-test-perps-wallet"
ALICE_PRIVKEY = 83
BOB_PRIVKEY = 84
ORACLE_PRIVKEY = 85
OPERATOR_PRIVKEY = 86
CAROL_PRIVKEY = 87
ALICE = "0x" + bls_pubkey_hex_from_privkey(ALICE_PRIVKEY)
BOB = "0x" + bls_pubkey_hex_from_privkey(BOB_PRIVKEY)
ORACLE = "0x" + bls_pubkey_hex_from_privkey(ORACLE_PRIVKEY)
OPERATOR = "0x" + bls_pubkey_hex_from_privkey(OPERATOR_PRIVKEY)
CAROL = "0x" + bls_pubkey_hex_from_privkey(CAROL_PRIVKEY)
MARKET_ID = "perp:ch2p:test"
ISOLATED_MARKET_ID = "perp:isolated:test"
ROOT_A = "0x" + "aa" * 32
ROOT_B = "0x" + "bb" * 32
FUTURE_DEADLINE = 4_102_444_800
PRODUCTION_HW_DEVICE_PRIVKEY_BYTES = bytes.fromhex("42" * 32)


def _with_balances(
    state: DexState,
    *entries: tuple[str, str, int],
) -> DexState:
    balances = copy_balance_table(state.balances)
    for pubkey, asset, amount in entries:
        balances.set(pubkey, asset, amount)
    return replace(state, balances=balances)


def _proof_wrapper_request_hash(obj: dict[str, object]) -> str:
    from src.integration.live_proof_wrapper import LIVE_PROOF_WRAPPER_HASH_DOMAIN
    from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

    return sha256_hex(domain_sep_bytes(LIVE_PROOF_WRAPPER_HASH_DOMAIN) + canonical_json_bytes(obj))


def _live_proof_ok_cmd(surface: str) -> list[str]:
    return [
        sys.executable,
        "-c",
        (
            "import json,sys; "
            "from src.integration.live_proof_wrapper import LIVE_PROOF_WRAPPER_HASH_DOMAIN; "
            "from src.state.canonical import canonical_json_bytes,domain_sep_bytes,sha256_hex; "
            "obj=json.load(sys.stdin); "
            f"assert obj['surface']=={surface!r}; "
            "request_hash=sha256_hex(domain_sep_bytes(LIVE_PROOF_WRAPPER_HASH_DOMAIN)+canonical_json_bytes(obj)); "
            "out={'ok': True, 'verifier_request_hash': request_hash}; "
            "expected=obj.get('expected_artifact_binding_hash'); "
            "out.update({'artifact_binding_hash': expected} if expected else {}); "
            "print(json.dumps(out))"
        ),
    ]


def _perps_wallet_signer_payload() -> dict[str, object]:
    return {
        "domain": "zenodex.perps.stream8.signer-execution.v1",
        "chain_id": CHAIN_ID,
        "nonce": 15,
        "action": "deposit_collateral",
        "stream_key": "8",
    }


def _perps_wallet_signer_payload_hash(payload: dict[str, object] | None = None) -> str:
    return hash_v0("zeno_key_manager_runtime_payload_v0", dict(payload or _perps_wallet_signer_payload()))


def _privkey_hex(value: int) -> str:
    return "0x" + int(value).to_bytes(32, byteorder="big", signed=False).hex()


_PRODUCTION_HANDLE_PERPS_WALLET_REQUEST = perps_wallet_api.handle_perps_wallet_request
_LEGACY_TEST_SIGNER_FIELDS = {
    "account_privkey": "account_pubkey",
    "account_a_privkey": "account_a_pubkey",
    "account_b_privkey": "account_b_pubkey",
    "operator_privkey": "operator_pubkey",
    "oracle_privkey": "oracle_pubkey",
}


def _test_external_signer_adapter(
    method: str,
    path: str,
    body: bytes | None,
) -> tuple[int, dict[str, object]]:
    """Adapt pre-boundary tests to the production external-signing protocol.

    Historical wallet tests supplied fixture private keys to the HTTP handler.
    Keep those fixtures test-local: ask the real prepare endpoint for its exact
    operation, sign it here, then submit an externally signed Tau transaction.
    Requests without legacy fixture fields go straight to the production
    handler unchanged.
    """
    if method != "POST" or body is None:
        return _PRODUCTION_HANDLE_PERPS_WALLET_REQUEST(method, path, body)
    try:
        parsed = json.loads(body)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return _PRODUCTION_HANDLE_PERPS_WALLET_REQUEST(method, path, body)
    if not isinstance(parsed, dict):
        return _PRODUCTION_HANDLE_PERPS_WALLET_REQUEST(method, path, body)

    fixture_keys: dict[str, int] = {}
    clean = dict(parsed)
    for private_field, public_field in _LEGACY_TEST_SIGNER_FIELDS.items():
        raw = clean.pop(private_field, None)
        if raw is None:
            continue
        private_key = int(raw)
        fixture_keys[public_field] = private_key
        clean.setdefault(public_field, "0x" + bls_pubkey_hex_from_privkey(private_key))
    if not fixture_keys or path not in {"/api/perps/wallet/prepare", "/api/perps/wallet/submit"}:
        return _PRODUCTION_HANDLE_PERPS_WALLET_REQUEST(
            method,
            path,
            json.dumps(clean).encode("utf-8"),
        )

    prepared_status, prepared = _PRODUCTION_HANDLE_PERPS_WALLET_REQUEST(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(clean).encode("utf-8"),
    )
    if prepared_status != 200 or prepared.get("ok") is not True:
        return prepared_status, prepared

    report = prepared.get("report")
    operation = report.get("operation") if isinstance(report, Mapping) else None
    transport = prepared.get("transport")
    if not isinstance(operation, Mapping) or not isinstance(transport, Mapping):
        raise AssertionError("test external signer received malformed prepare response")
    operation_to_sign = dict(operation)
    chain_id = str(transport["chain_id"])

    signature_specs = (
        ("account_a_pubkey", "sig_a", "nonce_a"),
        ("account_b_pubkey", "sig_b", "nonce_b"),
        ("oracle_pubkey", "oracle_sig", "oracle_nonce"),
    )
    for public_field, signature_field, nonce_field in signature_specs:
        private_key = fixture_keys.get(public_field)
        if private_key is None or clean.get(signature_field):
            continue
        signer_pubkey = clean.get(public_field)
        nonce = operation_to_sign.get(nonce_field)
        if not isinstance(signer_pubkey, str) or not isinstance(nonce, int):
            raise AssertionError(f"test external signer missing {public_field}/{nonce_field}")
        clean[signature_field] = sign_perp_op_for_engine(
            operation_to_sign,
            privkey=private_key,
            chain_id=chain_id,
            signer_pubkey=signer_pubkey,
            nonce=nonce,
        )

    signed_prepare_status, signed_prepare = _PRODUCTION_HANDLE_PERPS_WALLET_REQUEST(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(clean).encode("utf-8"),
    )
    if path == "/api/perps/wallet/prepare":
        return signed_prepare_status, signed_prepare
    if signed_prepare_status != 200 or signed_prepare.get("ok") is not True:
        return signed_prepare_status, signed_prepare

    signed_report = signed_prepare.get("report")
    signed_transport = signed_prepare.get("transport")
    if not isinstance(signed_report, Mapping) or not isinstance(signed_transport, Mapping):
        raise AssertionError("test external signer received malformed signed prepare response")
    if not isinstance(signed_report.get("preflight"), Mapping) or signed_report["preflight"].get("ok") is not True:
        return _PRODUCTION_HANDLE_PERPS_WALLET_REQUEST(
            "POST",
            path,
            json.dumps(clean).encode("utf-8"),
        )

    tx_sender = str(signed_transport["tx_sender_pubkey"]).lower()
    tx_private_key = next(
        (
            private_key
            for public_field, private_key in fixture_keys.items()
            if str(clean.get(public_field, "")).lower() == tx_sender
        ),
        None,
    )
    if tx_private_key is None:
        raise AssertionError(f"test external signer has no key for transaction sender {tx_sender}")
    clean["signed_tau_tx_payload"] = build_signed_tau_transaction(
        privkey=tx_private_key,
        sequence_number=int(signed_transport["tx_sequence_number"]),
        expiration_time=int(signed_transport["tx_expiration_time"]),
        operations=dict(signed_report["operations"]),
        fee_limit=str(signed_transport["tx_fee_limit"]),
    )
    return _PRODUCTION_HANDLE_PERPS_WALLET_REQUEST(
        "POST",
        path,
        json.dumps(clean).encode("utf-8"),
    )


@pytest.fixture(autouse=True)
def _keep_legacy_fixture_signing_outside_production(monkeypatch) -> None:
    monkeypatch.setattr(
        perps_wallet_api,
        "handle_perps_wallet_request",
        _test_external_signer_adapter,
    )


def _perps_wallet_key_manager(*, second_pubkey: str = BOB) -> dict[str, object]:
    return ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="perps-wallet-a", public_key=ALICE, recovery_policy_id="recovery-perps-wallet-a"),
            KeyRef(key_id="perps-wallet-b", public_key=second_pubkey, recovery_policy_id="recovery-perps-wallet-b"),
        ),
        recovery_policies=(
            SocialRecoveryPolicy(
                policy_id="recovery-perps-wallet-a",
                subject_key_id="perps-wallet-a",
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-oracle", public_key=ORACLE),
                    RecoveryGuardian(guardian_id="guardian-operator", public_key=OPERATOR),
                ),
            ),
            SocialRecoveryPolicy(
                policy_id="recovery-perps-wallet-b",
                subject_key_id="perps-wallet-b",
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-oracle", public_key=ORACLE),
                    RecoveryGuardian(guardian_id="guardian-operator", public_key=OPERATOR),
                ),
            ),
        ),
    ).public_dict()


def _perps_wallet_signer_registry(*, second_pubkey: str = BOB, threshold: int = 1) -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id="perps-wallet-authority-v1",
        payload_kind=PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
        threshold=threshold,
        signers=(
            {
                "signer_id": "wallet-a",
                "key_id": "perps-wallet-a",
                "public_key": ALICE,
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "wallet-b",
                "key_id": "perps-wallet-b",
                "public_key": second_pubkey,
                "weight": 1,
                "status": "active",
            },
        ),
    )


def _perps_wallet_authority_profile(**overrides: object) -> dict[str, object]:
    base = {
        "authority_id": "perps-wallet-mainnet-authority-v1",
        "chain_id": CHAIN_ID,
        "stage": "production",
        "enabled": True,
        "key_manager": _perps_wallet_key_manager(),
        "signer_registry": _perps_wallet_signer_registry(),
        "wallet_ux": {
            "external_signer_required": True,
            "key_manager_required": True,
            "device_approval_required": True,
            "replay_protection_required": True,
            "recovery_policy_required": True,
        },
        "proof_profile": {
            "stream8_proof_intent_required": True,
            "state_delta_witness_required": True,
            "zk_or_proof_required": True,
            "runtime_proof_profile": "perps-stream8-risc0-or-equivalent-v1",
        },
        "transaction_scope": {
            "stream_key": "8",
            "allowed_actions": [
                "init_market_2p",
                "deposit_collateral",
                "withdraw_collateral",
                "deposit_insurance",
                "set_position_pair",
                "advance_epoch",
                "publish_clearing_price",
                "settle_epoch",
                "partial_liquidate",
            ],
        },
    }
    base.update(overrides)
    return build_perps_wallet_authority_profile_v1(**base)


def _perps_wallet_recovery_exercise(**overrides: object) -> dict[str, object]:
    base = {
        "schema": PERPS_WALLET_RECOVERY_EXERCISE_SCHEMA_V1,
        "chain_id": CHAIN_ID,
        "authority_id": "perps-wallet-mainnet-authority-v1",
        "subject_key_id": "perps-wallet-a",
        "policy_id": "recovery-perps-wallet-a",
        "requested_at_epoch": 10,
        "current_epoch": 13,
        "approvals": ["guardian-oracle", "guardian-operator"],
    }
    base.update(overrides)
    exercise = dict(base)
    exercise_hash = perps_wallet_recovery_exercise_hash_v1(exercise)
    exercise["signature_envelopes"] = [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND,
            payload_hash=exercise_hash,
            signer_id="guardian-oracle",
            key_id="guardian-oracle",
            private_key_hex=_privkey_hex(ORACLE_PRIVKEY),
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND,
            payload_hash=exercise_hash,
            signer_id="guardian-operator",
            key_id="guardian-operator",
            private_key_hex=_privkey_hex(OPERATOR_PRIVKEY),
        ),
    ]
    return exercise


def _perps_wallet_rotated_profile() -> dict[str, object]:
    return build_perps_wallet_authority_profile_v1(
        authority_id="perps-wallet-mainnet-authority-v1",
        chain_id=CHAIN_ID,
        stage="production",
        enabled=True,
        key_manager=ZenoKeyManager(
            key_refs=(
                KeyRef(key_id="perps-wallet-c", public_key=CAROL, recovery_policy_id="recovery-perps-wallet-c"),
                KeyRef(key_id="perps-wallet-b", public_key=BOB, recovery_policy_id="recovery-perps-wallet-b"),
            ),
            recovery_policies=(
                SocialRecoveryPolicy(
                    policy_id="recovery-perps-wallet-c",
                    subject_key_id="perps-wallet-c",
                    threshold=2,
                    delay_epochs=3,
                    guardians=(
                        RecoveryGuardian(guardian_id="guardian-oracle", public_key=ORACLE),
                        RecoveryGuardian(guardian_id="guardian-operator", public_key=OPERATOR),
                    ),
                ),
                SocialRecoveryPolicy(
                    policy_id="recovery-perps-wallet-b",
                    subject_key_id="perps-wallet-b",
                    threshold=2,
                    delay_epochs=3,
                    guardians=(
                        RecoveryGuardian(guardian_id="guardian-oracle", public_key=ORACLE),
                        RecoveryGuardian(guardian_id="guardian-operator", public_key=OPERATOR),
                    ),
                ),
            ),
        ).public_dict(),
        signer_registry=build_signer_registry_v0(
            registry_id="perps-wallet-authority-v1",
            payload_kind=PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
            threshold=1,
            signers=(
                {
                    "signer_id": "wallet-c",
                    "key_id": "perps-wallet-c",
                    "public_key": CAROL,
                    "weight": 1,
                    "status": "active",
                },
                {
                    "signer_id": "wallet-b",
                    "key_id": "perps-wallet-b",
                    "public_key": BOB,
                    "weight": 1,
                    "status": "active",
                },
            ),
        ),
        wallet_ux={
            "external_signer_required": True,
            "key_manager_required": True,
            "device_approval_required": True,
            "replay_protection_required": True,
            "recovery_policy_required": True,
        },
        proof_profile={
            "stream8_proof_intent_required": True,
            "state_delta_witness_required": True,
            "zk_or_proof_required": True,
            "runtime_proof_profile": "perps-stream8-risc0-or-equivalent-v1",
        },
        transaction_scope={
            "stream_key": "8",
            "allowed_actions": [
                "init_market_2p",
                "deposit_collateral",
                "withdraw_collateral",
                "deposit_insurance",
                "set_position_pair",
                "advance_epoch",
                "publish_clearing_price",
                "settle_epoch",
                "partial_liquidate",
            ],
        },
    )


def _perps_wallet_rotation_exercise(**overrides: object) -> dict[str, object]:
    base = {
        "schema": PERPS_WALLET_ROTATION_EXERCISE_SCHEMA_V1,
        "chain_id": CHAIN_ID,
        "authority_id": "perps-wallet-mainnet-authority-v1",
        "rotated_key_id": "perps-wallet-a",
        "replacement_key_id": "perps-wallet-c",
        "policy_id": "recovery-perps-wallet-a",
        "requested_at_epoch": 10,
        "broadcast_at_epoch": 13,
        "broadcast_reference": "tau-tx:perps-wallet-rotation-1",
        "approvals": ["guardian-oracle", "guardian-operator"],
        "next_wallet_authority_profile": _perps_wallet_rotated_profile(),
    }
    base.update(overrides)
    exercise = dict(base)
    exercise_hash = perps_wallet_rotation_exercise_hash_v1(exercise)
    exercise["signature_envelopes"] = [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND,
            payload_hash=exercise_hash,
            signer_id="guardian-oracle",
            key_id="guardian-oracle",
            private_key_hex=_privkey_hex(ORACLE_PRIVKEY),
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND,
            payload_hash=exercise_hash,
            signer_id="guardian-operator",
            key_id="guardian-operator",
            private_key_hex=_privkey_hex(OPERATOR_PRIVKEY),
        ),
    ]
    return exercise


def _perps_wallet_device_approval_exercise(**overrides: object) -> dict[str, object]:
    backend = KeyBackendDescriptor(
        key_id="perps-wallet-a",
        backend_kind=BACKEND_OS_KEYCHAIN,
        backend_id="macbook-keychain-wallet-a",
        policy_hash=ROOT_A,
        metadata={
            "provider": "macos-keychain",
            "device_approval_mode": "local_user_presence",
        },
    ).public_dict()
    environment = KeyExecutionEnvironment(
        environment_id="perps-wallet-a-session-1",
        environment_kind=KEY_ENVIRONMENT_LOCAL_PROCESS,
        chain_id=CHAIN_ID,
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    ).public_dict()
    use_policy = build_perps_wallet_device_approval_use_policy_v1(
        allowed_payload_kinds=["perps_wallet_prepare"],
        allowed_chain_ids=[CHAIN_ID],
        allowed_purposes=["sign"],
        valid_from_epoch=10,
        valid_until_epoch=20,
    )
    environment_policy = build_perps_wallet_device_approval_environment_policy_v1(
        allowed_environment_kinds=[KEY_ENVIRONMENT_LOCAL_PROCESS],
        expected_chain_id=CHAIN_ID,
        expected_policy_hash=ROOT_A,
        expected_challenge_hash=ROOT_B,
        require_user_presence=True,
        require_rollback_protection=True,
    )
    base = build_perps_wallet_device_approval_exercise_v1(
        authority_id="perps-wallet-mainnet-authority-v1",
        chain_id=CHAIN_ID,
        key_id="perps-wallet-a",
        payload_kind="perps_wallet_prepare",
        purpose="sign",
        current_epoch=13,
        backend_descriptor=backend,
        use_policy=use_policy,
        environment=environment,
        environment_policy=environment_policy,
        payload={
            "domain": "zenodex.perps.stream8.device-approval.v1",
            "chain_id": CHAIN_ID,
            "nonce": 14,
            "action": "deposit_collateral",
            "stream_key": "8",
        },
        seen_nonces=[11, 12],
    )
    base.update(overrides)
    if "exercise_hash" in base:
        del base["exercise_hash"]
    return {
        **base,
        "schema": PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_SCHEMA_V1,
        "exercise_hash": perps_wallet_device_approval_exercise_hash_v1(base),
    }


def _perps_wallet_signer_device_integration(**overrides: object) -> dict[str, object]:
    backend = KeyBackendDescriptor(
        key_id="perps-wallet-a",
        backend_kind=BACKEND_OS_KEYCHAIN,
        backend_id="macbook-keychain-wallet-a",
        policy_hash=ROOT_A,
        metadata={
            "provider": "macos-keychain",
            "device_approval_mode": "local_user_presence",
        },
    ).public_dict()
    environment = KeyExecutionEnvironment(
        environment_id="perps-wallet-a-session-1",
        environment_kind=KEY_ENVIRONMENT_LOCAL_PROCESS,
        chain_id=CHAIN_ID,
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    ).public_dict()
    environment_policy = build_perps_wallet_device_approval_environment_policy_v1(
        allowed_environment_kinds=[KEY_ENVIRONMENT_LOCAL_PROCESS],
        expected_chain_id=CHAIN_ID,
        expected_policy_hash=ROOT_A,
        expected_challenge_hash=ROOT_B,
        require_user_presence=True,
        require_rollback_protection=True,
    )
    base = build_perps_wallet_signer_device_integration_v1(
        authority_id="perps-wallet-mainnet-authority-v1",
        chain_id=CHAIN_ID,
        key_id="perps-wallet-a",
        current_epoch=13,
        backend_descriptor=backend,
        environment=environment,
        environment_policy=environment_policy,
        device_label="MacBook Keychain Wallet A",
        approval_reference="os-prompt:wallet-a:epoch-13",
    )
    base.update(overrides)
    if "integration_hash" in base:
        del base["integration_hash"]
    return {
        **base,
        "schema": "zenodex/perps-wallet-signer-device-integration/v1",
        "integration_hash": perps_wallet_signer_device_integration_hash_v1(base),
    }


def _perps_wallet_signer_execution_exercise(**overrides: object) -> dict[str, object]:
    payload = dict(overrides.pop("payload", _perps_wallet_signer_payload()))
    signed_payload_hash = overrides.pop("signed_payload_hash", _perps_wallet_signer_payload_hash(payload))
    backend = KeyBackendDescriptor(
        key_id="perps-wallet-a",
        backend_kind=BACKEND_OS_KEYCHAIN,
        backend_id="macbook-keychain-wallet-a",
        policy_hash=ROOT_A,
        metadata={
            "provider": "macos-keychain",
            "device_approval_mode": "local_user_presence",
        },
    ).public_dict()
    environment = KeyExecutionEnvironment(
        environment_id="perps-wallet-a-session-1",
        environment_kind=KEY_ENVIRONMENT_LOCAL_PROCESS,
        chain_id=CHAIN_ID,
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    ).public_dict()
    use_policy = build_perps_wallet_device_approval_use_policy_v1(
        allowed_payload_kinds=["perps_wallet_submit"],
        allowed_chain_ids=[CHAIN_ID],
        allowed_purposes=["sign"],
        valid_from_epoch=10,
        valid_until_epoch=20,
    )
    environment_policy = build_perps_wallet_device_approval_environment_policy_v1(
        allowed_environment_kinds=[KEY_ENVIRONMENT_LOCAL_PROCESS],
        expected_chain_id=CHAIN_ID,
        expected_policy_hash=ROOT_A,
        expected_challenge_hash=ROOT_B,
        require_user_presence=True,
        require_rollback_protection=True,
    )
    base = build_perps_wallet_signer_execution_exercise_v1(
        authority_id="perps-wallet-mainnet-authority-v1",
        chain_id=CHAIN_ID,
        key_id="perps-wallet-a",
        payload_kind="perps_wallet_submit",
        purpose="sign",
        current_epoch=13,
        backend_descriptor=backend,
        use_policy=use_policy,
        environment=environment,
        environment_policy=environment_policy,
        device_label="MacBook Keychain Wallet A",
        approval_reference="os-prompt:wallet-a:epoch-13",
        prompt_reference="os-prompt:wallet-a:epoch-13",
        prompt_presented_at_epoch=12,
        prompt_confirmed_at_epoch=13,
        payload=payload,
        seen_nonces=[11, 12, 14],
        execution_reference="tau-submit:wallet-a:epoch-13",
        signed_payload_hash=str(signed_payload_hash),
    )
    base.update(overrides)
    if "exercise_hash" in base:
        del base["exercise_hash"]
    return {
        **base,
        "schema": PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_SCHEMA_V1,
        "exercise_hash": perps_wallet_signer_execution_exercise_hash_v1(base),
    }


def _perps_wallet_signer_prompt_capture(**overrides: object) -> dict[str, object]:
    prompt_message_hash = overrides.pop("prompt_message_hash", _perps_wallet_signer_payload_hash())
    backend = KeyBackendDescriptor(
        key_id="perps-wallet-a",
        backend_kind=BACKEND_OS_KEYCHAIN,
        backend_id="macbook-keychain-wallet-a",
        policy_hash=ROOT_A,
        metadata={
            "provider": "macos-keychain",
            "device_approval_mode": "local_user_presence",
        },
    ).public_dict()
    environment = KeyExecutionEnvironment(
        environment_id="perps-wallet-a-session-1",
        environment_kind=KEY_ENVIRONMENT_LOCAL_PROCESS,
        chain_id=CHAIN_ID,
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    ).public_dict()
    environment_policy = build_perps_wallet_device_approval_environment_policy_v1(
        allowed_environment_kinds=[KEY_ENVIRONMENT_LOCAL_PROCESS],
        expected_chain_id=CHAIN_ID,
        expected_policy_hash=ROOT_A,
        expected_challenge_hash=ROOT_B,
        require_user_presence=True,
        require_rollback_protection=True,
    )
    base = build_perps_wallet_signer_prompt_capture_v1(
        authority_id="perps-wallet-mainnet-authority-v1",
        chain_id=CHAIN_ID,
        key_id="perps-wallet-a",
        current_epoch=13,
        backend_descriptor=backend,
        environment=environment,
        environment_policy=environment_policy,
        device_label="MacBook Keychain Wallet A",
        approval_reference="os-prompt:wallet-a:epoch-13",
        prompt_reference="os-prompt:wallet-a:epoch-13",
        prompt_source="os-keychain-dialog",
        prompt_presented_at_epoch=12,
        prompt_confirmed_at_epoch=13,
        prompt_message_hash=str(prompt_message_hash),
        capture_source="operator-audit-log",
        capture_evidence_hash="0x" + "ab" * 32,
    )
    base.update(overrides)
    if "capture_hash" in base:
        del base["capture_hash"]
    return {
        **base,
        "schema": PERPS_WALLET_SIGNER_PROMPT_CAPTURE_SCHEMA_V1,
        "capture_hash": perps_wallet_signer_prompt_capture_hash_v1(base),
    }


def _perps_wallet_hardware_backend_descriptor() -> dict[str, object]:
    return KeyBackendDescriptor(
        key_id="perps-wallet-a",
        backend_kind=BACKEND_HARDWARE_WALLET_PLACEHOLDER,
        backend_id="hardware-wallet-a",
        policy_hash=ROOT_A,
        metadata={
            "provider": "hardware-wallet-demo",
            "device_approval_mode": "local_user_presence",
        },
    ).public_dict()


def _perps_wallet_live_hardware_backend_descriptor() -> dict[str, object]:
    return KeyBackendDescriptor(
        key_id="perps-wallet-a",
        backend_kind=BACKEND_HARDWARE_WALLET,
        backend_id="ledger-x-prod-01",
        policy_hash=ROOT_A,
        metadata={
            "provider": "ledger-live",
            "device_approval_mode": "hardware_device_confirm",
        },
    ).public_dict()


def _perps_wallet_hardware_environment() -> dict[str, object]:
    return KeyExecutionEnvironment(
        environment_id="perps-wallet-a-hardware-session-1",
        environment_kind=KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
        chain_id=CHAIN_ID,
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    ).public_dict()


def _perps_wallet_live_hardware_environment() -> dict[str, object]:
    return KeyExecutionEnvironment(
        environment_id="perps-wallet-a-live-hardware-session-1",
        environment_kind=KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
        chain_id=CHAIN_ID,
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        attestation_hash="0x" + "cc" * 32,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    ).public_dict()


def _perps_wallet_hardware_environment_policy() -> dict[str, object]:
    return build_perps_wallet_device_approval_environment_policy_v1(
        allowed_environment_kinds=[KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE],
        expected_chain_id=CHAIN_ID,
        expected_policy_hash=ROOT_A,
        expected_challenge_hash=ROOT_B,
        require_user_presence=True,
        require_rollback_protection=True,
    )


def _perps_wallet_device_approval_exercise_hardware(**overrides: object) -> dict[str, object]:
    return _perps_wallet_device_approval_exercise(
        backend_descriptor=_perps_wallet_hardware_backend_descriptor(),
        environment=_perps_wallet_hardware_environment(),
        environment_policy=_perps_wallet_hardware_environment_policy(),
        **overrides,
    )


def _perps_wallet_device_approval_exercise_live_hardware(**overrides: object) -> dict[str, object]:
    return _perps_wallet_device_approval_exercise(
        backend_descriptor=_perps_wallet_live_hardware_backend_descriptor(),
        environment=_perps_wallet_live_hardware_environment(),
        environment_policy=_perps_wallet_hardware_environment_policy(),
        **overrides,
    )


def _perps_wallet_signer_device_integration_hardware(**overrides: object) -> dict[str, object]:
    return _perps_wallet_signer_device_integration(
        backend_descriptor=_perps_wallet_hardware_backend_descriptor(),
        environment=_perps_wallet_hardware_environment(),
        environment_policy=_perps_wallet_hardware_environment_policy(),
        device_label="Hardware Wallet A",
        **overrides,
    )


def _perps_wallet_signer_device_integration_live_hardware(**overrides: object) -> dict[str, object]:
    return _perps_wallet_signer_device_integration(
        backend_descriptor=_perps_wallet_live_hardware_backend_descriptor(),
        environment=_perps_wallet_live_hardware_environment(),
        environment_policy=_perps_wallet_hardware_environment_policy(),
        device_label="Hardware Wallet A",
        **overrides,
    )


def _perps_wallet_signer_prompt_capture_hardware(**overrides: object) -> dict[str, object]:
    return _perps_wallet_signer_prompt_capture(
        backend_descriptor=_perps_wallet_hardware_backend_descriptor(),
        environment=_perps_wallet_hardware_environment(),
        environment_policy=_perps_wallet_hardware_environment_policy(),
        device_label="Hardware Wallet A",
        prompt_source="hardware-wallet-prompt",
        **overrides,
    )


def _perps_wallet_signer_prompt_capture_live_hardware(**overrides: object) -> dict[str, object]:
    return _perps_wallet_signer_prompt_capture(
        backend_descriptor=_perps_wallet_live_hardware_backend_descriptor(),
        environment=_perps_wallet_live_hardware_environment(),
        environment_policy=_perps_wallet_hardware_environment_policy(),
        device_label="Hardware Wallet A",
        prompt_source="hardware-wallet-prompt",
        **overrides,
    )


def _perps_wallet_signer_execution_exercise_hardware(**overrides: object) -> dict[str, object]:
    return _perps_wallet_signer_execution_exercise(
        backend_descriptor=_perps_wallet_hardware_backend_descriptor(),
        environment=_perps_wallet_hardware_environment(),
        environment_policy=_perps_wallet_hardware_environment_policy(),
        device_label="Hardware Wallet A",
        **overrides,
    )


def _perps_wallet_signer_execution_exercise_live_hardware(**overrides: object) -> dict[str, object]:
    return _perps_wallet_signer_execution_exercise(
        backend_descriptor=_perps_wallet_live_hardware_backend_descriptor(),
        environment=_perps_wallet_live_hardware_environment(),
        environment_policy=_perps_wallet_hardware_environment_policy(),
        device_label="Hardware Wallet A",
        **overrides,
    )


def _perps_wallet_production_device_private_key() -> Ed25519PrivateKey:
    return Ed25519PrivateKey.from_private_bytes(PRODUCTION_HW_DEVICE_PRIVKEY_BYTES)


def _perps_wallet_production_device_pubkey() -> str:
    return (
        _perps_wallet_production_device_private_key()
        .public_key()
        .public_bytes(Encoding.Raw, PublicFormat.Raw)
        .hex()
    )


def _perps_wallet_production_hardware_evidence(profile_hash: str, **overrides: object) -> dict[str, object]:
    private_key = _perps_wallet_production_device_private_key()
    body: dict[str, object] = {
        "schema": HARDWARE_WALLET_EVIDENCE_SCHEMA_V1,
        "device_id": "ledger-x-prod-01",
        "device_model": "ledger-nano-x",
        "device_firmware_version": "2.4.0",
        "device_attestation": {
            "pubkey": _perps_wallet_production_device_pubkey(),
            "challenge": "00" * 32,
            "signature": "00" * 64,
        },
        "os_prompt_capture": {
            "kind": "screenshot_hash",
            "hash": "ff" * 32,
            "captured_at": 1_700_000_020,
        },
        "device_approval_tx": {
            "tx_payload_hash": "10" * 32,
            "approval_signature": "20" * 64,
            "captured_at": 1_700_000_030,
        },
        "profile_wallet_authority_hash": profile_hash,
        "issued_at": 1_700_000_040,
    }
    body.update(overrides)
    attestation = body["device_attestation"]
    approval = body["device_approval_tx"]
    if not isinstance(attestation, dict) or not isinstance(approval, dict):
        raise AssertionError("production hardware evidence fixture must keep nested dicts")
    challenge = production_hardware_wallet_attestation_challenge_v1(body)
    tx_payload_hash = str(approval["tx_payload_hash"])
    attestation["challenge"] = challenge
    attestation["signature"] = private_key.sign(
        production_hardware_wallet_attestation_message_v1(challenge)
    ).hex()
    approval["approval_signature"] = private_key.sign(
        production_hardware_wallet_approval_message_v1(tx_payload_hash)
    ).hex()
    return attach_production_hardware_wallet_hash_v1(body)


def _perps_wallet_signer_ceremony_payload(**overrides: object) -> dict[str, object]:
    base = {
        "chain_id": CHAIN_ID,
        "device_approval_exercise": _perps_wallet_device_approval_exercise(),
        "signer_device_integration": _perps_wallet_signer_device_integration(),
        "signer_prompt_capture": _perps_wallet_signer_prompt_capture(),
        "signer_execution_exercise": _perps_wallet_signer_execution_exercise(),
    }
    base.update(overrides)
    return base


def _oracle_authority_key_manager(*, second_pubkey: str = OPERATOR) -> dict[str, object]:
    return ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="oracle-authority-a", public_key=ORACLE),
            KeyRef(key_id="oracle-authority-b", public_key=second_pubkey),
        )
    ).public_dict()


def _oracle_authority_signer_registry(*, second_pubkey: str = OPERATOR, threshold: int = 2) -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id="oracle-production-authority-v1",
        payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
        threshold=threshold,
        signers=(
            {
                "signer_id": "oracle-a",
                "key_id": "oracle-authority-a",
                "public_key": ORACLE,
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "oracle-b",
                "key_id": "oracle-authority-b",
                "public_key": second_pubkey,
                "weight": 1,
                "status": "active",
            },
        ),
    )


def _oracle_authority_profile(**overrides: object) -> dict[str, object]:
    base = {
        "authority_id": "oracle-production-authority-v1",
        "chain_id": CHAIN_ID,
        "stage": "production",
        "enabled": True,
        "key_manager": _oracle_authority_key_manager(),
        "signer_registry": _oracle_authority_signer_registry(),
        "wallet_ux": {
            "external_signer_required": True,
            "key_manager_required": True,
            "device_approval_required": True,
        },
        "proof_profile": {
            "zk_or_proof_required": True,
            "oracle_receipt_replay_required": True,
            "runtime_proof_profile": "zenooracle-o3-replay-zk-profile-v1",
        },
    }
    base.update(overrides)
    profile = build_oracle_authority_profile_v1(**base)
    profile["signature_envelopes"] = [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
            payload_hash=str(profile["authority_hash"]),
            signer_id="oracle-a",
            key_id="oracle-authority-a",
            private_key_hex=_privkey_hex(ORACLE_PRIVKEY),
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
            payload_hash=str(profile["authority_hash"]),
            signer_id="oracle-b",
            key_id="oracle-authority-b",
            private_key_hex=_privkey_hex(OPERATOR_PRIVKEY),
        ),
    ]
    return profile


def _wrapped_app_state(state: DexState) -> dict[str, object]:
    return {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(state).data,
        "proof_mining": None,
        "zusd_monetary": None,
    }


def _signed_init_op(*, quote_asset: str, nonce_a: int = 1, nonce_b: int = 1) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "init_market_2p",
        "quote_asset": quote_asset,
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "deadline": FUTURE_DEADLINE,
        "nonce_a": nonce_a,
        "nonce_b": nonce_b,
    }
    op["sig_a"] = sign_perp_op_for_engine(op, privkey=ALICE_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=ALICE, nonce=nonce_a)
    op["sig_b"] = sign_perp_op_for_engine(op, privkey=BOB_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=BOB, nonce=nonce_b)
    return op


def _state_with_market_and_balance(*, quote_asset: str) -> DexState:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    res = apply_perp_ops(
        config=PerpEngineConfig(chain_id=CHAIN_ID),
        state=state,
        operations={"5": [_signed_init_op(quote_asset=quote_asset)]},
        tx_sender_pubkey=ALICE,
        block_timestamp=1,
    )
    assert res.ok, res.error
    assert res.state is not None
    return _with_balances(res.state, (ALICE, quote_asset, 5_000))


def _apply_perps(state: DexState, ops: list[dict[str, object]], *, sender: str = OPERATOR) -> DexState:
    res = apply_perp_ops(
        config=PerpEngineConfig(chain_id=CHAIN_ID, oracle_pubkey=ORACLE),
        state=state,
        operations={"5": ops},
        tx_sender_pubkey=sender,
        block_timestamp=1,
    )
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _state_with_advanced_market(*, quote_asset: str) -> DexState:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply_perps(state, [_signed_init_op(quote_asset=quote_asset)])
    return _apply_perps(
        state,
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "advance_epoch", "delta": 1}],
    )


def _state_ready_to_settle(*, quote_asset: str) -> DexState:
    state = _state_with_advanced_market(quote_asset=quote_asset)
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "publish_clearing_price",
        "price_e8": 100_000_000,
        "deadline": FUTURE_DEADLINE,
        "oracle_nonce": 1,
    }
    op["oracle_sig"] = sign_perp_op_for_engine(
        op,
        privkey=ORACLE_PRIVKEY,
        chain_id=CHAIN_ID,
        signer_pubkey=ORACLE,
        nonce=1,
    )
    return _apply_perps(state, [op], sender=ORACLE)


def _signed_set_position_pair(*, new_a: int, new_b: int, nonce_a: int, nonce_b: int) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "set_position_pair",
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "new_position_base_a": int(new_a),
        "new_position_base_b": int(new_b),
        "deadline": FUTURE_DEADLINE,
        "nonce_a": int(nonce_a),
        "nonce_b": int(nonce_b),
    }
    op["sig_a"] = sign_perp_op_for_engine(op, privkey=ALICE_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=ALICE, nonce=nonce_a)
    op["sig_b"] = sign_perp_op_for_engine(op, privkey=BOB_PRIVKEY, chain_id=CHAIN_ID, signer_pubkey=BOB, nonce=nonce_b)
    return op


def _signed_publish_price(*, price_e8: int, oracle_nonce: int) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": MARKET_ID,
        "action": "publish_clearing_price",
        "price_e8": int(price_e8),
        "deadline": FUTURE_DEADLINE,
        "oracle_nonce": int(oracle_nonce),
    }
    op["oracle_sig"] = sign_perp_op_for_engine(
        op,
        privkey=ORACLE_PRIVKEY,
        chain_id=CHAIN_ID,
        signer_pubkey=ORACLE,
        nonce=oracle_nonce,
    )
    return op


def _state_after_pair_liquidation(*, quote_asset: str) -> DexState:
    state = _state_ready_to_settle(quote_asset=quote_asset)
    state = _apply_perps(
        state,
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "settle_epoch"}],
    )
    state = _with_balances(
        state,
        (ALICE, quote_asset, 1000),
        (BOB, quote_asset, 1000),
    )
    state = _apply_perps(
        state,
        [
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": MARKET_ID,
                "action": "deposit_collateral",
                "account_pubkey": ALICE,
                "amount": 100,
            }
        ],
        sender=ALICE,
    )
    state = _apply_perps(
        state,
        [
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": MARKET_ID,
                "action": "deposit_collateral",
                "account_pubkey": BOB,
                "amount": 100,
            }
        ],
        sender=BOB,
    )
    state = _apply_perps(state, [_signed_set_position_pair(new_a=1000, new_b=-1000, nonce_a=2, nonce_b=2)])
    state = _apply_perps(
        state,
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "advance_epoch", "delta": 1}],
    )
    state = _apply_perps(state, [_signed_publish_price(price_e8=105_000_000, oracle_nonce=2)], sender=ORACLE)
    return _apply_perps(
        state,
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "settle_epoch"}],
    )


def _state_with_posted_collateral(*, quote_asset: str) -> DexState:
    state = _state_with_market_and_balance(quote_asset=quote_asset)
    return _apply_perps(
        state,
        [
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": MARKET_ID,
                "action": "deposit_collateral",
                "account_pubkey": ALICE,
                "amount": 1_000,
            }
        ],
        sender=ALICE,
    )


def _state_with_isolated_liquidatable_account(*, quote_asset: str) -> DexState:
    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 5,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 4,
            "index_price_e8": 10_000_000_000,
            "max_oracle_staleness_epochs": 100,
            "max_oracle_move_bps": 500,
            "initial_margin_bps": 1000,
            "maintenance_margin_bps": 500,
            "depeg_buffer_bps": 100,
            "liquidation_penalty_bps": 50,
            "max_position_abs": 1_000_000,
            "fee_pool_quote": 0,
            "fee_income": 0,
            "initial_insurance": 100_000,
            "insurance_balance": 100_000,
            "claims_paid": 0,
            "min_notional_for_bounty": 100_000_000,
        }
    )
    market = PerpMarketState(
        quote_asset=quote_asset,
        global_state=global_state,
        accounts={
            ALICE: PerpAccountState(
                position_base=100,
                entry_price_e8=10_000_000_000,
                collateral_quote=300,
                funding_paid_cumulative=0,
                funding_last_applied_epoch=0,
                liquidated_this_step=False,
            )
        },
    )
    return DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION, markets={ISOLATED_MARKET_ID: market}),
    )


class _FakeClient:
    app_state: dict[str, object] = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    sent: list[dict[str, object]] = []
    native_balances: dict[str, int] = {}

    def __init__(self, _cfg=None) -> None:
        self.app_hash = "sha256:" + "cd" * 32
        pass

    def rpc(self, cmd: str) -> str:
        if cmd == "hello version=1":
            return "HELLO: ok"
        raise AssertionError(f"unexpected rpc call: {cmd}")

    def getappstate(self, *, full: bool = False) -> str:
        assert full is True
        return json.dumps({"app_hash": self.app_hash, "app_state": self.app_state}, sort_keys=True)

    def get_sequence(self, sender_pubkey_hex: str) -> int:
        if sender_pubkey_hex == ALICE[2:]:
            return 9
        if sender_pubkey_hex == BOB[2:]:
            return 11
        if sender_pubkey_hex == ORACLE[2:]:
            return 13
        if sender_pubkey_hex == OPERATOR[2:]:
            return 15
        return 0

    def get_balance(self, address_hex: str) -> int:
        return int(self.native_balances.get(address_hex, 0))

    def sendtx(self, payload):
        if isinstance(payload, dict) and isinstance(payload.get("operations"), dict):
            operations = payload["operations"]
            if "8" in operations:
                _fake_client_apply_stream8_payload(self, payload)
            else:
                self.sent.append(dict(payload))
        else:
            self.sent.append(dict(payload))
        return "SUCCESS tx accepted"

    def createblock(self) -> str:
        return "BLOCK created"


def _test_oracle_bridge_fixture(
    *,
    action: str,
    market_id: str,
    chain_id: str = CHAIN_ID,
    account_pubkey: str | None = None,
    fraction_bps: int = 0,
) -> dict[str, object]:
    return build_perps_oracle_bridge_fixture(
        state=perps_wallet_api._state_from_app_state(_FakeClient.app_state),
        config=perps_wallet_api._build_perp_config(chain_id=chain_id),
        market_id=market_id,
        action=action,
        account_pubkey=account_pubkey,
        fraction_bps=fraction_bps,
    )


def _assert_redacted_tau_tx_payload(
    redacted: object,
    actual: Mapping[str, object],
    *,
    operation_streams: list[str] | None = None,
) -> None:
    assert isinstance(redacted, Mapping)
    assert redacted["redacted"] is True
    assert redacted["redaction_reason"] == "signed_tau_tx_payload_response_redaction"
    assert redacted["payload_hash"] == perps_wallet_api._hash_payload(
        "zenodex.perps_wallet.tau_tx_payload/v1",
        actual,
    )
    assert redacted["sender_pubkey"] == actual["sender_pubkey"]
    assert redacted["sequence_number"] == actual["sequence_number"]
    assert redacted["fee_limit"] == str(actual["fee_limit"])
    assert redacted["operation_streams"] == (operation_streams or ["8"])


def _fake_client_apply_stream8_payload(client: _FakeClient, payload: object) -> None:
    client.sent.append(dict(payload))
    assert isinstance(payload, dict)
    wire_ops = payload.get("operations")
    assert isinstance(wire_ops, dict)
    stream_ops = json.loads(wire_ops["8"])
    state = perps_wallet_api._state_from_app_state(client.app_state)
    result = apply_perp_ops(
        config=PerpEngineConfig(
            chain_id=CHAIN_ID,
            oracle_pubkey=ORACLE,
            operator_pubkey=OPERATOR,
            allow_isolated_markets=True,
            oracle_adapter_bridge_verifier=perps_wallet_api._default_oracle_adapter_bridge_verifier,
            require_oracle_adapter_for_clearinghouse_settle_epoch=True,
            require_oracle_adapter_for_isolated_partial_liquidate=False,
        ),
        state=state,
        operations={"5": stream_ops},
        tx_sender_pubkey="0x" + str(payload["sender_pubkey"]),
        block_timestamp=1,
    )
    assert result.ok, result.error
    assert result.state is not None
    client.app_state = _wrapped_app_state(result.state)
    type(client).app_state = client.app_state
    client.app_hash = "sha256:" + hash_v0("test_perps_wallet_app_state", client.app_state)[2:]


@pytest.fixture(autouse=True)
def _reset_fake_client_balances(monkeypatch: pytest.MonkeyPatch) -> None:
    # The shipped runtime deliberately has no aggregate-adapter verifier until
    # one is promoted independently of the pre-MVP Oracle tooling.  These
    # integration vectors explicitly inject the test-only verifier instead of
    # relying on an environment-dependent production import.
    monkeypatch.setattr(
        perps_wallet_api,
        "verify_aggregate_adapter_bridge",
        verify_test_oracle_aggregate_adapter_bridge,
    )
    _FakeClient.native_balances = {}
    yield
    _FakeClient.native_balances = {}


def test_perps_wallet_authority_missing_profile_is_blocked() -> None:
    status = evaluate_perps_wallet_authority_profile_v1(None, expected_chain_id=CHAIN_ID)

    assert status["ok"] is False
    assert status["production_wallet_authority"] is False
    assert status["status"] == "blocked"
    assert status["readiness_gaps"] == ["perps wallet authority profile is missing"]


def test_perps_wallet_authority_complete_profile_is_ready() -> None:
    profile = _perps_wallet_authority_profile()
    status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=CHAIN_ID)

    assert status["ok"] is True
    assert status["production_wallet_authority"] is True
    assert status["status"] == "ready"
    assert status["readiness_gaps"] == []
    assert status["threshold"] == 1
    assert status["active_signer_count"] == 2
    assert status["key_ref_count"] == 2
    assert status["recovery_policy_count"] == 2
    assert status["recoverable_active_key_count"] == 2
    assert status["wallet_ux"]["device_approval_required"] is True
    assert status["wallet_ux"]["replay_protection_required"] is True
    assert status["wallet_ux"]["recovery_policy_required"] is True
    assert status["proof_profile"]["state_delta_witness_required"] is True
    assert status["proof_profile"]["runtime_proof_profile"] == "perps-stream8-risc0-or-equivalent-v1"
    assert status["transaction_scope"]["stream_key"] == "8"
    assert "deposit_collateral" in status["transaction_scope"]["allowed_actions"]
    assert "deposit_insurance" in status["transaction_scope"]["allowed_actions"]
    assert {policy["subject_key_id"] for policy in status["recovery_policies"]} == {
        "perps-wallet-a",
        "perps-wallet-b",
    }
    assert infer_artifact_hash_v0(
        artifact=profile,
        payload_kind=PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
    ) == profile["wallet_authority_hash"]


def test_perps_wallet_authority_blocks_bad_controls_and_chain_mismatch() -> None:
    profile = _perps_wallet_authority_profile(
        chain_id="wrong-chain",
        stage="devnet",
        enabled=False,
        wallet_ux={
            "external_signer_required": True,
            "key_manager_required": False,
            "device_approval_required": True,
            "replay_protection_required": False,
            "recovery_policy_required": False,
        },
        proof_profile={
            "stream8_proof_intent_required": True,
            "state_delta_witness_required": False,
            "zk_or_proof_required": False,
            "runtime_proof_profile": "",
        },
        transaction_scope={"stream_key": "9", "allowed_actions": []},
    )

    status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=CHAIN_ID)
    gaps = set(status["readiness_gaps"])

    assert status["production_wallet_authority"] is False
    assert "perps wallet authority profile is not enabled" in gaps
    assert "perps wallet authority profile stage must be production" in gaps
    assert "perps wallet authority profile chain_id mismatch" in gaps
    assert "wallet_ux.key_manager_required must be true" in gaps
    assert "wallet_ux.replay_protection_required must be true" in gaps
    assert "wallet_ux.recovery_policy_required must be true" in gaps
    assert "proof_profile.state_delta_witness_required must be true" in gaps
    assert "proof_profile.zk_or_proof_required must be true" in gaps
    assert "proof_profile.runtime_proof_profile must be a non-empty string" in gaps
    assert "transaction_scope.stream_key must be 8" in gaps
    assert "transaction_scope.allowed_actions must be a non-empty string list" in gaps


def test_perps_wallet_authority_blocks_signer_key_manager_public_key_mismatch() -> None:
    profile = _perps_wallet_authority_profile(
        key_manager=_perps_wallet_key_manager(second_pubkey=ORACLE),
        signer_registry=_perps_wallet_signer_registry(second_pubkey=BOB),
    )

    status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=CHAIN_ID)

    assert status["production_wallet_authority"] is False
    assert "active signer key_id perps-wallet-b public key mismatch" in status["readiness_gaps"]


def test_perps_wallet_authority_blocks_active_signer_without_recovery_policy() -> None:
    key_manager = ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="perps-wallet-a", public_key=ALICE),
            KeyRef(key_id="perps-wallet-b", public_key=BOB, recovery_policy_id="recovery-perps-wallet-b"),
        ),
        recovery_policies=(
            SocialRecoveryPolicy(
                policy_id="recovery-perps-wallet-b",
                subject_key_id="perps-wallet-b",
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-oracle", public_key=ORACLE),
                    RecoveryGuardian(guardian_id="guardian-operator", public_key=OPERATOR),
                ),
            ),
        ),
    ).public_dict()
    profile = _perps_wallet_authority_profile(key_manager=key_manager)

    status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=CHAIN_ID)

    assert status["production_wallet_authority"] is False
    assert status["recovery_policy_count"] == 1
    assert status["recoverable_active_key_count"] == 1
    assert "active signer key_id perps-wallet-a has no recovery_policy_id" in status["readiness_gaps"]


def test_perps_wallet_recovery_exercise_ready_receipt() -> None:
    profile = _perps_wallet_authority_profile()
    exercise = _perps_wallet_recovery_exercise()

    status = evaluate_perps_wallet_recovery_exercise_v1(profile, exercise, expected_chain_id=CHAIN_ID)

    assert status["ok"] is True
    assert status["recovery_exercise_ready"] is True
    assert status["status"] == "ready"
    assert status["errors"] == []
    assert status["wallet_authority_hash"] == profile["wallet_authority_hash"]
    assert status["exercise_hash"] == perps_wallet_recovery_exercise_hash_v1(exercise)
    assert status["subject_key_id"] == "perps-wallet-a"
    assert status["evaluation"]["ok"] is True
    assert status["evaluation"]["delay_ok"] is True
    assert status["evaluation"]["threshold_ok"] is True
    assert status["evaluation"]["accepted_weight"] == 2
    assert status["evaluation_hash"] == status["evaluation"]["evaluation_hash"]
    assert status["guardian_signature_quorum"]["accepted_weight"] == 2
    assert status["guardian_signature_quorum"]["threshold"] == 2
    assert status["guardian_signature_quorum_hash"] == status["guardian_signature_quorum"]["quorum_report_hash"]
    encoded = json.dumps(status, sort_keys=True)
    assert "private_key" not in encoded
    assert "secret_hex" not in encoded


def test_perps_wallet_recovery_exercise_blocks_early_request() -> None:
    status = evaluate_perps_wallet_recovery_exercise_v1(
        _perps_wallet_authority_profile(),
        _perps_wallet_recovery_exercise(current_epoch=12),
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["recovery_exercise_ready"] is False
    assert status["status"] == "blocked"
    assert "recovery_policy_not_satisfied" in status["errors"]
    assert status["evaluation"]["delay_ok"] is False
    assert status["evaluation"]["threshold_ok"] is True


def test_perps_wallet_recovery_exercise_blocks_bad_guardian_signature_quorum() -> None:
    exercise = _perps_wallet_recovery_exercise()
    exercise["signature_envelopes"] = list(exercise["signature_envelopes"])  # type: ignore[index]
    exercise["signature_envelopes"][0] = {  # type: ignore[index]
        **exercise["signature_envelopes"][0],  # type: ignore[index]
        "payload_hash": "0x" + "00" * 32,
    }

    status = evaluate_perps_wallet_recovery_exercise_v1(
        _perps_wallet_authority_profile(),
        exercise,
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["recovery_exercise_ready"] is False
    assert any("guardian signature quorum invalid" in error for error in status["errors"])


def test_perps_wallet_device_approval_exercise_ready_receipt() -> None:
    profile = _perps_wallet_authority_profile()
    exercise = _perps_wallet_device_approval_exercise()

    status = evaluate_perps_wallet_device_approval_exercise_v1(profile, exercise, expected_chain_id=CHAIN_ID)

    assert status["ok"] is True
    assert status["device_approval_ready"] is True
    assert status["status"] == "ready"
    assert status["errors"] == []
    assert status["wallet_authority_hash"] == profile["wallet_authority_hash"]
    assert status["exercise_hash"] == perps_wallet_device_approval_exercise_hash_v1(exercise)
    assert status["key_id"] == "perps-wallet-a"
    assert status["sign_admission_receipt"]["ok"] is True
    assert status["sign_admission_receipt"]["payload_nonce"] == 14
    assert status["sign_admission_receipt_hash"] == status["sign_admission_receipt"]["receipt_hash"]
    assert status["backend_hash"] == exercise["backend_descriptor"]["backend_hash"]
    assert status["environment_hash"] == exercise["environment"]["environment_hash"]
    encoded = json.dumps(status, sort_keys=True)
    assert "private_key" not in encoded
    assert "secret_hex" not in encoded


def test_perps_wallet_device_approval_exercise_blocks_missing_user_presence() -> None:
    exercise = _perps_wallet_device_approval_exercise()
    exercise["environment"] = {
        **exercise["environment"],
        "local_user_presence_confirmed": False,
    }
    exercise["environment"]["environment_hash"] = KeyExecutionEnvironment(
        environment_id=exercise["environment"]["environment_id"],
        environment_kind=exercise["environment"]["environment_kind"],
        chain_id=exercise["environment"]["chain_id"],
        policy_hash=exercise["environment"]["policy_hash"],
        challenge_hash=exercise["environment"]["challenge_hash"],
        issued_at_epoch=exercise["environment"]["issued_at_epoch"],
        expires_at_epoch=exercise["environment"]["expires_at_epoch"],
        local_user_presence_confirmed=False,
        rollback_protection_confirmed=exercise["environment"]["rollback_protection_confirmed"],
    ).public_dict()["environment_hash"]

    status = evaluate_perps_wallet_device_approval_exercise_v1(
        _perps_wallet_authority_profile(),
        exercise,
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["device_approval_ready"] is False
    assert "device_approval_sign_admission_rejected" in status["errors"]
    assert "local_user_presence_missing" in status["errors"]


def test_perps_wallet_device_approval_exercise_blocks_reused_nonce() -> None:
    status = evaluate_perps_wallet_device_approval_exercise_v1(
        _perps_wallet_authority_profile(),
        _perps_wallet_device_approval_exercise(seen_nonces=[11, 12, 14]),
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["device_approval_ready"] is False
    assert "device_approval_sign_admission_rejected" in status["errors"]
    assert "payload_nonce_reused" in status["errors"]


def test_perps_wallet_signer_device_integration_ready_receipt() -> None:
    profile = _perps_wallet_authority_profile()
    integration = _perps_wallet_signer_device_integration()

    status = evaluate_perps_wallet_signer_device_integration_v1(
        profile,
        integration,
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is True
    assert status["signer_device_ready"] is True
    assert status["status"] == "ready"
    assert status["wallet_authority_hash"] == profile["wallet_authority_hash"]
    assert status["integration_hash"] == perps_wallet_signer_device_integration_hash_v1(integration)
    assert status["backend_kind"] == BACKEND_OS_KEYCHAIN
    assert status["provider"] == "macos-keychain"
    assert status["device_approval_mode"] == "local_user_presence"
    assert status["local_user_presence_confirmed"] is True
    assert status["rollback_protection_confirmed"] is True
    assert status["backend_hash"] == integration["backend_descriptor"]["backend_hash"]
    assert status["environment_hash"] == integration["environment"]["environment_hash"]


def test_perps_wallet_signer_device_integration_rejects_integer_backend_booleans() -> None:
    integration = _perps_wallet_signer_device_integration()
    integration["backend_descriptor"] = {
        **integration["backend_descriptor"],
        "active": 1,
        "no_raw_private_key_exposure": 1,
    }
    body = {key: value for key, value in integration.items() if key != "integration_hash"}
    integration["integration_hash"] = perps_wallet_signer_device_integration_hash_v1(body)

    status = evaluate_perps_wallet_signer_device_integration_v1(
        _perps_wallet_authority_profile(),
        integration,
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["signer_device_ready"] is False
    assert any("backend_descriptor.active must be bool" in error for error in status["errors"])


def test_perps_wallet_signer_device_integration_blocks_missing_user_presence() -> None:
    integration = _perps_wallet_signer_device_integration()
    integration["environment"] = {
        **integration["environment"],
        "local_user_presence_confirmed": False,
    }
    integration["environment"]["environment_hash"] = KeyExecutionEnvironment(
        environment_id=integration["environment"]["environment_id"],
        environment_kind=integration["environment"]["environment_kind"],
        chain_id=integration["environment"]["chain_id"],
        policy_hash=integration["environment"]["policy_hash"],
        challenge_hash=integration["environment"]["challenge_hash"],
        issued_at_epoch=integration["environment"]["issued_at_epoch"],
        expires_at_epoch=integration["environment"]["expires_at_epoch"],
        local_user_presence_confirmed=False,
        rollback_protection_confirmed=integration["environment"]["rollback_protection_confirmed"],
    ).public_dict()["environment_hash"]

    status = evaluate_perps_wallet_signer_device_integration_v1(
        _perps_wallet_authority_profile(),
        integration,
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["signer_device_ready"] is False
    assert "signer_device_environment_rejected" in status["errors"]
    assert "local_user_presence_missing" in status["errors"]


def test_perps_wallet_signer_prompt_capture_ready_receipt() -> None:
    profile = _perps_wallet_authority_profile()
    capture = _perps_wallet_signer_prompt_capture()

    status = evaluate_perps_wallet_signer_prompt_capture_v1(
        profile,
        capture,
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is True
    assert status["signer_prompt_capture_ready"] is True
    assert status["status"] == "ready"
    assert status["wallet_authority_hash"] == profile["wallet_authority_hash"]
    assert status["capture_hash"] == perps_wallet_signer_prompt_capture_hash_v1(capture)
    assert status["provider"] == "macos-keychain"
    assert status["device_approval_mode"] == "local_user_presence"
    assert status["prompt_reference"] == "os-prompt:wallet-a:epoch-13"
    assert status["capture_source"] == "operator-audit-log"
    assert status["capture_evidence_hash"] == "0x" + "ab" * 32


def test_perps_wallet_signer_prompt_capture_blocks_reference_mismatch() -> None:
    status = evaluate_perps_wallet_signer_prompt_capture_v1(
        _perps_wallet_authority_profile(),
        _perps_wallet_signer_prompt_capture(prompt_reference="os-prompt:wallet-a:epoch-14"),
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["signer_prompt_capture_ready"] is False
    assert "signer prompt capture prompt_reference does not match approval_reference" in status["errors"]


def test_perps_wallet_signer_prompt_capture_blocks_bad_hash_shape() -> None:
    capture = _perps_wallet_signer_prompt_capture()
    capture["prompt_message_hash"] = "not-a-hash"
    status = evaluate_perps_wallet_signer_prompt_capture_v1(
        _perps_wallet_authority_profile(),
        capture,
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["signer_prompt_capture_ready"] is False
    assert any("prompt_message_hash" in error for error in status["errors"])


def test_perps_wallet_signer_execution_exercise_ready_receipt() -> None:
    profile = _perps_wallet_authority_profile()
    exercise = _perps_wallet_signer_execution_exercise()

    status = evaluate_perps_wallet_signer_execution_exercise_v1(
        profile,
        exercise,
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is True
    assert status["signer_execution_ready"] is True
    assert status["status"] == "ready"
    assert status["wallet_authority_hash"] == profile["wallet_authority_hash"]
    assert status["exercise_hash"] == perps_wallet_signer_execution_exercise_hash_v1(exercise)
    assert status["provider"] == "macos-keychain"
    assert status["device_approval_mode"] == "local_user_presence"
    assert status["prompt_reference"] == "os-prompt:wallet-a:epoch-13"
    assert status["execution_reference"] == "tau-submit:wallet-a:epoch-13"
    assert status["signed_payload_hash"] == _perps_wallet_signer_payload_hash()
    assert status["sign_admission_receipt"]["ok"] is True
    assert status["sign_admission_receipt"]["payload_nonce"] == 15
    assert status["sign_admission_receipt_hash"] == status["sign_admission_receipt"]["receipt_hash"]


def test_perps_wallet_signer_execution_builder_rejects_secret_payload_fields() -> None:
    with pytest.raises(ValueError, match="private key material"):
        _perps_wallet_signer_execution_exercise(payload={"private_key_hex": "0x" + "00" * 32, "nonce": 15})


def test_perps_wallet_signer_execution_exercise_blocks_bad_prompt_order() -> None:
    status = evaluate_perps_wallet_signer_execution_exercise_v1(
        _perps_wallet_authority_profile(),
        _perps_wallet_signer_execution_exercise(
            prompt_presented_at_epoch=13,
            prompt_confirmed_at_epoch=12,
        ),
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["signer_execution_ready"] is False
    assert "signer execution prompt confirmation precedes prompt presentation" in status["errors"]


def test_perps_wallet_signer_execution_exercise_blocks_signed_payload_hash_mismatch() -> None:
    status = evaluate_perps_wallet_signer_execution_exercise_v1(
        _perps_wallet_authority_profile(),
        _perps_wallet_signer_execution_exercise(signed_payload_hash="0x" + "cd" * 32),
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["signer_execution_ready"] is False
    assert "signer execution signed_payload_hash mismatch" in status["errors"]


def test_perps_wallet_signer_ceremony_ready_receipt() -> None:
    profile = _perps_wallet_authority_profile()
    device_approval_status = evaluate_perps_wallet_device_approval_exercise_v1(
        profile,
        _perps_wallet_device_approval_exercise(),
        expected_chain_id=CHAIN_ID,
    )
    signer_device_status = evaluate_perps_wallet_signer_device_integration_v1(
        profile,
        _perps_wallet_signer_device_integration(),
        expected_chain_id=CHAIN_ID,
    )
    signer_prompt_capture_status = evaluate_perps_wallet_signer_prompt_capture_v1(
        profile,
        _perps_wallet_signer_prompt_capture(),
        expected_chain_id=CHAIN_ID,
    )
    signer_execution_status = evaluate_perps_wallet_signer_execution_exercise_v1(
        profile,
        _perps_wallet_signer_execution_exercise(),
        expected_chain_id=CHAIN_ID,
    )

    status = evaluate_perps_wallet_signer_ceremony_v1(
        wallet_authority_hash=profile["wallet_authority_hash"],
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
    )

    assert status["ok"] is True
    assert status["signer_ceremony_ready"] is True
    assert status["status"] == "ready"
    assert status["approval_reference"] == "os-prompt:wallet-a:epoch-13"
    assert status["execution_reference"] == "tau-submit:wallet-a:epoch-13"
    assert status["device_approval_status_hash"] == device_approval_status["status_hash"]
    assert status["signer_execution_status_hash"] == signer_execution_status["status_hash"]


def test_perps_wallet_signer_ceremony_blocks_execution_prompt_mismatch() -> None:
    profile = _perps_wallet_authority_profile()
    device_approval_status = evaluate_perps_wallet_device_approval_exercise_v1(
        profile,
        _perps_wallet_device_approval_exercise(),
        expected_chain_id=CHAIN_ID,
    )
    signer_device_status = evaluate_perps_wallet_signer_device_integration_v1(
        profile,
        _perps_wallet_signer_device_integration(),
        expected_chain_id=CHAIN_ID,
    )
    signer_prompt_capture_status = evaluate_perps_wallet_signer_prompt_capture_v1(
        profile,
        _perps_wallet_signer_prompt_capture(),
        expected_chain_id=CHAIN_ID,
    )
    signer_execution_status = evaluate_perps_wallet_signer_execution_exercise_v1(
        profile,
        _perps_wallet_signer_execution_exercise(prompt_reference="os-prompt:wallet-a:epoch-14"),
        expected_chain_id=CHAIN_ID,
    )

    status = evaluate_perps_wallet_signer_ceremony_v1(
        wallet_authority_hash=profile["wallet_authority_hash"],
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
    )

    assert status["ok"] is False
    assert status["signer_ceremony_ready"] is False
    assert "signer ceremony prompt_reference mismatch" in status["errors"]


def test_perps_wallet_signer_ceremony_blocks_prompt_payload_hash_mismatch() -> None:
    profile = _perps_wallet_authority_profile()
    device_approval_status = evaluate_perps_wallet_device_approval_exercise_v1(
        profile,
        _perps_wallet_device_approval_exercise(),
        expected_chain_id=CHAIN_ID,
    )
    signer_device_status = evaluate_perps_wallet_signer_device_integration_v1(
        profile,
        _perps_wallet_signer_device_integration(),
        expected_chain_id=CHAIN_ID,
    )
    signer_prompt_capture_status = evaluate_perps_wallet_signer_prompt_capture_v1(
        profile,
        _perps_wallet_signer_prompt_capture(prompt_message_hash="0x" + "12" * 32),
        expected_chain_id=CHAIN_ID,
    )
    signer_execution_status = evaluate_perps_wallet_signer_execution_exercise_v1(
        profile,
        _perps_wallet_signer_execution_exercise(),
        expected_chain_id=CHAIN_ID,
    )

    status = evaluate_perps_wallet_signer_ceremony_v1(
        wallet_authority_hash=profile["wallet_authority_hash"],
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
    )

    assert signer_prompt_capture_status["signer_prompt_capture_ready"] is True
    assert signer_execution_status["signer_execution_ready"] is True
    assert status["ok"] is False
    assert status["signer_ceremony_ready"] is False
    assert "signer ceremony prompt_message_hash mismatch" in status["errors"]


def test_perps_wallet_hardware_custody_ready_receipt() -> None:
    profile = _perps_wallet_authority_profile()
    device_approval_status = evaluate_perps_wallet_device_approval_exercise_v1(
        profile,
        _perps_wallet_device_approval_exercise_hardware(),
        expected_chain_id=CHAIN_ID,
    )
    signer_device_status = evaluate_perps_wallet_signer_device_integration_v1(
        profile,
        _perps_wallet_signer_device_integration_hardware(),
        expected_chain_id=CHAIN_ID,
    )
    signer_prompt_capture_status = evaluate_perps_wallet_signer_prompt_capture_v1(
        profile,
        _perps_wallet_signer_prompt_capture_hardware(),
        expected_chain_id=CHAIN_ID,
    )
    signer_execution_status = evaluate_perps_wallet_signer_execution_exercise_v1(
        profile,
        _perps_wallet_signer_execution_exercise_hardware(),
        expected_chain_id=CHAIN_ID,
    )
    signer_ceremony_status = evaluate_perps_wallet_signer_ceremony_v1(
        wallet_authority_hash=profile["wallet_authority_hash"],
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
    )

    status = evaluate_perps_wallet_hardware_custody_v1(
        wallet_authority_hash=profile["wallet_authority_hash"],
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
        signer_ceremony_status=signer_ceremony_status,
    )

    assert status["ok"] is True
    assert status["hardware_custody_ready"] is True
    assert status["status"] == "ready"
    assert status["backend_kind"] == BACKEND_HARDWARE_WALLET_PLACEHOLDER
    assert status["environment_kind"] == KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE
    assert status["execution_reference"] == "tau-submit:wallet-a:epoch-13"
    assert status["signer_ceremony_status_hash"] == signer_ceremony_status["status_hash"]


def test_perps_wallet_hardware_custody_requires_bound_production_evidence_for_production_ready() -> None:
    profile = _perps_wallet_authority_profile()
    device_approval_status = evaluate_perps_wallet_device_approval_exercise_v1(
        profile,
        _perps_wallet_device_approval_exercise_live_hardware(),
        expected_chain_id=CHAIN_ID,
    )
    signer_device_status = evaluate_perps_wallet_signer_device_integration_v1(
        profile,
        _perps_wallet_signer_device_integration_live_hardware(),
        expected_chain_id=CHAIN_ID,
    )
    signer_prompt_capture_status = evaluate_perps_wallet_signer_prompt_capture_v1(
        profile,
        _perps_wallet_signer_prompt_capture_live_hardware(),
        expected_chain_id=CHAIN_ID,
    )
    signer_execution_status = evaluate_perps_wallet_signer_execution_exercise_v1(
        profile,
        _perps_wallet_signer_execution_exercise_live_hardware(),
        expected_chain_id=CHAIN_ID,
    )
    signer_ceremony_status = evaluate_perps_wallet_signer_ceremony_v1(
        wallet_authority_hash=profile["wallet_authority_hash"],
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
    )
    production_status = evaluate_production_hardware_wallet_evidence_v1(
        _perps_wallet_production_hardware_evidence(str(profile["wallet_authority_hash"])),
        wallet_authority_profile_hash=str(profile["wallet_authority_hash"]),
        expected_device_pubkey=_perps_wallet_production_device_pubkey(),
        now=1_700_000_050,
    )

    status = evaluate_perps_wallet_hardware_custody_v1(
        wallet_authority_hash=profile["wallet_authority_hash"],
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
        signer_ceremony_status=signer_ceremony_status,
        production_hardware_evidence_status=production_status,
    )

    assert status["hardware_custody_ready"] is True
    assert status["production_hardware_evidence_ready"] is True
    assert status["production_hardware_custody_ready"] is True
    assert status["production_hardware_evidence_hash"] == production_status["evidence_hash"]


def test_perps_wallet_fixture_hardware_custody_cannot_become_production_ready() -> None:
    profile = _perps_wallet_authority_profile()
    device_approval_status = evaluate_perps_wallet_device_approval_exercise_v1(
        profile,
        _perps_wallet_device_approval_exercise_hardware(),
        expected_chain_id=CHAIN_ID,
    )
    signer_device_status = evaluate_perps_wallet_signer_device_integration_v1(
        profile,
        _perps_wallet_signer_device_integration_hardware(),
        expected_chain_id=CHAIN_ID,
    )
    signer_prompt_capture_status = evaluate_perps_wallet_signer_prompt_capture_v1(
        profile,
        _perps_wallet_signer_prompt_capture_hardware(),
        expected_chain_id=CHAIN_ID,
    )
    signer_execution_status = evaluate_perps_wallet_signer_execution_exercise_v1(
        profile,
        _perps_wallet_signer_execution_exercise_hardware(),
        expected_chain_id=CHAIN_ID,
    )
    signer_ceremony_status = evaluate_perps_wallet_signer_ceremony_v1(
        wallet_authority_hash=profile["wallet_authority_hash"],
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
    )
    production_status = evaluate_production_hardware_wallet_evidence_v1(
        _perps_wallet_production_hardware_evidence(str(profile["wallet_authority_hash"])),
        wallet_authority_profile_hash=str(profile["wallet_authority_hash"]),
        expected_device_pubkey=_perps_wallet_production_device_pubkey(),
        now=1_700_000_050,
    )

    status = evaluate_perps_wallet_hardware_custody_v1(
        wallet_authority_hash=profile["wallet_authority_hash"],
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
        signer_ceremony_status=signer_ceremony_status,
        production_hardware_evidence_status=production_status,
    )

    assert status["hardware_custody_ready"] is True
    assert status["production_hardware_evidence_ready"] is True
    assert status["production_hardware_custody_ready"] is False
    assert status["custody_evidence_mode"] == "local_fixture"


def test_perps_wallet_hardware_custody_blocks_os_keychain_backend() -> None:
    profile = _perps_wallet_authority_profile()
    device_approval_status = evaluate_perps_wallet_device_approval_exercise_v1(
        profile,
        _perps_wallet_device_approval_exercise(),
        expected_chain_id=CHAIN_ID,
    )
    signer_device_status = evaluate_perps_wallet_signer_device_integration_v1(
        profile,
        _perps_wallet_signer_device_integration(),
        expected_chain_id=CHAIN_ID,
    )
    signer_prompt_capture_status = evaluate_perps_wallet_signer_prompt_capture_v1(
        profile,
        _perps_wallet_signer_prompt_capture(),
        expected_chain_id=CHAIN_ID,
    )
    signer_execution_status = evaluate_perps_wallet_signer_execution_exercise_v1(
        profile,
        _perps_wallet_signer_execution_exercise(),
        expected_chain_id=CHAIN_ID,
    )
    signer_ceremony_status = evaluate_perps_wallet_signer_ceremony_v1(
        wallet_authority_hash=profile["wallet_authority_hash"],
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
    )

    status = evaluate_perps_wallet_hardware_custody_v1(
        wallet_authority_hash=profile["wallet_authority_hash"],
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
        signer_ceremony_status=signer_ceremony_status,
    )

    assert status["ok"] is False
    assert status["hardware_custody_ready"] is False
    assert "hardware custody backend_kind is not hardware-backed" in status["errors"]


def test_perps_wallet_rotation_exercise_ready_receipt() -> None:
    profile = _perps_wallet_authority_profile()
    exercise = _perps_wallet_rotation_exercise()

    status = evaluate_perps_wallet_rotation_exercise_v1(profile, exercise, expected_chain_id=CHAIN_ID)

    assert status["ok"] is True
    assert status["rotation_exercise_ready"] is True
    assert status["status"] == "ready"
    assert status["errors"] == []
    assert status["wallet_authority_hash"] == profile["wallet_authority_hash"]
    assert status["exercise_hash"] == perps_wallet_rotation_exercise_hash_v1(exercise)
    assert status["rotated_key_id"] == "perps-wallet-a"
    assert status["replacement_key_id"] == "perps-wallet-c"
    assert status["next_wallet_authority_hash"] == exercise["next_wallet_authority_profile"]["wallet_authority_hash"]
    assert status["evaluation"]["ok"] is True
    assert status["evaluation"]["accepted_weight"] == 2
    assert status["guardian_signature_quorum"]["accepted_weight"] == 2
    assert status["guardian_signature_quorum"]["threshold"] == 2
    assert status["guardian_signature_quorum_hash"] == status["guardian_signature_quorum"]["quorum_report_hash"]


def test_perps_wallet_rotation_exercise_blocks_missing_rotation_transition() -> None:
    status = evaluate_perps_wallet_rotation_exercise_v1(
        _perps_wallet_authority_profile(),
        _perps_wallet_rotation_exercise(replacement_key_id="perps-wallet-b"),
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["rotation_exercise_ready"] is False
    assert status["status"] == "blocked"
    assert "replacement key is already active in current wallet authority" in status["errors"]


def test_perps_wallet_rotation_exercise_blocks_bad_guardian_signature_quorum() -> None:
    exercise = _perps_wallet_rotation_exercise()
    exercise["signature_envelopes"] = list(exercise["signature_envelopes"])  # type: ignore[index]
    exercise["signature_envelopes"][0] = {  # type: ignore[index]
        **exercise["signature_envelopes"][0],  # type: ignore[index]
        "payload_hash": "0x" + "00" * 32,
    }

    status = evaluate_perps_wallet_rotation_exercise_v1(
        _perps_wallet_authority_profile(),
        exercise,
        expected_chain_id=CHAIN_ID,
    )

    assert status["ok"] is False
    assert status["rotation_exercise_ready"] is False
    assert any("guardian signature quorum invalid" in error for error in status["errors"])


def test_external_signer_completes_init_market_2p_and_preflights(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 0}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_ALLOW_ISOLATED_PERPS", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)
    monkeypatch.setattr(_FakeClient, "sendtx", lambda self, payload: "SUCCESS tx accepted")

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["stream_key"] == "8"
    assert payload["transport"]["tx_sender_pubkey"] == ALICE
    assert payload["transport"]["tx_sequence_number"] == 9
    assert payload["transport"]["tx_fee_limit"] == "0"
    assert payload["transport"]["fee_limit_native_balance_ok"] is True
    assert payload["report"]["operations"]["8"][0]["action"] == "init_market_2p"
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["proof"]["profile"]["profile_id"] == "perps_stream8_live_wallet_v0"
    assert payload["proof"]["profile"]["zk_proof_verified"] is False
    assert "risc0_zkvm_wrapper" in payload["proof"]["profile"]["not_covered"]
    receipt = payload["proof"]["intent_receipt"]
    assert receipt["profile_id"] == "perps_stream8_live_wallet_v0"
    assert receipt["receipt_hash"].startswith("0x")
    assert receipt["body"]["stream_key"] == "8"
    assert receipt["body"]["engine_stream_key"] == "5"
    assert receipt["body"]["app_hash_before"] == "sha256:" + "cd" * 32
    assert receipt["body"]["app_hash_after"] is None
    assert receipt["body"]["action"] == "init_market_2p"
    assert receipt["body"]["preflight_ok"] is True
    assert receipt["body"]["tau_tx_payload_hash"] is None
    assert receipt["body"]["zk_proof_verified"] is False
    assert payload["proof"]["zk_wrapper"]["required"] is False
    assert payload["proof"]["zk_wrapper"]["proof_provided"] is False
    assert payload["proof"]["zk_wrapper"]["zk_proof_verified"] is False


def test_prepare_init_market_requires_zk_proof_when_enabled(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(_live_proof_ok_cmd("perps_stream8")),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["error"] == "zk_proof_required: zk_proof missing"


def test_prepare_init_market_accepts_verified_zk_wrapper(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(_live_proof_ok_cmd("perps_stream8")),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
        "zk_proof": {"system": "test-zk", "proof_bytes": "fixture"},
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    wrapper = payload["proof"]["zk_wrapper"]
    assert wrapper["surface"] == "perps_stream8"
    assert wrapper["required"] is True
    assert wrapper["proof_provided"] is True
    assert wrapper["verifier_configured"] is True
    assert wrapper["zk_proof_verified"] is True
    assert wrapper["artifact_binding_configured"] is False
    assert wrapper["artifact_binding_complete"] is False
    assert wrapper["proof_intent_receipt_hash"] == payload["proof"]["intent_receipt"]["receipt_hash"]
    assert payload["proof"]["profile"]["zk_proof_verified"] is True
    assert payload["proof"]["profile"]["artifact_binding_complete"] is False
    assert payload["proof"]["profile"]["promotion_ready"] is False


def test_prepare_init_market_accepts_artifact_bound_zk_wrapper(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(_live_proof_ok_cmd("perps_stream8")),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_ARTIFACT_JSON",
        json.dumps(
            {
                "artifact_id": "perps-proof-verifier-v1",
                "artifact_hash": "sha256:" + "11" * 32,
                "build_ref": "tools/proof_verifiers/perps_stream8_v1.py",
            }
        ),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_CIRCUIT_ARTIFACT_JSON",
        json.dumps(
            {
                "artifact_id": "perps-stream8-circuit-v1",
                "artifact_hash": "sha256:" + "22" * 32,
                "proof_system": "test-zk",
            }
        ),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
        "zk_proof": {"system": "test-zk", "proof_bytes": "fixture"},
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    wrapper = payload["proof"]["zk_wrapper"]
    assert wrapper["zk_proof_verified"] is True
    assert wrapper["artifact_binding_configured"] is True
    assert wrapper["artifact_binding_complete"] is True
    assert wrapper["artifact_binding"]["binding_hash"].startswith("0x")
    assert wrapper["artifact_binding"]["verifier_artifact_ready"] is True
    assert wrapper["artifact_binding"]["circuit_artifact_ready"] is True
    assert wrapper["artifact_binding"]["verifier_cmd_hash"].startswith("0x")
    assert payload["proof"]["profile"]["artifact_binding_complete"] is True
    assert payload["proof"]["profile"]["promotion_ready"] is False


def test_submit_deposit_collateral_rejected_zk_proof_blocks_sendtx(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(
            [
                sys.executable,
                "-c",
                "import json,sys; json.load(sys.stdin); print('{\"ok\": false, \"error\": \"fixture proof rejected\"}')",
            ]
        ),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def fail_sendtx(self, payload):  # pragma: no cover - this is a disaster-state sentinel.
        raise AssertionError("zk_reject_broadcasts_tx")

    monkeypatch.setattr(_FakeClient, "sendtx", fail_sendtx)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
        "zk_proof": {"system": "test-zk", "proof_bytes": "bad-fixture"},
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["error"] == "zk_proof_required: fixture proof rejected"
    assert _FakeClient.sent == []


def test_submit_required_zk_proof_rejects_stale_external_signature(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(_live_proof_ok_cmd("perps_stream8")),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def stale_sequence_sendtx(self, payload):
        self.sent.append(dict(payload))
        return "FAILURE: Invalid sequence number: expected 10, got 9."

    monkeypatch.setattr(_FakeClient, "sendtx", stale_sequence_sendtx)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
        "tx_fee_limit": "2",
        "zk_proof": {"system": "test-zk", "proof_bytes": "fixture"},
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["status"] == "submit_rejected"
    assert payload["error"] == "sendtx_failed"
    assert payload["submission"]["sendtx_response"] == "FAILURE: Invalid sequence number: expected 10, got 9."
    assert len(_FakeClient.sent) == 1


def test_prepare_reports_tau_fee_limit_native_balance_posture(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 1}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)
    monkeypatch.setattr(_FakeClient, "sendtx", lambda self, payload: "SUCCESS tx accepted")

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["tx_fee_limit"] == "2"
    assert payload["transport"]["native_balance_e8"] == 1
    assert payload["transport"]["fee_limit_native_balance_ok"] is False
    assert payload["transport"]["fee_limit_warning"] == "native balance is below requested Tau fee limit"
    assert payload["report"]["fee_limit"]["native_balance_covers_fee_limit"] is False


def test_prepare_rejects_bad_tx_fee_limit(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "tx_fee_limit": "1.5",
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "bad_tx_fee_limit"}


def test_prepare_rejects_bad_counterparty_signature_in_preflight(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    good = _signed_init_op(quote_asset=quote_asset)
    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "nonce_a": 1,
        "nonce_b": 1,
        "sig_a": good["sig_a"],
        "sig_b": "0x" + "00" * 96,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is False
    assert "account_b signature invalid" in payload["report"]["preflight"]["error"]


def test_submit_deposit_collateral_uses_sender_bound_account_and_stream_8(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_ALLOW_ISOLATED_PERPS", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def hashed_getappstate(self, *, full: bool = False) -> str:
        assert full is True
        app_hash = hash_v0("test_perps_wallet_app_state", self.app_state)
        return json.dumps({"app_hash": "sha256:" + app_hash[2:], "app_state": self.app_state}, sort_keys=True)

    def applied_sendtx(self, payload):
        _fake_client_apply_stream8_payload(self, payload)
        return "SUCCESS tx accepted"

    monkeypatch.setattr(_FakeClient, "getappstate", hashed_getappstate)
    monkeypatch.setattr(_FakeClient, "sendtx", applied_sendtx)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["account_pubkey"] == ALICE
    assert payload["transport"]["fee_limit_native_balance_ok"] is True
    assert payload["transport"]["quote_balance"] == 5_000
    _assert_redacted_tau_tx_payload(payload["report"]["tau_tx_payload"], _FakeClient.sent[0])
    assert _FakeClient.sent[0]["fee_limit"] == "2"
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"


def test_submit_deposit_insurance_uses_isolated_market_and_sender_balance(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    state = _state_with_isolated_liquidatable_account(quote_asset=quote_asset)
    state = _with_balances(state, (ALICE, quote_asset, 1_000))
    _FakeClient.app_state = _wrapped_app_state(state)
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_ALLOW_ISOLATED_PERPS", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def hashed_getappstate(self, *, full: bool = False) -> str:
        assert full is True
        app_hash = hash_v0("test_perps_wallet_app_state", self.app_state)
        return json.dumps({"app_hash": "sha256:" + app_hash[2:], "app_state": self.app_state}, sort_keys=True)

    monkeypatch.setattr(_FakeClient, "getappstate", hashed_getappstate)
    monkeypatch.setattr(_FakeClient, "sendtx", lambda self, payload: (_fake_client_apply_stream8_payload(self, payload), "SUCCESS tx accepted")[1])

    body = {
        "action": "deposit_insurance",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 123,
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["version"] == "0.1"
    assert payload["report"]["operation"]["action"] == "deposit_insurance"
    assert payload["post_submit"]["state_delta_witness"]["changed_markets"][0]["deltas"] == {
        "insurance_balance": 123,
    }
    post_state = perps_wallet_api._state_from_app_state(_FakeClient.app_state)
    assert post_state.perps is not None
    market = post_state.perps.markets[ISOLATED_MARKET_ID]
    assert isinstance(market, PerpMarketState)
    assert int(market.global_state["initial_insurance"]) == 100_123
    assert int(market.global_state["insurance_balance"]) == 100_123
    assert post_state.balances.get(ALICE, quote_asset) == 877


def test_state_delta_witness_accepts_set_position_pair_target_already_satisfied() -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    operation = {
        "action": "set_position_pair",
        "market_id": MARKET_ID,
        "new_position_base_a": 0,
        "new_position_base_b": 0,
    }

    witness = perps_wallet_api._perps_state_delta_witness(
        chain_id=CHAIN_ID,
        action="set_position_pair",
        operation=operation,
        app_hash_before="sha256:" + "ab" * 32,
        app_hash_after="sha256:" + "cd" * 32,
        app_state_before=app_state,
        app_state_after=app_state,
    )

    assert witness["changed_markets"] == []
    assert witness["target_already_satisfied"]["satisfied"] is True
    assert perps_wallet_api._state_delta_witness_matches_operation(witness, operation) is True


def test_state_delta_witness_tracks_same_price_epoch_publish() -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    before = _apply_perps(
        _apply_perps(
            _state_ready_to_settle(quote_asset=quote_asset),
            [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "settle_epoch"}],
        ),
        [{"module": "TauPerp", "version": "1.0", "market_id": MARKET_ID, "action": "advance_epoch", "delta": 1}],
    )
    after = _apply_perps(before, [_signed_publish_price(price_e8=100_000_000, oracle_nonce=2)], sender=ORACLE)
    operation = {"action": "publish_clearing_price", "market_id": MARKET_ID}

    witness = perps_wallet_api._perps_state_delta_witness(
        chain_id=CHAIN_ID,
        action="publish_clearing_price",
        operation=operation,
        app_hash_before="before",
        app_hash_after="after",
        app_state_before=_wrapped_app_state(before),
        app_state_after=_wrapped_app_state(after),
    )

    assert witness["changed_markets"][0]["market_id"] == MARKET_ID
    assert witness["changed_markets"][0]["deltas"] == {"clearing_price_epoch": 1}
    assert perps_wallet_api._state_delta_witness_matches_operation(witness, operation) is True


def test_submit_rejects_success_without_matching_state_delta(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)
    monkeypatch.setattr(_FakeClient, "sendtx", lambda self, payload: "SUCCESS tx accepted")

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["status"] == "submit_indeterminate"
    assert payload["error"] == "state_delta_witness_missing"
    assert payload["post_submit"]["state_delta_witness"]["changed_markets"] == []


def test_submit_never_calls_createblock_when_send_applies_state(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def hashed_getappstate(self, *, full: bool = False) -> str:
        assert full is True
        app_hash = hash_v0("test_perps_wallet_app_state", self.app_state)
        return json.dumps({"app_hash": "sha256:" + app_hash[2:], "app_state": self.app_state}, sort_keys=True)

    def applied_sendtx(self, payload):
        _fake_client_apply_stream8_payload(self, payload)
        return "SUCCESS tx accepted"

    monkeypatch.setattr(_FakeClient, "getappstate", hashed_getappstate)
    monkeypatch.setattr(_FakeClient, "sendtx", applied_sendtx)
    def forbidden_createblock(self):
        raise AssertionError("wallet API must not produce blocks")

    monkeypatch.setattr(_FakeClient, "createblock", forbidden_createblock)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert "createblock_response" not in payload["submission"]
    assert payload["post_submit"]["app_hash"] != payload["proof"]["intent_receipt"]["body"]["app_hash_before"]


def test_submit_without_app_delta_does_not_resubmit(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    submit_count = {"value": 0}

    def hashed_getappstate(self, *, full: bool = False) -> str:
        assert full is True
        app_hash = hash_v0("test_perps_wallet_app_state", self.app_state)
        return json.dumps({"app_hash": "sha256:" + app_hash[2:], "app_state": self.app_state}, sort_keys=True)

    def sendtx_without_app_delta(self, payload):
        self.sent.append(dict(payload))
        submit_count["value"] += 1
        if submit_count["value"] == 1:
            return "SUCCESS tx accepted"
        return "FAILURE: Invalid sequence number: expected 10, got 9."

    monkeypatch.setattr(_FakeClient, "getappstate", hashed_getappstate)
    monkeypatch.setattr(_FakeClient, "sendtx", sendtx_without_app_delta)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["status"] == "submit_indeterminate"
    assert payload["error"] == "state_delta_witness_missing"
    assert submit_count["value"] == 1
    assert "retry_sendtx_response" not in payload["submission"]


def test_submit_without_app_delta_ignores_stale_sequence_read(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    submit_count = {"value": 0}

    def hashed_getappstate(self, *, full: bool = False) -> str:
        assert full is True
        app_hash = hash_v0("test_perps_wallet_app_state", self.app_state)
        return json.dumps({"app_hash": "sha256:" + app_hash[2:], "app_state": self.app_state}, sort_keys=True)

    def sendtx_without_app_delta(self, payload):
        self.sent.append(dict(payload))
        submit_count["value"] += 1
        if submit_count["value"] == 1:
            return "SUCCESS tx accepted"
        return "FAILURE: Invalid sequence number: expected 10, got 9."

    monkeypatch.setattr(_FakeClient, "getappstate", hashed_getappstate)
    monkeypatch.setattr(_FakeClient, "sendtx", sendtx_without_app_delta)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["status"] == "submit_indeterminate"
    assert payload["error"] == "state_delta_witness_missing"
    assert submit_count["value"] == 1
    assert "retry_sequence_error" not in payload["submission"]


def test_submit_does_not_resign_external_tx_on_initial_stale_sequence(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    send_count = {"value": 0}

    def hashed_getappstate(self, *, full: bool = False) -> str:
        assert full is True
        app_hash = hash_v0("test_perps_wallet_app_state", self.app_state)
        return json.dumps({"app_hash": "sha256:" + app_hash[2:], "app_state": self.app_state}, sort_keys=True)

    def stale_then_applied_sendtx(self, payload):
        send_count["value"] += 1
        if send_count["value"] == 1:
            self.sent.append(dict(payload))
            return "FAILURE: Invalid sequence number: expected 10, got 9."
        _fake_client_apply_stream8_payload(self, payload)
        return "SUCCESS tx accepted"

    monkeypatch.setattr(_FakeClient, "getappstate", hashed_getappstate)
    monkeypatch.setattr(_FakeClient, "sendtx", stale_then_applied_sendtx)
    monkeypatch.setattr(_FakeClient, "createblock", lambda self: "SUCCESS block created")

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["status"] == "submit_rejected"
    assert payload["error"] == "sendtx_failed"
    assert payload["transport"]["tx_sequence_number"] == 9
    assert payload["submission"]["sendtx_response"] == "FAILURE: Invalid sequence number: expected 10, got 9."
    assert "retry_sendtx_response" not in payload["submission"]
    assert send_count["value"] == 1
    assert len(_FakeClient.sent) == 1
    assert _FakeClient.sent[0]["sequence_number"] == 9


def test_perps_wallet_testnet_faucet_route_is_removed() -> None:
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/testnet-faucet",
        json.dumps({}).encode("utf-8"),
    )

    assert status_code == 404
    assert payload == {"ok": False, "error": "not_found"}


@pytest.mark.parametrize(
    "field",
    (
        "account_privkey",
        "account_a_privkey",
        "account_b_privkey",
        "operator_privkey",
        "oracle_privkey",
        "tx_signer_privkey",
        "signer_privkey",
        "private_key",
        "private_key_hex",
        "secret_key",
        "mnemonic",
    ),
)
def test_perps_wallet_rejects_raw_signing_material_before_route_processing(field: str) -> None:
    status_code, payload = _PRODUCTION_HANDLE_PERPS_WALLET_REQUEST(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps({field: "forbidden"}).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": f"raw_signing_material_forbidden:{field}"}


def test_perps_wallet_rejects_nested_raw_signing_material() -> None:
    status_code, payload = _PRODUCTION_HANDLE_PERPS_WALLET_REQUEST(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps({"signer": {"private-key-hex": "forbidden"}}).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {
        "ok": False,
        "error": "raw_signing_material_forbidden:signer.private-key-hex",
    }


def test_perps_wallet_raw_key_boundary_allows_non_secret_policy_claim_names() -> None:
    status_code, payload = _PRODUCTION_HANDLE_PERPS_WALLET_REQUEST(
        "POST",
        "/api/perps/wallet/not-a-route",
        json.dumps({"no_raw_private_key_exposure": True}).encode("utf-8"),
    )

    assert status_code == 404
    assert payload == {"ok": False, "error": "not_found"}


def test_perps_wallet_prepare_returns_unsigned_operation_for_external_signer(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.native_balances = {ALICE[2:]: 10}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(
            {
                "action": "init_market_2p",
                "market_id": MARKET_ID,
                "quote_asset": quote_asset,
                "account_a_pubkey": ALICE,
                "account_b_pubkey": BOB,
                "deadline": FUTURE_DEADLINE,
            }
        ).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert "allow_local_signing" not in payload["transport"]
    assert payload["transport"]["signing_mode"] == "prepare_only"
    assert payload["transport"]["tx_expiration_time"] == FUTURE_DEADLINE
    assert payload["report"]["tau_tx_payload"] is None
    assert payload["report"]["operation"]["sig_a"] == ""
    assert payload["report"]["operation"]["sig_b"] == ""
    assert payload["report"]["preflight"]["ok"] is False


def test_submit_deposit_collateral_rejects_failed_sendtx(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def rejected_sendtx(self, payload):
        self.sent.append(dict(payload))
        return "REJECTED invalid signature"

    monkeypatch.setattr(_FakeClient, "sendtx", rejected_sendtx)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["status"] == "submit_rejected"
    assert payload["error"] == "sendtx_failed"
    assert payload["submission"]["sendtx_response"] == "REJECTED invalid signature"
    assert "post_submit" not in payload


def test_submit_deposit_collateral_rejected_sendtx_clears_promotion_ready(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(_live_proof_ok_cmd("perps_stream8")),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_ARTIFACT_JSON",
        json.dumps(
            {
                "artifact_id": "perps-proof-verifier-v1",
                "artifact_hash": "sha256:" + "11" * 32,
            }
        ),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_CIRCUIT_ARTIFACT_JSON",
        json.dumps(
            {
                "artifact_id": "perps-stream8-circuit-v1",
                "artifact_hash": "sha256:" + "22" * 32,
                "proof_system": "test-zk",
            }
        ),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def rejected_sendtx(self, payload):
        self.sent.append(dict(payload))
        return "REJECTED invalid signature"

    monkeypatch.setattr(_FakeClient, "sendtx", rejected_sendtx)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
        "zk_proof": {"system": "test-zk", "proof_bytes": "fixture"},
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["status"] == "submit_rejected"
    assert payload["error"] == "sendtx_failed"
    wrapper = payload["proof"]["zk_wrapper"]
    assert wrapper["zk_proof_verified"] is True
    assert wrapper["artifact_binding_complete"] is True
    assert payload["proof"]["profile"]["zk_proof_verified"] is True
    assert payload["proof"]["profile"]["artifact_binding_complete"] is True
    assert payload["proof"]["profile"]["promotion_ready"] is False


def test_submit_deposit_collateral_sets_promotion_ready_only_after_post_submit_binding(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(_live_proof_ok_cmd("perps_stream8")),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_ARTIFACT_JSON",
        json.dumps(
            {
                "artifact_id": "perps-proof-verifier-v1",
                "artifact_hash": "sha256:" + "11" * 32,
            }
        ),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_CIRCUIT_ARTIFACT_JSON",
        json.dumps(
            {
                "artifact_id": "perps-stream8-circuit-v1",
                "artifact_hash": "sha256:" + "22" * 32,
                "proof_system": "test-zk",
            }
        ),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def sendtx_and_apply(self, payload):
        _fake_client_apply_stream8_payload(self, payload)
        return "SUCCESS tx accepted"

    monkeypatch.setattr(_FakeClient, "sendtx", sendtx_and_apply)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
        "zk_proof": {"system": "test-zk", "proof_bytes": "fixture"},
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    receipt_body = payload["proof"]["intent_receipt"]["body"]
    assert receipt_body["app_hash_after"] == payload["post_submit"]["app_hash"]
    assert isinstance(receipt_body["state_delta_witness_hash"], str)
    assert payload["proof"]["profile"]["zk_proof_verified"] is True
    assert payload["proof"]["profile"]["artifact_binding_complete"] is True
    assert payload["proof"]["profile"]["promotion_ready"] is True


def test_submit_deposit_collateral_records_required_post_submit_zk_binding_gap(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv(
        "PERPS_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(
            [
                sys.executable,
                "-c",
                (
                    "import json,sys; "
                    "from src.integration.live_proof_wrapper import LIVE_PROOF_WRAPPER_HASH_DOMAIN; "
                    "from src.state.canonical import canonical_json_bytes,domain_sep_bytes,sha256_hex; "
                    "obj=json.load(sys.stdin); "
                    "after=obj['proof_intent_receipt']['body']['app_hash_after']; "
                    "out={'ok': after is None, 'error': None if after is None else 'post_submit_binding_failed'}; "
                    "out['verifier_request_hash']=sha256_hex("
                    "domain_sep_bytes(LIVE_PROOF_WRAPPER_HASH_DOMAIN)+canonical_json_bytes(obj)"
                    "); "
                    "print(json.dumps(out))"
                ),
            ]
        ),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 1000,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
        "zk_proof": {"system": "test-zk", "proof_bytes": "fixture"},
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"
    assert "post_submit" in payload
    wrapper = payload["proof"]["post_submit_zk_wrapper"]
    assert wrapper["required"] is True
    assert wrapper["zk_proof_verified"] is False
    assert wrapper["error"] == "post_submit_binding_failed"
    assert payload["proof"]["post_submit_zk_wrapper_gap"] == "post_submit_binding_failed"
    assert payload["proof"]["profile"]["promotion_ready"] is False


def test_submit_accepts_external_signed_tau_payload_without_local_signing(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def sendtx_and_apply(self, payload):
        _fake_client_apply_stream8_payload(self, payload)
        return "SUCCESS tx accepted"

    monkeypatch.setattr(_FakeClient, "sendtx", sendtx_and_apply)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, prepared = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    assert prepared["ok"] is True
    assert prepared["report"]["tau_tx_payload"] is None

    external_payload = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=FUTURE_DEADLINE,
        operations=prepared["report"]["operations"],
        fee_limit=2,
    )
    submit_body = {**body, "signed_tau_tx_payload": external_payload}
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(submit_body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert "allow_local_signing" not in payload["transport"]
    assert payload["transport"]["signing_mode"] == "external_signed_payload"
    assert payload["report"]["preflight"]["ok"] is True
    _assert_redacted_tau_tx_payload(payload["report"]["tau_tx_payload"], external_payload)
    assert _FakeClient.sent == [external_payload]
    assert external_payload["sender_pubkey"] == ALICE[2:]
    assert json.loads(external_payload["operations"]["8"])[0]["action"] == "deposit_collateral"
    proof_body = payload["proof"]["intent_receipt"]["body"]
    assert proof_body["app_hash_before"] == "sha256:" + "cd" * 32
    assert proof_body["app_hash_after"] == payload["post_submit"]["app_hash"]
    assert proof_body["signing_mode"] == "external_signed_payload"
    assert proof_body["tau_tx_payload_hash"].startswith("0x")
    assert proof_body["state_delta_witness_hash"].startswith("0x")
    witness = payload["proof"]["intent_receipt"]["state_delta_witness"]
    assert witness["schema"] == "zenodex/perps_wallet/state_delta_witness/v1"
    assert witness["stream_key"] == "8"
    assert witness["action"] == "deposit_collateral"
    assert witness["app_hash_before"] == "sha256:" + "cd" * 32
    assert witness["app_hash_after"] == payload["post_submit"]["app_hash"]
    assert len(witness["changed_markets"]) == 1
    assert witness["changed_markets"][0]["market_id"] == MARKET_ID
    assert witness["changed_markets"][0]["deltas"]["collateral_e8_a"] == 1000 * 100_000_000


def test_submit_external_signed_payload_can_retry_after_tau_send_failure_without_state_drift(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    initial_app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.app_state = json.loads(json.dumps(initial_app_state))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    _FakeClient.send_attempts = 0
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def flaky_sendtx(self, payload):
        type(self).send_attempts += 1
        if type(self).send_attempts == 1:
            raise TauNetRpcError("temporary tau node send failure")
        _fake_client_apply_stream8_payload(self, payload)
        return "SUCCESS tx accepted after retry"

    monkeypatch.setattr(_FakeClient, "sendtx", flaky_sendtx)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, prepared = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    external_payload = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=FUTURE_DEADLINE,
        operations=prepared["report"]["operations"],
        fee_limit=2,
    )
    submit_body = {**body, "signed_tau_tx_payload": external_payload}

    status_code, failed = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(submit_body).encode("utf-8"),
    )
    assert status_code == 502
    assert failed["ok"] is False
    assert failed["error"] == "tau_rpc_error"
    assert "temporary tau node send failure" in failed["detail"]
    assert _FakeClient.sent == []
    assert _FakeClient.app_state == initial_app_state

    status_code, accepted = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(submit_body).encode("utf-8"),
    )
    assert status_code == 200
    assert accepted["ok"] is True
    assert accepted["submission"]["sendtx_response"] == "SUCCESS tx accepted after retry"
    assert accepted["transport"]["signing_mode"] == "external_signed_payload"
    assert _FakeClient.sent == [external_payload]
    witness = accepted["proof"]["intent_receipt"]["state_delta_witness"]
    assert witness["changed_markets"][0]["deltas"]["collateral_e8_a"] == 1000 * 100_000_000


def test_submit_external_signed_payload_replay_after_node_restart_rejected_before_sendtx(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    _FakeClient.native_balances = {ALICE[2:]: 5}
    _FakeClient.sequence_by_sender = {ALICE[2:]: 9}
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    def sequence_from_persisted_node(self, sender_pubkey_hex: str) -> int:
        return int(type(self).sequence_by_sender.get(sender_pubkey_hex, 0))

    def sendtx_apply_and_advance(self, payload):
        _fake_client_apply_stream8_payload(self, payload)
        sender = str(payload["sender_pubkey"])
        type(self).sequence_by_sender[sender] = int(type(self).sequence_by_sender.get(sender, 0)) + 1
        type(self).app_state = json.loads(json.dumps(self.app_state))
        return "SUCCESS tx accepted before restart"

    monkeypatch.setattr(_FakeClient, "get_sequence", sequence_from_persisted_node)
    monkeypatch.setattr(_FakeClient, "sendtx", sendtx_apply_and_advance)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, prepared = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    assert prepared["transport"]["tx_sequence_number"] == 9
    external_payload = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=FUTURE_DEADLINE,
        operations=prepared["report"]["operations"],
        fee_limit=2,
    )
    submit_body = {**body, "signed_tau_tx_payload": external_payload}

    status_code, accepted = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(submit_body).encode("utf-8"),
    )
    assert status_code == 200
    assert accepted["ok"] is True
    assert accepted["submission"]["sendtx_response"] == "SUCCESS tx accepted before restart"
    assert len(_FakeClient.sent) == 1
    assert _FakeClient.sequence_by_sender[ALICE[2:]] == 10
    persisted_after_submit = json.loads(json.dumps(_FakeClient.app_state))

    class _RestartedFakeClient(_FakeClient):
        app_state = persisted_after_submit
        sent = _FakeClient.sent
        native_balances = _FakeClient.native_balances
        sequence_by_sender = dict(_FakeClient.sequence_by_sender)

    def restarted_sequence(self, sender_pubkey_hex: str) -> int:
        return int(type(self).sequence_by_sender.get(sender_pubkey_hex, 0))

    def restarted_sendtx(self, payload):
        raise AssertionError("replay should be rejected before sendtx after restart")

    monkeypatch.setattr(_RestartedFakeClient, "get_sequence", restarted_sequence)
    monkeypatch.setattr(_RestartedFakeClient, "sendtx", restarted_sendtx)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _RestartedFakeClient)

    status_code, replay = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(submit_body).encode("utf-8"),
    )

    assert status_code == 400
    assert replay == {"ok": False, "error": "signed_tau_tx_payload sequence mismatch"}
    assert _RestartedFakeClient.sent == [external_payload]
    assert _RestartedFakeClient.app_state == persisted_after_submit


def test_submit_rejects_external_signed_tau_payload_operation_mismatch(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "deposit_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "amount": 1000,
        "tx_fee_limit": "2",
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, prepared = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    wrong_operations = json.loads(json.dumps(prepared["report"]["operations"]))
    wrong_operations["8"][0]["amount"] = 999
    external_payload = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=FUTURE_DEADLINE,
        operations=wrong_operations,
        fee_limit=2,
    )

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps({**body, "signed_tau_tx_payload": external_payload}).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "signed_tau_tx_payload operations mismatch"}
    assert _FakeClient.sent == []


def test_submit_withdraw_collateral_uses_sender_bound_account_and_stream_8(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_posted_collateral(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "withdraw_collateral",
        "market_id": MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "amount": 100,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["action"] == "withdraw_collateral"
    _assert_redacted_tau_tx_payload(payload["report"]["tau_tx_payload"], _FakeClient.sent[0])
    assert _FakeClient.sent[0]["sender_pubkey"] == ALICE[2:]


def test_external_oracle_signer_completes_publish_price_prepare(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_advanced_market(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_PERP_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "publish_clearing_price",
        "market_id": MARKET_ID,
        "oracle_privkey": str(ORACLE_PRIVKEY),
        "price_e8": 100_000_000,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["tx_sender_pubkey"] == ORACLE
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["oracle_nonce"] == 1
    assert payload["report"]["operation"]["oracle_sig"].startswith("0x")


def test_submit_advance_epoch_uses_operator_signer(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_market_and_balance(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "advance_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "delta": 1,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["operation"]["action"] == "advance_epoch"
    _assert_redacted_tau_tx_payload(payload["report"]["tau_tx_payload"], _FakeClient.sent[0])
    assert _FakeClient.sent[0]["sender_pubkey"] == OPERATOR[2:]


def test_prepare_settle_epoch_can_fail_closed_on_missing_oracle_bridge(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_advanced_market(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "settle_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is False
    assert payload["report"]["preflight"]["error"] == "settle_epoch requires oracle_adapter_bridge"


def test_synthetic_oracle_bridge_template_route_is_removed() -> None:
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge-template",
        json.dumps({"action": "settle_epoch", "market_id": MARKET_ID}).encode("utf-8"),
    )

    assert status_code == 404
    assert payload == {"ok": False, "error": "not_found"}


def test_caller_supplied_oracle_bridge_preflights_required_settle_epoch(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_ready_to_settle(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    bridge_payload = _test_oracle_bridge_fixture(
        action="settle_epoch",
        market_id=MARKET_ID,
    )

    assert bridge_payload["ok"] is True
    assert bridge_payload["fixture_kind"] == "test_only_o3_aggregate_adapter"
    assert bridge_payload["production_authority"] is False
    assert bridge_payload["verify_result"]["status"] == "accepted"
    assert bridge_payload["target"]["consumer_module"] == "zenodex.perps"
    assert bridge_payload["target"]["action_kind"] == "settle_epoch"

    body = {
        "action": "settle_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "oracle_adapter_bridge": bridge_payload["bridge"],
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["oracle_adapter_bridge"]["bridge_id"] == bridge_payload["bridge"]["bridge_id"]


def test_submit_settle_epoch_binds_ready_oracle_authority_exercise(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_ready_to_settle(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.setenv(
        "PERPS_ORACLE_AUTHORITY_PROFILE_JSON",
        json.dumps(_oracle_authority_profile(), sort_keys=True),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    bridge_payload = _test_oracle_bridge_fixture(
        action="settle_epoch",
        market_id=MARKET_ID,
    )

    body = {
        "action": "settle_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "oracle_adapter_bridge": bridge_payload["bridge"],
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"
    exercise = payload["proof"]["oracle_authority_exercise"]
    assert exercise["schema"] == "zenodex/perps_wallet/oracle_authority_exercise/v1"
    assert exercise["authority_exercised"] is True
    assert exercise["production_authority"] is True
    assert exercise["status"] == "exercised"
    assert exercise["readiness_gaps"] == []
    assert exercise["authority_hash"] == _oracle_authority_profile()["authority_hash"]
    assert exercise["signature_quorum_accepted_weight"] == 2
    assert exercise["signature_quorum_threshold"] == 2
    assert exercise["oracle_adapter_bridge_id"] == bridge_payload["bridge"]["bridge_id"]
    assert str(exercise["oracle_adapter_bridge_hash"]).startswith("0x")
    receipt = payload["proof"]["intent_receipt"]
    assert receipt["body"]["oracle_authority_exercised"] is True
    assert receipt["body"]["oracle_authority_exercise_hash"] == exercise["exercise_hash"]
    assert receipt["oracle_authority_exercise"]["exercise_hash"] == exercise["exercise_hash"]


def test_submit_settle_epoch_requires_ready_oracle_authority_when_enabled(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_ready_to_settle(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_PRODUCTION_ORACLE_AUTHORITY", "1")
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.delenv("PERPS_ORACLE_AUTHORITY_PROFILE_JSON", raising=False)
    monkeypatch.delenv("PERPS_ORACLE_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    bridge_payload = _test_oracle_bridge_fixture(
        action="settle_epoch",
        market_id=MARKET_ID,
    )

    body = {
        "action": "settle_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "oracle_adapter_bridge": bridge_payload["bridge"],
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert "production_oracle_authority_required" in payload["error"]
    assert "oracle production authority profile is missing" in payload["error"]
    assert _FakeClient.sent == []


def test_submit_settle_epoch_requires_ready_oracle_authority_by_default_on_public_chain(monkeypatch) -> None:
    public_chain_id = "zenodex-public-testnet-v0"
    quote_asset = derive_zusd_tau_asset_id(chain_id=public_chain_id)
    _FakeClient.app_state = _wrapped_app_state(_state_ready_to_settle(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", public_chain_id)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.delenv("PERPS_WALLET_REQUIRE_PRODUCTION_ORACLE_AUTHORITY", raising=False)
    monkeypatch.delenv("PERPS_ORACLE_AUTHORITY_PROFILE_JSON", raising=False)
    monkeypatch.delenv("PERPS_ORACLE_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    bridge_payload = _test_oracle_bridge_fixture(
        action="settle_epoch",
        market_id=MARKET_ID,
        chain_id=public_chain_id,
    )

    body = {
        "action": "settle_epoch",
        "market_id": MARKET_ID,
        "operator_privkey": str(OPERATOR_PRIVKEY),
        "oracle_adapter_bridge": bridge_payload["bridge"],
        "chain_id": public_chain_id,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert "production_oracle_authority_required" in payload["error"]
    assert "oracle production authority profile is missing" in payload["error"]
    assert _FakeClient.sent == []


def test_oracle_bridge_inspector_summarizes_verified_settle_bridge(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_ready_to_settle(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    bridge_payload = _test_oracle_bridge_fixture(
        action="settle_epoch",
        market_id=MARKET_ID,
    )

    status_code, inspection = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge/inspect",
        json.dumps({"oracle_adapter_bridge": bridge_payload["bridge"]}).encode("utf-8"),
    )

    assert status_code == 200
    assert inspection["ok"] is True
    assert inspection["status"] == "accepted"
    assert inspection["production_authority"] is False
    summary = inspection["summary"]
    assert summary["bridge_id"] == bridge_payload["bridge"]["bridge_id"]
    assert summary["consumer_module"] == "zenodex.perps"
    assert summary["action_kind"] == "settle_epoch"
    assert summary["query_id"] == bridge_payload["target"]["query_id"]
    assert summary["profile_id"] == bridge_payload["target"]["profile_id"]
    assert summary["required_evidence_floor"] == "O3"
    assert summary["value_e8"] == 100_000_000
    assert summary["report_count"] == 3


def test_oracle_bridge_inspector_rejects_tampered_action_id(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_ready_to_settle(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_OPERATOR_PUBKEY", OPERATOR)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    bridge_payload = _test_oracle_bridge_fixture(
        action="settle_epoch",
        market_id=MARKET_ID,
    )
    tampered = json.loads(json.dumps(bridge_payload["bridge"]))
    tampered["action"]["action_id"] = "sha256:" + "0" * 64

    status_code, inspection = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/oracle-bridge/inspect",
        json.dumps({"oracle_adapter_bridge": tampered}).encode("utf-8"),
    )

    assert status_code == 200
    assert inspection["ok"] is False
    assert inspection["status"] == "rejected"
    assert "adapter:adapter_action_id_mismatch" in inspection["verify_result"]["errors"]


def test_status_exposes_clearinghouse_liquidation_summary_fields(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_JSON", raising=False)
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    for name in (
        "PERPS_ORACLE_AUTHORITY_PROFILE_JSON",
        "PERPS_ORACLE_AUTHORITY_PROFILE_FILE",
        "ZENO_ORACLE_AUTHORITY_PROFILE_JSON",
        "ZENO_ORACLE_AUTHORITY_PROFILE_FILE",
        "ZENO_ORACLE_PRODUCTION_AUTHORITY_PROFILE_FILE",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    assert payload["ok"] is True
    assert "allow_local_signing" not in payload["status"]
    proof_profile = payload["status"]["proof_profile"]
    assert proof_profile["profile_id"] == "perps_stream8_live_wallet_v0"
    assert proof_profile["zk_wrapper_required_for_production_claim"] is True
    assert proof_profile["artifact_binding_required_for_production_claim"] is True
    assert proof_profile["artifact_binding_complete"] is False
    assert proof_profile["promotion_ready"] is False
    assert "does_not_claim_perps_zk_execution" in proof_profile["non_claims"]
    wallet_authority = payload["status"]["wallet_authority"]
    assert payload["status"]["production_wallet_authority"] is False
    assert wallet_authority["status"] == "blocked"
    assert wallet_authority["readiness_gaps"] == ["perps wallet authority profile is missing"]
    oracle_authority = payload["status"]["oracle_authority"]
    assert payload["status"]["production_oracle_authority"] is False
    assert oracle_authority["status"] == "blocked"
    assert oracle_authority["readiness_gaps"] == ["oracle production authority profile is missing"]
    markets = payload["status"]["markets"]
    assert len(markets) == 1
    market = markets[0]
    assert market["market_id"] == MARKET_ID
    assert market["liquidated_this_step"] is True
    assert market["account_a_quote_balance"] == 900
    assert market["account_b_quote_balance"] == 900
    assert market["fee_pool_e8"] == 525_000_000
    assert market["position_base_a"] == 0
    assert market["position_base_b"] == 0
    assert market["net_deposited_e8"] == 20_000_000_000


def test_status_loads_ready_perps_wallet_authority_profile(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["status"]["production_wallet_authority"] is True
    wallet_authority = payload["status"]["wallet_authority"]
    assert wallet_authority["status"] == "ready"
    assert wallet_authority["readiness_gaps"] == []
    assert wallet_authority["key_ref_count"] == 2
    assert wallet_authority["recovery_policy_count"] == 2
    assert wallet_authority["recoverable_active_key_count"] == 2
    assert wallet_authority["active_signer_count"] == 2
    assert wallet_authority["transaction_scope"]["stream_key"] == "8"
    encoded = json.dumps(wallet_authority, sort_keys=True)
    assert "private_key" not in encoded
    assert "secret_hex" not in encoded


def test_status_loads_ready_perps_wallet_recovery_exercise(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_RECOVERY_EXERCISE_JSON",
        json.dumps(_perps_wallet_recovery_exercise(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.delenv("PERPS_WALLET_RECOVERY_EXERCISE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    recovery = payload["status"]["wallet_authority"]["recovery_exercise"]
    assert recovery["recovery_exercise_ready"] is True
    assert recovery["status"] == "ready"
    assert recovery["evaluation"]["accepted_weight"] == 2
    assert recovery["evaluation"]["delay_ok"] is True
    assert recovery["evaluation"]["threshold_ok"] is True
    assert recovery["guardian_signature_quorum"]["accepted_weight"] == 2
    assert recovery["guardian_signature_quorum"]["threshold"] == 2


def test_status_loads_ready_perps_wallet_rotation_exercise(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_ROTATION_EXERCISE_JSON",
        json.dumps(_perps_wallet_rotation_exercise(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.delenv("PERPS_WALLET_ROTATION_EXERCISE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    rotation = payload["status"]["wallet_authority"]["rotation_exercise"]
    assert rotation["rotation_exercise_ready"] is True
    assert rotation["status"] == "ready"
    assert rotation["rotated_key_id"] == "perps-wallet-a"
    assert rotation["replacement_key_id"] == "perps-wallet-c"
    assert rotation["broadcast_reference"] == "tau-tx:perps-wallet-rotation-1"
    assert rotation["guardian_signature_quorum"]["accepted_weight"] == 2
    assert rotation["guardian_signature_quorum"]["threshold"] == 2


def test_status_loads_ready_perps_wallet_device_approval_exercise(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_JSON",
        json.dumps(_perps_wallet_device_approval_exercise(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.delenv("PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    device_approval = payload["status"]["wallet_authority"]["device_approval_exercise"]
    assert device_approval["device_approval_ready"] is True
    assert device_approval["status"] == "ready"
    assert device_approval["sign_admission_receipt"]["ok"] is True
    assert device_approval["sign_admission_receipt"]["payload_nonce"] == 14


def test_status_loads_ready_perps_wallet_signer_device_integration(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_JSON",
        json.dumps(_perps_wallet_signer_device_integration(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.delenv("PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    signer_device = payload["status"]["wallet_authority"]["signer_device_integration"]
    assert signer_device["signer_device_ready"] is True
    assert signer_device["status"] == "ready"
    assert signer_device["backend_kind"] == BACKEND_OS_KEYCHAIN
    assert signer_device["provider"] == "macos-keychain"
    assert signer_device["approval_reference"] == "os-prompt:wallet-a:epoch-13"


def test_status_loads_ready_perps_wallet_signer_prompt_capture(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_SIGNER_PROMPT_CAPTURE_JSON",
        json.dumps(_perps_wallet_signer_prompt_capture(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.delenv("PERPS_WALLET_SIGNER_PROMPT_CAPTURE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    signer_prompt_capture = payload["status"]["wallet_authority"]["signer_prompt_capture"]
    assert signer_prompt_capture["signer_prompt_capture_ready"] is True
    assert signer_prompt_capture["status"] == "ready"
    assert signer_prompt_capture["capture_source"] == "operator-audit-log"
    assert signer_prompt_capture["prompt_reference"] == "os-prompt:wallet-a:epoch-13"


def test_status_loads_ready_perps_wallet_signer_execution_exercise(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_JSON",
        json.dumps(_perps_wallet_device_approval_exercise(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_JSON",
        json.dumps(_perps_wallet_signer_device_integration(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_SIGNER_PROMPT_CAPTURE_JSON",
        json.dumps(_perps_wallet_signer_prompt_capture(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_JSON",
        json.dumps(_perps_wallet_signer_execution_exercise(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.delenv("PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_FILE", raising=False)
    monkeypatch.delenv("PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_FILE", raising=False)
    monkeypatch.delenv("PERPS_WALLET_SIGNER_PROMPT_CAPTURE_FILE", raising=False)
    monkeypatch.delenv("PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    signer_execution = payload["status"]["wallet_authority"]["signer_execution_exercise"]
    assert signer_execution["signer_execution_ready"] is True
    assert signer_execution["status"] == "ready"
    assert signer_execution["prompt_reference"] == "os-prompt:wallet-a:epoch-13"
    assert signer_execution["execution_reference"] == "tau-submit:wallet-a:epoch-13"

    signer_ceremony = payload["status"]["wallet_authority"]["signer_ceremony"]
    assert signer_ceremony["signer_ceremony_ready"] is True
    assert signer_ceremony["status"] == "ready"
    assert signer_ceremony["execution_reference"] == "tau-submit:wallet-a:epoch-13"


def test_status_loads_ready_perps_wallet_hardware_custody(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_JSON",
        json.dumps(_perps_wallet_device_approval_exercise_hardware(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_JSON",
        json.dumps(_perps_wallet_signer_device_integration_hardware(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_SIGNER_PROMPT_CAPTURE_JSON",
        json.dumps(_perps_wallet_signer_prompt_capture_hardware(), sort_keys=True),
    )
    monkeypatch.setenv(
        "PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_JSON",
        json.dumps(_perps_wallet_signer_execution_exercise_hardware(), sort_keys=True),
    )
    for name in (
        "PERPS_WALLET_AUTHORITY_PROFILE_FILE",
        "PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_FILE",
        "PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_FILE",
        "PERPS_WALLET_SIGNER_PROMPT_CAPTURE_FILE",
        "PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_FILE",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    hardware_custody = payload["status"]["wallet_authority"]["hardware_custody"]
    assert hardware_custody["hardware_custody_ready"] is True
    assert hardware_custody["backend_kind"] == BACKEND_HARDWARE_WALLET_PLACEHOLDER
    assert hardware_custody["execution_reference"] == "tau-submit:wallet-a:epoch-13"


def test_recovery_evaluate_endpoint_blocks_threshold_gap(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/recovery/evaluate",
        json.dumps(_perps_wallet_recovery_exercise(approvals=["guardian-oracle"])).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is False
    recovery = payload["recovery_exercise"]
    assert recovery["recovery_exercise_ready"] is False
    assert "recovery_policy_not_satisfied" in recovery["errors"]


def test_recovery_evaluate_endpoint_blocks_bad_guardian_signature_quorum(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    exercise = _perps_wallet_recovery_exercise()
    exercise["signature_envelopes"] = list(exercise["signature_envelopes"])  # type: ignore[index]
    exercise["signature_envelopes"][0] = {  # type: ignore[index]
        **exercise["signature_envelopes"][0],  # type: ignore[index]
        "payload_hash": "0x" + "00" * 32,
    }

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/recovery/evaluate",
        json.dumps(exercise).encode("utf-8"),
    )

    assert status_code == 200
    recovery = payload["recovery_exercise"]
    assert recovery["recovery_exercise_ready"] is False
    assert any("guardian signature quorum invalid" in error for error in recovery["errors"])


def test_rotation_evaluate_endpoint_blocks_bad_broadcast_epoch(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/rotation/evaluate",
        json.dumps(_perps_wallet_rotation_exercise(broadcast_at_epoch=9)).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is False
    rotation = payload["rotation_exercise"]
    assert rotation["rotation_exercise_ready"] is False
    assert "perps wallet rotation exercise broadcast_at_epoch precedes request" in rotation["errors"]


def test_rotation_evaluate_endpoint_blocks_bad_guardian_signature_quorum(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    exercise = _perps_wallet_rotation_exercise()
    exercise["signature_envelopes"] = list(exercise["signature_envelopes"])  # type: ignore[index]
    exercise["signature_envelopes"][0] = {  # type: ignore[index]
        **exercise["signature_envelopes"][0],  # type: ignore[index]
        "payload_hash": "0x" + "00" * 32,
    }

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/rotation/evaluate",
        json.dumps(exercise).encode("utf-8"),
    )

    assert status_code == 200
    rotation = payload["rotation_exercise"]
    assert rotation["rotation_exercise_ready"] is False
    assert any("guardian signature quorum invalid" in error for error in rotation["errors"])


def test_device_approval_evaluate_endpoint_blocks_missing_user_presence(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    exercise = _perps_wallet_device_approval_exercise()
    exercise["environment"] = {
        **exercise["environment"],
        "local_user_presence_confirmed": False,
    }
    exercise["environment"]["environment_hash"] = KeyExecutionEnvironment(
        environment_id=exercise["environment"]["environment_id"],
        environment_kind=exercise["environment"]["environment_kind"],
        chain_id=exercise["environment"]["chain_id"],
        policy_hash=exercise["environment"]["policy_hash"],
        challenge_hash=exercise["environment"]["challenge_hash"],
        issued_at_epoch=exercise["environment"]["issued_at_epoch"],
        expires_at_epoch=exercise["environment"]["expires_at_epoch"],
        local_user_presence_confirmed=False,
        rollback_protection_confirmed=exercise["environment"]["rollback_protection_confirmed"],
    ).public_dict()["environment_hash"]

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/device-approval/evaluate",
        json.dumps(exercise).encode("utf-8"),
    )

    assert status_code == 200
    device_approval = payload["device_approval_exercise"]
    assert device_approval["device_approval_ready"] is False
    assert "local_user_presence_missing" in device_approval["errors"]


def test_device_approval_evaluate_endpoint_blocks_reused_nonce(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/device-approval/evaluate",
        json.dumps(_perps_wallet_device_approval_exercise(seen_nonces=[11, 12, 14])).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is False
    device_approval = payload["device_approval_exercise"]
    assert device_approval["device_approval_ready"] is False
    assert "payload_nonce_reused" in device_approval["errors"]


def test_signer_device_evaluate_endpoint_blocks_missing_user_presence(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    integration = _perps_wallet_signer_device_integration()
    integration["environment"] = {
        **integration["environment"],
        "local_user_presence_confirmed": False,
    }
    integration["environment"]["environment_hash"] = KeyExecutionEnvironment(
        environment_id=integration["environment"]["environment_id"],
        environment_kind=integration["environment"]["environment_kind"],
        chain_id=integration["environment"]["chain_id"],
        policy_hash=integration["environment"]["policy_hash"],
        challenge_hash=integration["environment"]["challenge_hash"],
        issued_at_epoch=integration["environment"]["issued_at_epoch"],
        expires_at_epoch=integration["environment"]["expires_at_epoch"],
        local_user_presence_confirmed=False,
        rollback_protection_confirmed=integration["environment"]["rollback_protection_confirmed"],
    ).public_dict()["environment_hash"]

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/signer-device/evaluate",
        json.dumps(integration).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is False
    signer_device = payload["signer_device_integration"]
    assert signer_device["signer_device_ready"] is False
    assert "local_user_presence_missing" in signer_device["errors"]


def test_signer_device_evaluate_endpoint_blocks_missing_provider(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    integration = _perps_wallet_signer_device_integration()
    integration["backend_descriptor"] = {
        **integration["backend_descriptor"],
        "metadata": {
            **integration["backend_descriptor"]["metadata"],
            "provider": "",
        },
    }
    integration["backend_descriptor"]["backend_hash"] = KeyBackendDescriptor(
        key_id=integration["backend_descriptor"]["key_id"],
        backend_kind=integration["backend_descriptor"]["backend_kind"],
        backend_id=integration["backend_descriptor"]["backend_id"],
        policy_hash=integration["backend_descriptor"]["policy_hash"],
        active=integration["backend_descriptor"]["active"],
        no_raw_private_key_exposure=integration["backend_descriptor"]["no_raw_private_key_exposure"],
        metadata=integration["backend_descriptor"]["metadata"],
    ).public_dict()["backend_hash"]

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/signer-device/evaluate",
        json.dumps(integration).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is False
    signer_device = payload["signer_device_integration"]
    assert signer_device["signer_device_ready"] is False
    assert "signer-device backend provider missing" in signer_device["errors"]


def test_signer_prompt_capture_evaluate_endpoint_blocks_reference_mismatch(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/signer-prompt-capture/evaluate",
        json.dumps(
            _perps_wallet_signer_prompt_capture(prompt_reference="os-prompt:wallet-a:epoch-14")
        ).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is False
    signer_prompt_capture = payload["signer_prompt_capture"]
    assert signer_prompt_capture["signer_prompt_capture_ready"] is False
    assert "signer prompt capture prompt_reference does not match approval_reference" in signer_prompt_capture["errors"]


def test_signer_execution_evaluate_endpoint_blocks_bad_prompt_order(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/signer-execution/evaluate",
        json.dumps(
            _perps_wallet_signer_execution_exercise(
                prompt_presented_at_epoch=13,
                prompt_confirmed_at_epoch=12,
            )
        ).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is False
    signer_execution = payload["signer_execution_exercise"]
    assert signer_execution["signer_execution_ready"] is False
    assert "signer execution prompt confirmation precedes prompt presentation" in signer_execution["errors"]


def test_signer_ceremony_evaluate_endpoint_blocks_prompt_mismatch(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    payload_in = _perps_wallet_signer_ceremony_payload(
        signer_execution_exercise=_perps_wallet_signer_execution_exercise(
            prompt_reference="os-prompt:wallet-a:epoch-14"
        ),
    )
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/signer-ceremony/evaluate",
        json.dumps(payload_in).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is False
    signer_ceremony = payload["signer_ceremony"]
    assert signer_ceremony["signer_ceremony_ready"] is False
    assert "signer ceremony prompt_reference mismatch" in signer_ceremony["errors"]


def test_hardware_custody_evaluate_endpoint_blocks_os_keychain_backend(monkeypatch) -> None:
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON",
        json.dumps(_perps_wallet_authority_profile(), sort_keys=True),
    )
    monkeypatch.delenv("PERPS_WALLET_AUTHORITY_PROFILE_FILE", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    payload_in = _perps_wallet_signer_ceremony_payload()
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/hardware-custody/evaluate",
        json.dumps(payload_in).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is False
    hardware_custody = payload["hardware_custody"]
    assert hardware_custody["hardware_custody_ready"] is False
    assert "hardware custody backend_kind is not hardware-backed" in hardware_custody["errors"]


def test_status_loads_ready_oracle_authority_profile(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_ORACLE_AUTHORITY_PROFILE_JSON",
        json.dumps(_oracle_authority_profile(), sort_keys=True),
    )
    for name in (
        "PERPS_ORACLE_AUTHORITY_PROFILE_FILE",
        "ZENO_ORACLE_AUTHORITY_PROFILE_JSON",
        "ZENO_ORACLE_AUTHORITY_PROFILE_FILE",
        "ZENO_ORACLE_PRODUCTION_AUTHORITY_PROFILE_FILE",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["status"]["production_oracle_authority"] is True
    oracle_authority = payload["status"]["oracle_authority"]
    assert oracle_authority["status"] == "ready"
    assert oracle_authority["readiness_gaps"] == []
    assert oracle_authority["active_signer_count"] == 2
    assert oracle_authority["threshold"] == 2
    assert oracle_authority["signature_count"] == 2
    assert oracle_authority["signature_quorum"]["accepted_weight"] == 2
    assert oracle_authority["proof_profile"]["runtime_proof_profile"] == "zenooracle-o3-replay-zk-profile-v1"
    encoded = json.dumps(oracle_authority, sort_keys=True)
    assert "private_key" not in encoded
    assert "secret_hex" not in encoded


def test_status_blocks_oracle_authority_profile_chain_mismatch(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_after_pair_liquidation(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv(
        "PERPS_ORACLE_AUTHORITY_PROFILE_JSON",
        json.dumps(_oracle_authority_profile(chain_id="wrong-chain"), sort_keys=True),
    )
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = perps_wallet_api.handle_perps_wallet_request("GET", "/api/perps/wallet/status", None)

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["status"]["production_oracle_authority"] is False
    assert "oracle production authority profile chain_id mismatch" in payload["status"]["oracle_authority"]["readiness_gaps"]


def test_prepare_partial_liquidate_is_opt_in_for_isolated_markets(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_isolated_liquidatable_account(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.delenv("TAU_DEX_ALLOW_ISOLATED_PERPS", raising=False)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "partial_liquidate",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "fraction_bps": 2500,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["operation"]["version"] == "0.1"
    assert payload["report"]["operation"]["action"] == "partial_liquidate"
    assert payload["report"]["preflight"]["ok"] is False
    assert "isolated perps disabled" in payload["report"]["preflight"]["error"]


def test_prepare_partial_liquidate_accepts_auto_fraction_zero(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_isolated_liquidatable_account(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_ALLOW_ISOLATED_PERPS", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "partial_liquidate",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "fraction_bps": 0,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["operation"]["action"] == "partial_liquidate"
    assert payload["report"]["operation"]["fraction_bps"] == 0


def test_caller_supplied_oracle_bridge_preflights_required_partial_liquidate(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_isolated_liquidatable_account(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_ALLOW_ISOLATED_PERPS", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE", "1")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    bridge_payload = _test_oracle_bridge_fixture(
        action="partial_liquidate",
        market_id=ISOLATED_MARKET_ID,
        account_pubkey=ALICE,
        fraction_bps=0,
    )

    assert bridge_payload["ok"] is True
    assert bridge_payload["action"] == "partial_liquidate"
    assert bridge_payload["target"]["action_kind"] == "liquidate_account"
    assert bridge_payload["target"]["wallet_action"] == "partial_liquidate"
    assert bridge_payload["verify_result"]["status"] == "accepted"

    body = {
        "action": "partial_liquidate",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "fraction_bps": 0,
        "oracle_adapter_bridge": bridge_payload["bridge"],
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["oracle_adapter_bridge"]["bridge_id"] == bridge_payload["bridge"]["bridge_id"]


def test_submit_partial_liquidate_builds_account_bound_stream_8_tx(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(_state_with_isolated_liquidatable_account(quote_asset=quote_asset))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setenv("TAU_DEX_ALLOW_ISOLATED_PERPS", "1")
    monkeypatch.setenv("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE", "0")
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "partial_liquidate",
        "market_id": ISOLATED_MARKET_ID,
        "account_pubkey": ALICE,
        "account_privkey": str(ALICE_PRIVKEY),
        "fraction_bps": 5000,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["stream_key"] == "8"
    assert payload["transport"]["tx_sender_pubkey"] == ALICE
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["operation"]["version"] == "0.1"
    assert payload["report"]["operation"]["action"] == "partial_liquidate"
    assert payload["report"]["operation"]["fraction_bps"] == 5000
    _assert_redacted_tau_tx_payload(payload["report"]["tau_tx_payload"], _FakeClient.sent[0])
    assert _FakeClient.sent[0]["sender_pubkey"] == ALICE[2:]
    wire_ops = json.loads(_FakeClient.sent[0]["operations"]["8"])
    assert wire_ops[0]["action"] == "partial_liquidate"
    assert wire_ops[0]["account_pubkey"] == ALICE
    assert wire_ops[0]["fraction_bps"] == 5000
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"


def test_submit_rejects_preflight_failure_before_sendtx(monkeypatch) -> None:
    quote_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    _FakeClient.app_state = _wrapped_app_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()))
    _FakeClient.sent = []
    monkeypatch.setenv("PERPS_WALLET_CHAIN_ID", CHAIN_ID)
    monkeypatch.setattr(perps_wallet_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "init_market_2p",
        "market_id": MARKET_ID,
        "quote_asset": quote_asset,
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "account_a_privkey": str(ALICE_PRIVKEY),
        "account_b_privkey": str(BOB_PRIVKEY),
        "nonce_a": 1,
        "nonce_b": 1,
        "sig_a": "0x" + "00" * 96,
        "sig_b": "0x" + "00" * 96,
        "deadline": FUTURE_DEADLINE,
        "block_timestamp": 1,
    }
    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert payload["error"].startswith("preflight_failed:")
    assert _FakeClient.sent == []
