from __future__ import annotations

import base64
import hashlib
import json
import os
import shutil
import socket
import socketserver
import subprocess
import threading
import time
from pathlib import Path
from urllib.parse import urlencode, urlparse
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import pytest

from src.core.dex import DexState
from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
from src.integration import tau_testnet_dex_plugin as plugin
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.perp_engine import PerpEngineConfig, _kernel_initial_global_state, apply_perp_ops
from src.integration.perps_wallet_authority import (
    PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
    PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_SCHEMA_V1,
    PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND,
    PERPS_WALLET_RECOVERY_EXERCISE_SCHEMA_V1,
    PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND,
    PERPS_WALLET_ROTATION_EXERCISE_SCHEMA_V1,
    PERPS_WALLET_SIGNER_PROMPT_CAPTURE_SCHEMA_V1,
    PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_SCHEMA_V1,
    build_perps_wallet_device_approval_environment_policy_v1,
    build_perps_wallet_device_approval_exercise_v1,
    build_perps_wallet_device_approval_use_policy_v1,
    build_perps_wallet_authority_profile_v1,
    build_perps_wallet_signer_device_integration_v1,
    build_perps_wallet_signer_prompt_capture_v1,
    build_perps_wallet_signer_execution_exercise_v1,
    perps_wallet_device_approval_exercise_hash_v1,
    perps_wallet_recovery_exercise_hash_v1,
    perps_wallet_rotation_exercise_hash_v1,
    perps_wallet_signer_device_integration_hash_v1,
    perps_wallet_signer_prompt_capture_hash_v1,
    perps_wallet_signer_execution_exercise_hash_v1,
)
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, build_signed_tau_transaction, sign_perp_op_for_engine
from src.integration.zeno_key_manager import (
    KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
    KEY_ENVIRONMENT_LOCAL_PROCESS,
    KeyExecutionEnvironment,
    KeyRef,
    RecoveryGuardian,
    SocialRecoveryPolicy,
    ZenoKeyManager,
)
from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_key_manager_v0 import (
    BACKEND_HARDWARE_WALLET_PLACEHOLDER,
    BACKEND_OS_KEYCHAIN,
    KeyBackendDescriptor,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zeno_oracle_authority import (
    ORACLE_AUTHORITY_PAYLOAD_KIND,
    build_oracle_authority_profile_v1,
)
from src.integration.zeno_oracle_authorization import (
    _PERPS_INDEX_QUERY_ID,
    _PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
    _PERPS_SETTLE_EPOCH_PROFILE_ID,
)
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from src.state import BalanceTable, LPTable
from tests.chaos.conftest import requires_toxiproxy
from tests.integration.tau_rpc_fault_proxy import TauRpcFaultProxy
from tools.chaos.toxiproxy_harness import ToxiproxyHarness


ROOT = Path(__file__).resolve().parents[2]
DEX_UI = ROOT / "tools" / "dex-ui"
ORACLE_CLI = ROOT / "tools" / "zenodex_oracle.py"
ROOT_A = "0x" + "aa" * 32
ROOT_B = "0x" + "bb" * 32


def _smoke_url(base: str, *, query: dict[str, object], secrets: dict[str, object]) -> str:
    public_query = urlencode({key: str(value) for key, value in query.items() if value is not None})
    secret_fragment = urlencode({key: str(value) for key, value in secrets.items() if value is not None})
    if secret_fragment:
        return f"{base}/?{public_query}#{secret_fragment}"
    return f"{base}/?{public_query}"


def _perps_wallet_signer_payload(*, chain_id: str) -> dict[str, object]:
    return {
        "domain": "zenodex.perps.stream8.signer-execution.v1",
        "chain_id": chain_id,
        "nonce": 15,
        "action": "deposit_collateral",
        "stream_key": "8",
    }


def _perps_wallet_signer_payload_hash(*, chain_id: str, payload: dict[str, object] | None = None) -> str:
    return hash_v0("zeno_key_manager_runtime_payload_v0", dict(payload or _perps_wallet_signer_payload(chain_id=chain_id)))


def _privkey_hex(value: int) -> str:
    return "0x" + int(value).to_bytes(32, byteorder="big", signed=False).hex()


def _oracle_authority_profile(
    *,
    chain_id: str,
    oracle_pubkey: str,
    operator_pubkey: str,
    oracle_privkey: int,
    operator_privkey: int,
) -> dict[str, object]:
    key_manager = ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="oracle-authority-a", public_key=oracle_pubkey),
            KeyRef(key_id="oracle-authority-b", public_key=operator_pubkey),
        )
    ).public_dict()
    signer_registry = build_signer_registry_v0(
        registry_id="oracle-production-authority-v1",
        payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
        threshold=2,
        signers=(
            {
                "signer_id": "oracle-a",
                "key_id": "oracle-authority-a",
                "public_key": oracle_pubkey,
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "oracle-b",
                "key_id": "oracle-authority-b",
                "public_key": operator_pubkey,
                "weight": 1,
                "status": "active",
            },
        ),
    )
    profile = build_oracle_authority_profile_v1(
        authority_id="oracle-production-authority-v1",
        chain_id=chain_id,
        stage="production",
        enabled=True,
        key_manager=key_manager,
        signer_registry=signer_registry,
        wallet_ux={
            "external_signer_required": True,
            "key_manager_required": True,
            "device_approval_required": True,
        },
        proof_profile={
            "zk_or_proof_required": True,
            "oracle_receipt_replay_required": True,
            "runtime_proof_profile": "zenooracle-o3-replay-zk-profile-v1",
        },
    )
    profile["signature_envelopes"] = [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
            payload_hash=str(profile["authority_hash"]),
            signer_id="oracle-a",
            key_id="oracle-authority-a",
            private_key_hex=_privkey_hex(oracle_privkey),
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
            payload_hash=str(profile["authority_hash"]),
            signer_id="oracle-b",
            key_id="oracle-authority-b",
            private_key_hex=_privkey_hex(operator_privkey),
        ),
    ]
    return profile


def _perps_wallet_authority_profile(
    *,
    chain_id: str,
    account_a_pubkey: str,
    account_b_pubkey: str,
    guardian_a_pubkey: str,
    guardian_b_pubkey: str,
) -> dict[str, object]:
    key_manager = ZenoKeyManager(
        key_refs=(
            KeyRef(key_id="perps-wallet-a", public_key=account_a_pubkey, recovery_policy_id="recovery-perps-wallet-a"),
            KeyRef(key_id="perps-wallet-b", public_key=account_b_pubkey, recovery_policy_id="recovery-perps-wallet-b"),
        ),
        recovery_policies=(
            SocialRecoveryPolicy(
                policy_id="recovery-perps-wallet-a",
                subject_key_id="perps-wallet-a",
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-a", public_key=guardian_a_pubkey),
                    RecoveryGuardian(guardian_id="guardian-b", public_key=guardian_b_pubkey),
                ),
            ),
            SocialRecoveryPolicy(
                policy_id="recovery-perps-wallet-b",
                subject_key_id="perps-wallet-b",
                threshold=2,
                delay_epochs=3,
                guardians=(
                    RecoveryGuardian(guardian_id="guardian-a", public_key=guardian_a_pubkey),
                    RecoveryGuardian(guardian_id="guardian-b", public_key=guardian_b_pubkey),
                ),
            ),
        ),
    ).public_dict()
    signer_registry = build_signer_registry_v0(
        registry_id="perps-wallet-authority-v1",
        payload_kind=PERPS_WALLET_AUTHORITY_PAYLOAD_KIND,
        threshold=1,
        signers=(
            {
                "signer_id": "wallet-a",
                "key_id": "perps-wallet-a",
                "public_key": account_a_pubkey,
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "wallet-b",
                "key_id": "perps-wallet-b",
                "public_key": account_b_pubkey,
                "weight": 1,
                "status": "active",
            },
        ),
    )
    return build_perps_wallet_authority_profile_v1(
        authority_id="perps-wallet-authority-v1",
        chain_id=chain_id,
        stage="production",
        enabled=True,
        key_manager=key_manager,
        signer_registry=signer_registry,
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


def _perps_wallet_recovery_exercise(*, chain_id: str) -> dict[str, object]:
    exercise = {
        "schema": PERPS_WALLET_RECOVERY_EXERCISE_SCHEMA_V1,
        "chain_id": chain_id,
        "authority_id": "perps-wallet-authority-v1",
        "subject_key_id": "perps-wallet-a",
        "policy_id": "recovery-perps-wallet-a",
        "requested_at_epoch": 10,
        "current_epoch": 13,
        "approvals": ["guardian-a", "guardian-b"],
    }
    exercise_hash = perps_wallet_recovery_exercise_hash_v1(exercise)
    exercise["signature_envelopes"] = [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND,
            payload_hash=exercise_hash,
            signer_id="guardian-a",
            key_id="guardian-a",
            private_key_hex=_privkey_hex(185),
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND,
            payload_hash=exercise_hash,
            signer_id="guardian-b",
            key_id="guardian-b",
            private_key_hex=_privkey_hex(186),
        ),
    ]
    return exercise


def _perps_wallet_rotation_exercise(
    *,
    chain_id: str,
    account_b_pubkey: str,
) -> dict[str, object]:
    account_c_pubkey = "0x" + bls_pubkey_hex_from_privkey(187)
    guardian_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(185)
    guardian_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(186)
    next_profile = build_perps_wallet_authority_profile_v1(
        authority_id="perps-wallet-authority-v1",
        chain_id=chain_id,
        stage="production",
        enabled=True,
        key_manager=ZenoKeyManager(
            key_refs=(
                KeyRef(key_id="perps-wallet-c", public_key=account_c_pubkey, recovery_policy_id="recovery-perps-wallet-c"),
                KeyRef(key_id="perps-wallet-b", public_key=account_b_pubkey, recovery_policy_id="recovery-perps-wallet-b"),
            ),
            recovery_policies=(
                SocialRecoveryPolicy(
                    policy_id="recovery-perps-wallet-c",
                    subject_key_id="perps-wallet-c",
                    threshold=2,
                    delay_epochs=3,
                    guardians=(
                        RecoveryGuardian(guardian_id="guardian-a", public_key=guardian_a_pubkey),
                        RecoveryGuardian(guardian_id="guardian-b", public_key=guardian_b_pubkey),
                    ),
                ),
                SocialRecoveryPolicy(
                    policy_id="recovery-perps-wallet-b",
                    subject_key_id="perps-wallet-b",
                    threshold=2,
                    delay_epochs=3,
                    guardians=(
                        RecoveryGuardian(guardian_id="guardian-a", public_key=guardian_a_pubkey),
                        RecoveryGuardian(guardian_id="guardian-b", public_key=guardian_b_pubkey),
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
                    "public_key": account_c_pubkey,
                    "weight": 1,
                    "status": "active",
                },
                {
                    "signer_id": "wallet-b",
                    "key_id": "perps-wallet-b",
                    "public_key": account_b_pubkey,
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
    exercise = {
        "schema": PERPS_WALLET_ROTATION_EXERCISE_SCHEMA_V1,
        "chain_id": chain_id,
        "authority_id": "perps-wallet-authority-v1",
        "rotated_key_id": "perps-wallet-a",
        "replacement_key_id": "perps-wallet-c",
        "policy_id": "recovery-perps-wallet-a",
        "requested_at_epoch": 10,
        "broadcast_at_epoch": 13,
        "broadcast_reference": "tau-tx:perps-wallet-rotation-1",
        "approvals": ["guardian-a", "guardian-b"],
        "next_wallet_authority_profile": next_profile,
    }
    exercise_hash = perps_wallet_rotation_exercise_hash_v1(exercise)
    exercise["signature_envelopes"] = [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND,
            payload_hash=exercise_hash,
            signer_id="guardian-a",
            key_id="guardian-a",
            private_key_hex=_privkey_hex(185),
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND,
            payload_hash=exercise_hash,
            signer_id="guardian-b",
            key_id="guardian-b",
            private_key_hex=_privkey_hex(186),
        ),
    ]
    return exercise


def _perps_wallet_device_approval_exercise(*, chain_id: str) -> dict[str, object]:
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
        chain_id=chain_id,
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    ).public_dict()
    use_policy = build_perps_wallet_device_approval_use_policy_v1(
        allowed_payload_kinds=["perps_wallet_prepare"],
        allowed_chain_ids=[chain_id],
        allowed_purposes=["sign"],
        valid_from_epoch=10,
        valid_until_epoch=20,
    )
    environment_policy = build_perps_wallet_device_approval_environment_policy_v1(
        allowed_environment_kinds=[KEY_ENVIRONMENT_LOCAL_PROCESS],
        expected_chain_id=chain_id,
        expected_policy_hash=ROOT_A,
        expected_challenge_hash=ROOT_B,
        require_user_presence=True,
        require_rollback_protection=True,
    )
    exercise = build_perps_wallet_device_approval_exercise_v1(
        authority_id="perps-wallet-authority-v1",
        chain_id=chain_id,
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
            "chain_id": chain_id,
            "nonce": 14,
            "action": "deposit_collateral",
            "stream_key": "8",
        },
        seen_nonces=[11, 12],
    )
    return {
        **exercise,
        "schema": PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_SCHEMA_V1,
        "exercise_hash": perps_wallet_device_approval_exercise_hash_v1(exercise),
    }


def _perps_wallet_signer_device_integration(*, chain_id: str) -> dict[str, object]:
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
        chain_id=chain_id,
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    ).public_dict()
    environment_policy = build_perps_wallet_device_approval_environment_policy_v1(
        allowed_environment_kinds=[KEY_ENVIRONMENT_LOCAL_PROCESS],
        expected_chain_id=chain_id,
        expected_policy_hash=ROOT_A,
        expected_challenge_hash=ROOT_B,
        require_user_presence=True,
        require_rollback_protection=True,
    )
    integration = build_perps_wallet_signer_device_integration_v1(
        authority_id="perps-wallet-authority-v1",
        chain_id=chain_id,
        key_id="perps-wallet-a",
        current_epoch=13,
        backend_descriptor=backend,
        environment=environment,
        environment_policy=environment_policy,
        device_label="MacBook Keychain Wallet A",
        approval_reference="os-prompt:wallet-a:epoch-13",
    )
    return {
        **integration,
        "schema": "zenodex/perps-wallet-signer-device-integration/v1",
        "integration_hash": perps_wallet_signer_device_integration_hash_v1(integration),
    }


def _perps_wallet_signer_execution_exercise(*, chain_id: str) -> dict[str, object]:
    payload = _perps_wallet_signer_payload(chain_id=chain_id)
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
        chain_id=chain_id,
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    ).public_dict()
    use_policy = build_perps_wallet_device_approval_use_policy_v1(
        allowed_payload_kinds=["perps_wallet_submit"],
        allowed_chain_ids=[chain_id],
        allowed_purposes=["sign"],
        valid_from_epoch=10,
        valid_until_epoch=20,
    )
    environment_policy = build_perps_wallet_device_approval_environment_policy_v1(
        allowed_environment_kinds=[KEY_ENVIRONMENT_LOCAL_PROCESS],
        expected_chain_id=chain_id,
        expected_policy_hash=ROOT_A,
        expected_challenge_hash=ROOT_B,
        require_user_presence=True,
        require_rollback_protection=True,
    )
    exercise = build_perps_wallet_signer_execution_exercise_v1(
        authority_id="perps-wallet-authority-v1",
        chain_id=chain_id,
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
        signed_payload_hash=_perps_wallet_signer_payload_hash(chain_id=chain_id, payload=payload),
    )
    return {
        **exercise,
        "schema": PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_SCHEMA_V1,
        "exercise_hash": perps_wallet_signer_execution_exercise_hash_v1(exercise),
    }


def _perps_wallet_signer_prompt_capture(*, chain_id: str) -> dict[str, object]:
    prompt_message_hash = _perps_wallet_signer_payload_hash(chain_id=chain_id)
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
        chain_id=chain_id,
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    ).public_dict()
    environment_policy = build_perps_wallet_device_approval_environment_policy_v1(
        allowed_environment_kinds=[KEY_ENVIRONMENT_LOCAL_PROCESS],
        expected_chain_id=chain_id,
        expected_policy_hash=ROOT_A,
        expected_challenge_hash=ROOT_B,
        require_user_presence=True,
        require_rollback_protection=True,
    )
    capture = build_perps_wallet_signer_prompt_capture_v1(
        authority_id="perps-wallet-authority-v1",
        chain_id=chain_id,
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
        prompt_message_hash=prompt_message_hash,
        capture_source="operator-audit-log",
        capture_evidence_hash="0x" + "ab" * 32,
    )
    return {
        **capture,
        "schema": PERPS_WALLET_SIGNER_PROMPT_CAPTURE_SCHEMA_V1,
        "capture_hash": perps_wallet_signer_prompt_capture_hash_v1(capture),
    }


def _perps_wallet_hardware_backend_descriptor(*, chain_id: str) -> dict[str, object]:
    _ = chain_id
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


def _perps_wallet_hardware_environment(*, chain_id: str) -> dict[str, object]:
    return KeyExecutionEnvironment(
        environment_id="perps-wallet-a-hardware-session-1",
        environment_kind=KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
        chain_id=chain_id,
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    ).public_dict()


def _perps_wallet_hardware_environment_policy(*, chain_id: str) -> dict[str, object]:
    return build_perps_wallet_device_approval_environment_policy_v1(
        allowed_environment_kinds=[KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE],
        expected_chain_id=chain_id,
        expected_policy_hash=ROOT_A,
        expected_challenge_hash=ROOT_B,
        require_user_presence=True,
        require_rollback_protection=True,
    )


def _chrome_binary() -> str | None:
    for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
        path = shutil.which(name)
        if path:
            return path
    return None


def _chrome_rendered_haystack(
    *,
    chrome: str,
    url: str,
    profile: Path,
    snippets: tuple[str, ...],
    timeout_s: float = 60.0,
) -> str:
    """Return hydrated page text plus HTML using Chrome DevTools Protocol."""

    profile.mkdir(parents=True, exist_ok=True)
    proc = subprocess.Popen(
        [
            chrome,
            "--headless=new",
            "--disable-gpu",
            "--no-sandbox",
            "--disable-dev-shm-usage",
            "--no-first-run",
            "--remote-debugging-port=0",
            f"--user-data-dir={profile}",
            url,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    try:
        deadline = time.monotonic() + timeout_s
        active_port = profile / "DevToolsActivePort"
        while time.monotonic() < deadline and not active_port.exists():
            time.sleep(0.1)
        if not active_port.exists():
            raise AssertionError("Chrome did not publish DevToolsActivePort")
        lines = active_port.read_text(encoding="utf-8").splitlines()
        if not lines:
            raise AssertionError("Chrome DevToolsActivePort was empty")
        port = int(lines[0])
        ws_url = ""
        while time.monotonic() < deadline and not ws_url:
            try:
                with urlopen(f"http://127.0.0.1:{port}/json/list", timeout=2) as response:  # noqa: S310
                    targets = json.loads(response.read().decode("utf-8"))
                for target in targets:
                    if isinstance(target, dict) and target.get("type") == "page" and target.get("webSocketDebuggerUrl"):
                        ws_url = str(target["webSocketDebuggerUrl"])
                        break
            except Exception:
                time.sleep(0.1)
        if not ws_url:
            raise AssertionError("Chrome page DevTools target was not available")

        sock = _ws_connect(ws_url, timeout=max(1.0, deadline - time.monotonic()))
        try:
            request_id = 1
            _ws_send_json(sock, {"id": request_id, "method": "Page.enable"})
            _ws_read_until_id(sock, request_id, deadline=deadline)
            request_id += 1
            _ws_send_json(sock, {"id": request_id, "method": "Page.navigate", "params": {"url": url}})
            _ws_read_until_id(sock, request_id, deadline=deadline)
            request_id += 1
            time.sleep(0.5)
            wait_ms = max(1_000, int((deadline - time.monotonic()) * 1_000) - 500)
            expression = f"""
new Promise((resolve) => {{
  const snippets = {json.dumps(list(snippets))};
  const deadline = Date.now() + {wait_ms};
  const tick = () => {{
    const text = document.body ? document.body.innerText : '';
    const html = document.documentElement ? document.documentElement.outerHTML : '';
    const haystack = `${{text}}\\n${{html}}`;
    if (snippets.every((snippet) => haystack.includes(snippet)) || Date.now() >= deadline) {{
      resolve({{ text, html, readyState: document.readyState, href: location.href }});
      return;
    }}
    setTimeout(tick, 100);
  }};
  tick();
}})
""".strip()
            last_msg: dict[str, object] | None = None
            while time.monotonic() < deadline:
                _ws_send_json(
                    sock,
                    {
                        "id": request_id,
                        "method": "Runtime.evaluate",
                        "params": {
                            "expression": expression,
                            "awaitPromise": True,
                            "returnByValue": True,
                        },
                    },
                )
                msg = _ws_read_until_id(sock, request_id, deadline=deadline)
                request_id += 1
                last_msg = msg
                result = msg.get("result", {}).get("result", {}).get("value", {})
                if isinstance(result, dict):
                    return f"{result.get('text') or ''}\n{result.get('html') or ''}"
                time.sleep(0.2)
            raise AssertionError(f"Chrome Runtime.evaluate returned unexpected result: {last_msg!r}")
        finally:
            sock.close()
    finally:
        if proc.poll() is None:
            proc.terminate()
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def _ws_connect(ws_url: str, *, timeout: float) -> socket.socket:
    parsed = urlparse(ws_url)
    host = parsed.hostname or "127.0.0.1"
    port = int(parsed.port or 80)
    path = parsed.path or "/"
    if parsed.query:
        path = f"{path}?{parsed.query}"
    sock = socket.create_connection((host, port), timeout=timeout)
    key = base64.b64encode(os.urandom(16)).decode("ascii")
    request = (
        f"GET {path} HTTP/1.1\r\n"
        f"Host: {host}:{port}\r\n"
        "Upgrade: websocket\r\n"
        "Connection: Upgrade\r\n"
        f"Sec-WebSocket-Key: {key}\r\n"
        "Sec-WebSocket-Version: 13\r\n"
        "\r\n"
    ).encode("ascii")
    sock.sendall(request)
    raw = b""
    while b"\r\n\r\n" not in raw:
        chunk = sock.recv(4096)
        if not chunk:
            raise AssertionError("Chrome DevTools websocket closed during handshake")
        raw += chunk
    if b" 101 " not in raw.split(b"\r\n", 1)[0]:
        raise AssertionError(f"Chrome DevTools websocket handshake failed: {raw[:200]!r}")
    expected_accept = base64.b64encode(
        hashlib.sha1((key + "258EAFA5-E914-47DA-95CA-C5AB0DC85B11").encode("ascii")).digest()
    ).decode("ascii")
    if f"sec-websocket-accept: {expected_accept}".lower().encode("ascii") not in raw.lower():
        raise AssertionError("Chrome DevTools websocket accept header mismatch")
    return sock


def _ws_send_json(sock: socket.socket, payload: dict[str, object]) -> None:
    _ws_send_frame(sock, opcode=0x1, payload=json.dumps(payload, separators=(",", ":")).encode("utf-8"))


def _ws_send_frame(sock: socket.socket, *, opcode: int, payload: bytes) -> None:
    header = bytearray([0x80 | opcode])
    length = len(payload)
    if length < 126:
        header.append(0x80 | length)
    elif length < 65536:
        header.extend((0x80 | 126, *length.to_bytes(2, "big")))
    else:
        header.extend((0x80 | 127, *length.to_bytes(8, "big")))
    mask = os.urandom(4)
    header.extend(mask)
    masked = bytes(byte ^ mask[index % 4] for index, byte in enumerate(payload))
    sock.sendall(bytes(header) + masked)


def _ws_read_until_id(sock: socket.socket, msg_id: int, *, deadline: float) -> dict[str, object]:
    while time.monotonic() < deadline:
        sock.settimeout(max(0.1, deadline - time.monotonic()))
        raw = _ws_recv_text(sock)
        msg = json.loads(raw)
        if isinstance(msg, dict) and msg.get("id") == msg_id:
            return msg
    raise TimeoutError(f"Chrome DevTools response {msg_id} timed out")


def _ws_recv_text(sock: socket.socket) -> str:
    chunks: list[bytes] = []
    while True:
        first = _recv_exact(sock, 2)
        fin = bool(first[0] & 0x80)
        opcode = first[0] & 0x0F
        masked = bool(first[1] & 0x80)
        length = first[1] & 0x7F
        if length == 126:
            length = int.from_bytes(_recv_exact(sock, 2), "big")
        elif length == 127:
            length = int.from_bytes(_recv_exact(sock, 8), "big")
        mask = _recv_exact(sock, 4) if masked else b""
        payload = _recv_exact(sock, length) if length else b""
        if masked:
            payload = bytes(byte ^ mask[index % 4] for index, byte in enumerate(payload))
        if opcode == 0x8:
            raise AssertionError("Chrome DevTools websocket closed")
        if opcode == 0x9:
            _ws_send_frame(sock, opcode=0xA, payload=payload)
            continue
        if opcode in (0x1, 0x0):
            chunks.append(payload)
        if fin:
            return b"".join(chunks).decode("utf-8")


def _recv_exact(sock: socket.socket, size: int) -> bytes:
    out = bytearray()
    while len(out) < size:
        chunk = sock.recv(size - len(out))
        if not chunk:
            raise AssertionError("Chrome DevTools websocket closed")
        out.extend(chunk)
    return bytes(out)


def _free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return int(sock.getsockname()[1])


def _wait_for_http(url: str, *, timeout_s: float = 30) -> None:
    deadline = time.monotonic() + timeout_s
    last_error: Exception | None = None
    while time.monotonic() < deadline:
        try:
            with urlopen(url, timeout=2) as response:  # noqa: S310 - local test servers only
                response.read(1)
            return
        except Exception as exc:
            last_error = exc
            time.sleep(0.2)
    raise AssertionError(f"server did not become ready at {url}: {last_error}")


def _post_json(url: str, payload: dict[str, object]) -> dict[str, object]:
    request = Request(
        url,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urlopen(request, timeout=10) as response:  # noqa: S310 - local test servers only
            return json.loads(response.read().decode("utf-8"))
    except HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise AssertionError(f"POST {url} failed with HTTP {exc.code}: {detail}") from exc


def _post_json_status(url: str, payload: dict[str, object]) -> tuple[int, dict[str, object]]:
    request = Request(
        url,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urlopen(request, timeout=10) as response:  # noqa: S310 - local test servers only
            return int(response.status), json.loads(response.read().decode("utf-8"))
    except HTTPError as exc:
        return int(exc.code), json.loads(exc.read().decode("utf-8"))


def _tau_command_count(tau_server: socketserver.ThreadingTCPServer, command: str) -> int:
    state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
    with state.lock:
        return int(state.command_counts.get(command, 0))


def _wait_for_tau_command_count(
    tau_server: socketserver.ThreadingTCPServer,
    command: str,
    minimum: int,
    *,
    timeout_s: float = 10.0,
) -> None:
    deadline = time.monotonic() + float(timeout_s)
    while time.monotonic() < deadline:
        if _tau_command_count(tau_server, command) >= int(minimum):
            return
        time.sleep(0.05)
    raise AssertionError(f"tau command {command!r} did not reach count {minimum}")


def _seed_oracle_authorization(base: str, *, action_kind: str = "settle_epoch") -> dict[str, object]:
    query_id = _PERPS_INDEX_QUERY_ID
    action_marker = "8" if action_kind == "settle_epoch" else "7"
    action_id = "sha256:" + action_marker * 64
    profile_id = (
        _PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID
        if action_kind == "liquidate_account"
        else _PERPS_SETTLE_EPOCH_PROFILE_ID
    )
    action_facts_hash = "sha256:" + "9" * 64
    pre_state_hash = "sha256:" + "a" * 64
    identity = _post_json(f"{base}/api/oracle/identity/create", {"force": True})
    _post_json(
        f"{base}/api/oracle/query/register",
        {
            "base_asset": "AGRS",
            "quote_asset": "ZDEX",
            "query_id": query_id,
            "source_policy_id": "source-policy:registered-diverse-v1",
            "min_reporters": 1,
            "report_reward_e8": 17,
            "force": True,
        },
    )
    _post_json(f"{base}/api/oracle/query/fund", {"query_id": query_id, "amount_e8": 20})
    _post_json(f"{base}/api/oracle/reporter/register", {"query_id": query_id, "required_bond_e8": 1, "force": True})
    _post_json(f"{base}/api/oracle/reporter/bond", {"amount_e8": 1})
    _post_json(
        f"{base}/api/oracle/source/register",
        {
            "source_id": "source:perps-ui-picker",
            "source_kind": "cex",
            "control_group_id": "control:perps-ui-picker",
            "venue_id": "venue:perps-ui-picker",
            "data_family_id": "price:cex-last-trade",
            "transport_id": "api:https:perps-ui-picker",
            "asset_class": "crypto",
            "query_id": query_id,
            "assurance_class": "S3",
            "force": True,
        },
    )
    submitted = _post_json(
        f"{base}/api/oracle/report/submit",
        {
            "query_id": query_id,
            "price_e8": 123456789,
            "source_observed_epoch": 12,
            "source_id": "source:perps-ui-picker",
        },
    )
    aggregate = _post_json(f"{base}/api/oracle/aggregate/build", {"query_id": query_id, "epoch": 12})
    read = _post_json(
        f"{base}/api/oracle/read/accept",
        {
            "aggregate_id": aggregate["aggregate_id"],
            "consumer_module": "zenodex.perps",
            "profile_id": profile_id,
        },
    )
    authorization = _post_json(
        f"{base}/api/oracle/authorization/build",
        {
            "read_id": read["read_id"],
            "action_kind": action_kind,
            "action_id": action_id,
            "action_facts_hash": action_facts_hash,
            "pre_state_hash": pre_state_hash,
            "now_epoch": 12,
        },
    )
    return {
        "identity": identity,
        "submitted": submitted,
        "aggregate": aggregate,
        "read": read,
        "authorization": authorization,
    }


def _initial_app_state_json(dex_state: DexState | None = None) -> str:
    if dex_state is None:
        dex_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    payload = {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(dex_state).data,
        "proof_mining": None,
        "zusd_monetary": None,
    }
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


def _advanced_market_state(
    *,
    chain_id: str,
    market_id: str,
    quote_asset: str,
    account_a_privkey: int,
    account_b_privkey: int,
    oracle_pubkey: str,
) -> DexState:
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    account_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_b_privkey)
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    init_op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "init_market_2p",
        "quote_asset": quote_asset,
        "account_a_pubkey": account_a_pubkey,
        "account_b_pubkey": account_b_pubkey,
        "deadline": 999_999_999,
        "nonce_a": 1,
        "nonce_b": 1,
    }
    init_op["sig_a"] = sign_perp_op_for_engine(
        init_op,
        privkey=account_a_privkey,
        chain_id=chain_id,
        signer_pubkey=account_a_pubkey,
        nonce=1,
    )
    init_op["sig_b"] = sign_perp_op_for_engine(
        init_op,
        privkey=account_b_privkey,
        chain_id=chain_id,
        signer_pubkey=account_b_pubkey,
        nonce=1,
    )
    cfg = PerpEngineConfig(chain_id=chain_id, oracle_pubkey=oracle_pubkey)
    res1 = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [init_op]},
        tx_sender_pubkey=account_a_pubkey,
        block_timestamp=1,
    )
    assert res1.ok, res1.error
    assert res1.state is not None
    res2 = apply_perp_ops(
        config=cfg,
        state=res1.state,
        operations={"5": [{"module": "TauPerp", "version": "1.0", "market_id": market_id, "action": "advance_epoch", "delta": 1}]},
        tx_sender_pubkey=account_a_pubkey,
        block_timestamp=2,
    )
    assert res2.ok, res2.error
    assert res2.state is not None
    return res2.state


def _settle_ready_market_state(
    *,
    chain_id: str,
    market_id: str,
    quote_asset: str,
    account_a_privkey: int,
    account_b_privkey: int,
    oracle_privkey: int,
) -> DexState:
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(oracle_privkey)
    state = _advanced_market_state(
        chain_id=chain_id,
        market_id=market_id,
        quote_asset=quote_asset,
        account_a_privkey=account_a_privkey,
        account_b_privkey=account_b_privkey,
        oracle_pubkey=oracle_pubkey,
    )
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "publish_clearing_price",
        "price_e8": 100_000_000,
        "deadline": 999_999_999,
        "oracle_nonce": 1,
    }
    op["oracle_sig"] = sign_perp_op_for_engine(
        op,
        privkey=oracle_privkey,
        chain_id=chain_id,
        signer_pubkey=oracle_pubkey,
        nonce=1,
    )
    cfg = PerpEngineConfig(chain_id=chain_id, oracle_pubkey=oracle_pubkey)
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [op]},
        tx_sender_pubkey=oracle_pubkey,
        block_timestamp=3,
    )
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _signed_set_position_pair(
    *,
    chain_id: str,
    market_id: str,
    account_a_privkey: int,
    account_b_privkey: int,
    new_a: int,
    new_b: int,
    nonce_a: int,
    nonce_b: int,
) -> dict[str, object]:
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    account_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_b_privkey)
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "set_position_pair",
        "account_a_pubkey": account_a_pubkey,
        "account_b_pubkey": account_b_pubkey,
        "new_position_base_a": int(new_a),
        "new_position_base_b": int(new_b),
        "deadline": 999_999_999,
        "nonce_a": int(nonce_a),
        "nonce_b": int(nonce_b),
    }
    op["sig_a"] = sign_perp_op_for_engine(
        op,
        privkey=account_a_privkey,
        chain_id=chain_id,
        signer_pubkey=account_a_pubkey,
        nonce=nonce_a,
    )
    op["sig_b"] = sign_perp_op_for_engine(
        op,
        privkey=account_b_privkey,
        chain_id=chain_id,
        signer_pubkey=account_b_pubkey,
        nonce=nonce_b,
    )
    return op


def _signed_publish_price(
    *,
    chain_id: str,
    market_id: str,
    oracle_privkey: int,
    price_e8: int,
    oracle_nonce: int,
) -> dict[str, object]:
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(oracle_privkey)
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "publish_clearing_price",
        "price_e8": int(price_e8),
        "deadline": 999_999_999,
        "oracle_nonce": int(oracle_nonce),
    }
    op["oracle_sig"] = sign_perp_op_for_engine(
        op,
        privkey=oracle_privkey,
        chain_id=chain_id,
        signer_pubkey=oracle_pubkey,
        nonce=oracle_nonce,
    )
    return op


def _liquidation_ready_market_state(
    *,
    chain_id: str,
    market_id: str,
    quote_asset: str,
    account_a_privkey: int,
    account_b_privkey: int,
    oracle_privkey: int,
) -> DexState:
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(oracle_privkey)
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    account_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_b_privkey)
    cfg = PerpEngineConfig(chain_id=chain_id, oracle_pubkey=oracle_pubkey)
    state = _settle_ready_market_state(
        chain_id=chain_id,
        market_id=market_id,
        quote_asset=quote_asset,
        account_a_privkey=account_a_privkey,
        account_b_privkey=account_b_privkey,
        oracle_privkey=oracle_privkey,
    )
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [{"module": "TauPerp", "version": "1.0", "market_id": market_id, "action": "settle_epoch"}]},
        tx_sender_pubkey=account_a_pubkey,
        block_timestamp=4,
    )
    assert res.ok, res.error
    assert res.state is not None
    state = res.state
    state.balances.set(account_a_pubkey, quote_asset, 1000)
    state.balances.set(account_b_pubkey, quote_asset, 1000)
    for sender, op in (
        (
            account_a_pubkey,
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": market_id,
                "action": "deposit_collateral",
                "account_pubkey": account_a_pubkey,
                "amount": 100,
            },
        ),
        (
            account_b_pubkey,
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": market_id,
                "action": "deposit_collateral",
                "account_pubkey": account_b_pubkey,
                "amount": 100,
            },
        ),
    ):
        res = apply_perp_ops(config=cfg, state=state, operations={"5": [op]}, tx_sender_pubkey=sender, block_timestamp=5)
        assert res.ok, res.error
        assert res.state is not None
        state = res.state
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={
            "5": [
                _signed_set_position_pair(
                    chain_id=chain_id,
                    market_id=market_id,
                    account_a_privkey=account_a_privkey,
                    account_b_privkey=account_b_privkey,
                    new_a=1000,
                    new_b=-1000,
                    nonce_a=2,
                    nonce_b=2,
                )
            ]
        },
        tx_sender_pubkey=account_a_pubkey,
        block_timestamp=6,
    )
    assert res.ok, res.error
    assert res.state is not None
    state = res.state
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [{"module": "TauPerp", "version": "1.0", "market_id": market_id, "action": "advance_epoch", "delta": 1}]},
        tx_sender_pubkey=account_a_pubkey,
        block_timestamp=7,
    )
    assert res.ok, res.error
    assert res.state is not None
    res = apply_perp_ops(
        config=cfg,
        state=res.state,
        operations={
            "5": [
                _signed_publish_price(
                    chain_id=chain_id,
                    market_id=market_id,
                    oracle_privkey=oracle_privkey,
                    price_e8=105_000_000,
                    oracle_nonce=2,
                )
            ]
        },
        tx_sender_pubkey=oracle_pubkey,
        block_timestamp=8,
    )
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _isolated_liquidation_ready_market_state(
    *,
    market_id: str,
    quote_asset: str,
    account_privkey: int,
) -> DexState:
    account_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_privkey)
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
            "insurance_balance": 100_000,
            "initial_insurance": 100_000,
            "claims_paid": 0,
            "min_notional_for_bounty": 100_000_000,
        }
    )
    market = PerpMarketState(
        quote_asset=quote_asset,
        global_state=global_state,
        accounts={
            account_pubkey: PerpAccountState(
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
        perps=PerpsState(version=PERPS_STATE_VERSION, markets={market_id: market}),
    )


class _TauRpcState:
    def __init__(self, *, app_state_json: str | None = None) -> None:
        self.app_state_json = app_state_json or _initial_app_state_json()
        self.app_hash = "ef" * 32
        self.pending_tx: dict[str, object] | None = None
        self.sequences: dict[str, int] = {}
        self.native_balances: dict[str, int] = {}
        self.command_counts: dict[str, int] = {}
        self.lock = threading.Lock()

    def app_state_payload(self) -> dict[str, object]:
        return {"app_hash": self.app_hash, "app_state": json.loads(self.app_state_json)}

    def apply_pending(self) -> None:
        with self.lock:
            if self.pending_tx is None:
                return
            payload = dict(self.pending_tx)
            sender_wire = str(payload["sender_pubkey"]).lower()
            sender = sender_wire if sender_wire.startswith("0x") else f"0x{sender_wire}"
            sequence_number = int(payload["sequence_number"])
            ops = payload["operations"]
            assert isinstance(ops, dict)
            ok, next_json, app_hash, _patch, err = plugin.apply_app_tx(
                app_state_json=self.app_state_json,
                chain_balances=dict(self.native_balances),
                operations=ops,
                tx_sender_pubkey=sender,
                block_timestamp=int(time.time()),
            )
            assert ok, err
            self.app_state_json = next_json
            self.app_hash = app_hash
            self.sequences[sender_wire] = sequence_number + 1
            self.pending_tx = None


class _TauRpcHandler(socketserver.StreamRequestHandler):
    def handle(self) -> None:
        line = self.rfile.readline().decode("utf-8").strip()
        state: _TauRpcState = self.server.state  # type: ignore[attr-defined]
        command = line.split(" ", 1)[0] if line else ""
        with state.lock:
            state.command_counts[command] = int(state.command_counts.get(command, 0)) + 1
        self._dispatch_line(line)

    def _dispatch_line(self, line: str) -> None:
        state: _TauRpcState = self.server.state  # type: ignore[attr-defined]
        if line == "hello version=1":
            self.wfile.write(b"HELLO: ok\n")
            return
        if line.startswith("getsequence "):
            pubkey = line.split(" ", 1)[1].strip().lower()
            self.wfile.write(f"SEQUENCE: {state.sequences.get(pubkey, 0)}\n".encode("utf-8"))
            return
        if line.startswith("getbalance "):
            pubkey = line.split(" ", 1)[1].strip().lower()
            self.wfile.write(f"BALANCE: {state.native_balances.get(pubkey, 0)}\n".encode("utf-8"))
            return
        if line == "getappstate full":
            self.wfile.write((json.dumps(state.app_state_payload(), sort_keys=True) + "\n").encode("utf-8"))
            return
        if line.startswith("sendtx "):
            payload = json.loads(line.split(" ", 1)[1])
            with state.lock:
                state.pending_tx = payload
            self.wfile.write(b"SUCCESS tx accepted\n")
            return
        if line == "createblock":
            state.apply_pending()
            self.wfile.write(b"BLOCK created\n")
            return
        self.wfile.write(b"ERR unsupported\n")


class _TauRpcPartialSendTimeoutHandler(_TauRpcHandler):
    def handle(self) -> None:
        line = self.rfile.readline().decode("utf-8").strip()
        if line.startswith("sendtx "):
            self.wfile.write(b"PARTIAL_PRIVATE_RESPONSE")
            self.wfile.flush()
            time.sleep(1.0)
            return
        self._dispatch_line(line)


class _TauRpcSendDropBeforeResponseHandler(_TauRpcHandler):
    def handle(self) -> None:
        line = self.rfile.readline().decode("utf-8").strip()
        if line.startswith("sendtx "):
            return
        self._dispatch_line(line)


class _TauRpcDelayedSendSuccessHandler(_TauRpcHandler):
    def handle(self) -> None:
        line = self.rfile.readline().decode("utf-8").strip()
        if line.startswith("sendtx "):
            time.sleep(float(getattr(self.server, "send_delay_s", 0.0)))
        self._dispatch_line(line)


class _TauRpcGatedSendSuccessHandler(_TauRpcHandler):
    def _dispatch_line(self, line: str) -> None:
        if line.startswith("sendtx "):
            state: _TauRpcState = self.server.state  # type: ignore[attr-defined]
            payload = json.loads(line.split(" ", 1)[1])
            with state.lock:
                state.pending_tx = payload
            gate = getattr(self.server, "send_response_event", None)
            if gate is not None:
                assert gate.wait(timeout=10.0)
            self.wfile.write(b"SUCCESS tx accepted\n")
            return
        super()._dispatch_line(line)


def test_perps_wallet_ui_smoke_through_browser(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui"
    account_a_privkey = 83
    account_b_privkey = 84
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    account_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_b_privkey)
    recovery_guardian_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(185)
    recovery_guardian_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(186)
    wallet_profile = _perps_wallet_authority_profile(
        chain_id=chain_id,
        account_a_pubkey=account_a_pubkey,
        account_b_pubkey=account_b_pubkey,
        guardian_a_pubkey=recovery_guardian_a_pubkey,
        guardian_b_pubkey=recovery_guardian_b_pubkey,
    )
    from tools.zenoctl_testnet_local.fixtures import _perps_wallet_encrypted_sss_backup_bundle

    encrypted_sss_bundle = _perps_wallet_encrypted_sss_backup_bundle(
        chain_id=chain_id,
        wallet_authority_hash=str(wallet_profile["wallet_authority_hash"]),
        subject_key_id="perps-wallet-a",
        subject_privkey=account_a_privkey.to_bytes(32, "big"),
        fixture_seed=b"perps-wallet-ui-governance-sss",
    )
    encrypted_sss_backup = encrypted_sss_bundle["backup"]
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui"

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState()  # type: ignore[attr-defined]
    tau_server.state.sequences[account_a_pubkey[2:].lower()] = 4  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_a_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
        "ZENODEX_ENV": "local",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON": json.dumps(wallet_profile, sort_keys=True),
        "PERPS_WALLET_RECOVERY_EXERCISE_JSON": json.dumps(
            _perps_wallet_recovery_exercise(chain_id=chain_id),
            sort_keys=True,
        ),
        "PERPS_WALLET_ROTATION_EXERCISE_JSON": json.dumps(
            _perps_wallet_rotation_exercise(chain_id=chain_id, account_b_pubkey=account_b_pubkey),
            sort_keys=True,
        ),
        "PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_JSON": json.dumps(
            _perps_wallet_device_approval_exercise(chain_id=chain_id),
            sort_keys=True,
        ),
        "PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_JSON": json.dumps(
            _perps_wallet_signer_device_integration(chain_id=chain_id),
            sort_keys=True,
        ),
        "PERPS_WALLET_SIGNER_PROMPT_CAPTURE_JSON": json.dumps(
            _perps_wallet_signer_prompt_capture(chain_id=chain_id),
            sort_keys=True,
        ),
        "PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_JSON": json.dumps(
            _perps_wallet_signer_execution_exercise(chain_id=chain_id),
            sort_keys=True,
        ),
        "PERPS_WALLET_ENCRYPTED_SSS_BACKUP_JSON": json.dumps(encrypted_sss_backup, sort_keys=True),
        "PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_JSON": json.dumps(
            encrypted_sss_bundle["recipient_keys"],
            sort_keys=True,
        ),
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false", "CHOKIDAR_USEPOLLING": "1"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        url = _smoke_url(
            vite_base,
            query={
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "init_market_2p",
                "marketId": market_id,
                "quoteAsset": quote_asset,
                "txFeeLimit": "2",
                "perpsDeadline": str(int(time.time()) + 3600),
            },
            secrets={
                "accountAPrivkey": account_a_privkey,
                "accountBPrivkey": account_b_privkey,
            },
        )
        chrome_profile = tmp_path / "chrome-profile"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=50000",
                "--dump-dom",
                url,
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=80,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Live Perps Wallet" in dom
        assert "Stream" in dom
        assert "submit accepted" in dom
        assert "preflight ok" in dom
        assert "fee limit 2" in dom
        assert "fee covered yes" in dom
        assert "proof profile perps_stream8_live_wallet_v0" in dom
        assert "proof receipt 0x" in dom
        assert "zk proof pending" in dom
        assert "delta witness 1" in dom
        assert "wallet authority ready" in dom
        assert "wallet keys 2" in dom
        assert "wallet recovery 2/2" in dom
        assert "recovery exercise ready" in dom
        assert "recovery signed quorum 2/2" in dom
        assert "recovery receipt 0x" in dom
        assert "rotation exercise ready" in dom
        assert "rotation signed quorum 2/2" in dom
        assert "rotation receipt 0x" in dom
        assert "device approval ready" in dom
        assert "device sign admission ok" in dom
        assert "device approval receipt 0x" in dom
        assert "signer device ready" in dom
        assert "signer backend os-keychain" in dom
        assert "signer device receipt 0x" in dom
        assert "signer prompt capture ready" in dom
        assert "prompt capture source operator-audit-log" in dom
        assert "signer prompt capture receipt 0x" in dom
        assert "signer execution ready" in dom
        assert "signer prompt os-prompt:wallet-a:epoch-13" in dom
        assert "signer execution receipt 0x" in dom
        assert "signer ceremony ready" in dom
        assert "ceremony execution tau-submit:wallet-a:epoch-13" in dom
        assert "signer ceremony receipt 0x" in dom
        assert market_id in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_governance_smoke_through_browser(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "zeno-ledger-localtest-ui-gov"
    account_a_privkey = 83
    account_b_privkey = 84
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    account_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_b_privkey)
    recovery_guardian_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(185)
    recovery_guardian_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(186)
    wallet_profile = _perps_wallet_authority_profile(
        chain_id=chain_id,
        account_a_pubkey=account_a_pubkey,
        account_b_pubkey=account_b_pubkey,
        guardian_a_pubkey=recovery_guardian_a_pubkey,
        guardian_b_pubkey=recovery_guardian_b_pubkey,
    )
    from tools.zenoctl_testnet_local.fixtures import _perps_wallet_encrypted_sss_backup_bundle

    encrypted_sss_bundle = _perps_wallet_encrypted_sss_backup_bundle(
        chain_id=chain_id,
        wallet_authority_hash=str(wallet_profile["wallet_authority_hash"]),
        subject_key_id="perps-wallet-a",
        subject_privkey=account_a_privkey.to_bytes(32, "big"),
        fixture_seed=b"perps-wallet-ui-governance-sss",
    )
    encrypted_sss_backup = encrypted_sss_bundle["backup"]

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState()  # type: ignore[attr-defined]
    tau_server.state.sequences[account_a_pubkey[2:].lower()] = 4  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_a_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
        "ZENODEX_ENV": "local",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON": json.dumps(wallet_profile, sort_keys=True),
        "PERPS_WALLET_RECOVERY_EXERCISE_JSON": json.dumps(
            _perps_wallet_recovery_exercise(chain_id=chain_id),
            sort_keys=True,
        ),
        "PERPS_WALLET_ROTATION_EXERCISE_JSON": json.dumps(
            _perps_wallet_rotation_exercise(chain_id=chain_id, account_b_pubkey=account_b_pubkey),
            sort_keys=True,
        ),
        "PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_JSON": json.dumps(
            _perps_wallet_device_approval_exercise(chain_id=chain_id),
            sort_keys=True,
        ),
        "PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_JSON": json.dumps(
            _perps_wallet_signer_device_integration(chain_id=chain_id),
            sort_keys=True,
        ),
        "PERPS_WALLET_SIGNER_PROMPT_CAPTURE_JSON": json.dumps(
            _perps_wallet_signer_prompt_capture(chain_id=chain_id),
            sort_keys=True,
        ),
        "PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_JSON": json.dumps(
            _perps_wallet_signer_execution_exercise(chain_id=chain_id),
            sort_keys=True,
        ),
        "PERPS_WALLET_ENCRYPTED_SSS_BACKUP_JSON": json.dumps(encrypted_sss_backup, sort_keys=True),
        "PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_JSON": json.dumps(
            encrypted_sss_bundle["recipient_keys"],
            sort_keys=True,
        ),
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false", "CHOKIDAR_USEPOLLING": "1"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    config_file = DEX_UI / "public" / "zenodex-config.json"
    original_config = config_file.read_text(encoding="utf-8") if config_file.exists() else None
    try:
        gov_fixtures = {
            "recoveryExercise": _perps_wallet_recovery_exercise(chain_id=chain_id),
            "rotationExercise": _perps_wallet_rotation_exercise(chain_id=chain_id, account_b_pubkey=account_b_pubkey),
            "deviceApprovalExercise": _perps_wallet_device_approval_exercise(chain_id=chain_id),
            "signerDeviceIntegration": _perps_wallet_signer_device_integration(chain_id=chain_id),
            "encryptedSssBackup": encrypted_sss_backup,
        }
        test_config = {
            "apiBase": "",
            "demoMode": False,
            "deployment": "local-testnet",
            "oracleApiBase": "",
            "zenoOracleApiBase": "",
            "localTestnetGovernanceFixtures": gov_fixtures,
            "localTestnetZkPosture": {
                "zk_mode_requested": "auto-strict",
                "zk_mode_effective": "open",
                "zk_required": False,
                "zk_fallback_reason": "proof verifier command unavailable",
                "proof_verifier_kind": "disabled",
                "proof_artifact_hashes": {},
                "production_security_claim": False,
            },
        }
        config_file.write_text(json.dumps(test_config, indent=2), encoding="utf-8")

        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode(
            {
                "tab": "governance",
                "demo": "false",
                "zenodexUiSmokeGovernance": "1",
                "zenodexUiSmokeSssDelivery": "1",
            }
        )
        chrome_profile = tmp_path / "chrome-profile-gov"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=50000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=80,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Keys &amp; Governance" in dom or "Keys & Governance" in dom
        assert "Wallet authority ready" in dom
        assert "Recovery evaluation ready" in dom
        assert "Rotation evaluation ready" in dom
        assert "Device approval ready" in dom
        assert "Signer device ready" in dom
        assert "Encrypted SSS ready" in dom
        assert "fixture evidence ready" in dom
        assert "provider adapter required" in dom
        assert "SSS provider delivery is wired to the backend" in dom
        assert "encrypted_sss_delivery_provider_not_configured:" in dom
        assert "Deliver" in dom
        assert "SSS external delivery is not implemented for local-testnet" not in dom
        assert "local provider receipts ready" not in dom
        assert "SMTP receipt ready" not in dom
        assert "Dropbox receipt ready" not in dom
        assert "Box receipt ready" not in dom
        assert "Export receipt ready" not in dom
        assert "Download Fixture Backup" in dom
        assert "Evaluate Fixture Backup" in dom
        assert "open requested auto-strict" in dom
    finally:
        if original_config is not None:
            config_file.write_text(original_config, encoding="utf-8")
        elif config_file.exists():
            config_file.unlink()

        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_renders_ready_hardware_custody(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-hardware"
    account_a_privkey = 83
    account_b_privkey = 84
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    account_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_b_privkey)
    recovery_guardian_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(185)
    recovery_guardian_b_pubkey = "0x" + bls_pubkey_hex_from_privkey(186)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-hardware"

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState()  # type: ignore[attr-defined]
    tau_server.state.sequences[account_a_pubkey[2:].lower()] = 4  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_a_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
        "ZENODEX_ENV": "local",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "PERPS_WALLET_AUTHORITY_PROFILE_JSON": json.dumps(
            _perps_wallet_authority_profile(
                chain_id=chain_id,
                account_a_pubkey=account_a_pubkey,
                account_b_pubkey=account_b_pubkey,
                guardian_a_pubkey=recovery_guardian_a_pubkey,
                guardian_b_pubkey=recovery_guardian_b_pubkey,
            ),
            sort_keys=True,
        ),
        "PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_JSON": json.dumps(
            {
                **_perps_wallet_device_approval_exercise(chain_id=chain_id),
                "backend_descriptor": _perps_wallet_hardware_backend_descriptor(chain_id=chain_id),
                "environment": _perps_wallet_hardware_environment(chain_id=chain_id),
                "environment_policy": _perps_wallet_hardware_environment_policy(chain_id=chain_id),
                "exercise_hash": perps_wallet_device_approval_exercise_hash_v1(
                    {
                        **_perps_wallet_device_approval_exercise(chain_id=chain_id),
                        "schema": PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_SCHEMA_V1,
                        "backend_descriptor": _perps_wallet_hardware_backend_descriptor(chain_id=chain_id),
                        "environment": _perps_wallet_hardware_environment(chain_id=chain_id),
                        "environment_policy": _perps_wallet_hardware_environment_policy(chain_id=chain_id),
                    }
                ),
            },
            sort_keys=True,
        ),
        "PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_JSON": json.dumps(
            {
                **_perps_wallet_signer_device_integration(chain_id=chain_id),
                "backend_descriptor": _perps_wallet_hardware_backend_descriptor(chain_id=chain_id),
                "environment": _perps_wallet_hardware_environment(chain_id=chain_id),
                "environment_policy": _perps_wallet_hardware_environment_policy(chain_id=chain_id),
                "device_label": "Hardware Wallet A",
                "integration_hash": perps_wallet_signer_device_integration_hash_v1(
                    {
                        **_perps_wallet_signer_device_integration(chain_id=chain_id),
                        "schema": "zenodex/perps-wallet-signer-device-integration/v1",
                        "backend_descriptor": _perps_wallet_hardware_backend_descriptor(chain_id=chain_id),
                        "environment": _perps_wallet_hardware_environment(chain_id=chain_id),
                        "environment_policy": _perps_wallet_hardware_environment_policy(chain_id=chain_id),
                        "device_label": "Hardware Wallet A",
                    }
                ),
            },
            sort_keys=True,
        ),
        "PERPS_WALLET_SIGNER_PROMPT_CAPTURE_JSON": json.dumps(
            {
                **_perps_wallet_signer_prompt_capture(chain_id=chain_id),
                "backend_descriptor": _perps_wallet_hardware_backend_descriptor(chain_id=chain_id),
                "environment": _perps_wallet_hardware_environment(chain_id=chain_id),
                "environment_policy": _perps_wallet_hardware_environment_policy(chain_id=chain_id),
                "device_label": "Hardware Wallet A",
                "prompt_source": "hardware-wallet-prompt",
                "capture_hash": perps_wallet_signer_prompt_capture_hash_v1(
                    {
                        **_perps_wallet_signer_prompt_capture(chain_id=chain_id),
                        "schema": PERPS_WALLET_SIGNER_PROMPT_CAPTURE_SCHEMA_V1,
                        "backend_descriptor": _perps_wallet_hardware_backend_descriptor(chain_id=chain_id),
                        "environment": _perps_wallet_hardware_environment(chain_id=chain_id),
                        "environment_policy": _perps_wallet_hardware_environment_policy(chain_id=chain_id),
                        "device_label": "Hardware Wallet A",
                        "prompt_source": "hardware-wallet-prompt",
                    }
                ),
            },
            sort_keys=True,
        ),
        "PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_JSON": json.dumps(
            {
                **_perps_wallet_signer_execution_exercise(chain_id=chain_id),
                "backend_descriptor": _perps_wallet_hardware_backend_descriptor(chain_id=chain_id),
                "environment": _perps_wallet_hardware_environment(chain_id=chain_id),
                "environment_policy": _perps_wallet_hardware_environment_policy(chain_id=chain_id),
                "device_label": "Hardware Wallet A",
                "exercise_hash": perps_wallet_signer_execution_exercise_hash_v1(
                    {
                        **_perps_wallet_signer_execution_exercise(chain_id=chain_id),
                        "schema": PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_SCHEMA_V1,
                        "backend_descriptor": _perps_wallet_hardware_backend_descriptor(chain_id=chain_id),
                        "environment": _perps_wallet_hardware_environment(chain_id=chain_id),
                        "environment_policy": _perps_wallet_hardware_environment_policy(chain_id=chain_id),
                        "device_label": "Hardware Wallet A",
                    }
                ),
            },
            sort_keys=True,
        ),
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false", "CHOKIDAR_USEPOLLING": "1"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        url = _smoke_url(
            vite_base,
            query={
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "init_market_2p",
                "marketId": market_id,
                "quoteAsset": quote_asset,
                "txFeeLimit": "2",
                "perpsDeadline": str(int(time.time()) + 3600),
            },
            secrets={
                "accountAPrivkey": account_a_privkey,
                "accountBPrivkey": account_b_privkey,
            },
        )
        chrome_profile = tmp_path / "chrome-profile-hardware"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=50000",
                "--dump-dom",
                url,
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=80,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "hardware custody ready" in dom
        assert "hardware backend hardware-wallet-placeholder" in dom
        assert "hardware custody receipt 0x" in dom
        assert "signer ceremony ready" in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_accepts_external_signed_payload_without_local_signing(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-external"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(85)
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-external"
    deadline = int(time.time()) + 3600
    sequence_number = 7
    deposit_amount = 125

    dex_state = _advanced_market_state(
        chain_id=chain_id,
        market_id=market_id,
        quote_asset=quote_asset,
        account_a_privkey=account_a_privkey,
        account_b_privkey=account_b_privkey,
        oracle_pubkey=oracle_pubkey,
    )
    dex_state.balances.set(account_a_pubkey, quote_asset, 1000)
    app_state_json = _initial_app_state_json(dex_state)
    signed_payload = build_signed_tau_transaction(
        privkey=account_a_privkey,
        sequence_number=sequence_number,
        expiration_time=deadline,
        operations={
            "8": [
                {
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": market_id,
                    "action": "deposit_collateral",
                    "account_pubkey": account_a_pubkey,
                    "amount": deposit_amount,
                }
            ]
        },
        fee_limit=2,
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[account_a_pubkey[2:].lower()] = sequence_number  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_a_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
        "ZENODEX_ENV": "local",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "false",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false", "CHOKIDAR_USEPOLLING": "1"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "deposit_collateral",
                "marketId": market_id,
                "accountPubkey": account_a_pubkey,
                "amount": str(deposit_amount),
                "txFeeLimit": "2",
                "perpsDeadline": str(deadline),
                "signedTauTxPayload": json.dumps(signed_payload, sort_keys=True, separators=(",", ":")),
            }
        )
        dom = _chrome_rendered_haystack(
            chrome=chrome,
            url=f"{vite_base}/?{query}",
            profile=tmp_path / "chrome-profile-external-signed",
            snippets=(
                "Live Perps Wallet",
                "Deposit Collateral",
                "submit accepted",
                "signing external_signed_payload",
            ),
            timeout_s=60,
        )
        assert "Live Perps Wallet" in dom
        assert "Deposit Collateral" in dom
        assert "submit accepted" in dom
        assert "preflight ok" in dom
        assert "fee limit 2" in dom
        assert "fee covered yes" in dom
        assert "signing external_signed_payload" in dom
        assert "posted A 12500000000" in dom
        assert "quote A 875" in dom
        assert market_id in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_succeeds_under_bounded_tau_send_jitter(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-jitter"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(85)
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-jitter"
    deadline = int(time.time()) + 3600
    sequence_number = 7
    deposit_amount = 125

    dex_state = _advanced_market_state(
        chain_id=chain_id,
        market_id=market_id,
        quote_asset=quote_asset,
        account_a_privkey=account_a_privkey,
        account_b_privkey=account_b_privkey,
        oracle_pubkey=oracle_pubkey,
    )
    dex_state.balances.set(account_a_pubkey, quote_asset, 1000)
    app_state_json = _initial_app_state_json(dex_state)
    signed_payload = build_signed_tau_transaction(
        privkey=account_a_privkey,
        sequence_number=sequence_number,
        expiration_time=deadline,
        operations={
            "8": [
                {
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": market_id,
                    "action": "deposit_collateral",
                    "account_pubkey": account_a_pubkey,
                    "amount": deposit_amount,
                }
            ]
        },
        fee_limit=2,
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcDelayedSendSuccessHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[account_a_pubkey[2:].lower()] = sequence_number  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_a_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_server.send_delay_s = 0.15  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
        "ZENODEX_ENV": "local",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "false",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "PERPS_WALLET_TAU_TIMEOUT_S": "2.0",
        "TAU_DEX_CHAIN_ID": chain_id,
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false", "CHOKIDAR_USEPOLLING": "1"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "deposit_collateral",
                "marketId": market_id,
                "accountPubkey": account_a_pubkey,
                "amount": str(deposit_amount),
                "txFeeLimit": "2",
                "perpsDeadline": str(deadline),
                "signedTauTxPayload": json.dumps(signed_payload, sort_keys=True, separators=(",", ":")),
            }
        )
        dom = _chrome_rendered_haystack(
            chrome=chrome,
            url=f"{vite_base}/?{query}",
            profile=tmp_path / "chrome-profile-perps-jitter",
            snippets=(
                "Live Perps Wallet",
                "Tau node connected",
                "submit accepted",
            ),
            timeout_s=80,
        )
        assert "Live Perps Wallet" in dom
        assert "Tau node connected" in dom
        assert "submit accepted" in dom
        assert "posted A 12500000000" in dom
        rpc_state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
        assert json.loads(rpc_state.app_state_json) != json.loads(app_state_json)
        assert rpc_state.pending_tx is None
        assert rpc_state.sequences[account_a_pubkey[2:].lower()] == sequence_number + 1
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        tau_thread.join(timeout=2.0)
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_fails_closed_on_tau_send_drop_before_response(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-send-drop"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(85)
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-send-drop"
    deadline = int(time.time()) + 3600
    sequence_number = 7
    deposit_amount = 125

    dex_state = _advanced_market_state(
        chain_id=chain_id,
        market_id=market_id,
        quote_asset=quote_asset,
        account_a_privkey=account_a_privkey,
        account_b_privkey=account_b_privkey,
        oracle_pubkey=oracle_pubkey,
    )
    dex_state.balances.set(account_a_pubkey, quote_asset, 1000)
    app_state_json = _initial_app_state_json(dex_state)
    operations = {
        "8": [
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": market_id,
                "action": "deposit_collateral",
                "account_pubkey": account_a_pubkey,
                "amount": deposit_amount,
            }
        ]
    }
    signed_payload = build_signed_tau_transaction(
        privkey=account_a_privkey,
        sequence_number=sequence_number,
        expiration_time=deadline,
        operations=operations,
        fee_limit=2,
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcSendDropBeforeResponseHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[account_a_pubkey[2:].lower()] = sequence_number  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_a_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
        "ZENODEX_ENV": "local",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "false",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "PERPS_WALLET_TAU_TIMEOUT_S": "0.5",
        "TAU_DEX_CHAIN_ID": chain_id,
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false", "CHOKIDAR_USEPOLLING": "1"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)

        submit_body = {
            "action": "deposit_collateral",
            "market_id": market_id,
            "account_pubkey": account_a_pubkey,
            "amount": deposit_amount,
            "tx_fee_limit": "2",
            "deadline": deadline,
            "signed_tau_tx_payload": signed_payload,
        }
        status, api_rejected = _post_json_status(api_base + "/api/perps/wallet/submit", submit_body)
        api_error_text = json.dumps(api_rejected, sort_keys=True)
        assert status == 502
        assert api_rejected["ok"] is False
        assert api_rejected["error"] == "tau_rpc_error"
        assert "deposit_collateral" not in api_error_text
        assert "sender_pubkey" not in api_error_text
        assert "signature" not in api_error_text
        rpc_state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
        assert json.loads(rpc_state.app_state_json) == json.loads(app_state_json)
        assert rpc_state.pending_tx is None
        assert rpc_state.sequences[account_a_pubkey[2:].lower()] == sequence_number

        query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "deposit_collateral",
                "marketId": market_id,
                "accountPubkey": account_a_pubkey,
                "amount": str(deposit_amount),
                "txFeeLimit": "2",
                "perpsDeadline": str(deadline),
                "signedTauTxPayload": json.dumps(signed_payload, sort_keys=True, separators=(",", ":")),
            }
        )
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={tmp_path / 'chrome-profile-perps-send-drop'}",
                "--virtual-time-budget=20000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Live Perps Wallet" in dom
        assert "Tau node connected" in dom
        assert "tau_rpc_error" in dom, dom[-8000:]
        assert json.loads(rpc_state.app_state_json) == json.loads(app_state_json)
        assert rpc_state.pending_tx is None
        assert rpc_state.sequences[account_a_pubkey[2:].lower()] == sequence_number
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        tau_thread.join(timeout=2.0)
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_fails_closed_on_truncated_proxy_sendtx_response(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-proxy-truncate"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(85)
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-proxy-truncate"
    deadline = int(time.time()) + 3600
    sequence_number = 7
    deposit_amount = 125

    dex_state = _advanced_market_state(
        chain_id=chain_id,
        market_id=market_id,
        quote_asset=quote_asset,
        account_a_privkey=account_a_privkey,
        account_b_privkey=account_b_privkey,
        oracle_pubkey=oracle_pubkey,
    )
    dex_state.balances.set(account_a_pubkey, quote_asset, 1000)
    app_state_json = _initial_app_state_json(dex_state)
    signed_payload = build_signed_tau_transaction(
        privkey=account_a_privkey,
        sequence_number=sequence_number,
        expiration_time=deadline,
        operations={
            "8": [
                {
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": market_id,
                    "action": "deposit_collateral",
                    "account_pubkey": account_a_pubkey,
                    "amount": deposit_amount,
                }
            ]
        },
        fee_limit=2,
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[account_a_pubkey[2:].lower()] = sequence_number  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_a_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()
    proxy = TauRpcFaultProxy(
        upstream_host="127.0.0.1",
        upstream_port=tau_port,
        truncate_sendtx_response_bytes=7,
    ).start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
        "ZENODEX_ENV": "local",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "false",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": proxy.host,
        "PERPS_WALLET_TAU_PORT": str(proxy.port),
        "PERPS_WALLET_TAU_TIMEOUT_S": "1.0",
        "TAU_DEX_CHAIN_ID": chain_id,
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false", "CHOKIDAR_USEPOLLING": "1"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)

        submit_body = {
            "action": "deposit_collateral",
            "market_id": market_id,
            "account_pubkey": account_a_pubkey,
            "amount": deposit_amount,
            "tx_fee_limit": "2",
            "deadline": deadline,
            "signed_tau_tx_payload": signed_payload,
        }
        status, api_rejected = _post_json_status(api_base + "/api/perps/wallet/submit", submit_body)
        assert status == 502
        assert api_rejected["ok"] is False
        assert api_rejected["error"] == "tau_rpc_error"
        rpc_state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
        assert json.loads(rpc_state.app_state_json) == json.loads(app_state_json)
        assert rpc_state.pending_tx is not None
        assert rpc_state.sequences[account_a_pubkey[2:].lower()] == sequence_number
        stats = proxy.stats()
        assert stats.sendtx_requests == 1
        assert stats.truncated_sendtx_responses == 1

        query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "deposit_collateral",
                "marketId": market_id,
                "accountPubkey": account_a_pubkey,
                "amount": str(deposit_amount),
                "txFeeLimit": "2",
                "perpsDeadline": str(deadline),
                "signedTauTxPayload": json.dumps(signed_payload, sort_keys=True, separators=(",", ":")),
            }
        )
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={tmp_path / 'chrome-profile-perps-proxy-truncate'}",
                "--virtual-time-budget=20000",
                "--dump-dom",
                f"{vite_base}/?{query}",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Live Perps Wallet" in dom
        assert "Tau node connected" in dom
        assert "tau_rpc_error" in dom, dom[-8000:]
        assert "SUCCESS tx accepted" not in dom
        assert json.loads(rpc_state.app_state_json) == json.loads(app_state_json)
        assert rpc_state.pending_tx is not None
        assert rpc_state.sequences[account_a_pubkey[2:].lower()] == sequence_number
        stats = proxy.stats()
        assert stats.sendtx_requests == 2
        assert stats.truncated_sendtx_responses == 2
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        vite_proc.terminate()
        api_proc.terminate()
        proxy.close()
        tau_server.shutdown()
        tau_server.server_close()
        tau_thread.join(timeout=2.0)
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


@requires_toxiproxy
def test_perps_wallet_ui_fails_closed_through_toxiproxy_limit_data(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-toxiproxy"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(85)
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-toxiproxy"
    deadline = int(time.time()) + 3600
    sequence_number = 7
    deposit_amount = 125

    dex_state = _advanced_market_state(
        chain_id=chain_id,
        market_id=market_id,
        quote_asset=quote_asset,
        account_a_privkey=account_a_privkey,
        account_b_privkey=account_b_privkey,
        oracle_pubkey=oracle_pubkey,
    )
    dex_state.balances.set(account_a_pubkey, quote_asset, 1000)
    app_state_json = _initial_app_state_json(dex_state)
    signed_payload = build_signed_tau_transaction(
        privkey=account_a_privkey,
        sequence_number=sequence_number,
        expiration_time=deadline,
        operations={
            "8": [
                {
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": market_id,
                    "action": "deposit_collateral",
                    "account_pubkey": account_a_pubkey,
                    "amount": deposit_amount,
                }
            ]
        },
        fee_limit=2,
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("0.0.0.0", tau_port), _TauRpcGatedSendSuccessHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[account_a_pubkey[2:].lower()] = sequence_number  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_a_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_server.send_response_event = threading.Event()  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    api_proc: subprocess.Popen[str] | None = None
    vite_proc: subprocess.Popen[str] | None = None
    chrome_proc: subprocess.Popen[str] | None = None
    try:
        os.environ["TAU_DEX_CHAIN_ID"] = chain_id
        with ToxiproxyHarness(upstream_host="0.0.0.0", upstream_port=tau_port) as toxiproxy:
            api_port = _free_port()
            api_base = f"http://127.0.0.1:{api_port}"
            api_env = {
                **os.environ,
                "API_HOST": "127.0.0.1",
                "API_PORT": str(api_port),
                "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
                "PERPS_API_ENABLED": "true",
                "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
                "ZENODEX_ENV": "local",
                "PERPS_WALLET_API_ENABLED": "true",
                "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "false",
                "PERPS_WALLET_AUTO_MINE": "true",
                "PERPS_WALLET_CHAIN_ID": chain_id,
                "PERPS_WALLET_TAU_HOST": toxiproxy.listen_host,
                "PERPS_WALLET_TAU_PORT": str(toxiproxy.listen_port),
                "PERPS_WALLET_TAU_TIMEOUT_S": "1.0",
                "TAU_DEX_CHAIN_ID": chain_id,
            }
            api_proc = subprocess.Popen(
                ["python3", "-m", "src.integration.api_server"],
                cwd=ROOT,
                env=api_env,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )

            vite_port = _free_port()
            vite_base = f"http://127.0.0.1:{vite_port}"
            vite_proc = subprocess.Popen(
                ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
                cwd=DEX_UI,
                env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false", "CHOKIDAR_USEPOLLING": "1"},
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )

            _wait_for_http(api_base + "/health", timeout_s=30)
            _wait_for_http(vite_base, timeout_s=30)

            getappstate_before = _tau_command_count(tau_server, "getappstate")
            query = urlencode(
                {
                    "tab": "perps",
                    "demo": "false",
                    "zenodexUiSmokePerpsWallet": "1",
                    "perpsWalletAction": "deposit_collateral",
                    "marketId": market_id,
                    "accountPubkey": account_a_pubkey,
                    "amount": str(deposit_amount),
                    "txFeeLimit": "2",
                    "perpsDeadline": str(deadline),
                    "signedTauTxPayload": json.dumps(signed_payload, sort_keys=True, separators=(",", ":")),
                }
            )
            chrome_proc = subprocess.Popen(
                [
                    chrome,
                    "--headless=new",
                    "--disable-gpu",
                    "--no-sandbox",
                    f"--user-data-dir={tmp_path / 'chrome-profile-perps-toxiproxy-limit-data'}",
                    "--virtual-time-budget=22000",
                    "--dump-dom",
                    f"{vite_base}/?{query}",
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            _wait_for_tau_command_count(tau_server, "getappstate", getappstate_before + 1)
            _wait_for_tau_command_count(tau_server, "sendtx", 1)
            toxiproxy.limit_data(7)
            tau_server.send_response_event.set()  # type: ignore[attr-defined]
            stdout, stderr = chrome_proc.communicate(timeout=70)
            assert chrome_proc.returncode == 0, stderr[-2000:]
            dom = stdout
            assert "Live Perps Wallet" in dom
            assert "Tau node connected" in dom
            assert "tau_rpc_error" in dom, dom[-8000:]
            assert "SUCCESS tx accepted" not in dom
            rpc_state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
            assert json.loads(rpc_state.app_state_json) == json.loads(app_state_json)
            assert rpc_state.pending_tx is not None
            assert rpc_state.sequences[account_a_pubkey[2:].lower()] == sequence_number
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        if chrome_proc is not None and chrome_proc.poll() is None:
            chrome_proc.kill()
            chrome_proc.wait(timeout=5)
        for proc in (vite_proc, api_proc):
            if proc is None:
                continue
            proc.terminate()
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)
        tau_server.shutdown()
        tau_server.server_close()
        tau_thread.join(timeout=2.0)


def test_perps_wallet_ui_fails_closed_on_partial_tau_send_timeout(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-chaos"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(85)
    account_a_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_a_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-chaos"
    deadline = int(time.time()) + 3600
    sequence_number = 7
    deposit_amount = 125

    dex_state = _advanced_market_state(
        chain_id=chain_id,
        market_id=market_id,
        quote_asset=quote_asset,
        account_a_privkey=account_a_privkey,
        account_b_privkey=account_b_privkey,
        oracle_pubkey=oracle_pubkey,
    )
    dex_state.balances.set(account_a_pubkey, quote_asset, 1000)
    app_state_json = _initial_app_state_json(dex_state)
    operations = {
        "8": [
            {
                "module": "TauPerp",
                "version": "1.0",
                "market_id": market_id,
                "action": "deposit_collateral",
                "account_pubkey": account_a_pubkey,
                "amount": deposit_amount,
            }
        ]
    }
    signed_payload = build_signed_tau_transaction(
        privkey=account_a_privkey,
        sequence_number=sequence_number,
        expiration_time=deadline,
        operations=operations,
        fee_limit=2,
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcPartialSendTimeoutHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[account_a_pubkey[2:].lower()] = sequence_number  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_a_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
        "ZENODEX_ENV": "local",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "false",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "PERPS_WALLET_TAU_TIMEOUT_S": "0.2",
        "TAU_DEX_CHAIN_ID": chain_id,
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false", "CHOKIDAR_USEPOLLING": "1"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)

        submit_body = {
            "action": "deposit_collateral",
            "market_id": market_id,
            "account_pubkey": account_a_pubkey,
            "amount": deposit_amount,
            "tx_fee_limit": "2",
            "deadline": deadline,
            "signed_tau_tx_payload": signed_payload,
        }
        status, api_rejected = _post_json_status(api_base + "/api/perps/wallet/submit", submit_body)
        assert status == 502
        assert api_rejected["ok"] is False
        assert api_rejected["error"] == "tau_rpc_error"
        assert "PARTIAL_PRIVATE_RESPONSE" not in json.dumps(api_rejected, sort_keys=True)
        rpc_state: _TauRpcState = tau_server.state  # type: ignore[attr-defined]
        assert json.loads(rpc_state.app_state_json) == json.loads(app_state_json)
        assert rpc_state.pending_tx is None
        assert rpc_state.sequences[account_a_pubkey[2:].lower()] == sequence_number

        query = urlencode(
            {
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "deposit_collateral",
                "marketId": market_id,
                "accountPubkey": account_a_pubkey,
                "amount": str(deposit_amount),
                "txFeeLimit": "2",
                "perpsDeadline": str(deadline),
                "signedTauTxPayload": json.dumps(signed_payload, sort_keys=True, separators=(",", ":")),
            }
        )
        dom = _chrome_rendered_haystack(
            chrome=chrome,
            url=f"{vite_base}/?{query}",
            profile=tmp_path / "chrome-profile-perps-chaos",
            snippets=("Live Perps Wallet", "Tau node connected", "tau_rpc_error"),
            timeout_s=60,
        )
        assert "Live Perps Wallet" in dom
        assert "Tau node connected" in dom
        assert "tau_rpc_error" in dom, dom[-8000:]
        assert "PARTIAL_PRIVATE_RESPONSE" not in dom
        assert json.loads(rpc_state.app_state_json) == json.loads(app_state_json)
        assert rpc_state.pending_tx is None
        assert rpc_state.sequences[account_a_pubkey[2:].lower()] == sequence_number
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        tau_thread.join(timeout=2.0)
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_publish_price_smoke_through_browser(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-price"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_privkey = 85
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(oracle_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-price"
    app_state_json = _initial_app_state_json(
        _advanced_market_state(
            chain_id=chain_id,
            market_id=market_id,
            quote_asset=quote_asset,
            account_a_privkey=account_a_privkey,
            account_b_privkey=account_b_privkey,
            oracle_pubkey=oracle_pubkey,
        )
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[oracle_pubkey[2:].lower()] = 6  # type: ignore[attr-defined]
    tau_server.state.native_balances[oracle_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
        "ZENODEX_ENV": "local",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_DEX_PERP_ORACLE_PUBKEY": oracle_pubkey,
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    old_oracle = os.environ.get("TAU_DEX_PERP_ORACLE_PUBKEY")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    os.environ["TAU_DEX_PERP_ORACLE_PUBKEY"] = oracle_pubkey
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false", "CHOKIDAR_USEPOLLING": "1"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        url = _smoke_url(
            vite_base,
            query={
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "publish_clearing_price",
                "marketId": market_id,
                "priceE8": "100000000",
                "txFeeLimit": "2",
                "perpsDeadline": str(int(time.time()) + 3600),
            },
            secrets={"oraclePrivkey": oracle_privkey},
        )
        chrome_profile = tmp_path / "chrome-profile-price"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=20000",
                "--dump-dom",
                url,
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=50,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Live Perps Wallet" in dom
        assert "Publish Price" in dom
        assert "submit accepted" in dom
        assert "preflight ok" in dom
        assert "fee limit 2" in dom
        assert "fee covered yes" in dom
        assert market_id in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        if old_oracle is None:
            os.environ.pop("TAU_DEX_PERP_ORACLE_PUBKEY", None)
        else:
            os.environ["TAU_DEX_PERP_ORACLE_PUBKEY"] = old_oracle
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-settle"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_privkey = 85
    operator_privkey = 86
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(oracle_privkey)
    operator_pubkey = "0x" + bls_pubkey_hex_from_privkey(operator_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-settle"
    app_state_json = _initial_app_state_json(
        _settle_ready_market_state(
            chain_id=chain_id,
            market_id=market_id,
            quote_asset=quote_asset,
            account_a_privkey=account_a_privkey,
            account_b_privkey=account_b_privkey,
            oracle_privkey=oracle_privkey,
        )
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[operator_pubkey[2:].lower()] = 8  # type: ignore[attr-defined]
    tau_server.state.native_balances[operator_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
        "ZENODEX_ENV": "local",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_DEX_OPERATOR_PUBKEY": operator_pubkey,
        "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH": "1",
        "PERPS_ORACLE_AUTHORITY_PROFILE_JSON": json.dumps(
            _oracle_authority_profile(
                chain_id=chain_id,
                oracle_pubkey=oracle_pubkey,
                operator_pubkey=operator_pubkey,
                oracle_privkey=oracle_privkey,
                operator_privkey=operator_privkey,
            ),
            sort_keys=True,
        ),
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    old_operator = os.environ.get("TAU_DEX_OPERATOR_PUBKEY")
    old_require = os.environ.get("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    os.environ["TAU_DEX_OPERATOR_PUBKEY"] = operator_pubkey
    os.environ["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH"] = "1"

    oracle_home = tmp_path / "oracle-home-settle-picker"
    init_oracle = subprocess.run(
        ["python3", str(ORACLE_CLI), "--json", "init", "--home", str(oracle_home)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert init_oracle.returncode == 0, init_oracle.stderr
    oracle_port = _free_port()
    oracle_base = f"http://127.0.0.1:{oracle_port}"
    oracle_proc = subprocess.Popen(
        [
            "python3",
            str(ORACLE_CLI),
            "serve",
            "--home",
            str(oracle_home),
            "--host",
            "127.0.0.1",
            "--port",
            str(oracle_port),
            "--quiet",
            "--allow-writes",
            "--now-epoch",
            "12",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={
            **os.environ,
            "API_PROXY_TARGET": api_base,
            "VITE_DEMO_MODE": "false",
            "CHOKIDAR_USEPOLLING": "1",
            "VITE_ZENO_ORACLE_API_URL": oracle_base,
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        assert oracle_proc.stdout is not None
        oracle_ready = json.loads(oracle_proc.stdout.readline())
        assert oracle_ready["ok"] is True
        assert oracle_ready["write_paths_enabled"] is True
        _wait_for_http(oracle_base + "/api/oracle/health", timeout_s=30)
        seeded_oracle = _seed_oracle_authorization(oracle_base)
        assert str(seeded_oracle["authorization"]["authorization_id"]).startswith("sha256:")
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        url = _smoke_url(
            vite_base,
            query={
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "settle_epoch",
                "marketId": market_id,
                "perpsUseOracleFixture": "1",
                "perpsLoadOracleEvidence": "1",
                "txFeeLimit": "2",
                "perpsDeadline": str(int(time.time()) + 3600),
            },
            secrets={"operatorPrivkey": operator_privkey},
        )
        chrome_profile = tmp_path / "chrome-profile-settle"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=40000",
                "--dump-dom",
                url,
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=90,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Live Perps Wallet" in dom
        assert "Settle Epoch" in dom
        assert "submit accepted" in dom
        assert "preflight ok" in dom
        assert "oracle bridge sha256:" in dom
        assert "oracle evidence accepted" in dom
        assert "oracle action settle_epoch" in dom
        assert "oracle value 100000000" in dom
        assert "oracle reports 3" in dom
        assert "oracle production local" in dom
        assert "oracle service connected" in dom
        assert "oracle replay ok" in dom
        assert "oracle accepted reads 1" in dom
        assert "oracle authorizations 1" in dom
        assert "oracle candidates 3" in dom
        assert "oracle selected authorization" in dom
        assert "oracle selected action settle_epoch" in dom
        assert "oracle selected value 123456789" in dom
        assert "oracle network local" in dom
        assert "oracle authority ready" in dom
        assert "oracle signers 2/2" in dom
        assert "oracle signed quorum 2/2" in dom
        assert "oracle authority exercised yes" in dom
        assert "oracle authority receipt 0x" in dom
        assert "fee covered yes" in dom
        assert market_id in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        if old_operator is None:
            os.environ.pop("TAU_DEX_OPERATOR_PUBKEY", None)
        else:
            os.environ["TAU_DEX_OPERATOR_PUBKEY"] = old_operator
        if old_require is None:
            os.environ.pop("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", None)
        else:
            os.environ["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH"] = old_require
        vite_proc.terminate()
        api_proc.terminate()
        oracle_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc, oracle_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_partial_liquidate_builds_typed_oracle_bridge(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-partial-liquidate"
    account_privkey = 87
    account_pubkey = "0x" + bls_pubkey_hex_from_privkey(account_privkey)
    oracle_privkey = 88
    operator_privkey = 89
    oracle_pubkey = "0x" + bls_pubkey_hex_from_privkey(oracle_privkey)
    operator_pubkey = "0x" + bls_pubkey_hex_from_privkey(operator_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:isolated:ui-liquidation"
    app_state_json = _initial_app_state_json(
        _isolated_liquidation_ready_market_state(
            market_id=market_id,
            quote_asset=quote_asset,
            account_privkey=account_privkey,
        )
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[account_pubkey[2:].lower()] = 6  # type: ignore[attr-defined]
    tau_server.state.native_balances[account_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
        "ZENODEX_ENV": "local",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_DEX_ALLOW_ISOLATED_PERPS": "1",
        "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE": "1",
        "PERPS_ORACLE_AUTHORITY_PROFILE_JSON": json.dumps(
            _oracle_authority_profile(
                chain_id=chain_id,
                oracle_pubkey=oracle_pubkey,
                operator_pubkey=operator_pubkey,
                oracle_privkey=oracle_privkey,
                operator_privkey=operator_privkey,
            ),
            sort_keys=True,
        ),
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    old_allow_isolated = os.environ.get("TAU_DEX_ALLOW_ISOLATED_PERPS")
    old_require = os.environ.get("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    os.environ["TAU_DEX_ALLOW_ISOLATED_PERPS"] = "1"
    os.environ["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE"] = "1"

    oracle_home = tmp_path / "oracle-home-partial-picker"
    init_oracle = subprocess.run(
        ["python3", str(ORACLE_CLI), "--json", "init", "--home", str(oracle_home)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert init_oracle.returncode == 0, init_oracle.stderr
    oracle_port = _free_port()
    oracle_base = f"http://127.0.0.1:{oracle_port}"
    oracle_proc = subprocess.Popen(
        [
            "python3",
            str(ORACLE_CLI),
            "serve",
            "--home",
            str(oracle_home),
            "--host",
            "127.0.0.1",
            "--port",
            str(oracle_port),
            "--quiet",
            "--allow-writes",
            "--now-epoch",
            "12",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={
            **os.environ,
            "API_PROXY_TARGET": api_base,
            "VITE_DEMO_MODE": "false",
            "CHOKIDAR_USEPOLLING": "1",
            "VITE_ZENO_ORACLE_API_URL": oracle_base,
        },
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        assert oracle_proc.stdout is not None
        oracle_ready = json.loads(oracle_proc.stdout.readline())
        assert oracle_ready["ok"] is True
        assert oracle_ready["write_paths_enabled"] is True
        _wait_for_http(oracle_base + "/api/oracle/health", timeout_s=30)
        seeded_oracle = _seed_oracle_authorization(oracle_base, action_kind="liquidate_account")
        assert str(seeded_oracle["authorization"]["authorization_id"]).startswith("sha256:")
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        url = _smoke_url(
            vite_base,
            query={
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "partial_liquidate",
                "marketId": market_id,
                "fractionBps": "0",
                "perpsUseOracleFixture": "1",
                "perpsLoadOracleEvidence": "1",
                "txFeeLimit": "2",
                "perpsDeadline": str(int(time.time()) + 3600),
            },
            secrets={"accountPrivkey": account_privkey},
        )
        chrome_profile = tmp_path / "chrome-profile-partial-liquidation"
        result = subprocess.run(
            [
                chrome,
                "--headless=new",
                "--disable-gpu",
                "--no-sandbox",
                f"--user-data-dir={chrome_profile}",
                "--virtual-time-budget=40000",
                "--dump-dom",
                url,
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=90,
        )
        assert result.returncode == 0, result.stderr[-2000:]
        dom = result.stdout
        assert "Live Perps Wallet" in dom
        assert "Partial Liquidate" in dom
        assert "submit accepted" in dom
        assert "preflight ok" in dom
        assert "oracle bridge sha256:" in dom
        assert "oracle evidence accepted" in dom
        assert "oracle action liquidate_account" in dom
        assert "oracle service connected" in dom
        assert "oracle replay ok" in dom
        assert "oracle accepted reads 1" in dom
        assert "oracle authorizations 1" in dom
        assert "oracle candidates 3" in dom
        assert "oracle target liquidate_account" in dom
        assert "oracle selected authorization" in dom
        assert "oracle selected action liquidate_account" in dom
        assert "oracle selected value 123456789" in dom
        assert "oracle network local" in dom
        assert "oracle authority ready" in dom
        assert "oracle signers 2/2" in dom
        assert "oracle signed quorum 2/2" in dom
        assert "oracle authority exercised yes" in dom
        assert "oracle authority receipt 0x" in dom
        assert "partial liquidation fraction 0 bps" in dom
        assert "isolated liquidated yes" in dom
        assert market_id in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        if old_allow_isolated is None:
            os.environ.pop("TAU_DEX_ALLOW_ISOLATED_PERPS", None)
        else:
            os.environ["TAU_DEX_ALLOW_ISOLATED_PERPS"] = old_allow_isolated
        if old_require is None:
            os.environ.pop("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE", None)
        else:
            os.environ["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE"] = old_require
        vite_proc.terminate()
        api_proc.terminate()
        oracle_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc, oracle_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)


def test_perps_wallet_ui_settle_epoch_reports_liquidation_evidence(tmp_path: Path) -> None:
    chrome = _chrome_binary()
    if chrome is None:
        pytest.skip("Chrome/Chromium is required for the browser UI smoke test")
    if shutil.which("npm") is None:
        pytest.skip("npm is required for the browser UI smoke test")
    if not (DEX_UI / "node_modules" / ".bin" / "vite").exists():
        pytest.skip("tools/dex-ui dependencies are not installed")

    chain_id = "tau-test-perps-wallet-ui-liquidation"
    account_a_privkey = 83
    account_b_privkey = 84
    oracle_privkey = 85
    operator_privkey = 86
    operator_pubkey = "0x" + bls_pubkey_hex_from_privkey(operator_privkey)
    quote_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
    market_id = "perp:ch2p:ui-liquidation"
    app_state_json = _initial_app_state_json(
        _liquidation_ready_market_state(
            chain_id=chain_id,
            market_id=market_id,
            quote_asset=quote_asset,
            account_a_privkey=account_a_privkey,
            account_b_privkey=account_b_privkey,
            oracle_privkey=oracle_privkey,
        )
    )

    tau_port = _free_port()
    tau_server = socketserver.ThreadingTCPServer(("127.0.0.1", tau_port), _TauRpcHandler)
    tau_server.allow_reuse_address = True
    tau_server.state = _TauRpcState(app_state_json=app_state_json)  # type: ignore[attr-defined]
    tau_server.state.sequences[operator_pubkey[2:].lower()] = 9  # type: ignore[attr-defined]
    tau_server.state.native_balances[operator_pubkey[2:].lower()] = 50  # type: ignore[attr-defined]
    tau_thread = threading.Thread(target=tau_server.serve_forever, daemon=True)
    tau_thread.start()

    api_port = _free_port()
    api_base = f"http://127.0.0.1:{api_port}"
    api_env = {
        **os.environ,
        "API_HOST": "127.0.0.1",
        "API_PORT": str(api_port),
        "ZENODEX_EXTERNAL_AUTH_ENFORCED": "1",
        "PERPS_API_ENABLED": "true",
        "PERPS_DEMO_API_UNSAFE_ENABLED": "true",
        "ZENODEX_ENV": "local",
        "PERPS_WALLET_API_ENABLED": "true",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "true",
        "PERPS_WALLET_AUTO_MINE": "true",
        "PERPS_WALLET_CHAIN_ID": chain_id,
        "PERPS_WALLET_TAU_HOST": "127.0.0.1",
        "PERPS_WALLET_TAU_PORT": str(tau_port),
        "TAU_DEX_CHAIN_ID": chain_id,
        "TAU_DEX_OPERATOR_PUBKEY": operator_pubkey,
        "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH": "1",
    }
    old_chain_id = os.environ.get("TAU_DEX_CHAIN_ID")
    old_operator = os.environ.get("TAU_DEX_OPERATOR_PUBKEY")
    old_require = os.environ.get("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH")
    os.environ["TAU_DEX_CHAIN_ID"] = chain_id
    os.environ["TAU_DEX_OPERATOR_PUBKEY"] = operator_pubkey
    os.environ["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH"] = "1"
    api_proc = subprocess.Popen(
        ["python3", "-m", "src.integration.api_server"],
        cwd=ROOT,
        env=api_env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    vite_port = _free_port()
    vite_base = f"http://127.0.0.1:{vite_port}"
    vite_proc = subprocess.Popen(
        ["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", str(vite_port)],
        cwd=DEX_UI,
        env={**os.environ, "API_PROXY_TARGET": api_base, "VITE_DEMO_MODE": "false", "CHOKIDAR_USEPOLLING": "1"},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    try:
        _wait_for_http(api_base + "/health", timeout_s=30)
        _wait_for_http(vite_base, timeout_s=30)
        url = _smoke_url(
            vite_base,
            query={
                "tab": "perps",
                "demo": "false",
                "zenodexUiSmokePerpsWallet": "1",
                "perpsWalletAction": "settle_epoch",
                "marketId": market_id,
                "perpsUseOracleFixture": "1",
                "txFeeLimit": "2",
                "perpsDeadline": str(int(time.time()) + 3600),
            },
            secrets={"operatorPrivkey": operator_privkey},
        )
        dom = _chrome_rendered_haystack(
            chrome=chrome,
            url=url,
            profile=tmp_path / "chrome-profile-liquidation",
            snippets=(
                "Live Perps Wallet",
                "Settle Epoch",
                "submit accepted",
                "preflight ok",
                "liquidated yes",
            ),
            timeout_s=60,
        )
        assert "Live Perps Wallet" in dom
        assert "Settle Epoch" in dom
        assert "submit accepted" in dom
        assert "preflight ok" in dom
        assert "oracle bridge sha256:" in dom
        assert "liquidated yes" in dom
        assert "fee pool 525000000" in dom
        assert "positions 0/0" in dom
        assert "quote A 900" in dom
        assert "quote B 900" in dom
        assert "posted A 15000000000" in dom
        assert "posted B 4475000000" in dom
        assert market_id in dom
    finally:
        if old_chain_id is None:
            os.environ.pop("TAU_DEX_CHAIN_ID", None)
        else:
            os.environ["TAU_DEX_CHAIN_ID"] = old_chain_id
        if old_operator is None:
            os.environ.pop("TAU_DEX_OPERATOR_PUBKEY", None)
        else:
            os.environ["TAU_DEX_OPERATOR_PUBKEY"] = old_operator
        if old_require is None:
            os.environ.pop("TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", None)
        else:
            os.environ["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH"] = old_require
        vite_proc.terminate()
        api_proc.terminate()
        tau_server.shutdown()
        tau_server.server_close()
        for proc in (vite_proc, api_proc):
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)
