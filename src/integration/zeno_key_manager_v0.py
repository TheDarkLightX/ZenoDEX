"""Runtime admission contracts for local Zeno key use.

This module is a deterministic policy façade over ``zeno_key_manager``. It does
not add a custody service and it does not persist private key material.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Mapping, Sequence

from src.integration.zeno_key_manager import (
    KEY_STATUS_ACTIVE,
    KeyEnvironmentPolicy,
    KeyExecutionEnvironment,
    KeyRef,
    KeyUsePolicy,
    PolicyDecision,
    SignRequestContext,
    is_secret_field_name,
)
from src.integration.zeno_ledger_v0 import hash_v0

KEY_MANAGER_RUNTIME_SCHEMA_V0 = "zenodex/zeno_key_manager_runtime/v0"
KEY_BACKEND_DESCRIPTOR_SCHEMA_V0 = "zenodex/zeno_key_manager/backend_descriptor/v0"
SIGN_ADMISSION_RECEIPT_SCHEMA_V0 = "zenodex/zeno_key_manager/sign_admission_receipt/v0"

BACKEND_ENCRYPTED_LOCAL_KEYSTORE = "encrypted-local-keystore"
BACKEND_EXTERNAL_SIGNER_COMMAND = "external-signer-command"
BACKEND_OS_KEYCHAIN = "os-keychain"
BACKEND_HARDWARE_WALLET = "hardware-wallet"
BACKEND_HARDWARE_WALLET_PLACEHOLDER = "hardware-wallet-placeholder"
BACKEND_HSM = "hsm"
BACKEND_HSM_PLACEHOLDER = "hsm-placeholder"
BACKEND_MPC_PLACEHOLDER = "mpc-placeholder"
BACKEND_TAU_BLS_IMPORT = "tau-bls-import"
BACKEND_THRESHOLD_BLS_LOCAL = "threshold-bls-local"
BACKEND_THRESHOLD_BLS_EXTERNAL_SERVICE = "threshold-bls-external-service"

SUPPORTED_BACKENDS = frozenset(
    {
        BACKEND_ENCRYPTED_LOCAL_KEYSTORE,
        BACKEND_EXTERNAL_SIGNER_COMMAND,
        BACKEND_OS_KEYCHAIN,
        BACKEND_HARDWARE_WALLET,
        BACKEND_HARDWARE_WALLET_PLACEHOLDER,
        BACKEND_HSM,
        BACKEND_HSM_PLACEHOLDER,
        BACKEND_MPC_PLACEHOLDER,
        BACKEND_TAU_BLS_IMPORT,
        BACKEND_THRESHOLD_BLS_LOCAL,
        BACKEND_THRESHOLD_BLS_EXTERNAL_SERVICE,
    }
)

def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _reject_secret_fields(value: object, *, name: str = "payload") -> None:
    if isinstance(value, Mapping):
        for key, item in value.items():
            if is_secret_field_name(key):
                raise ValueError(f"{name} must not contain private key material")
            _reject_secret_fields(item, name=f"{name}.{key}")
        return
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        for index, item in enumerate(value):
            _reject_secret_fields(item, name=f"{name}[{index}]")


@dataclass(frozen=True)
class KeyBackendDescriptor:
    key_id: str
    backend_kind: str
    backend_id: str
    policy_hash: str
    active: bool = True
    no_raw_private_key_exposure: bool = True
    metadata: Mapping[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        _require_str(self.key_id, name="key_id")
        if self.backend_kind not in SUPPORTED_BACKENDS:
            raise ValueError("backend_kind is not supported")
        _require_str(self.backend_id, name="backend_id")
        _require_str(self.policy_hash, name="policy_hash")
        if not isinstance(self.active, bool):
            raise TypeError("active must be bool")
        if not isinstance(self.no_raw_private_key_exposure, bool):
            raise TypeError("no_raw_private_key_exposure must be bool")
        _reject_secret_fields(self.metadata, name="metadata")

    def public_dict(self) -> dict[str, Any]:
        body = {
            "schema": KEY_BACKEND_DESCRIPTOR_SCHEMA_V0,
            "key_id": self.key_id,
            "backend_kind": self.backend_kind,
            "backend_id": self.backend_id,
            "policy_hash": self.policy_hash,
            "active": self.active,
            "no_raw_private_key_exposure": self.no_raw_private_key_exposure,
            "metadata": dict(self.metadata),
        }
        return {**body, "backend_hash": hash_v0("zeno_key_backend_descriptor_v0", body)}


@dataclass(frozen=True)
class SignAdmissionRequest:
    key_ref: KeyRef
    backend: KeyBackendDescriptor
    policy: KeyUsePolicy
    context: SignRequestContext
    payload: Mapping[str, Any]
    environment: KeyExecutionEnvironment | None = None
    environment_policy: KeyEnvironmentPolicy | None = None
    seen_nonces: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.key_ref, KeyRef):
            raise TypeError("key_ref must be KeyRef")
        if not isinstance(self.backend, KeyBackendDescriptor):
            raise TypeError("backend must be KeyBackendDescriptor")
        if not isinstance(self.policy, KeyUsePolicy):
            raise TypeError("policy must be KeyUsePolicy")
        if not isinstance(self.context, SignRequestContext):
            raise TypeError("context must be SignRequestContext")
        if not isinstance(self.payload, Mapping):
            raise TypeError("payload must be a mapping")
        _reject_secret_fields(self.payload, name="payload")
        for index, nonce in enumerate(self.seen_nonces):
            _require_nonnegative_int(nonce, name=f"seen_nonces[{index}]")


def evaluate_sign_admission_v0(request: SignAdmissionRequest) -> dict[str, Any]:
    errors: list[str] = []
    if request.key_ref.status != KEY_STATUS_ACTIVE:
        errors.append("key_not_active")
    if request.backend.key_id != request.key_ref.key_id:
        errors.append("backend_key_id_mismatch")
    if not request.backend.active:
        errors.append("backend_inactive")
    if not request.backend.no_raw_private_key_exposure:
        errors.append("backend_raw_private_key_exposure")

    policy_decision = request.policy.evaluate(key_ref=request.key_ref, context=request.context)
    errors.extend(policy_decision.errors)

    if request.environment_policy is not None:
        if request.environment is None:
            errors.append("environment_required")
        else:
            env_decision = request.environment_policy.evaluate(
                environment=request.environment,
                current_epoch=request.context.current_epoch,
            )
            errors.extend(env_decision.errors)

    domain = request.payload.get("domain")
    if not isinstance(domain, str) or not domain:
        errors.append("payload_domain_missing")
    chain_id = request.payload.get("chain_id")
    if chain_id != request.context.chain_id:
        errors.append("payload_chain_id_mismatch")
    nonce = request.payload.get("nonce")
    if not isinstance(nonce, int) or isinstance(nonce, bool) or nonce < 0:
        errors.append("payload_nonce_invalid")
        normalized_nonce = None
    else:
        normalized_nonce = int(nonce)
        if normalized_nonce in set(request.seen_nonces):
            errors.append("payload_nonce_reused")

    body = {
        "schema": SIGN_ADMISSION_RECEIPT_SCHEMA_V0,
        "key_ref_hash": request.key_ref.public_dict()["key_ref_hash"],
        "backend_hash": request.backend.public_dict()["backend_hash"],
        "payload_hash": hash_v0("zeno_key_manager_runtime_payload_v0", dict(request.payload)),
        "payload_kind": request.context.payload_kind,
        "chain_id": request.context.chain_id,
        "purpose": request.context.purpose,
        "current_epoch": request.context.current_epoch,
        "payload_domain": domain if isinstance(domain, str) else "",
        "payload_nonce": normalized_nonce,
        "ok": not errors,
        "errors": tuple(errors),
    }
    return {**body, "receipt_hash": hash_v0("zeno_key_sign_admission_receipt_v0", body)}


def sign_ok_decision_v0(request: SignAdmissionRequest) -> PolicyDecision:
    receipt = evaluate_sign_admission_v0(request)
    return PolicyDecision(ok=receipt["ok"] is True, errors=tuple(receipt["errors"]))
