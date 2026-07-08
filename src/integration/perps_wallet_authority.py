"""Production wallet-authority preflight for the mounted perps stream-8 lane.

This checks public key-manager, signer-registry, wallet UX, and proof posture
metadata. It does not custody keys, verify a hardware wallet, or prove perps
execution in a zkVM.
"""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.zeno_key_manager import (
    KEY_ENVIRONMENT_LOCAL_PROCESS,
    KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
    KEY_ENVIRONMENT_TEE_ATTESTED,
    KEY_MANAGER_SCHEMA_V0,
    KEY_STATUS_ACTIVE,
    KEY_STATUS_REVOKED,
    KeyEnvironmentPolicy,
    KeyExecutionEnvironment,
    KeyRef,
    KeyUsePolicy,
    RecoveryGuardian,
    SignRequestContext,
    SOCIAL_RECOVERY_POLICY_SCHEMA_V0,
    SocialRecoveryPolicy,
    is_secret_field_name,
)
from src.integration.zeno_key_manager_v0 import (
    BACKEND_HARDWARE_WALLET,
    BACKEND_HARDWARE_WALLET_PLACEHOLDER,
    BACKEND_HSM,
    BACKEND_HSM_PLACEHOLDER,
    BACKEND_OS_KEYCHAIN,
    KeyBackendDescriptor,
    SignAdmissionRequest,
    evaluate_sign_admission_v0,
)
from src.integration.zeno_ledger_signer_registry import (
    build_signer_registry_v0,
    validate_signer_registry_v0,
    verify_signature_quorum_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x


PERPS_WALLET_AUTHORITY_PROFILE_SCHEMA_V1 = "zenodex/perps-wallet-authority-profile/v1"
PERPS_WALLET_AUTHORITY_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-authority-status/v1"
PERPS_WALLET_RECOVERY_EXERCISE_SCHEMA_V1 = "zenodex/perps-wallet-recovery-exercise/v1"
PERPS_WALLET_RECOVERY_EXERCISE_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-recovery-exercise-status/v1"
PERPS_WALLET_ROTATION_EXERCISE_SCHEMA_V1 = "zenodex/perps-wallet-rotation-exercise/v1"
PERPS_WALLET_ROTATION_EXERCISE_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-rotation-exercise-status/v1"
PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_SCHEMA_V1 = "zenodex/perps-wallet-device-approval-exercise/v1"
PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-device-approval-exercise-status/v1"
PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_SCHEMA_V1 = "zenodex/perps-wallet-signer-device-integration/v1"
PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-signer-device-integration-status/v1"
PERPS_WALLET_SIGNER_PROMPT_CAPTURE_SCHEMA_V1 = "zenodex/perps-wallet-signer-prompt-capture/v1"
PERPS_WALLET_SIGNER_PROMPT_CAPTURE_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-signer-prompt-capture-status/v1"
PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_SCHEMA_V1 = "zenodex/perps-wallet-signer-execution-exercise/v1"
PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-signer-execution-exercise-status/v1"
PERPS_WALLET_SIGNER_CEREMONY_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-signer-ceremony-status/v1"
PERPS_WALLET_HARDWARE_CUSTODY_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-hardware-custody-status/v1"
PERPS_WALLET_DEVICE_APPROVAL_USE_POLICY_SCHEMA_V1 = "zenodex/perps-wallet-device-approval-use-policy/v1"
PERPS_WALLET_DEVICE_APPROVAL_ENVIRONMENT_POLICY_SCHEMA_V1 = "zenodex/perps-wallet-device-approval-environment-policy/v1"
PERPS_WALLET_AUTHORITY_PAYLOAD_KIND = "perps_wallet_authority_profile"
PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND = "perps_wallet_recovery_exercise"
PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND = "perps_wallet_rotation_exercise"
PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_PAYLOAD_KIND = "perps_wallet_device_approval_exercise"
PERPS_WALLET_SIGNER_PROMPT_CAPTURE_PAYLOAD_KIND = "perps_wallet_signer_prompt_capture"
PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_PAYLOAD_KIND = "perps_wallet_signer_execution_exercise"
_RECOVERY_NON_HASH_FIELDS = frozenset({"exercise_hash", "signature_envelopes", "guardian_signature_quorum"})
_ROTATION_NON_HASH_FIELDS = frozenset({"exercise_hash", "signature_envelopes", "guardian_signature_quorum"})
_DEVICE_APPROVAL_NON_HASH_FIELDS = frozenset({"exercise_hash"})
_SIGNER_DEVICE_INTEGRATION_NON_HASH_FIELDS = frozenset({"integration_hash"})
_SIGNER_PROMPT_CAPTURE_NON_HASH_FIELDS = frozenset({"capture_hash"})
_SIGNER_EXECUTION_NON_HASH_FIELDS = frozenset({"exercise_hash"})

_REQUIRED_WALLET_UX_FLAGS = (
    "external_signer_required",
    "key_manager_required",
    "device_approval_required",
    "replay_protection_required",
    "recovery_policy_required",
)
_REQUIRED_PROOF_FLAGS = (
    "stream8_proof_intent_required",
    "state_delta_witness_required",
    "zk_or_proof_required",
)
_NOT_CLAIMED = (
    "does_not_claim_hardware_wallet_custody",
    "does_not_claim_perps_zk_execution",
    "does_not_claim_production_finality",
    "does_not_claim_oracle_truth",
    "does_not_claim_recovery_rotation_broadcast",
)


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_nonempty_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_root_hash(value: object, *, name: str) -> str:
    text = _require_nonempty_str(value, name=name)
    canonical = canonical_hex_fixed_allow_0x(text, nbytes=32, name=name)
    if text != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be bool")
    return value


def _require_string_list(value: object, *, name: str) -> list[str]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    out: list[str] = []
    for index, item in enumerate(value):
        if not isinstance(item, str) or not item:
            raise ValueError(f"{name}[{index}] must be a non-empty string")
        out.append(item)
    return out


def _require_int_list(value: object, *, name: str) -> list[int]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    out: list[int] = []
    for index, item in enumerate(value):
        out.append(_require_nonnegative_int(item, name=f"{name}[{index}]"))
    return out


def _reject_secret_fields(value: object, *, name: str = "payload") -> None:
    if isinstance(value, Mapping):
        for key, item in value.items():
            if is_secret_field_name(key):
                raise ValueError(f"{name} must not contain private key material")
            _reject_secret_fields(item, name=f"{name}.{key}")
        return
    if isinstance(value, list):
        for index, item in enumerate(value):
            _reject_secret_fields(item, name=f"{name}[{index}]")


def _body(profile: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(profile).items() if key != "wallet_authority_hash"}


def perps_wallet_authority_profile_hash_v1(profile: Mapping[str, Any]) -> str:
    return hash_v0("perps_wallet_authority_profile_v1", _body(profile))


def _recovery_exercise_body(exercise: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(exercise).items() if key not in _RECOVERY_NON_HASH_FIELDS}


def perps_wallet_recovery_exercise_hash_v1(exercise: Mapping[str, Any]) -> str:
    return hash_v0("perps_wallet_recovery_exercise_v1", _recovery_exercise_body(exercise))


def _rotation_exercise_body(exercise: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(exercise).items() if key not in _ROTATION_NON_HASH_FIELDS}


def perps_wallet_rotation_exercise_hash_v1(exercise: Mapping[str, Any]) -> str:
    return hash_v0("perps_wallet_rotation_exercise_v1", _rotation_exercise_body(exercise))


def _device_approval_exercise_body(exercise: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(exercise).items() if key not in _DEVICE_APPROVAL_NON_HASH_FIELDS}


def perps_wallet_device_approval_exercise_hash_v1(exercise: Mapping[str, Any]) -> str:
    return hash_v0("perps_wallet_device_approval_exercise_v1", _device_approval_exercise_body(exercise))


def _signer_device_integration_body(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(payload).items() if key not in _SIGNER_DEVICE_INTEGRATION_NON_HASH_FIELDS}


def perps_wallet_signer_device_integration_hash_v1(payload: Mapping[str, Any]) -> str:
    return hash_v0("perps_wallet_signer_device_integration_v1", _signer_device_integration_body(payload))


def _signer_prompt_capture_body(capture: Mapping[str, Any]) -> dict[str, Any]:
    return {
        key: value
        for key, value in dict(capture).items()
        if key not in _SIGNER_PROMPT_CAPTURE_NON_HASH_FIELDS
    }


def perps_wallet_signer_prompt_capture_hash_v1(capture: Mapping[str, Any]) -> str:
    return hash_v0("perps_wallet_signer_prompt_capture_v1", _signer_prompt_capture_body(capture))


def _signer_execution_exercise_body(exercise: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(exercise).items() if key not in _SIGNER_EXECUTION_NON_HASH_FIELDS}


def perps_wallet_signer_execution_exercise_hash_v1(exercise: Mapping[str, Any]) -> str:
    return hash_v0("perps_wallet_signer_execution_exercise_v1", _signer_execution_exercise_body(exercise))


def build_perps_wallet_authority_profile_v1(
    *,
    authority_id: str,
    chain_id: str,
    stage: str,
    enabled: bool,
    key_manager: Mapping[str, Any],
    signer_registry: Mapping[str, Any],
    wallet_ux: Mapping[str, Any],
    proof_profile: Mapping[str, Any],
    transaction_scope: Mapping[str, Any],
) -> dict[str, Any]:
    body = {
        "schema": PERPS_WALLET_AUTHORITY_PROFILE_SCHEMA_V1,
        "authority_id": _require_nonempty_str(authority_id, name="authority_id"),
        "chain_id": _require_nonempty_str(chain_id, name="chain_id"),
        "stage": _require_nonempty_str(stage, name="stage"),
        "enabled": bool(enabled),
        "key_manager": dict(_require_mapping(key_manager, name="key_manager")),
        "signer_registry": dict(_require_mapping(signer_registry, name="signer_registry")),
        "wallet_ux": dict(_require_mapping(wallet_ux, name="wallet_ux")),
        "proof_profile": dict(_require_mapping(proof_profile, name="proof_profile")),
        "transaction_scope": dict(_require_mapping(transaction_scope, name="transaction_scope")),
    }
    return {**body, "wallet_authority_hash": perps_wallet_authority_profile_hash_v1(body)}


def _device_approval_use_policy_public_dict(policy: KeyUsePolicy) -> dict[str, Any]:
    body: dict[str, Any] = {
        "schema": PERPS_WALLET_DEVICE_APPROVAL_USE_POLICY_SCHEMA_V1,
        "allowed_payload_kinds": list(policy.allowed_payload_kinds),
        "allowed_chain_ids": list(policy.allowed_chain_ids),
        "allowed_purposes": list(policy.allowed_purposes),
        "valid_from_epoch": int(policy.valid_from_epoch),
        "allow_rotated_keys": bool(policy.allow_rotated_keys),
    }
    if policy.valid_until_epoch is not None:
        body["valid_until_epoch"] = int(policy.valid_until_epoch)
    return {**body, "use_policy_hash": hash_v0("perps_wallet_device_approval_use_policy_v1", body)}


def build_perps_wallet_device_approval_use_policy_v1(
    *,
    allowed_payload_kinds: list[str],
    allowed_chain_ids: list[str],
    allowed_purposes: list[str] | None = None,
    valid_from_epoch: int = 0,
    valid_until_epoch: int | None = None,
    allow_rotated_keys: bool = False,
) -> dict[str, Any]:
    policy = KeyUsePolicy(
        allowed_payload_kinds=tuple(_require_string_list(allowed_payload_kinds, name="allowed_payload_kinds")),
        allowed_chain_ids=tuple(_require_string_list(allowed_chain_ids, name="allowed_chain_ids")),
        allowed_purposes=tuple(
            _require_string_list(
                [] if allowed_purposes is None else allowed_purposes,
                name="allowed_purposes",
            )
            if allowed_purposes is not None
            else ("sign",)
        ),
        valid_from_epoch=_require_nonnegative_int(valid_from_epoch, name="valid_from_epoch"),
        valid_until_epoch=None
        if valid_until_epoch is None
        else _require_nonnegative_int(valid_until_epoch, name="valid_until_epoch"),
        allow_rotated_keys=_require_bool(allow_rotated_keys, name="allow_rotated_keys"),
    )
    return _device_approval_use_policy_public_dict(policy)


def _device_approval_environment_policy_public_dict(policy: KeyEnvironmentPolicy) -> dict[str, Any]:
    body: dict[str, Any] = {
        "schema": PERPS_WALLET_DEVICE_APPROVAL_ENVIRONMENT_POLICY_SCHEMA_V1,
        "allowed_environment_kinds": list(policy.allowed_environment_kinds),
        "require_attestation": bool(policy.require_attestation),
        "require_tee_measurement": bool(policy.require_tee_measurement),
        "require_user_presence": bool(policy.require_user_presence),
        "require_rollback_protection": bool(policy.require_rollback_protection),
    }
    if policy.expected_chain_id is not None:
        body["expected_chain_id"] = policy.expected_chain_id
    if policy.expected_policy_hash is not None:
        body["expected_policy_hash"] = policy.expected_policy_hash
    if policy.expected_challenge_hash is not None:
        body["expected_challenge_hash"] = policy.expected_challenge_hash
    return {
        **body,
        "environment_policy_hash": hash_v0("perps_wallet_device_approval_environment_policy_v1", body),
    }


def build_perps_wallet_device_approval_environment_policy_v1(
    *,
    allowed_environment_kinds: list[str],
    expected_chain_id: str | None = None,
    expected_policy_hash: str | None = None,
    expected_challenge_hash: str | None = None,
    require_attestation: bool = False,
    require_tee_measurement: bool = False,
    require_user_presence: bool = True,
    require_rollback_protection: bool = True,
) -> dict[str, Any]:
    policy = KeyEnvironmentPolicy(
        allowed_environment_kinds=tuple(_require_string_list(allowed_environment_kinds, name="allowed_environment_kinds")),
        expected_chain_id=None
        if expected_chain_id is None
        else _require_nonempty_str(expected_chain_id, name="expected_chain_id"),
        expected_policy_hash=expected_policy_hash,
        expected_challenge_hash=expected_challenge_hash,
        require_attestation=_require_bool(require_attestation, name="require_attestation"),
        require_tee_measurement=_require_bool(require_tee_measurement, name="require_tee_measurement"),
        require_user_presence=_require_bool(require_user_presence, name="require_user_presence"),
        require_rollback_protection=_require_bool(require_rollback_protection, name="require_rollback_protection"),
    )
    return _device_approval_environment_policy_public_dict(policy)


def build_perps_wallet_device_approval_exercise_v1(
    *,
    authority_id: str,
    chain_id: str,
    key_id: str,
    payload_kind: str,
    purpose: str,
    current_epoch: int,
    backend_descriptor: Mapping[str, Any],
    use_policy: Mapping[str, Any],
    environment: Mapping[str, Any],
    environment_policy: Mapping[str, Any],
    payload: Mapping[str, Any],
    seen_nonces: list[int] | None = None,
) -> dict[str, Any]:
    _reject_secret_fields(payload, name="payload")
    body = {
        "schema": PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_SCHEMA_V1,
        "authority_id": _require_nonempty_str(authority_id, name="authority_id"),
        "chain_id": _require_nonempty_str(chain_id, name="chain_id"),
        "key_id": _require_nonempty_str(key_id, name="key_id"),
        "payload_kind": _require_nonempty_str(payload_kind, name="payload_kind"),
        "purpose": _require_nonempty_str(purpose, name="purpose"),
        "current_epoch": _require_nonnegative_int(current_epoch, name="current_epoch"),
        "backend_descriptor": dict(_require_mapping(backend_descriptor, name="backend_descriptor")),
        "use_policy": dict(_require_mapping(use_policy, name="use_policy")),
        "environment": dict(_require_mapping(environment, name="environment")),
        "environment_policy": dict(_require_mapping(environment_policy, name="environment_policy")),
        "payload": dict(_require_mapping(payload, name="payload")),
        "seen_nonces": [] if seen_nonces is None else _require_int_list(seen_nonces, name="seen_nonces"),
    }
    return {**body, "exercise_hash": perps_wallet_device_approval_exercise_hash_v1(body)}


def build_perps_wallet_signer_device_integration_v1(
    *,
    authority_id: str,
    chain_id: str,
    key_id: str,
    current_epoch: int,
    backend_descriptor: Mapping[str, Any],
    environment: Mapping[str, Any],
    environment_policy: Mapping[str, Any],
    device_label: str,
    approval_reference: str,
) -> dict[str, Any]:
    body = {
        "schema": PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_SCHEMA_V1,
        "authority_id": _require_nonempty_str(authority_id, name="authority_id"),
        "chain_id": _require_nonempty_str(chain_id, name="chain_id"),
        "key_id": _require_nonempty_str(key_id, name="key_id"),
        "current_epoch": _require_nonnegative_int(current_epoch, name="current_epoch"),
        "backend_descriptor": dict(_require_mapping(backend_descriptor, name="backend_descriptor")),
        "environment": dict(_require_mapping(environment, name="environment")),
        "environment_policy": dict(_require_mapping(environment_policy, name="environment_policy")),
        "device_label": _require_nonempty_str(device_label, name="device_label"),
        "approval_reference": _require_nonempty_str(approval_reference, name="approval_reference"),
    }
    return {**body, "integration_hash": perps_wallet_signer_device_integration_hash_v1(body)}


def build_perps_wallet_signer_prompt_capture_v1(
    *,
    authority_id: str,
    chain_id: str,
    key_id: str,
    current_epoch: int,
    backend_descriptor: Mapping[str, Any],
    environment: Mapping[str, Any],
    environment_policy: Mapping[str, Any],
    device_label: str,
    approval_reference: str,
    prompt_reference: str,
    prompt_source: str,
    prompt_presented_at_epoch: int,
    prompt_confirmed_at_epoch: int,
    prompt_message_hash: str,
    capture_source: str,
    capture_evidence_hash: str,
) -> dict[str, Any]:
    body = {
        "schema": PERPS_WALLET_SIGNER_PROMPT_CAPTURE_SCHEMA_V1,
        "authority_id": _require_nonempty_str(authority_id, name="authority_id"),
        "chain_id": _require_nonempty_str(chain_id, name="chain_id"),
        "key_id": _require_nonempty_str(key_id, name="key_id"),
        "current_epoch": _require_nonnegative_int(current_epoch, name="current_epoch"),
        "backend_descriptor": dict(_require_mapping(backend_descriptor, name="backend_descriptor")),
        "environment": dict(_require_mapping(environment, name="environment")),
        "environment_policy": dict(_require_mapping(environment_policy, name="environment_policy")),
        "device_label": _require_nonempty_str(device_label, name="device_label"),
        "approval_reference": _require_nonempty_str(approval_reference, name="approval_reference"),
        "prompt_reference": _require_nonempty_str(prompt_reference, name="prompt_reference"),
        "prompt_source": _require_nonempty_str(prompt_source, name="prompt_source"),
        "prompt_presented_at_epoch": _require_nonnegative_int(
            prompt_presented_at_epoch,
            name="prompt_presented_at_epoch",
        ),
        "prompt_confirmed_at_epoch": _require_nonnegative_int(
            prompt_confirmed_at_epoch,
            name="prompt_confirmed_at_epoch",
        ),
        "prompt_message_hash": _require_root_hash(prompt_message_hash, name="prompt_message_hash"),
        "capture_source": _require_nonempty_str(capture_source, name="capture_source"),
        "capture_evidence_hash": _require_root_hash(capture_evidence_hash, name="capture_evidence_hash"),
    }
    return {**body, "capture_hash": perps_wallet_signer_prompt_capture_hash_v1(body)}


def build_perps_wallet_signer_execution_exercise_v1(
    *,
    authority_id: str,
    chain_id: str,
    key_id: str,
    payload_kind: str,
    purpose: str,
    current_epoch: int,
    backend_descriptor: Mapping[str, Any],
    use_policy: Mapping[str, Any],
    environment: Mapping[str, Any],
    environment_policy: Mapping[str, Any],
    device_label: str,
    approval_reference: str,
    prompt_reference: str,
    prompt_presented_at_epoch: int,
    prompt_confirmed_at_epoch: int,
    payload: Mapping[str, Any],
    seen_nonces: list[int] | None = None,
    execution_reference: str,
    signed_payload_hash: str,
) -> dict[str, Any]:
    _reject_secret_fields(payload, name="payload")
    body = {
        "schema": PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_SCHEMA_V1,
        "authority_id": _require_nonempty_str(authority_id, name="authority_id"),
        "chain_id": _require_nonempty_str(chain_id, name="chain_id"),
        "key_id": _require_nonempty_str(key_id, name="key_id"),
        "payload_kind": _require_nonempty_str(payload_kind, name="payload_kind"),
        "purpose": _require_nonempty_str(purpose, name="purpose"),
        "current_epoch": _require_nonnegative_int(current_epoch, name="current_epoch"),
        "backend_descriptor": dict(_require_mapping(backend_descriptor, name="backend_descriptor")),
        "use_policy": dict(_require_mapping(use_policy, name="use_policy")),
        "environment": dict(_require_mapping(environment, name="environment")),
        "environment_policy": dict(_require_mapping(environment_policy, name="environment_policy")),
        "device_label": _require_nonempty_str(device_label, name="device_label"),
        "approval_reference": _require_nonempty_str(approval_reference, name="approval_reference"),
        "prompt_reference": _require_nonempty_str(prompt_reference, name="prompt_reference"),
        "prompt_presented_at_epoch": _require_nonnegative_int(
            prompt_presented_at_epoch,
            name="prompt_presented_at_epoch",
        ),
        "prompt_confirmed_at_epoch": _require_nonnegative_int(
            prompt_confirmed_at_epoch,
            name="prompt_confirmed_at_epoch",
        ),
        "payload": dict(_require_mapping(payload, name="payload")),
        "seen_nonces": [] if seen_nonces is None else _require_int_list(seen_nonces, name="seen_nonces"),
        "execution_reference": _require_nonempty_str(execution_reference, name="execution_reference"),
        "signed_payload_hash": _require_root_hash(signed_payload_hash, name="signed_payload_hash"),
    }
    return {**body, "exercise_hash": perps_wallet_signer_execution_exercise_hash_v1(body)}


def _validate_key_manager_public(
    key_manager: Mapping[str, Any],
    gaps: list[str],
) -> tuple[dict[str, KeyRef], list[Mapping[str, Any]]]:
    if key_manager.get("schema") != KEY_MANAGER_SCHEMA_V0:
        gaps.append("key manager schema mismatch")
        return {}, []

    key_refs_raw = key_manager.get("key_refs")
    recovery_policies_raw = key_manager.get("recovery_policies")
    if not isinstance(key_refs_raw, list):
        gaps.append("key manager key_refs must be a list")
        return {}, []
    if not isinstance(recovery_policies_raw, list):
        gaps.append("key manager recovery_policies must be a list")
        return {}, []

    body = {
        "schema": key_manager.get("schema"),
        "key_refs": key_refs_raw,
        "recovery_policies": recovery_policies_raw,
    }
    expected_hash = hash_v0("zeno_key_manager_v0", body)
    if key_manager.get("manager_hash") != expected_hash:
        gaps.append("key manager hash mismatch")

    refs: dict[str, KeyRef] = {}
    for index, raw_ref in enumerate(key_refs_raw):
        try:
            ref = KeyRef.from_public_dict(_require_mapping(raw_ref, name=f"key_refs[{index}]"))
        except Exception as exc:
            gaps.append(f"key manager key_ref {index} invalid: {exc}")
            continue
        if ref.key_id in refs:
            gaps.append(f"duplicate key manager key_id: {ref.key_id}")
            continue
        refs[ref.key_id] = ref
    if not refs:
        gaps.append("key manager has no public key refs")
    return refs, recovery_policies_raw


def _validate_recovery_policies_public(
    *,
    recovery_policies_raw: list[Mapping[str, Any]],
    key_refs: Mapping[str, KeyRef],
    active_signers: list[Mapping[str, Any]],
    gaps: list[str],
) -> tuple[list[dict[str, Any]], int]:
    policies_by_id: dict[str, Mapping[str, Any]] = {}
    summaries: list[dict[str, Any]] = []
    for index, raw_policy in enumerate(recovery_policies_raw):
        policy = _require_mapping(raw_policy, name=f"recovery_policies[{index}]")
        if policy.get("schema") != SOCIAL_RECOVERY_POLICY_SCHEMA_V0:
            gaps.append(f"recovery policy {index} schema mismatch")
            continue
        policy_id = policy.get("policy_id")
        subject_key_id = policy.get("subject_key_id")
        threshold = policy.get("threshold")
        delay_epochs = policy.get("delay_epochs")
        guardians = policy.get("guardians")
        if not isinstance(policy_id, str) or not policy_id:
            gaps.append(f"recovery policy {index} policy_id must be a non-empty string")
            continue
        if policy_id in policies_by_id:
            gaps.append(f"duplicate recovery policy_id: {policy_id}")
            continue
        if not isinstance(subject_key_id, str) or not subject_key_id:
            gaps.append(f"recovery policy {policy_id} subject_key_id must be a non-empty string")
        elif subject_key_id not in key_refs:
            gaps.append(f"recovery policy {policy_id} subject key missing from key manager")
        if not isinstance(threshold, int) or isinstance(threshold, bool) or threshold <= 0:
            gaps.append(f"recovery policy {policy_id} threshold must be a positive int")
            threshold = 0
        if not isinstance(delay_epochs, int) or isinstance(delay_epochs, bool) or delay_epochs < 0:
            gaps.append(f"recovery policy {policy_id} delay_epochs must be a non-negative int")
            delay_epochs = 0
        if not isinstance(guardians, list) or not guardians:
            gaps.append(f"recovery policy {policy_id} guardians must be a non-empty list")
            guardians = []
        active_guardian_weight = 0
        guardian_ids: set[str] = set()
        for guardian_index, guardian_raw in enumerate(guardians):
            guardian = _require_mapping(guardian_raw, name=f"recovery_policies[{index}].guardians[{guardian_index}]")
            guardian_id = guardian.get("guardian_id")
            public_key = guardian.get("public_key")
            weight = guardian.get("weight")
            status = guardian.get("status")
            if not isinstance(guardian_id, str) or not guardian_id:
                gaps.append(f"recovery policy {policy_id} guardian {guardian_index} guardian_id must be a non-empty string")
                continue
            if guardian_id in guardian_ids:
                gaps.append(f"recovery policy {policy_id} duplicate guardian_id: {guardian_id}")
            guardian_ids.add(guardian_id)
            if not isinstance(public_key, str) or not public_key:
                gaps.append(f"recovery policy {policy_id} guardian {guardian_id} public_key must be a non-empty string")
            if not isinstance(weight, int) or isinstance(weight, bool) or weight <= 0:
                gaps.append(f"recovery policy {policy_id} guardian {guardian_id} weight must be a positive int")
                weight = 0
            if status not in {KEY_STATUS_ACTIVE, KEY_STATUS_REVOKED}:
                gaps.append(f"recovery policy {policy_id} guardian {guardian_id} status must be active or revoked")
            if status == KEY_STATUS_ACTIVE:
                active_guardian_weight += int(weight)
            guardian_body = {
                "guardian_id": guardian.get("guardian_id"),
                "public_key": guardian.get("public_key"),
                "weight": guardian.get("weight"),
                "status": guardian.get("status"),
            }
            if guardian.get("guardian_hash") != hash_v0("zeno_recovery_guardian_v0", guardian_body):
                gaps.append(f"recovery policy {policy_id} guardian {guardian_id} hash mismatch")
        if isinstance(threshold, int) and threshold > active_guardian_weight:
            gaps.append(f"recovery policy {policy_id} threshold exceeds active guardian weight")
        policy_body = {
            "schema": policy.get("schema"),
            "policy_id": policy.get("policy_id"),
            "subject_key_id": policy.get("subject_key_id"),
            "threshold": policy.get("threshold"),
            "delay_epochs": policy.get("delay_epochs"),
            "guardians": guardians,
        }
        expected_policy_hash = hash_v0("zeno_social_recovery_policy_v0", policy_body)
        if policy.get("policy_hash") != expected_policy_hash:
            gaps.append(f"recovery policy {policy_id} hash mismatch")
        policies_by_id[policy_id] = policy
        summaries.append(
            {
                "policy_id": policy_id,
                "subject_key_id": subject_key_id,
                "threshold": int(threshold) if isinstance(threshold, int) else 0,
                "delay_epochs": int(delay_epochs) if isinstance(delay_epochs, int) else 0,
                "guardian_count": len(guardians),
                "active_guardian_weight": active_guardian_weight,
                "policy_hash": policy.get("policy_hash"),
            }
        )

    recoverable_active_key_ids: set[str] = set()
    for signer in active_signers:
        key_id = signer.get("key_id")
        if not isinstance(key_id, str) or not key_id:
            continue
        ref = key_refs.get(key_id)
        if ref is None:
            continue
        if ref.recovery_policy_id is None:
            gaps.append(f"active signer key_id {key_id} has no recovery_policy_id")
            continue
        active_policy = policies_by_id.get(ref.recovery_policy_id)
        if active_policy is None:
            gaps.append(f"active signer key_id {key_id} recovery policy missing")
            continue
        if active_policy.get("subject_key_id") != key_id:
            gaps.append(f"active signer key_id {key_id} recovery policy subject mismatch")
            continue
        recoverable_active_key_ids.add(key_id)

    return sorted(summaries, key=lambda item: str(item["policy_id"])), len(recoverable_active_key_ids)


def _active_signer_entries(signer_registry: Mapping[str, Any], gaps: list[str]) -> tuple[list[Mapping[str, Any]], int]:
    try:
        validate_signer_registry_v0(signer_registry)
    except Exception as exc:
        gaps.append(f"signer registry invalid: {exc}")
        return [], 0

    if signer_registry.get("payload_kind") != PERPS_WALLET_AUTHORITY_PAYLOAD_KIND:
        gaps.append("signer registry payload_kind is not perps_wallet_authority_profile")

    threshold_obj = signer_registry.get("threshold")
    threshold = int(threshold_obj) if isinstance(threshold_obj, int) and not isinstance(threshold_obj, bool) else 0
    if threshold < 1:
        gaps.append("active signer threshold must be at least 1")

    raw_entries = signer_registry.get("signers")
    if not isinstance(raw_entries, list):
        gaps.append("signer registry signers must be a list")
        return [], threshold
    active = [
        entry
        for entry in raw_entries
        if isinstance(entry, Mapping) and entry.get("status") == KEY_STATUS_ACTIVE
    ]
    if not active:
        gaps.append("at least one active wallet signer is required")
    return active, threshold


def _validate_signer_key_bindings(
    *,
    active_signers: list[Mapping[str, Any]],
    key_refs: Mapping[str, KeyRef],
    gaps: list[str],
) -> None:
    for signer in active_signers:
        key_id = signer.get("key_id")
        if not isinstance(key_id, str) or key_id == "":
            gaps.append("active signer has missing key_id")
            continue
        ref = key_refs.get(key_id)
        if ref is None:
            gaps.append(f"active signer key_id {key_id} missing from key manager")
            continue
        if ref.status != KEY_STATUS_ACTIVE:
            gaps.append(f"active signer key_id {key_id} is not active in key manager")
        if signer.get("public_key") != ref.public_key:
            gaps.append(f"active signer key_id {key_id} public key mismatch")


def _validate_flag_profile(
    *,
    profile: Mapping[str, Any],
    required_flags: tuple[str, ...],
    profile_name: str,
    gaps: list[str],
) -> None:
    for flag in required_flags:
        if profile.get(flag) is not True:
            gaps.append(f"{profile_name}.{flag} must be true")


def _public_flag_profile(profile: Mapping[str, Any], flags: tuple[str, ...]) -> dict[str, bool]:
    return {flag: profile.get(flag) is True for flag in flags}


def _key_ref_summaries(key_refs: Mapping[str, KeyRef]) -> list[dict[str, Any]]:
    return [
        {
            "key_id": ref.key_id,
            "status": ref.status,
            "origin": ref.origin,
            "algorithm": ref.algorithm,
            "public_key": ref.public_key,
            "key_ref_hash": ref.public_dict()["key_ref_hash"],
            "recovery_policy_id": ref.recovery_policy_id,
        }
        for ref in sorted(key_refs.values(), key=lambda item: item.key_id)
    ]


def _social_recovery_policy_from_public_dict(policy: Mapping[str, Any]) -> SocialRecoveryPolicy:
    obj = _require_mapping(policy, name="recovery_policy")
    if obj.get("schema") != SOCIAL_RECOVERY_POLICY_SCHEMA_V0:
        raise ValueError("recovery policy schema mismatch")
    guardians_raw = obj.get("guardians")
    if not isinstance(guardians_raw, list):
        raise TypeError("recovery policy guardians must be a list")
    guardians: list[RecoveryGuardian] = []
    for index, raw in enumerate(guardians_raw):
        guardian = _require_mapping(raw, name=f"guardians[{index}]")
        guardians.append(
            RecoveryGuardian(
                guardian_id=_require_nonempty_str(guardian.get("guardian_id"), name="guardian_id"),
                public_key=_require_nonempty_str(guardian.get("public_key"), name="public_key"),
                weight=_require_nonnegative_int(guardian.get("weight"), name="weight"),
                status=_require_nonempty_str(guardian.get("status"), name="status"),
            )
        )
    policy_obj = SocialRecoveryPolicy(
        policy_id=_require_nonempty_str(obj.get("policy_id"), name="policy_id"),
        subject_key_id=_require_nonempty_str(obj.get("subject_key_id"), name="subject_key_id"),
        threshold=_require_nonnegative_int(obj.get("threshold"), name="threshold"),
        delay_epochs=_require_nonnegative_int(obj.get("delay_epochs"), name="delay_epochs"),
        guardians=tuple(guardians),
    )
    if dict(obj) != policy_obj.public_dict():
        raise ValueError("recovery policy binding mismatch")
    return policy_obj


def _guardian_signature_quorum_summary(report: Mapping[str, Any]) -> dict[str, Any]:
    accepted = report.get("accepted_signatures")
    accepted_signatures = accepted if isinstance(accepted, list) else []
    return {
        "registry_hash": report.get("registry_hash"),
        "payload_kind": report.get("payload_kind"),
        "payload_hash": report.get("payload_hash"),
        "threshold": int(report.get("threshold", 0)) if isinstance(report.get("threshold"), int) else 0,
        "accepted_weight": int(report.get("accepted_weight", 0)) if isinstance(report.get("accepted_weight"), int) else 0,
        "accepted_signature_count": len(accepted_signatures),
        "accepted_signatures": [
            {
                "guardian_id": str(item.get("signer_id", "")) if isinstance(item, Mapping) else "",
                "key_id": str(item.get("key_id", "")) if isinstance(item, Mapping) else "",
                "weight": int(item.get("weight", 0)) if isinstance(item, Mapping) and isinstance(item.get("weight"), int) else 0,
                "envelope_hash": item.get("envelope_hash") if isinstance(item, Mapping) else None,
            }
            for item in accepted_signatures
        ],
        "quorum_report_hash": report.get("quorum_report_hash"),
    }


def _guardian_registry_for_policy(*, policy: SocialRecoveryPolicy, payload_kind: str) -> Mapping[str, Any]:
    return build_signer_registry_v0(
        registry_id=f"{policy.policy_id}:guardian-signers",
        payload_kind=payload_kind,
        threshold=int(policy.threshold),
        signers=tuple(
            {
                "signer_id": guardian.guardian_id,
                "key_id": guardian.guardian_id,
                "public_key": guardian.public_key,
                "weight": int(guardian.weight),
                "status": guardian.status,
            }
            for guardian in sorted(policy.guardians, key=lambda item: item.guardian_id)
        ),
    )


def _validate_guardian_signature_quorum(
    *,
    exercise: Mapping[str, Any],
    policy: SocialRecoveryPolicy,
    payload_kind: str,
    payload_hash: str,
    accepted_approvals: list[dict[str, Any]] | None,
    errors: list[str],
    label: str,
) -> dict[str, Any] | None:
    raw_envelopes = exercise.get("signature_envelopes")
    if not isinstance(raw_envelopes, list) or not raw_envelopes:
        errors.append(f"{label} guardian signature_envelopes must be a non-empty list")
        return None
    envelopes: list[Mapping[str, Any]] = []
    for index, raw_envelope in enumerate(raw_envelopes):
        try:
            envelopes.append(_require_mapping(raw_envelope, name=f"signature_envelopes[{index}]"))
        except Exception as exc:
            errors.append(f"{label} guardian signature envelope {index} invalid: {exc}")
    if not envelopes:
        return None
    try:
        registry = _guardian_registry_for_policy(policy=policy, payload_kind=payload_kind)
        report = verify_signature_quorum_v0(
            registry=registry,
            payload_kind=payload_kind,
            payload_hash=payload_hash,
            envelopes=envelopes,
        )
    except Exception as exc:
        errors.append(f"{label} guardian signature quorum invalid: {exc}")
        return None
    summary = _guardian_signature_quorum_summary(report)
    accepted_guardian_ids = sorted(
        {
            str(item.get("guardian_id"))
            for item in summary.get("accepted_signatures", [])
            if isinstance(item, Mapping) and isinstance(item.get("guardian_id"), str) and item.get("guardian_id")
        }
    )
    expected_guardian_ids = sorted(
        {
            str(item.get("guardian_id"))
            for item in (accepted_approvals or [])
            if isinstance(item, Mapping) and isinstance(item.get("guardian_id"), str) and item.get("guardian_id")
        }
    )
    if accepted_guardian_ids != expected_guardian_ids:
        errors.append(f"{label} guardian signatures do not match accepted approvals")
    return summary


def _key_ref_from_key_manager_public(
    *,
    key_manager: Mapping[str, Any],
    key_id: str,
) -> KeyRef:
    key_refs_raw = key_manager.get("key_refs")
    if not isinstance(key_refs_raw, list):
        raise TypeError("key manager key_refs must be a list")
    matches = [
        KeyRef.from_public_dict(_require_mapping(raw, name="key_ref"))
        for raw in key_refs_raw
        if isinstance(raw, Mapping) and raw.get("key_id") == key_id
    ]
    if len(matches) != 1:
        raise ValueError("key ref not found")
    return matches[0]


def _key_backend_descriptor_from_public_dict(payload: Mapping[str, Any]) -> KeyBackendDescriptor:
    obj = _require_mapping(payload, name="backend_descriptor")
    descriptor = KeyBackendDescriptor(
        key_id=_require_nonempty_str(obj.get("key_id"), name="backend_descriptor.key_id"),
        backend_kind=_require_nonempty_str(obj.get("backend_kind"), name="backend_descriptor.backend_kind"),
        backend_id=_require_nonempty_str(obj.get("backend_id"), name="backend_descriptor.backend_id"),
        policy_hash=_require_nonempty_str(obj.get("policy_hash"), name="backend_descriptor.policy_hash"),
        active=bool(obj.get("active", True)),
        no_raw_private_key_exposure=bool(obj.get("no_raw_private_key_exposure", True)),
        metadata=dict(_require_mapping(obj.get("metadata", {}), name="backend_descriptor.metadata")),
    )
    if dict(obj) != descriptor.public_dict():
        raise ValueError("backend_descriptor binding mismatch")
    return descriptor


def _device_approval_use_policy_from_public_dict(payload: Mapping[str, Any]) -> KeyUsePolicy:
    obj = _require_mapping(payload, name="use_policy")
    if obj.get("schema") != PERPS_WALLET_DEVICE_APPROVAL_USE_POLICY_SCHEMA_V1:
        raise ValueError("device approval use policy schema mismatch")
    policy = KeyUsePolicy(
        allowed_payload_kinds=tuple(_require_string_list(obj.get("allowed_payload_kinds"), name="allowed_payload_kinds")),
        allowed_chain_ids=tuple(_require_string_list(obj.get("allowed_chain_ids"), name="allowed_chain_ids")),
        allowed_purposes=tuple(_require_string_list(obj.get("allowed_purposes"), name="allowed_purposes")),
        valid_from_epoch=_require_nonnegative_int(obj.get("valid_from_epoch"), name="valid_from_epoch"),
        valid_until_epoch=None
        if obj.get("valid_until_epoch") is None
        else _require_nonnegative_int(obj.get("valid_until_epoch"), name="valid_until_epoch"),
        allow_rotated_keys=_require_bool(obj.get("allow_rotated_keys"), name="allow_rotated_keys"),
    )
    if dict(obj) != _device_approval_use_policy_public_dict(policy):
        raise ValueError("device approval use policy binding mismatch")
    return policy


def _key_execution_environment_from_public_dict(payload: Mapping[str, Any]) -> KeyExecutionEnvironment:
    obj = _require_mapping(payload, name="environment")
    environment = KeyExecutionEnvironment(
        environment_id=_require_nonempty_str(obj.get("environment_id"), name="environment_id"),
        environment_kind=_require_nonempty_str(obj.get("environment_kind"), name="environment_kind"),
        chain_id=_require_nonempty_str(obj.get("chain_id"), name="chain_id"),
        policy_hash=_require_nonempty_str(obj.get("policy_hash"), name="policy_hash"),
        challenge_hash=_require_nonempty_str(obj.get("challenge_hash"), name="challenge_hash"),
        issued_at_epoch=_require_nonnegative_int(obj.get("issued_at_epoch"), name="issued_at_epoch"),
        expires_at_epoch=_require_nonnegative_int(obj.get("expires_at_epoch"), name="expires_at_epoch"),
        attestation_hash=None
        if obj.get("attestation_hash") is None
        else _require_nonempty_str(obj.get("attestation_hash"), name="attestation_hash"),
        tee_measurement_hash=None
        if obj.get("tee_measurement_hash") is None
        else _require_nonempty_str(obj.get("tee_measurement_hash"), name="tee_measurement_hash"),
        local_user_presence_confirmed=_require_bool(
            obj.get("local_user_presence_confirmed"),
            name="local_user_presence_confirmed",
        ),
        rollback_protection_confirmed=_require_bool(
            obj.get("rollback_protection_confirmed"),
            name="rollback_protection_confirmed",
        ),
    )
    if dict(obj) != environment.public_dict():
        raise ValueError("environment binding mismatch")
    return environment


def _device_approval_environment_policy_from_public_dict(payload: Mapping[str, Any]) -> KeyEnvironmentPolicy:
    obj = _require_mapping(payload, name="environment_policy")
    if obj.get("schema") != PERPS_WALLET_DEVICE_APPROVAL_ENVIRONMENT_POLICY_SCHEMA_V1:
        raise ValueError("device approval environment policy schema mismatch")
    policy = KeyEnvironmentPolicy(
        allowed_environment_kinds=tuple(
            _require_string_list(obj.get("allowed_environment_kinds"), name="allowed_environment_kinds")
        ),
        expected_chain_id=None
        if obj.get("expected_chain_id") is None
        else _require_nonempty_str(obj.get("expected_chain_id"), name="expected_chain_id"),
        expected_policy_hash=None
        if obj.get("expected_policy_hash") is None
        else _require_nonempty_str(obj.get("expected_policy_hash"), name="expected_policy_hash"),
        expected_challenge_hash=None
        if obj.get("expected_challenge_hash") is None
        else _require_nonempty_str(obj.get("expected_challenge_hash"), name="expected_challenge_hash"),
        require_attestation=_require_bool(obj.get("require_attestation"), name="require_attestation"),
        require_tee_measurement=_require_bool(obj.get("require_tee_measurement"), name="require_tee_measurement"),
        require_user_presence=_require_bool(obj.get("require_user_presence"), name="require_user_presence"),
        require_rollback_protection=_require_bool(
            obj.get("require_rollback_protection"),
            name="require_rollback_protection",
        ),
    )
    if dict(obj) != _device_approval_environment_policy_public_dict(policy):
        raise ValueError("device approval environment policy binding mismatch")
    return policy


def _recovery_exercise_status(
    *,
    ok: bool,
    errors: list[str],
    exercise: Mapping[str, Any] | None,
    wallet_authority_hash: str | None,
    evaluation: Mapping[str, Any] | None,
    guardian_signature_quorum: Mapping[str, Any] | None,
) -> dict[str, Any]:
    body = {
        "schema": PERPS_WALLET_RECOVERY_EXERCISE_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "recovery_exercise_ready": bool(ok),
        "status": "ready" if ok else "blocked",
        "errors": list(errors),
        "wallet_authority_hash": wallet_authority_hash,
        "exercise_hash": None if exercise is None else perps_wallet_recovery_exercise_hash_v1(exercise),
        "chain_id": None if exercise is None else exercise.get("chain_id"),
        "authority_id": None if exercise is None else exercise.get("authority_id"),
        "subject_key_id": None if exercise is None else exercise.get("subject_key_id"),
        "policy_id": None if exercise is None else exercise.get("policy_id"),
        "requested_at_epoch": None if exercise is None else exercise.get("requested_at_epoch"),
        "current_epoch": None if exercise is None else exercise.get("current_epoch"),
        "evaluation": None if evaluation is None else dict(evaluation),
        "evaluation_hash": None if evaluation is None else evaluation.get("evaluation_hash"),
        "guardian_signature_quorum": None if guardian_signature_quorum is None else dict(guardian_signature_quorum),
        "guardian_signature_quorum_hash": None if guardian_signature_quorum is None else guardian_signature_quorum.get("quorum_report_hash"),
        "not_claimed": [
            "does_not_claim_hardware_wallet_custody",
            "does_not_claim_recovery_rotation_broadcast",
        ],
    }
    return {**body, "status_hash": hash_v0("perps_wallet_recovery_exercise_status_v1", body)}


def evaluate_perps_wallet_recovery_exercise_v1(
    profile: Mapping[str, Any] | None,
    exercise: Mapping[str, Any] | None,
    *,
    expected_chain_id: str | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    if exercise is None:
        return _recovery_exercise_status(
            ok=False,
            errors=["perps wallet recovery exercise is missing"],
            exercise=None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            evaluation=None,
            guardian_signature_quorum=None,
        )
    try:
        exercise_obj = _require_mapping(exercise, name="recovery_exercise")
        _reject_secret_fields(exercise_obj, name="recovery_exercise")
    except Exception as exc:
        return _recovery_exercise_status(
            ok=False,
            errors=[f"perps wallet recovery exercise invalid: {exc}"],
            exercise=exercise if isinstance(exercise, Mapping) else None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            evaluation=None,
            guardian_signature_quorum=None,
        )
    if profile is None:
        return _recovery_exercise_status(
            ok=False,
            errors=["perps wallet authority profile is missing"],
            exercise=exercise_obj,
            wallet_authority_hash=None,
            evaluation=None,
            guardian_signature_quorum=None,
        )

    authority_status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=expected_chain_id)
    if authority_status["production_wallet_authority"] is not True:
        errors.append("perps wallet authority profile is not ready")
        errors.extend(str(gap) for gap in authority_status.get("readiness_gaps", []))

    try:
        if exercise_obj.get("schema") != PERPS_WALLET_RECOVERY_EXERCISE_SCHEMA_V1:
            errors.append("perps wallet recovery exercise schema mismatch")
        chain_id = _require_nonempty_str(exercise_obj.get("chain_id"), name="chain_id")
        authority_id = _require_nonempty_str(exercise_obj.get("authority_id"), name="authority_id")
        subject_key_id = _require_nonempty_str(exercise_obj.get("subject_key_id"), name="subject_key_id")
        policy_id = _require_nonempty_str(exercise_obj.get("policy_id"), name="policy_id")
        requested_at_epoch = _require_nonnegative_int(exercise_obj.get("requested_at_epoch"), name="requested_at_epoch")
        current_epoch = _require_nonnegative_int(exercise_obj.get("current_epoch"), name="current_epoch")
        approvals = _require_string_list(exercise_obj.get("approvals"), name="approvals")
    except Exception as exc:
        errors.append(str(exc))
        return _recovery_exercise_status(
            ok=False,
            errors=errors,
            exercise=exercise_obj,
            wallet_authority_hash=profile.get("wallet_authority_hash"),
            evaluation=None,
            guardian_signature_quorum=None,
        )
    if expected_chain_id is not None and chain_id != expected_chain_id:
        errors.append("perps wallet recovery exercise chain_id mismatch")
    if chain_id != profile.get("chain_id"):
        errors.append("perps wallet recovery exercise profile chain_id mismatch")
    if authority_id != profile.get("authority_id"):
        errors.append("perps wallet recovery exercise authority_id mismatch")

    active_key_ids = {str(item.get("key_id")) for item in authority_status.get("active_signers", []) if isinstance(item, Mapping)}
    if subject_key_id not in active_key_ids:
        errors.append("perps wallet recovery exercise subject key is not active")

    evaluation: Mapping[str, Any] | None = None
    guardian_signature_quorum: Mapping[str, Any] | None = None
    try:
        key_manager = _require_mapping(profile.get("key_manager"), name="key_manager")
        policies_raw = key_manager.get("recovery_policies")
        if not isinstance(policies_raw, list):
            raise TypeError("key manager recovery_policies must be a list")
        matching = [
            _social_recovery_policy_from_public_dict(_require_mapping(raw, name="recovery_policy"))
            for raw in policies_raw
            if isinstance(raw, Mapping) and raw.get("policy_id") == policy_id
        ]
        if len(matching) != 1:
            raise ValueError("recovery policy not found")
        policy = matching[0]
        if policy.subject_key_id != subject_key_id:
            errors.append("perps wallet recovery exercise policy subject mismatch")
        evaluation = policy.evaluate(
            approvals=approvals,
            requested_at_epoch=requested_at_epoch,
            current_epoch=current_epoch,
        )
        if evaluation.get("ok") is not True:
            errors.append("recovery_policy_not_satisfied")
        guardian_signature_quorum = _validate_guardian_signature_quorum(
            exercise=exercise_obj,
            policy=policy,
            payload_kind=PERPS_WALLET_RECOVERY_EXERCISE_PAYLOAD_KIND,
            payload_hash=perps_wallet_recovery_exercise_hash_v1(exercise_obj),
            accepted_approvals=evaluation.get("accepted_approvals") if isinstance(evaluation.get("accepted_approvals"), list) else None,
            errors=errors,
            label="recovery exercise",
        )
    except Exception as exc:
        errors.append(f"recovery policy evaluation failed: {exc}")

    return _recovery_exercise_status(
        ok=(
            not errors
            and evaluation is not None
            and evaluation.get("ok") is True
            and guardian_signature_quorum is not None
        ),
        errors=errors,
        exercise=exercise_obj,
        wallet_authority_hash=profile.get("wallet_authority_hash"),
        evaluation=evaluation,
        guardian_signature_quorum=guardian_signature_quorum,
    )


def _rotation_exercise_status(
    *,
    ok: bool,
    errors: list[str],
    exercise: Mapping[str, Any] | None,
    wallet_authority_hash: str | None,
    current_authority_status: Mapping[str, Any] | None,
    next_authority_status: Mapping[str, Any] | None,
    policy_id: str | None,
    evaluation: Mapping[str, Any] | None,
    guardian_signature_quorum: Mapping[str, Any] | None,
) -> dict[str, Any]:
    body = {
        "schema": PERPS_WALLET_ROTATION_EXERCISE_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "rotation_exercise_ready": bool(ok),
        "status": "ready" if ok else "blocked",
        "errors": list(errors),
        "wallet_authority_hash": wallet_authority_hash,
        "exercise_hash": None if exercise is None else perps_wallet_rotation_exercise_hash_v1(exercise),
        "chain_id": None if exercise is None else exercise.get("chain_id"),
        "authority_id": None if exercise is None else exercise.get("authority_id"),
        "rotated_key_id": None if exercise is None else exercise.get("rotated_key_id"),
        "replacement_key_id": None if exercise is None else exercise.get("replacement_key_id"),
        "policy_id": policy_id,
        "requested_at_epoch": None if exercise is None else exercise.get("requested_at_epoch"),
        "broadcast_at_epoch": None if exercise is None else exercise.get("broadcast_at_epoch"),
        "broadcast_reference": None if exercise is None else exercise.get("broadcast_reference"),
        "current_wallet_authority_hash": None if current_authority_status is None else current_authority_status.get("wallet_authority_hash"),
        "next_wallet_authority_hash": None if next_authority_status is None else next_authority_status.get("wallet_authority_hash"),
        "current_signer_registry_hash": None if current_authority_status is None else current_authority_status.get("signer_registry_hash"),
        "next_signer_registry_hash": None if next_authority_status is None else next_authority_status.get("signer_registry_hash"),
        "current_key_manager_hash": None if current_authority_status is None else current_authority_status.get("key_manager_hash"),
        "next_key_manager_hash": None if next_authority_status is None else next_authority_status.get("key_manager_hash"),
        "evaluation": None if evaluation is None else dict(evaluation),
        "evaluation_hash": None if evaluation is None else evaluation.get("evaluation_hash"),
        "guardian_signature_quorum": None if guardian_signature_quorum is None else dict(guardian_signature_quorum),
        "guardian_signature_quorum_hash": None if guardian_signature_quorum is None else guardian_signature_quorum.get("quorum_report_hash"),
        "not_claimed": [
            "does_not_claim_hardware_wallet_custody",
            "does_not_claim_recovery_rotation_chain_finality",
            "does_not_claim_device_approval_verification",
        ],
    }
    return {**body, "status_hash": hash_v0("perps_wallet_rotation_exercise_status_v1", body)}


def _device_approval_exercise_status(
    *,
    ok: bool,
    errors: list[str],
    exercise: Mapping[str, Any] | None,
    wallet_authority_hash: str | None,
    sign_admission_receipt: Mapping[str, Any] | None,
    backend_hash: str | None,
    environment_hash: str | None,
    use_policy_hash: str | None,
    environment_policy_hash: str | None,
) -> dict[str, Any]:
    body = {
        "schema": PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "device_approval_ready": bool(ok),
        "status": "ready" if ok else "blocked",
        "errors": list(errors),
        "wallet_authority_hash": wallet_authority_hash,
        "exercise_hash": None if exercise is None else perps_wallet_device_approval_exercise_hash_v1(exercise),
        "chain_id": None if exercise is None else exercise.get("chain_id"),
        "authority_id": None if exercise is None else exercise.get("authority_id"),
        "key_id": None if exercise is None else exercise.get("key_id"),
        "payload_kind": None if exercise is None else exercise.get("payload_kind"),
        "purpose": None if exercise is None else exercise.get("purpose"),
        "current_epoch": None if exercise is None else exercise.get("current_epoch"),
        "backend_hash": backend_hash,
        "environment_hash": environment_hash,
        "use_policy_hash": use_policy_hash,
        "environment_policy_hash": environment_policy_hash,
        "sign_admission_receipt": None if sign_admission_receipt is None else dict(sign_admission_receipt),
        "sign_admission_receipt_hash": None
        if sign_admission_receipt is None
        else sign_admission_receipt.get("receipt_hash"),
        "not_claimed": [
            "does_not_claim_hardware_wallet_custody",
            "does_not_claim_live_device_prompt_execution",
            "does_not_claim_production_chain_finality",
        ],
    }
    return {**body, "status_hash": hash_v0("perps_wallet_device_approval_exercise_status_v1", body)}


def _signer_device_integration_status(
    *,
    ok: bool,
    errors: list[str],
    integration: Mapping[str, Any] | None,
    wallet_authority_hash: str | None,
    backend_hash: str | None,
    environment_hash: str | None,
    environment_policy_hash: str | None,
    provider: str | None,
    device_approval_mode: str | None,
    no_raw_private_key_exposure: bool | None,
    attestation_present: bool,
    tee_measurement_present: bool,
) -> dict[str, Any]:
    body = {
        "schema": PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "signer_device_ready": bool(ok),
        "status": "ready" if ok else "blocked",
        "errors": list(errors),
        "wallet_authority_hash": wallet_authority_hash,
        "integration_hash": None if integration is None else perps_wallet_signer_device_integration_hash_v1(integration),
        "chain_id": None if integration is None else integration.get("chain_id"),
        "authority_id": None if integration is None else integration.get("authority_id"),
        "key_id": None if integration is None else integration.get("key_id"),
        "current_epoch": None if integration is None else integration.get("current_epoch"),
        "device_label": None if integration is None else integration.get("device_label"),
        "approval_reference": None if integration is None else integration.get("approval_reference"),
        "backend_hash": backend_hash,
        "environment_hash": environment_hash,
        "environment_policy_hash": environment_policy_hash,
        "backend_kind": None if integration is None else integration.get("backend_descriptor", {}).get("backend_kind"),
        "backend_id": None if integration is None else integration.get("backend_descriptor", {}).get("backend_id"),
        "environment_kind": None if integration is None else integration.get("environment", {}).get("environment_kind"),
        "provider": provider,
        "device_approval_mode": device_approval_mode,
        "no_raw_private_key_exposure": no_raw_private_key_exposure,
        "local_user_presence_confirmed": None if integration is None else integration.get("environment", {}).get("local_user_presence_confirmed"),
        "rollback_protection_confirmed": None if integration is None else integration.get("environment", {}).get("rollback_protection_confirmed"),
        "attestation_present": bool(attestation_present),
        "tee_measurement_present": bool(tee_measurement_present),
        "not_claimed": [
            "does_not_claim_hardware_wallet_custody",
            "does_not_claim_live_os_prompt_capture",
            "does_not_claim_chain_finality",
        ],
    }
    return {**body, "status_hash": hash_v0("perps_wallet_signer_device_integration_status_v1", body)}


def _signer_prompt_capture_status(
    *,
    ok: bool,
    errors: list[str],
    capture: Mapping[str, Any] | None,
    wallet_authority_hash: str | None,
    backend_hash: str | None,
    environment_hash: str | None,
    environment_policy_hash: str | None,
    provider: str | None,
    device_approval_mode: str | None,
) -> dict[str, Any]:
    body = {
        "schema": PERPS_WALLET_SIGNER_PROMPT_CAPTURE_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "signer_prompt_capture_ready": bool(ok),
        "status": "ready" if ok else "blocked",
        "errors": list(errors),
        "wallet_authority_hash": wallet_authority_hash,
        "capture_hash": None if capture is None else perps_wallet_signer_prompt_capture_hash_v1(capture),
        "chain_id": None if capture is None else capture.get("chain_id"),
        "authority_id": None if capture is None else capture.get("authority_id"),
        "key_id": None if capture is None else capture.get("key_id"),
        "current_epoch": None if capture is None else capture.get("current_epoch"),
        "device_label": None if capture is None else capture.get("device_label"),
        "approval_reference": None if capture is None else capture.get("approval_reference"),
        "prompt_reference": None if capture is None else capture.get("prompt_reference"),
        "prompt_source": None if capture is None else capture.get("prompt_source"),
        "prompt_presented_at_epoch": None if capture is None else capture.get("prompt_presented_at_epoch"),
        "prompt_confirmed_at_epoch": None if capture is None else capture.get("prompt_confirmed_at_epoch"),
        "prompt_message_hash": None if capture is None else capture.get("prompt_message_hash"),
        "capture_source": None if capture is None else capture.get("capture_source"),
        "capture_evidence_hash": None if capture is None else capture.get("capture_evidence_hash"),
        "backend_hash": backend_hash,
        "environment_hash": environment_hash,
        "environment_policy_hash": environment_policy_hash,
        "provider": provider,
        "device_approval_mode": device_approval_mode,
        "not_claimed": [
            "does_not_claim_live_os_prompt_verification",
            "does_not_claim_hardware_wallet_execution",
            "does_not_claim_production_chain_finality",
        ],
    }
    return {**body, "status_hash": hash_v0("perps_wallet_signer_prompt_capture_status_v1", body)}


def _signer_execution_exercise_status(
    *,
    ok: bool,
    errors: list[str],
    exercise: Mapping[str, Any] | None,
    wallet_authority_hash: str | None,
    sign_admission_receipt: Mapping[str, Any] | None,
    backend_hash: str | None,
    environment_hash: str | None,
    use_policy_hash: str | None,
    environment_policy_hash: str | None,
    provider: str | None,
    device_approval_mode: str | None,
) -> dict[str, Any]:
    body = {
        "schema": PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "signer_execution_ready": bool(ok),
        "status": "ready" if ok else "blocked",
        "errors": list(errors),
        "wallet_authority_hash": wallet_authority_hash,
        "exercise_hash": None if exercise is None else perps_wallet_signer_execution_exercise_hash_v1(exercise),
        "chain_id": None if exercise is None else exercise.get("chain_id"),
        "authority_id": None if exercise is None else exercise.get("authority_id"),
        "key_id": None if exercise is None else exercise.get("key_id"),
        "payload_kind": None if exercise is None else exercise.get("payload_kind"),
        "purpose": None if exercise is None else exercise.get("purpose"),
        "current_epoch": None if exercise is None else exercise.get("current_epoch"),
        "device_label": None if exercise is None else exercise.get("device_label"),
        "approval_reference": None if exercise is None else exercise.get("approval_reference"),
        "prompt_reference": None if exercise is None else exercise.get("prompt_reference"),
        "prompt_presented_at_epoch": None if exercise is None else exercise.get("prompt_presented_at_epoch"),
        "prompt_confirmed_at_epoch": None if exercise is None else exercise.get("prompt_confirmed_at_epoch"),
        "execution_reference": None if exercise is None else exercise.get("execution_reference"),
        "signed_payload_hash": None if exercise is None else exercise.get("signed_payload_hash"),
        "backend_hash": backend_hash,
        "environment_hash": environment_hash,
        "use_policy_hash": use_policy_hash,
        "environment_policy_hash": environment_policy_hash,
        "provider": provider,
        "device_approval_mode": device_approval_mode,
        "sign_admission_receipt": None if sign_admission_receipt is None else dict(sign_admission_receipt),
        "sign_admission_receipt_hash": None
        if sign_admission_receipt is None
        else sign_admission_receipt.get("receipt_hash"),
        "not_claimed": [
            "does_not_claim_system_prompt_capture_verification",
            "does_not_claim_hardware_wallet_execution",
            "does_not_claim_production_chain_finality",
        ],
    }
    return {**body, "status_hash": hash_v0("perps_wallet_signer_execution_exercise_status_v1", body)}


def _signer_ceremony_status(
    *,
    ok: bool,
    errors: list[str],
    wallet_authority_hash: str | None,
    device_approval_status: Mapping[str, Any] | None,
    signer_device_status: Mapping[str, Any] | None,
    signer_prompt_capture_status: Mapping[str, Any] | None,
    signer_execution_status: Mapping[str, Any] | None,
) -> dict[str, Any]:
    body = {
        "schema": PERPS_WALLET_SIGNER_CEREMONY_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "signer_ceremony_ready": bool(ok),
        "status": "ready" if ok else "blocked",
        "errors": list(errors),
        "wallet_authority_hash": wallet_authority_hash,
        "device_approval_status_hash": None
        if device_approval_status is None
        else device_approval_status.get("status_hash"),
        "signer_device_status_hash": None
        if signer_device_status is None
        else signer_device_status.get("status_hash"),
        "signer_prompt_capture_status_hash": None
        if signer_prompt_capture_status is None
        else signer_prompt_capture_status.get("status_hash"),
        "signer_execution_status_hash": None
        if signer_execution_status is None
        else signer_execution_status.get("status_hash"),
        "key_id": None if signer_execution_status is None else signer_execution_status.get("key_id"),
        "approval_reference": None
        if signer_device_status is None
        else signer_device_status.get("approval_reference"),
        "prompt_reference": None
        if signer_prompt_capture_status is None
        else signer_prompt_capture_status.get("prompt_reference"),
        "execution_reference": None
        if signer_execution_status is None
        else signer_execution_status.get("execution_reference"),
        "provider": None if signer_device_status is None else signer_device_status.get("provider"),
        "device_approval_mode": None
        if signer_device_status is None
        else signer_device_status.get("device_approval_mode"),
        "backend_hash": None if signer_device_status is None else signer_device_status.get("backend_hash"),
        "environment_hash": None if signer_device_status is None else signer_device_status.get("environment_hash"),
        "not_claimed": [
            "does_not_claim_live_os_prompt_verification",
            "does_not_claim_hardware_wallet_custody",
            "does_not_claim_hardware_wallet_execution",
            "does_not_claim_production_chain_finality",
        ],
    }
    return {**body, "status_hash": hash_v0("perps_wallet_signer_ceremony_status_v1", body)}


def _hardware_custody_status(
    *,
    ok: bool,
    errors: list[str],
    wallet_authority_hash: str | None,
    device_approval_status: Mapping[str, Any] | None,
    signer_device_status: Mapping[str, Any] | None,
    signer_prompt_capture_status: Mapping[str, Any] | None,
    signer_execution_status: Mapping[str, Any] | None,
    signer_ceremony_status: Mapping[str, Any] | None,
    production_hardware_evidence_status: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    provider = None if signer_device_status is None else signer_device_status.get("provider")
    backend_kind = None if signer_device_status is None else signer_device_status.get("backend_kind")
    attestation_present = None if signer_device_status is None else signer_device_status.get("attestation_present")
    tee_measurement_present = None if signer_device_status is None else signer_device_status.get("tee_measurement_present")
    fixture_custody = provider == "local-testnet-fixture" or backend_kind in {
        BACKEND_HARDWARE_WALLET_PLACEHOLDER,
        BACKEND_HSM_PLACEHOLDER,
    }
    production_hardware_evidence_ready = (
        production_hardware_evidence_status is not None
        and production_hardware_evidence_status.get("production_ready") is True
    )
    production_hardware_custody_ready = (
        bool(ok)
        and not fixture_custody
        and (attestation_present is True or tee_measurement_present is True)
        and production_hardware_evidence_ready
    )
    production_evidence_gaps: list[str] = []
    if production_hardware_evidence_status is not None:
        raw_gaps = production_hardware_evidence_status.get("gaps", [])
        production_evidence_gaps = [str(item) for item in raw_gaps] if isinstance(raw_gaps, list) else [str(raw_gaps)]
    body = {
        "schema": PERPS_WALLET_HARDWARE_CUSTODY_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "hardware_custody_ready": bool(ok),
        "production_hardware_custody_ready": production_hardware_custody_ready,
        "production_hardware_evidence_ready": production_hardware_evidence_ready,
        "production_hardware_evidence_hash": None
        if production_hardware_evidence_status is None
        else production_hardware_evidence_status.get("evidence_hash"),
        "production_hardware_evidence_gaps": production_evidence_gaps,
        "custody_evidence_mode": "missing" if signer_device_status is None else ("local_fixture" if fixture_custody else "live_attested"),
        "status": "ready" if ok else "blocked",
        "errors": list(errors),
        "wallet_authority_hash": wallet_authority_hash,
        "device_approval_status_hash": None
        if device_approval_status is None
        else device_approval_status.get("status_hash"),
        "signer_device_status_hash": None
        if signer_device_status is None
        else signer_device_status.get("status_hash"),
        "signer_prompt_capture_status_hash": None
        if signer_prompt_capture_status is None
        else signer_prompt_capture_status.get("status_hash"),
        "signer_execution_status_hash": None
        if signer_execution_status is None
        else signer_execution_status.get("status_hash"),
        "signer_ceremony_status_hash": None
        if signer_ceremony_status is None
        else signer_ceremony_status.get("status_hash"),
        "key_id": None if signer_device_status is None else signer_device_status.get("key_id"),
        "approval_reference": None if signer_device_status is None else signer_device_status.get("approval_reference"),
        "prompt_reference": None if signer_prompt_capture_status is None else signer_prompt_capture_status.get("prompt_reference"),
        "execution_reference": None if signer_execution_status is None else signer_execution_status.get("execution_reference"),
        "backend_kind": backend_kind,
        "backend_id": None if signer_device_status is None else signer_device_status.get("backend_id"),
        "environment_kind": None if signer_device_status is None else signer_device_status.get("environment_kind"),
        "provider": provider,
        "device_approval_mode": None
        if signer_device_status is None
        else signer_device_status.get("device_approval_mode"),
        "no_raw_private_key_exposure": None
        if signer_device_status is None
        else signer_device_status.get("no_raw_private_key_exposure"),
        "attestation_present": attestation_present,
        "tee_measurement_present": tee_measurement_present,
        "local_user_presence_confirmed": None
        if signer_device_status is None
        else signer_device_status.get("local_user_presence_confirmed"),
        "rollback_protection_confirmed": None
        if signer_device_status is None
        else signer_device_status.get("rollback_protection_confirmed"),
        "backend_hash": None if signer_device_status is None else signer_device_status.get("backend_hash"),
        "environment_hash": None if signer_device_status is None else signer_device_status.get("environment_hash"),
        "not_claimed": [
            "does_not_claim_live_hardware_device_possession",
            "does_not_claim_private_key_non_extractability_proof",
            "does_not_claim_vendor_attestation_soundness",
            "does_not_claim_production_chain_finality",
        ],
    }
    return {**body, "status_hash": hash_v0("perps_wallet_hardware_custody_status_v1", body)}


def evaluate_perps_wallet_rotation_exercise_v1(
    profile: Mapping[str, Any] | None,
    exercise: Mapping[str, Any] | None,
    *,
    expected_chain_id: str | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    if exercise is None:
        return _rotation_exercise_status(
            ok=False,
            errors=["perps wallet rotation exercise is missing"],
            exercise=None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            current_authority_status=None,
            next_authority_status=None,
            policy_id=None,
            evaluation=None,
            guardian_signature_quorum=None,
        )
    try:
        exercise_obj = _require_mapping(exercise, name="rotation_exercise")
        _reject_secret_fields(exercise_obj, name="rotation_exercise")
    except Exception as exc:
        return _rotation_exercise_status(
            ok=False,
            errors=[f"perps wallet rotation exercise invalid: {exc}"],
            exercise=exercise if isinstance(exercise, Mapping) else None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            current_authority_status=None,
            next_authority_status=None,
            policy_id=None,
            evaluation=None,
            guardian_signature_quorum=None,
        )
    if profile is None:
        return _rotation_exercise_status(
            ok=False,
            errors=["perps wallet authority profile is missing"],
            exercise=exercise_obj,
            wallet_authority_hash=None,
            current_authority_status=None,
            next_authority_status=None,
            policy_id=None,
            evaluation=None,
            guardian_signature_quorum=None,
        )

    current_authority_status = evaluate_perps_wallet_authority_profile_v1(
        profile,
        expected_chain_id=expected_chain_id,
    )
    if current_authority_status["production_wallet_authority"] is not True:
        errors.append("perps wallet authority profile is not ready")
        errors.extend(str(gap) for gap in current_authority_status.get("readiness_gaps", []))

    try:
        if exercise_obj.get("schema") != PERPS_WALLET_ROTATION_EXERCISE_SCHEMA_V1:
            errors.append("perps wallet rotation exercise schema mismatch")
        chain_id = _require_nonempty_str(exercise_obj.get("chain_id"), name="chain_id")
        authority_id = _require_nonempty_str(exercise_obj.get("authority_id"), name="authority_id")
        rotated_key_id = _require_nonempty_str(exercise_obj.get("rotated_key_id"), name="rotated_key_id")
        replacement_key_id = _require_nonempty_str(exercise_obj.get("replacement_key_id"), name="replacement_key_id")
        policy_id = _require_nonempty_str(exercise_obj.get("policy_id"), name="policy_id")
        requested_at_epoch = _require_nonnegative_int(exercise_obj.get("requested_at_epoch"), name="requested_at_epoch")
        broadcast_at_epoch = _require_nonnegative_int(exercise_obj.get("broadcast_at_epoch"), name="broadcast_at_epoch")
        broadcast_reference = _require_nonempty_str(exercise_obj.get("broadcast_reference"), name="broadcast_reference")
        approvals = _require_string_list(exercise_obj.get("approvals"), name="approvals")
        next_profile = _require_mapping(
            exercise_obj.get("next_wallet_authority_profile"),
            name="next_wallet_authority_profile",
        )
    except Exception as exc:
        errors.append(str(exc))
        return _rotation_exercise_status(
            ok=False,
            errors=errors,
            exercise=exercise_obj,
            wallet_authority_hash=profile.get("wallet_authority_hash"),
            current_authority_status=current_authority_status,
            next_authority_status=None,
            policy_id=None,
            evaluation=None,
            guardian_signature_quorum=None,
        )

    if expected_chain_id is not None and chain_id != expected_chain_id:
        errors.append("perps wallet rotation exercise chain_id mismatch")
    if chain_id != profile.get("chain_id"):
        errors.append("perps wallet rotation exercise profile chain_id mismatch")
    if authority_id != profile.get("authority_id"):
        errors.append("perps wallet rotation exercise authority_id mismatch")
    if broadcast_at_epoch < requested_at_epoch:
        errors.append("perps wallet rotation exercise broadcast_at_epoch precedes request")

    next_authority_status = evaluate_perps_wallet_authority_profile_v1(
        next_profile,
        expected_chain_id=expected_chain_id,
    )
    if next_authority_status["production_wallet_authority"] is not True:
        errors.append("next perps wallet authority profile is not ready")
        errors.extend(str(gap) for gap in next_authority_status.get("readiness_gaps", []))
    if next_profile.get("chain_id") != chain_id:
        errors.append("next perps wallet authority profile chain_id mismatch")
    if next_profile.get("authority_id") != authority_id:
        errors.append("next perps wallet authority profile authority_id mismatch")

    current_active_key_ids = {
        str(item.get("key_id"))
        for item in current_authority_status.get("active_signers", [])
        if isinstance(item, Mapping)
    }
    next_active_key_ids = {
        str(item.get("key_id"))
        for item in next_authority_status.get("active_signers", [])
        if isinstance(item, Mapping)
    }
    if rotated_key_id not in current_active_key_ids:
        errors.append("rotated key is not active in current wallet authority")
    if replacement_key_id not in next_active_key_ids:
        errors.append("replacement key is not active in next wallet authority")
    if replacement_key_id in current_active_key_ids:
        errors.append("replacement key is already active in current wallet authority")
    if rotated_key_id in next_active_key_ids:
        errors.append("rotated key remains active in next wallet authority")
    if current_authority_status.get("wallet_authority_hash") == next_authority_status.get("wallet_authority_hash"):
        errors.append("next wallet authority hash must differ from current wallet authority hash")
    if (
        current_authority_status.get("signer_registry_hash") == next_authority_status.get("signer_registry_hash")
        and current_authority_status.get("key_manager_hash") == next_authority_status.get("key_manager_hash")
    ):
        errors.append("rotation exercise does not change key manager or signer registry")

    evaluation: Mapping[str, Any] | None = None
    guardian_signature_quorum: Mapping[str, Any] | None = None
    try:
        key_manager = _require_mapping(profile.get("key_manager"), name="key_manager")
        policies_raw = key_manager.get("recovery_policies")
        if not isinstance(policies_raw, list):
            raise TypeError("key manager recovery_policies must be a list")
        matching = [
            _social_recovery_policy_from_public_dict(_require_mapping(raw, name="recovery_policy"))
            for raw in policies_raw
            if isinstance(raw, Mapping) and raw.get("policy_id") == policy_id
        ]
        if len(matching) != 1:
            raise ValueError("recovery policy not found")
        policy = matching[0]
        if policy.subject_key_id != rotated_key_id:
            errors.append("perps wallet rotation exercise policy subject mismatch")
        evaluation = policy.evaluate(
            approvals=approvals,
            requested_at_epoch=requested_at_epoch,
            current_epoch=broadcast_at_epoch,
        )
        if evaluation.get("ok") is not True:
            errors.append("rotation_recovery_policy_not_satisfied")
        guardian_signature_quorum = _validate_guardian_signature_quorum(
            exercise=exercise_obj,
            policy=policy,
            payload_kind=PERPS_WALLET_ROTATION_EXERCISE_PAYLOAD_KIND,
            payload_hash=perps_wallet_rotation_exercise_hash_v1(exercise_obj),
            accepted_approvals=evaluation.get("accepted_approvals") if isinstance(evaluation.get("accepted_approvals"), list) else None,
            errors=errors,
            label="rotation exercise",
        )
    except Exception as exc:
        errors.append(f"rotation recovery policy evaluation failed: {exc}")

    _ = broadcast_reference
    return _rotation_exercise_status(
        ok=not errors and guardian_signature_quorum is not None and evaluation is not None and evaluation.get("ok") is True,
        errors=errors,
        exercise=exercise_obj,
        wallet_authority_hash=profile.get("wallet_authority_hash"),
        current_authority_status=current_authority_status,
        next_authority_status=next_authority_status,
        policy_id=policy_id,
        evaluation=evaluation,
        guardian_signature_quorum=guardian_signature_quorum,
    )


def evaluate_perps_wallet_device_approval_exercise_v1(
    profile: Mapping[str, Any] | None,
    exercise: Mapping[str, Any] | None,
    *,
    expected_chain_id: str | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    if exercise is None:
        return _device_approval_exercise_status(
            ok=False,
            errors=["perps wallet device approval exercise is missing"],
            exercise=None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            sign_admission_receipt=None,
            backend_hash=None,
            environment_hash=None,
            use_policy_hash=None,
            environment_policy_hash=None,
        )
    try:
        exercise_obj = _require_mapping(exercise, name="device_approval_exercise")
        _reject_secret_fields(exercise_obj, name="device_approval_exercise")
    except Exception as exc:
        return _device_approval_exercise_status(
            ok=False,
            errors=[f"perps wallet device approval exercise invalid: {exc}"],
            exercise=exercise if isinstance(exercise, Mapping) else None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            sign_admission_receipt=None,
            backend_hash=None,
            environment_hash=None,
            use_policy_hash=None,
            environment_policy_hash=None,
        )
    if profile is None:
        return _device_approval_exercise_status(
            ok=False,
            errors=["perps wallet authority profile is missing"],
            exercise=exercise_obj,
            wallet_authority_hash=None,
            sign_admission_receipt=None,
            backend_hash=None,
            environment_hash=None,
            use_policy_hash=None,
            environment_policy_hash=None,
        )

    authority_status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=expected_chain_id)
    if authority_status["production_wallet_authority"] is not True:
        errors.append("perps wallet authority profile is not ready")
        errors.extend(str(gap) for gap in authority_status.get("readiness_gaps", []))

    backend_hash: str | None = None
    environment_hash: str | None = None
    use_policy_hash: str | None = None
    environment_policy_hash: str | None = None
    sign_admission_receipt: Mapping[str, Any] | None = None

    try:
        if exercise_obj.get("schema") != PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_SCHEMA_V1:
            errors.append("perps wallet device approval exercise schema mismatch")
        chain_id = _require_nonempty_str(exercise_obj.get("chain_id"), name="chain_id")
        authority_id = _require_nonempty_str(exercise_obj.get("authority_id"), name="authority_id")
        key_id = _require_nonempty_str(exercise_obj.get("key_id"), name="key_id")
        payload_kind = _require_nonempty_str(exercise_obj.get("payload_kind"), name="payload_kind")
        purpose = _require_nonempty_str(exercise_obj.get("purpose"), name="purpose")
        current_epoch = _require_nonnegative_int(exercise_obj.get("current_epoch"), name="current_epoch")
        backend_descriptor = _key_backend_descriptor_from_public_dict(
            _require_mapping(exercise_obj.get("backend_descriptor"), name="backend_descriptor")
        )
        use_policy = _device_approval_use_policy_from_public_dict(
            _require_mapping(exercise_obj.get("use_policy"), name="use_policy")
        )
        environment = _key_execution_environment_from_public_dict(
            _require_mapping(exercise_obj.get("environment"), name="environment")
        )
        environment_policy = _device_approval_environment_policy_from_public_dict(
            _require_mapping(exercise_obj.get("environment_policy"), name="environment_policy")
        )
        payload = dict(_require_mapping(exercise_obj.get("payload"), name="payload"))
        seen_nonces = tuple(_require_int_list(exercise_obj.get("seen_nonces", []), name="seen_nonces"))
        _reject_secret_fields(payload, name="payload")
    except Exception as exc:
        errors.append(str(exc))
        return _device_approval_exercise_status(
            ok=False,
            errors=errors,
            exercise=exercise_obj,
            wallet_authority_hash=profile.get("wallet_authority_hash"),
            sign_admission_receipt=None,
            backend_hash=None,
            environment_hash=None,
            use_policy_hash=None,
            environment_policy_hash=None,
        )

    if expected_chain_id is not None and chain_id != expected_chain_id:
        errors.append("perps wallet device approval exercise chain_id mismatch")
    if chain_id != profile.get("chain_id"):
        errors.append("perps wallet device approval exercise profile chain_id mismatch")
    if authority_id != profile.get("authority_id"):
        errors.append("perps wallet device approval exercise authority_id mismatch")

    active_key_ids = {
        str(item.get("key_id"))
        for item in authority_status.get("active_signers", [])
        if isinstance(item, Mapping)
    }
    if key_id not in active_key_ids:
        errors.append("perps wallet device approval exercise key is not active")

    try:
        key_manager = _require_mapping(profile.get("key_manager"), name="key_manager")
        key_ref = _key_ref_from_key_manager_public(key_manager=key_manager, key_id=key_id)
        context = SignRequestContext(
            payload_kind=payload_kind,
            chain_id=chain_id,
            purpose=purpose,
            current_epoch=current_epoch,
        )
        sign_admission_receipt = evaluate_sign_admission_v0(
            SignAdmissionRequest(
                key_ref=key_ref,
                backend=backend_descriptor,
                policy=use_policy,
                context=context,
                payload=payload,
                environment=environment,
                environment_policy=environment_policy,
                seen_nonces=seen_nonces,
            )
        )
        backend_hash = backend_descriptor.public_dict()["backend_hash"]
        environment_hash = environment.public_dict()["environment_hash"]
        use_policy_hash = _device_approval_use_policy_public_dict(use_policy)["use_policy_hash"]
        environment_policy_hash = _device_approval_environment_policy_public_dict(environment_policy)[
            "environment_policy_hash"
        ]
        if sign_admission_receipt.get("ok") is not True:
            errors.append("device_approval_sign_admission_rejected")
            errors.extend(str(item) for item in sign_admission_receipt.get("errors", ()))
    except Exception as exc:
        errors.append(f"device approval sign admission failed: {exc}")

    return _device_approval_exercise_status(
        ok=not errors and sign_admission_receipt is not None and sign_admission_receipt.get("ok") is True,
        errors=errors,
        exercise=exercise_obj,
        wallet_authority_hash=profile.get("wallet_authority_hash"),
        sign_admission_receipt=sign_admission_receipt,
        backend_hash=backend_hash,
        environment_hash=environment_hash,
        use_policy_hash=use_policy_hash,
        environment_policy_hash=environment_policy_hash,
    )


def evaluate_perps_wallet_signer_device_integration_v1(
    profile: Mapping[str, Any] | None,
    integration: Mapping[str, Any] | None,
    *,
    expected_chain_id: str | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    if integration is None:
        return _signer_device_integration_status(
            ok=False,
            errors=["perps wallet signer-device integration is missing"],
            integration=None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            backend_hash=None,
            environment_hash=None,
            environment_policy_hash=None,
            provider=None,
            device_approval_mode=None,
            no_raw_private_key_exposure=None,
            attestation_present=False,
            tee_measurement_present=False,
        )
    try:
        integration_obj = _require_mapping(integration, name="signer_device_integration")
        _reject_secret_fields(integration_obj, name="signer_device_integration")
    except Exception as exc:
        return _signer_device_integration_status(
            ok=False,
            errors=[f"perps wallet signer-device integration invalid: {exc}"],
            integration=integration if isinstance(integration, Mapping) else None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            backend_hash=None,
            environment_hash=None,
            environment_policy_hash=None,
            provider=None,
            device_approval_mode=None,
            no_raw_private_key_exposure=None,
            attestation_present=False,
            tee_measurement_present=False,
        )
    if profile is None:
        return _signer_device_integration_status(
            ok=False,
            errors=["perps wallet authority profile is missing"],
            integration=integration_obj,
            wallet_authority_hash=None,
            backend_hash=None,
            environment_hash=None,
            environment_policy_hash=None,
            provider=None,
            device_approval_mode=None,
            no_raw_private_key_exposure=None,
            attestation_present=False,
            tee_measurement_present=False,
        )

    authority_status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=expected_chain_id)
    if authority_status["production_wallet_authority"] is not True:
        errors.append("perps wallet authority profile is not ready")
        errors.extend(str(gap) for gap in authority_status.get("readiness_gaps", []))

    backend_hash: str | None = None
    environment_hash: str | None = None
    environment_policy_hash: str | None = None
    provider: str | None = None
    device_approval_mode: str | None = None
    no_raw_private_key_exposure: bool | None = None
    attestation_present = False
    tee_measurement_present = False

    try:
        if integration_obj.get("schema") != PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_SCHEMA_V1:
            errors.append("perps wallet signer-device integration schema mismatch")
        chain_id = _require_nonempty_str(integration_obj.get("chain_id"), name="chain_id")
        authority_id = _require_nonempty_str(integration_obj.get("authority_id"), name="authority_id")
        key_id = _require_nonempty_str(integration_obj.get("key_id"), name="key_id")
        current_epoch = _require_nonnegative_int(integration_obj.get("current_epoch"), name="current_epoch")
        device_label = _require_nonempty_str(integration_obj.get("device_label"), name="device_label")
        approval_reference = _require_nonempty_str(integration_obj.get("approval_reference"), name="approval_reference")
        backend_descriptor = _key_backend_descriptor_from_public_dict(
            _require_mapping(integration_obj.get("backend_descriptor"), name="backend_descriptor")
        )
        environment = _key_execution_environment_from_public_dict(
            _require_mapping(integration_obj.get("environment"), name="environment")
        )
        environment_policy = _device_approval_environment_policy_from_public_dict(
            _require_mapping(integration_obj.get("environment_policy"), name="environment_policy")
        )
    except Exception as exc:
        errors.append(str(exc))
        return _signer_device_integration_status(
            ok=False,
            errors=errors,
            integration=integration_obj,
            wallet_authority_hash=profile.get("wallet_authority_hash"),
            backend_hash=None,
            environment_hash=None,
            environment_policy_hash=None,
            provider=None,
            device_approval_mode=None,
            no_raw_private_key_exposure=None,
            attestation_present=False,
            tee_measurement_present=False,
        )

    _ = device_label
    _ = approval_reference
    if expected_chain_id is not None and chain_id != expected_chain_id:
        errors.append("perps wallet signer-device integration chain_id mismatch")
    if chain_id != profile.get("chain_id"):
        errors.append("perps wallet signer-device integration profile chain_id mismatch")
    if authority_id != profile.get("authority_id"):
        errors.append("perps wallet signer-device integration authority_id mismatch")

    active_key_ids = {
        str(item.get("key_id"))
        for item in authority_status.get("active_signers", [])
        if isinstance(item, Mapping)
    }
    if key_id not in active_key_ids:
        errors.append("perps wallet signer-device integration key is not active")
    if backend_descriptor.key_id != key_id:
        errors.append("signer-device backend key_id mismatch")

    provider_raw = backend_descriptor.metadata.get("provider")
    device_mode_raw = backend_descriptor.metadata.get("device_approval_mode")
    if not isinstance(provider_raw, str) or not provider_raw:
        errors.append("signer-device backend provider missing")
    else:
        provider = provider_raw
    if not isinstance(device_mode_raw, str) or not device_mode_raw:
        errors.append("signer-device backend device_approval_mode missing")
    else:
        device_approval_mode = device_mode_raw
    no_raw_private_key_exposure = bool(backend_descriptor.no_raw_private_key_exposure)

    if backend_descriptor.backend_kind == BACKEND_OS_KEYCHAIN and environment.environment_kind not in {
        KEY_ENVIRONMENT_LOCAL_PROCESS,
        KEY_ENVIRONMENT_TEE_ATTESTED,
    }:
        errors.append("os_keychain_environment_kind_invalid")
    if backend_descriptor.backend_kind in {
        BACKEND_HARDWARE_WALLET,
        BACKEND_HARDWARE_WALLET_PLACEHOLDER,
        BACKEND_HSM,
        BACKEND_HSM_PLACEHOLDER,
    } and environment.environment_kind not in {
        KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
        KEY_ENVIRONMENT_TEE_ATTESTED,
    }:
        errors.append("hardware_signer_environment_kind_invalid")

    attestation_present = environment.attestation_hash is not None
    tee_measurement_present = environment.tee_measurement_hash is not None
    try:
        env_decision = environment_policy.evaluate(
            environment=environment,
            current_epoch=current_epoch,
        )
        if not env_decision.ok:
            errors.append("signer_device_environment_rejected")
            errors.extend(str(item) for item in env_decision.errors)
        backend_hash = backend_descriptor.public_dict()["backend_hash"]
        environment_hash = environment.public_dict()["environment_hash"]
        environment_policy_hash = _device_approval_environment_policy_public_dict(environment_policy)["environment_policy_hash"]
    except Exception as exc:
        errors.append(f"signer-device environment evaluation failed: {exc}")

    return _signer_device_integration_status(
        ok=not errors,
        errors=errors,
        integration=integration_obj,
        wallet_authority_hash=profile.get("wallet_authority_hash"),
        backend_hash=backend_hash,
        environment_hash=environment_hash,
        environment_policy_hash=environment_policy_hash,
        provider=provider,
        device_approval_mode=device_approval_mode,
        no_raw_private_key_exposure=no_raw_private_key_exposure,
        attestation_present=attestation_present,
        tee_measurement_present=tee_measurement_present,
    )


def evaluate_perps_wallet_signer_prompt_capture_v1(
    profile: Mapping[str, Any] | None,
    capture: Mapping[str, Any] | None,
    *,
    expected_chain_id: str | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    if capture is None:
        return _signer_prompt_capture_status(
            ok=False,
            errors=["perps wallet signer prompt capture is missing"],
            capture=None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            backend_hash=None,
            environment_hash=None,
            environment_policy_hash=None,
            provider=None,
            device_approval_mode=None,
        )
    try:
        capture_obj = _require_mapping(capture, name="signer_prompt_capture")
        _reject_secret_fields(capture_obj, name="signer_prompt_capture")
    except Exception as exc:
        return _signer_prompt_capture_status(
            ok=False,
            errors=[f"perps wallet signer prompt capture invalid: {exc}"],
            capture=capture if isinstance(capture, Mapping) else None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            backend_hash=None,
            environment_hash=None,
            environment_policy_hash=None,
            provider=None,
            device_approval_mode=None,
        )
    if profile is None:
        return _signer_prompt_capture_status(
            ok=False,
            errors=["perps wallet authority profile is missing"],
            capture=capture_obj,
            wallet_authority_hash=None,
            backend_hash=None,
            environment_hash=None,
            environment_policy_hash=None,
            provider=None,
            device_approval_mode=None,
        )

    authority_status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=expected_chain_id)
    if authority_status["production_wallet_authority"] is not True:
        errors.append("perps wallet authority profile is not ready")
        errors.extend(str(gap) for gap in authority_status.get("readiness_gaps", []))

    backend_hash: str | None = None
    environment_hash: str | None = None
    environment_policy_hash: str | None = None
    provider: str | None = None
    device_approval_mode: str | None = None

    try:
        if capture_obj.get("schema") != PERPS_WALLET_SIGNER_PROMPT_CAPTURE_SCHEMA_V1:
            errors.append("perps wallet signer prompt capture schema mismatch")
        chain_id = _require_nonempty_str(capture_obj.get("chain_id"), name="chain_id")
        authority_id = _require_nonempty_str(capture_obj.get("authority_id"), name="authority_id")
        key_id = _require_nonempty_str(capture_obj.get("key_id"), name="key_id")
        current_epoch = _require_nonnegative_int(capture_obj.get("current_epoch"), name="current_epoch")
        _require_nonempty_str(capture_obj.get("device_label"), name="device_label")
        approval_reference = _require_nonempty_str(capture_obj.get("approval_reference"), name="approval_reference")
        prompt_reference = _require_nonempty_str(capture_obj.get("prompt_reference"), name="prompt_reference")
        _require_nonempty_str(capture_obj.get("prompt_source"), name="prompt_source")
        prompt_presented_at_epoch = _require_nonnegative_int(
            capture_obj.get("prompt_presented_at_epoch"),
            name="prompt_presented_at_epoch",
        )
        prompt_confirmed_at_epoch = _require_nonnegative_int(
            capture_obj.get("prompt_confirmed_at_epoch"),
            name="prompt_confirmed_at_epoch",
        )
        _require_root_hash(capture_obj.get("prompt_message_hash"), name="prompt_message_hash")
        _require_nonempty_str(capture_obj.get("capture_source"), name="capture_source")
        _require_root_hash(capture_obj.get("capture_evidence_hash"), name="capture_evidence_hash")
        backend_descriptor = _key_backend_descriptor_from_public_dict(
            _require_mapping(capture_obj.get("backend_descriptor"), name="backend_descriptor")
        )
        environment = _key_execution_environment_from_public_dict(
            _require_mapping(capture_obj.get("environment"), name="environment")
        )
        environment_policy = _device_approval_environment_policy_from_public_dict(
            _require_mapping(capture_obj.get("environment_policy"), name="environment_policy")
        )
    except Exception as exc:
        errors.append(str(exc))
        return _signer_prompt_capture_status(
            ok=False,
            errors=errors,
            capture=capture_obj,
            wallet_authority_hash=profile.get("wallet_authority_hash"),
            backend_hash=None,
            environment_hash=None,
            environment_policy_hash=None,
            provider=None,
            device_approval_mode=None,
        )

    if expected_chain_id is not None and chain_id != expected_chain_id:
        errors.append("perps wallet signer prompt capture chain_id mismatch")
    if chain_id != profile.get("chain_id"):
        errors.append("perps wallet signer prompt capture profile chain_id mismatch")
    if authority_id != profile.get("authority_id"):
        errors.append("perps wallet signer prompt capture authority_id mismatch")
    if prompt_reference != approval_reference:
        errors.append("signer prompt capture prompt_reference does not match approval_reference")
    if prompt_confirmed_at_epoch < prompt_presented_at_epoch:
        errors.append("signer prompt capture confirmation precedes prompt presentation")
    if current_epoch < prompt_confirmed_at_epoch:
        errors.append("signer prompt capture current_epoch precedes prompt confirmation")

    active_key_ids = {
        str(item.get("key_id"))
        for item in authority_status.get("active_signers", [])
        if isinstance(item, Mapping)
    }
    if key_id not in active_key_ids:
        errors.append("perps wallet signer prompt capture key is not active")
    if backend_descriptor.key_id != key_id:
        errors.append("signer prompt capture backend key_id mismatch")

    provider_raw = backend_descriptor.metadata.get("provider")
    device_mode_raw = backend_descriptor.metadata.get("device_approval_mode")
    if not isinstance(provider_raw, str) or not provider_raw:
        errors.append("signer prompt capture backend provider missing")
    else:
        provider = provider_raw
    if not isinstance(device_mode_raw, str) or not device_mode_raw:
        errors.append("signer prompt capture backend device_approval_mode missing")
    else:
        device_approval_mode = device_mode_raw

    if backend_descriptor.backend_kind == BACKEND_OS_KEYCHAIN and environment.environment_kind not in {
        KEY_ENVIRONMENT_LOCAL_PROCESS,
        KEY_ENVIRONMENT_TEE_ATTESTED,
    }:
        errors.append("os_keychain_environment_kind_invalid")
    if backend_descriptor.backend_kind in {
        BACKEND_HARDWARE_WALLET,
        BACKEND_HARDWARE_WALLET_PLACEHOLDER,
        BACKEND_HSM,
        BACKEND_HSM_PLACEHOLDER,
    } and environment.environment_kind not in {
        KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
        KEY_ENVIRONMENT_TEE_ATTESTED,
    }:
        errors.append("hardware_signer_environment_kind_invalid")

    try:
        env_decision = environment_policy.evaluate(
            environment=environment,
            current_epoch=current_epoch,
        )
        if not env_decision.ok:
            errors.append("signer_prompt_capture_environment_rejected")
            errors.extend(str(item) for item in env_decision.errors)
        backend_hash = backend_descriptor.public_dict()["backend_hash"]
        environment_hash = environment.public_dict()["environment_hash"]
        environment_policy_hash = _device_approval_environment_policy_public_dict(environment_policy)[
            "environment_policy_hash"
        ]
    except Exception as exc:
        errors.append(f"signer prompt capture environment evaluation failed: {exc}")

    return _signer_prompt_capture_status(
        ok=not errors,
        errors=errors,
        capture=capture_obj,
        wallet_authority_hash=profile.get("wallet_authority_hash"),
        backend_hash=backend_hash,
        environment_hash=environment_hash,
        environment_policy_hash=environment_policy_hash,
        provider=provider,
        device_approval_mode=device_approval_mode,
    )


def evaluate_perps_wallet_signer_execution_exercise_v1(
    profile: Mapping[str, Any] | None,
    exercise: Mapping[str, Any] | None,
    *,
    expected_chain_id: str | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    if exercise is None:
        return _signer_execution_exercise_status(
            ok=False,
            errors=["perps wallet signer execution exercise is missing"],
            exercise=None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            sign_admission_receipt=None,
            backend_hash=None,
            environment_hash=None,
            use_policy_hash=None,
            environment_policy_hash=None,
            provider=None,
            device_approval_mode=None,
        )
    try:
        exercise_obj = _require_mapping(exercise, name="signer_execution_exercise")
        _reject_secret_fields(exercise_obj, name="signer_execution_exercise")
    except Exception as exc:
        return _signer_execution_exercise_status(
            ok=False,
            errors=[f"perps wallet signer execution exercise invalid: {exc}"],
            exercise=exercise if isinstance(exercise, Mapping) else None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            sign_admission_receipt=None,
            backend_hash=None,
            environment_hash=None,
            use_policy_hash=None,
            environment_policy_hash=None,
            provider=None,
            device_approval_mode=None,
        )
    if profile is None:
        return _signer_execution_exercise_status(
            ok=False,
            errors=["perps wallet authority profile is missing"],
            exercise=exercise_obj,
            wallet_authority_hash=None,
            sign_admission_receipt=None,
            backend_hash=None,
            environment_hash=None,
            use_policy_hash=None,
            environment_policy_hash=None,
            provider=None,
            device_approval_mode=None,
        )

    authority_status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=expected_chain_id)
    if authority_status["production_wallet_authority"] is not True:
        errors.append("perps wallet authority profile is not ready")
        errors.extend(str(gap) for gap in authority_status.get("readiness_gaps", []))

    backend_hash: str | None = None
    environment_hash: str | None = None
    use_policy_hash: str | None = None
    environment_policy_hash: str | None = None
    provider: str | None = None
    device_approval_mode: str | None = None
    sign_admission_receipt: Mapping[str, Any] | None = None

    try:
        if exercise_obj.get("schema") != PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_SCHEMA_V1:
            errors.append("perps wallet signer execution exercise schema mismatch")
        chain_id = _require_nonempty_str(exercise_obj.get("chain_id"), name="chain_id")
        authority_id = _require_nonempty_str(exercise_obj.get("authority_id"), name="authority_id")
        key_id = _require_nonempty_str(exercise_obj.get("key_id"), name="key_id")
        payload_kind = _require_nonempty_str(exercise_obj.get("payload_kind"), name="payload_kind")
        purpose = _require_nonempty_str(exercise_obj.get("purpose"), name="purpose")
        current_epoch = _require_nonnegative_int(exercise_obj.get("current_epoch"), name="current_epoch")
        _require_nonempty_str(exercise_obj.get("device_label"), name="device_label")
        _require_nonempty_str(exercise_obj.get("approval_reference"), name="approval_reference")
        _require_nonempty_str(exercise_obj.get("prompt_reference"), name="prompt_reference")
        prompt_presented_at_epoch = _require_nonnegative_int(
            exercise_obj.get("prompt_presented_at_epoch"),
            name="prompt_presented_at_epoch",
        )
        prompt_confirmed_at_epoch = _require_nonnegative_int(
            exercise_obj.get("prompt_confirmed_at_epoch"),
            name="prompt_confirmed_at_epoch",
        )
        _require_nonempty_str(exercise_obj.get("execution_reference"), name="execution_reference")
        signed_payload_hash = _require_root_hash(exercise_obj.get("signed_payload_hash"), name="signed_payload_hash")
        backend_descriptor = _key_backend_descriptor_from_public_dict(
            _require_mapping(exercise_obj.get("backend_descriptor"), name="backend_descriptor")
        )
        use_policy = _device_approval_use_policy_from_public_dict(
            _require_mapping(exercise_obj.get("use_policy"), name="use_policy")
        )
        environment = _key_execution_environment_from_public_dict(
            _require_mapping(exercise_obj.get("environment"), name="environment")
        )
        environment_policy = _device_approval_environment_policy_from_public_dict(
            _require_mapping(exercise_obj.get("environment_policy"), name="environment_policy")
        )
        payload = dict(_require_mapping(exercise_obj.get("payload"), name="payload"))
        seen_nonces = tuple(_require_int_list(exercise_obj.get("seen_nonces", []), name="seen_nonces"))
        _reject_secret_fields(payload, name="payload")
    except Exception as exc:
        errors.append(str(exc))
        return _signer_execution_exercise_status(
            ok=False,
            errors=errors,
            exercise=exercise_obj,
            wallet_authority_hash=profile.get("wallet_authority_hash"),
            sign_admission_receipt=None,
            backend_hash=None,
            environment_hash=None,
            use_policy_hash=None,
            environment_policy_hash=None,
            provider=None,
            device_approval_mode=None,
        )

    if expected_chain_id is not None and chain_id != expected_chain_id:
        errors.append("perps wallet signer execution exercise chain_id mismatch")
    if chain_id != profile.get("chain_id"):
        errors.append("perps wallet signer execution exercise profile chain_id mismatch")
    if authority_id != profile.get("authority_id"):
        errors.append("perps wallet signer execution exercise authority_id mismatch")
    if prompt_confirmed_at_epoch < prompt_presented_at_epoch:
        errors.append("signer execution prompt confirmation precedes prompt presentation")
    if current_epoch < prompt_confirmed_at_epoch:
        errors.append("signer execution current_epoch precedes prompt confirmation")

    active_key_ids = {
        str(item.get("key_id"))
        for item in authority_status.get("active_signers", [])
        if isinstance(item, Mapping)
    }
    if key_id not in active_key_ids:
        errors.append("perps wallet signer execution exercise key is not active")
    if backend_descriptor.key_id != key_id:
        errors.append("signer execution backend key_id mismatch")

    provider_raw = backend_descriptor.metadata.get("provider")
    device_mode_raw = backend_descriptor.metadata.get("device_approval_mode")
    if not isinstance(provider_raw, str) or not provider_raw:
        errors.append("signer execution backend provider missing")
    else:
        provider = provider_raw
    if not isinstance(device_mode_raw, str) or not device_mode_raw:
        errors.append("signer execution backend device_approval_mode missing")
    else:
        device_approval_mode = device_mode_raw

    if backend_descriptor.backend_kind == BACKEND_OS_KEYCHAIN and environment.environment_kind not in {
        KEY_ENVIRONMENT_LOCAL_PROCESS,
        KEY_ENVIRONMENT_TEE_ATTESTED,
    }:
        errors.append("os_keychain_environment_kind_invalid")
    if backend_descriptor.backend_kind in {
        BACKEND_HARDWARE_WALLET,
        BACKEND_HARDWARE_WALLET_PLACEHOLDER,
        BACKEND_HSM,
        BACKEND_HSM_PLACEHOLDER,
    } and environment.environment_kind not in {
        KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
        KEY_ENVIRONMENT_TEE_ATTESTED,
    }:
        errors.append("hardware_signer_environment_kind_invalid")

    try:
        key_manager = _require_mapping(profile.get("key_manager"), name="key_manager")
        key_ref = _key_ref_from_key_manager_public(key_manager=key_manager, key_id=key_id)
        context = SignRequestContext(
            payload_kind=payload_kind,
            chain_id=chain_id,
            purpose=purpose,
            current_epoch=current_epoch,
        )
        sign_admission_receipt = evaluate_sign_admission_v0(
            SignAdmissionRequest(
                key_ref=key_ref,
                backend=backend_descriptor,
                policy=use_policy,
                context=context,
                payload=payload,
                environment=environment,
                environment_policy=environment_policy,
                seen_nonces=seen_nonces,
            )
        )
        backend_hash = backend_descriptor.public_dict()["backend_hash"]
        environment_hash = environment.public_dict()["environment_hash"]
        use_policy_hash = _device_approval_use_policy_public_dict(use_policy)["use_policy_hash"]
        environment_policy_hash = _device_approval_environment_policy_public_dict(environment_policy)[
            "environment_policy_hash"
        ]
        if sign_admission_receipt.get("ok") is not True:
            errors.append("signer_execution_sign_admission_rejected")
            errors.extend(str(item) for item in sign_admission_receipt.get("errors", ()))
        if sign_admission_receipt.get("payload_hash") != signed_payload_hash:
            errors.append("signer execution signed_payload_hash mismatch")
    except Exception as exc:
        errors.append(f"signer execution sign admission failed: {exc}")

    return _signer_execution_exercise_status(
        ok=not errors and sign_admission_receipt is not None and sign_admission_receipt.get("ok") is True,
        errors=errors,
        exercise=exercise_obj,
        wallet_authority_hash=profile.get("wallet_authority_hash"),
        sign_admission_receipt=sign_admission_receipt,
        backend_hash=backend_hash,
        environment_hash=environment_hash,
        use_policy_hash=use_policy_hash,
        environment_policy_hash=environment_policy_hash,
        provider=provider,
        device_approval_mode=device_approval_mode,
    )


def evaluate_perps_wallet_signer_ceremony_v1(
    *,
    wallet_authority_hash: str | None,
    device_approval_status: Mapping[str, Any] | None,
    signer_device_status: Mapping[str, Any] | None,
    signer_prompt_capture_status: Mapping[str, Any] | None,
    signer_execution_status: Mapping[str, Any] | None,
) -> dict[str, Any]:
    errors: list[str] = []
    components = {
        "device_approval_status": device_approval_status,
        "signer_device_status": signer_device_status,
        "signer_prompt_capture_status": signer_prompt_capture_status,
        "signer_execution_status": signer_execution_status,
    }
    for name, component in components.items():
        if component is None:
            errors.append(f"{name} is missing")

    if device_approval_status is not None and device_approval_status.get("device_approval_ready") is not True:
        errors.append("signer ceremony device approval is not ready")
    if signer_device_status is not None and signer_device_status.get("signer_device_ready") is not True:
        errors.append("signer ceremony signer-device report is not ready")
    if signer_prompt_capture_status is not None and signer_prompt_capture_status.get("signer_prompt_capture_ready") is not True:
        errors.append("signer ceremony signer prompt capture is not ready")
    if signer_execution_status is not None and signer_execution_status.get("signer_execution_ready") is not True:
        errors.append("signer ceremony signer execution is not ready")

    if wallet_authority_hash is not None:
        for label, component in (
            ("device approval", device_approval_status),
            ("signer device", signer_device_status),
            ("signer prompt capture", signer_prompt_capture_status),
            ("signer execution", signer_execution_status),
        ):
            if component is not None and component.get("wallet_authority_hash") != wallet_authority_hash:
                errors.append(f"signer ceremony {label} wallet_authority_hash mismatch")

    def _match(
        label: str,
        left: Mapping[str, Any] | None,
        left_name: str,
        right: Mapping[str, Any] | None,
        right_name: str,
    ) -> None:
        if left is None or right is None:
            return
        if left.get(left_name) != right.get(right_name):
            errors.append(f"signer ceremony {label} mismatch")

    _match("key_id", signer_device_status, "key_id", signer_prompt_capture_status, "key_id")
    _match("key_id", signer_device_status, "key_id", signer_execution_status, "key_id")
    _match("approval_reference", signer_device_status, "approval_reference", signer_prompt_capture_status, "approval_reference")
    _match("approval_reference", signer_device_status, "approval_reference", signer_execution_status, "approval_reference")
    _match("prompt_reference", signer_prompt_capture_status, "prompt_reference", signer_execution_status, "prompt_reference")
    _match("prompt_message_hash", signer_prompt_capture_status, "prompt_message_hash", signer_execution_status, "signed_payload_hash")
    _match("provider", signer_device_status, "provider", signer_prompt_capture_status, "provider")
    _match("provider", signer_device_status, "provider", signer_execution_status, "provider")
    _match("device_approval_mode", signer_device_status, "device_approval_mode", signer_prompt_capture_status, "device_approval_mode")
    _match("device_approval_mode", signer_device_status, "device_approval_mode", signer_execution_status, "device_approval_mode")
    _match("backend_hash", signer_device_status, "backend_hash", signer_prompt_capture_status, "backend_hash")
    _match("backend_hash", signer_device_status, "backend_hash", signer_execution_status, "backend_hash")
    _match("environment_hash", signer_device_status, "environment_hash", signer_prompt_capture_status, "environment_hash")
    _match("environment_hash", signer_device_status, "environment_hash", signer_execution_status, "environment_hash")

    return _signer_ceremony_status(
        ok=not errors,
        errors=errors,
        wallet_authority_hash=wallet_authority_hash,
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
    )


def evaluate_perps_wallet_hardware_custody_v1(
    *,
    wallet_authority_hash: str | None,
    device_approval_status: Mapping[str, Any] | None,
    signer_device_status: Mapping[str, Any] | None,
    signer_prompt_capture_status: Mapping[str, Any] | None,
    signer_execution_status: Mapping[str, Any] | None,
    signer_ceremony_status: Mapping[str, Any] | None,
    production_hardware_evidence_status: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    components = {
        "device_approval_status": device_approval_status,
        "signer_device_status": signer_device_status,
        "signer_prompt_capture_status": signer_prompt_capture_status,
        "signer_execution_status": signer_execution_status,
        "signer_ceremony_status": signer_ceremony_status,
    }
    for name, component in components.items():
        if component is None:
            errors.append(f"{name} is missing")

    if device_approval_status is not None and device_approval_status.get("device_approval_ready") is not True:
        errors.append("hardware custody device approval is not ready")
    if signer_device_status is not None and signer_device_status.get("signer_device_ready") is not True:
        errors.append("hardware custody signer-device report is not ready")
    if signer_prompt_capture_status is not None and signer_prompt_capture_status.get("signer_prompt_capture_ready") is not True:
        errors.append("hardware custody signer prompt capture is not ready")
    if signer_execution_status is not None and signer_execution_status.get("signer_execution_ready") is not True:
        errors.append("hardware custody signer execution is not ready")
    if signer_ceremony_status is not None and signer_ceremony_status.get("signer_ceremony_ready") is not True:
        errors.append("hardware custody signer ceremony is not ready")

    if wallet_authority_hash is not None:
        for label, component in (
            ("device approval", device_approval_status),
            ("signer device", signer_device_status),
            ("signer prompt capture", signer_prompt_capture_status),
            ("signer execution", signer_execution_status),
            ("signer ceremony", signer_ceremony_status),
        ):
            if component is not None and component.get("wallet_authority_hash") != wallet_authority_hash:
                errors.append(f"hardware custody {label} wallet_authority_hash mismatch")

    if signer_device_status is not None:
        backend_kind = signer_device_status.get("backend_kind")
        if backend_kind not in {
            BACKEND_HARDWARE_WALLET,
            BACKEND_HARDWARE_WALLET_PLACEHOLDER,
            BACKEND_HSM,
            BACKEND_HSM_PLACEHOLDER,
        }:
            errors.append("hardware custody backend_kind is not hardware-backed")

        environment_kind = signer_device_status.get("environment_kind")
        if environment_kind not in {KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE, KEY_ENVIRONMENT_TEE_ATTESTED}:
            errors.append("hardware custody environment_kind is not hardware-backed")

        if signer_device_status.get("no_raw_private_key_exposure") is not True:
            errors.append("hardware custody backend raw private key exposure not ruled out")
        if signer_device_status.get("local_user_presence_confirmed") is not True:
            errors.append("hardware custody local user presence not confirmed")
        if signer_device_status.get("rollback_protection_confirmed") is not True:
            errors.append("hardware custody rollback protection not confirmed")
        if environment_kind == KEY_ENVIRONMENT_TEE_ATTESTED and signer_device_status.get("tee_measurement_present") is not True:
            errors.append("hardware custody tee measurement missing")

    def _match(
        label: str,
        left: Mapping[str, Any] | None,
        left_name: str,
        right: Mapping[str, Any] | None,
        right_name: str,
    ) -> None:
        if left is None or right is None:
            return
        if left.get(left_name) != right.get(right_name):
            errors.append(f"hardware custody {label} mismatch")

    _match("backend_hash", signer_device_status, "backend_hash", signer_prompt_capture_status, "backend_hash")
    _match("backend_hash", signer_device_status, "backend_hash", signer_execution_status, "backend_hash")
    _match("environment_hash", signer_device_status, "environment_hash", signer_prompt_capture_status, "environment_hash")
    _match("environment_hash", signer_device_status, "environment_hash", signer_execution_status, "environment_hash")
    _match("approval_reference", signer_device_status, "approval_reference", signer_prompt_capture_status, "approval_reference")
    _match("approval_reference", signer_device_status, "approval_reference", signer_execution_status, "approval_reference")
    _match("prompt_reference", signer_prompt_capture_status, "prompt_reference", signer_execution_status, "prompt_reference")
    _match("execution_reference", signer_execution_status, "execution_reference", signer_ceremony_status, "execution_reference")

    return _hardware_custody_status(
        ok=not errors,
        errors=errors,
        wallet_authority_hash=wallet_authority_hash,
        device_approval_status=device_approval_status,
        signer_device_status=signer_device_status,
        signer_prompt_capture_status=signer_prompt_capture_status,
        signer_execution_status=signer_execution_status,
        signer_ceremony_status=signer_ceremony_status,
        production_hardware_evidence_status=production_hardware_evidence_status,
    )


def _active_signer_summaries(active_signers: list[Mapping[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "signer_id": str(signer.get("signer_id", "")),
            "key_id": str(signer.get("key_id", "")),
            "weight": int(signer.get("weight", 0)) if isinstance(signer.get("weight"), int) else 0,
            "signer_hash": signer.get("signer_hash"),
        }
        for signer in sorted(active_signers, key=lambda item: (str(item.get("signer_id")), str(item.get("key_id"))))
    ]


def _transaction_scope_summary(scope: Mapping[str, Any], gaps: list[str]) -> dict[str, Any]:
    stream_key = scope.get("stream_key")
    if stream_key != "22":
        gaps.append("transaction_scope.stream_key must be 22")
    allowed_actions = scope.get("allowed_actions")
    if (
        not isinstance(allowed_actions, list)
        or len(allowed_actions) == 0
        or not all(isinstance(item, str) and item for item in allowed_actions)
    ):
        gaps.append("transaction_scope.allowed_actions must be a non-empty string list")
        allowed_actions_summary: list[str] = []
    else:
        allowed_actions_summary = sorted(set(allowed_actions))
    return {
        "stream_key": stream_key,
        "allowed_actions": allowed_actions_summary,
    }


def evaluate_perps_wallet_authority_profile_v1(
    profile: Mapping[str, Any] | None,
    *,
    expected_chain_id: str | None = None,
) -> dict[str, Any]:
    gaps: list[str] = []
    if profile is None:
        gaps.append("perps wallet authority profile is missing")
        return _status(
            ok=False,
            production_wallet_authority=False,
            readiness_gaps=gaps,
            profile=None,
            active_signer_count=0,
            threshold=0,
            key_ref_count=0,
            recovery_policy_count=0,
            recoverable_active_key_count=0,
            key_refs=[],
            active_signers=[],
            recovery_policies=[],
            wallet_ux={},
            proof_profile={},
            transaction_scope={},
        )

    try:
        obj = _require_mapping(profile, name="profile")
    except Exception as exc:
        gaps.append(f"perps wallet authority profile invalid: {exc}")
        return _status(
            ok=False,
            production_wallet_authority=False,
            readiness_gaps=gaps,
            profile=None,
            active_signer_count=0,
            threshold=0,
            key_ref_count=0,
            recovery_policy_count=0,
            recoverable_active_key_count=0,
            key_refs=[],
            active_signers=[],
            recovery_policies=[],
            wallet_ux={},
            proof_profile={},
            transaction_scope={},
        )

    if obj.get("schema") != PERPS_WALLET_AUTHORITY_PROFILE_SCHEMA_V1:
        gaps.append("perps wallet authority profile schema mismatch")
    if obj.get("enabled") is not True:
        gaps.append("perps wallet authority profile is not enabled")
    if obj.get("stage") != "production":
        gaps.append("perps wallet authority profile stage must be production")

    try:
        _require_nonempty_str(obj.get("authority_id"), name="authority_id")
    except Exception as exc:
        gaps.append(str(exc))
    try:
        chain_id = _require_nonempty_str(obj.get("chain_id"), name="chain_id")
        if expected_chain_id is not None and chain_id != expected_chain_id:
            gaps.append("perps wallet authority profile chain_id mismatch")
    except Exception as exc:
        gaps.append(str(exc))

    expected_hash = perps_wallet_authority_profile_hash_v1(obj)
    if obj.get("wallet_authority_hash") != expected_hash:
        gaps.append("perps wallet authority profile hash mismatch")

    key_refs: dict[str, KeyRef] = {}
    recovery_policies_raw: list[Mapping[str, Any]] = []
    try:
        key_manager = _require_mapping(obj.get("key_manager"), name="key_manager")
        key_refs, recovery_policies_raw = _validate_key_manager_public(key_manager, gaps)
    except Exception as exc:
        gaps.append(f"key manager invalid: {exc}")

    active_signers: list[Mapping[str, Any]] = []
    threshold = 0
    try:
        signer_registry = _require_mapping(obj.get("signer_registry"), name="signer_registry")
        active_signers, threshold = _active_signer_entries(signer_registry, gaps)
        _validate_signer_key_bindings(active_signers=active_signers, key_refs=key_refs, gaps=gaps)
    except Exception as exc:
        gaps.append(f"signer registry invalid: {exc}")

    recovery_policy_summaries: list[dict[str, Any]] = []
    recoverable_active_key_count = 0
    try:
        recovery_policy_summaries, recoverable_active_key_count = _validate_recovery_policies_public(
            recovery_policies_raw=recovery_policies_raw,
            key_refs=key_refs,
            active_signers=active_signers,
            gaps=gaps,
        )
    except Exception as exc:
        gaps.append(f"recovery policies invalid: {exc}")

    wallet_ux_summary: dict[str, bool] = {}
    try:
        wallet_ux = _require_mapping(obj.get("wallet_ux"), name="wallet_ux")
        wallet_ux_summary = _public_flag_profile(wallet_ux, _REQUIRED_WALLET_UX_FLAGS)
        _validate_flag_profile(
            profile=wallet_ux,
            required_flags=_REQUIRED_WALLET_UX_FLAGS,
            profile_name="wallet_ux",
            gaps=gaps,
        )
    except Exception as exc:
        gaps.append(f"wallet_ux invalid: {exc}")

    proof_profile_summary: dict[str, Any] = {}
    try:
        proof_profile = _require_mapping(obj.get("proof_profile"), name="proof_profile")
        proof_profile_summary = {
            **_public_flag_profile(proof_profile, _REQUIRED_PROOF_FLAGS),
            "runtime_proof_profile": proof_profile.get("runtime_proof_profile"),
        }
        _validate_flag_profile(
            profile=proof_profile,
            required_flags=_REQUIRED_PROOF_FLAGS,
            profile_name="proof_profile",
            gaps=gaps,
        )
        if not isinstance(proof_profile.get("runtime_proof_profile"), str) or not proof_profile.get("runtime_proof_profile"):
            gaps.append("proof_profile.runtime_proof_profile must be a non-empty string")
    except Exception as exc:
        gaps.append(f"proof_profile invalid: {exc}")

    transaction_scope_summary: dict[str, Any] = {}
    try:
        transaction_scope = _require_mapping(obj.get("transaction_scope"), name="transaction_scope")
        transaction_scope_summary = _transaction_scope_summary(transaction_scope, gaps)
    except Exception as exc:
        gaps.append(f"transaction_scope invalid: {exc}")

    production_wallet_authority = not gaps
    return _status(
        ok=production_wallet_authority,
        production_wallet_authority=production_wallet_authority,
        readiness_gaps=gaps,
        profile=obj,
        active_signer_count=len(active_signers),
        threshold=threshold,
        key_ref_count=len(key_refs),
        recovery_policy_count=len(recovery_policy_summaries),
        recoverable_active_key_count=recoverable_active_key_count,
        expected_wallet_authority_hash=expected_hash,
        key_refs=_key_ref_summaries(key_refs),
        active_signers=_active_signer_summaries(active_signers),
        recovery_policies=recovery_policy_summaries,
        wallet_ux=wallet_ux_summary,
        proof_profile=proof_profile_summary,
        transaction_scope=transaction_scope_summary,
    )


def _status(
    *,
    ok: bool,
    production_wallet_authority: bool,
    readiness_gaps: list[str],
    profile: Mapping[str, Any] | None,
    active_signer_count: int,
    threshold: int,
    key_ref_count: int,
    recovery_policy_count: int,
    recoverable_active_key_count: int,
    expected_wallet_authority_hash: str | None = None,
    key_refs: list[dict[str, Any]] | None = None,
    active_signers: list[dict[str, Any]] | None = None,
    recovery_policies: list[dict[str, Any]] | None = None,
    wallet_ux: Mapping[str, Any] | None = None,
    proof_profile: Mapping[str, Any] | None = None,
    transaction_scope: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return {
        "schema": PERPS_WALLET_AUTHORITY_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "production_wallet_authority": bool(production_wallet_authority),
        "status": "ready" if production_wallet_authority else "blocked",
        "readiness_gaps": list(readiness_gaps),
        "authority_id": None if profile is None else profile.get("authority_id"),
        "chain_id": None if profile is None else profile.get("chain_id"),
        "stage": None if profile is None else profile.get("stage"),
        "enabled": False if profile is None else bool(profile.get("enabled") is True),
        "wallet_authority_hash": None if profile is None else profile.get("wallet_authority_hash"),
        "expected_wallet_authority_hash": expected_wallet_authority_hash,
        "signer_registry_hash": None
        if profile is None or not isinstance(profile.get("signer_registry"), Mapping)
        else profile["signer_registry"].get("registry_hash"),
        "key_manager_hash": None
        if profile is None or not isinstance(profile.get("key_manager"), Mapping)
        else profile["key_manager"].get("manager_hash"),
        "active_signer_count": int(active_signer_count),
        "threshold": int(threshold),
        "key_ref_count": int(key_ref_count),
        "recovery_policy_count": int(recovery_policy_count),
        "recoverable_active_key_count": int(recoverable_active_key_count),
        "key_refs": list(key_refs or []),
        "active_signers": list(active_signers or []),
        "recovery_policies": list(recovery_policies or []),
        "wallet_ux": dict(wallet_ux or {}),
        "proof_profile": dict(proof_profile or {}),
        "transaction_scope": dict(transaction_scope or {}),
        "not_claimed": list(_NOT_CLAIMED),
    }
