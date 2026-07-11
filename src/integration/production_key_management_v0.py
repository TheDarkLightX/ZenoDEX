"""Pure production key-management admission for privileged actions."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Callable, Mapping

from src.integration.zeno_ledger_v0 import ZERO_ROOT_V0, hash_v0


KEY_DESCRIPTOR_SCHEMA_V0 = "zenodex.production_key_management.key_descriptor.v0"
ACTION_POLICY_SCHEMA_V0 = "zenodex.production_key_management.action_policy.v0"
PRIVILEGED_ACTION_PACKET_SCHEMA_V0 = "zenodex.production_key_management.privileged_action_packet.v0"
SIGNATURE_ENVELOPE_SCHEMA_V0 = "zenodex.production_key_management.signature_envelope.v0"
ADMISSION_RECEIPT_SCHEMA_V0 = "zenodex.production_key_management.admission_receipt.v0"

ENVIRONMENTS_V0 = frozenset({"testnet", "production"})
KEY_STATUSES_V0 = frozenset({"active", "revoked", "expired"})
STORAGE_CLASSES_V0 = frozenset({"software", "hardware", "hsm", "mpc"})
NON_SOFTWARE_STORAGE_CLASSES_V0 = frozenset({"hardware", "hsm", "mpc"})
ROLES_V0 = frozenset({"treasury", "config", "validator", "oracle", "verifier", "release", "emergency"})
ACTIONS_V0 = frozenset(
    {
        "protocol_treasury_spend",
        "dao_treasury_grant",
        "public_network_config_update",
        "validator_set_update",
        "oracle_reporter_registry_update",
        "verifier_registry_update",
        "release_artifact_publish",
        "emergency_pause",
        "emergency_unpause",
        "key_revocation",
        "signer_rotation",
        "routine_node_heartbeat",
    }
)
SIGNATURE_SCHEMES_V0 = frozenset({"external-verifier-v0"})
RECEIPT_STATUSES_V0 = frozenset({"accepted", "rejected"})

_ROOT = Path(__file__).resolve().parents[2]
_PROPERTY_MODEL_PATH = _ROOT / "formal/property/production_key_management_v0.json"

SignatureVerifierV0 = Callable[[Mapping[str, Any], Mapping[str, Any], Mapping[str, Any]], bool]


def _load_default_action_policies() -> dict[str, dict[str, Any]]:
    model = json.loads(_PROPERTY_MODEL_PATH.read_text(encoding="utf-8"))
    policies = model.get("action_policies")
    if not isinstance(policies, dict):
        raise ValueError("production key-management action_policies must be an object")
    return {
        str(action): build_action_policy_v0(action=str(action), **dict(policy))
        for action, policy in sorted(policies.items())
    }


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty str")
    return value


def _require_optional_str(value: object, *, name: str) -> str | None:
    if value is None:
        return None
    return _require_str(value, name=name)


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return value


def _require_positive_int(value: object, *, name: str) -> int:
    value_int = _require_nonnegative_int(value, name=name)
    if value_int <= 0:
        raise ValueError(f"{name} must be a positive int")
    return value_int


def _require_list(value: object, *, name: str) -> list[Any]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    return value


def _content_hash(domain: str, obj: Mapping[str, Any], *, omit_key: str) -> str:
    body = dict(obj)
    body.pop(omit_key, None)
    return hash_v0(domain, body)


def key_descriptor_content_hash_v0(descriptor: Mapping[str, Any]) -> str:
    return _content_hash("production_key_descriptor_v0", descriptor, omit_key="key_descriptor_hash")


def action_policy_content_hash_v0(policy: Mapping[str, Any]) -> str:
    return _content_hash("production_action_policy_v0", policy, omit_key="policy_hash")


def privileged_action_packet_content_hash_v0(packet: Mapping[str, Any]) -> str:
    return _content_hash("production_privileged_action_packet_v0", packet, omit_key="packet_hash")


def signature_envelope_content_hash_v0(envelope: Mapping[str, Any]) -> str:
    return _content_hash("production_signature_envelope_v0", envelope, omit_key="signature_envelope_hash")


def admission_receipt_content_hash_v0(receipt: Mapping[str, Any]) -> str:
    return _content_hash("production_admission_receipt_v0", receipt, omit_key="receipt_hash")


def build_key_descriptor_v0(
    *,
    key_id: str,
    public_key: str,
    role: str,
    environment: str,
    status: str,
    storage_class: str,
    custodian_id: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
    break_glass: bool = False,
    custody_model: str | None = None,
    recovery_policy_hash: str | None = None,
) -> dict[str, Any]:
    descriptor = {
        "schema": KEY_DESCRIPTOR_SCHEMA_V0,
        "key_id": key_id,
        "public_key": public_key,
        "role": role,
        "environment": environment,
        "status": status,
        "storage_class": storage_class,
        "custodian_id": custodian_id,
        "break_glass": break_glass,
        "custody_model": custody_model,
        "recovery_policy_hash": recovery_policy_hash,
        "valid_from_epoch": valid_from_epoch,
        "valid_until_epoch": valid_until_epoch,
        "key_descriptor_hash": ZERO_ROOT_V0,
    }
    descriptor["key_descriptor_hash"] = key_descriptor_content_hash_v0(descriptor)
    validate_key_descriptor_v0(descriptor)
    return descriptor


def validate_key_descriptor_v0(descriptor: Mapping[str, Any]) -> None:
    obj = _require_mapping(descriptor, name="key_descriptor")
    expected = {
        "schema",
        "key_id",
        "public_key",
        "role",
        "environment",
        "status",
        "storage_class",
        "custodian_id",
        "break_glass",
        "custody_model",
        "recovery_policy_hash",
        "valid_from_epoch",
        "valid_until_epoch",
        "key_descriptor_hash",
    }
    if set(obj.keys()) != expected:
        raise ValueError("key_descriptor keys mismatch")
    if obj.get("schema") != KEY_DESCRIPTOR_SCHEMA_V0:
        raise ValueError("key_descriptor schema mismatch")
    _require_str(obj.get("key_id"), name="key_descriptor.key_id")
    _require_str(obj.get("public_key"), name="key_descriptor.public_key")
    role = _require_str(obj.get("role"), name="key_descriptor.role")
    if role not in ROLES_V0:
        raise ValueError("key_descriptor role is not allowed")
    environment = _require_str(obj.get("environment"), name="key_descriptor.environment")
    if environment not in ENVIRONMENTS_V0:
        raise ValueError("key_descriptor environment is not allowed")
    status = _require_str(obj.get("status"), name="key_descriptor.status")
    if status not in KEY_STATUSES_V0:
        raise ValueError("key_descriptor status is not allowed")
    storage_class = _require_str(obj.get("storage_class"), name="key_descriptor.storage_class")
    if storage_class not in STORAGE_CLASSES_V0:
        raise ValueError("key_descriptor storage_class is not allowed")
    _require_str(obj.get("custodian_id"), name="key_descriptor.custodian_id")
    break_glass = _require_bool(obj.get("break_glass"), name="key_descriptor.break_glass")
    if break_glass and role != "emergency":
        raise ValueError("break_glass key_descriptor must use emergency role")
    _require_optional_str(obj.get("custody_model"), name="key_descriptor.custody_model")
    _require_optional_str(obj.get("recovery_policy_hash"), name="key_descriptor.recovery_policy_hash")
    valid_from = _require_nonnegative_int(obj.get("valid_from_epoch"), name="key_descriptor.valid_from_epoch")
    valid_until = _require_nonnegative_int(obj.get("valid_until_epoch"), name="key_descriptor.valid_until_epoch")
    if valid_until < valid_from:
        raise ValueError("key_descriptor valid_until_epoch precedes valid_from_epoch")
    expected_hash = key_descriptor_content_hash_v0(obj)
    if obj.get("key_descriptor_hash") != expected_hash:
        raise ValueError("key_descriptor hash mismatch")


def build_action_policy_v0(
    *,
    action: str,
    role: str,
    critical: bool,
    threshold: int,
    min_distinct_custodians: int,
    hardware_required: bool,
    timelock_required: bool,
    break_glass_allowed: bool,
    transparency_required: bool,
) -> dict[str, Any]:
    policy = {
        "schema": ACTION_POLICY_SCHEMA_V0,
        "action": action,
        "role": role,
        "critical": critical,
        "threshold": threshold,
        "min_distinct_custodians": min_distinct_custodians,
        "hardware_required": hardware_required,
        "timelock_required": timelock_required,
        "break_glass_allowed": break_glass_allowed,
        "transparency_required": transparency_required,
        "policy_hash": ZERO_ROOT_V0,
    }
    policy["policy_hash"] = action_policy_content_hash_v0(policy)
    validate_action_policy_v0(policy)
    return policy


def validate_action_policy_v0(policy: Mapping[str, Any]) -> None:
    obj = _require_mapping(policy, name="action_policy")
    expected = {
        "schema",
        "action",
        "role",
        "critical",
        "threshold",
        "min_distinct_custodians",
        "hardware_required",
        "timelock_required",
        "break_glass_allowed",
        "transparency_required",
        "policy_hash",
    }
    if set(obj.keys()) != expected:
        raise ValueError("action_policy keys mismatch")
    if obj.get("schema") != ACTION_POLICY_SCHEMA_V0:
        raise ValueError("action_policy schema mismatch")
    action = _require_str(obj.get("action"), name="action_policy.action")
    if action not in ACTIONS_V0:
        raise ValueError("action_policy action is not allowed")
    role = _require_str(obj.get("role"), name="action_policy.role")
    if role not in ROLES_V0:
        raise ValueError("action_policy role is not allowed")
    critical = _require_bool(obj.get("critical"), name="action_policy.critical")
    threshold = _require_positive_int(obj.get("threshold"), name="action_policy.threshold")
    min_distinct = _require_positive_int(
        obj.get("min_distinct_custodians"),
        name="action_policy.min_distinct_custodians",
    )
    if critical and (threshold < 2 or min_distinct < 2):
        raise ValueError("critical action_policy requires multi-key distinct-custodian quorum")
    if min_distinct > threshold:
        raise ValueError("action_policy min_distinct_custodians exceeds threshold")
    _require_bool(obj.get("hardware_required"), name="action_policy.hardware_required")
    _require_bool(obj.get("timelock_required"), name="action_policy.timelock_required")
    break_glass_allowed = _require_bool(obj.get("break_glass_allowed"), name="action_policy.break_glass_allowed")
    if break_glass_allowed and action != "emergency_pause":
        raise ValueError("break_glass action_policy is only allowed for emergency_pause")
    _require_bool(obj.get("transparency_required"), name="action_policy.transparency_required")
    if obj.get("policy_hash") != action_policy_content_hash_v0(obj):
        raise ValueError("action_policy hash mismatch")


def build_privileged_action_packet_v0(
    *,
    environment: str,
    action: str,
    target_kind: str,
    target_hash: str,
    policy_hash: str,
    nonce: int,
    epoch: int,
    not_before_epoch: int,
    expires_at_epoch: int,
    payload_hash: str,
) -> dict[str, Any]:
    packet = {
        "schema": PRIVILEGED_ACTION_PACKET_SCHEMA_V0,
        "environment": environment,
        "action": action,
        "target_kind": target_kind,
        "target_hash": target_hash,
        "policy_hash": policy_hash,
        "nonce": nonce,
        "epoch": epoch,
        "not_before_epoch": not_before_epoch,
        "expires_at_epoch": expires_at_epoch,
        "payload_hash": payload_hash,
        "packet_hash": ZERO_ROOT_V0,
    }
    packet["packet_hash"] = privileged_action_packet_content_hash_v0(packet)
    validate_privileged_action_packet_v0(packet)
    return packet


def validate_privileged_action_packet_v0(packet: Mapping[str, Any]) -> None:
    obj = _require_mapping(packet, name="privileged_action_packet")
    expected = {
        "schema",
        "environment",
        "action",
        "target_kind",
        "target_hash",
        "policy_hash",
        "nonce",
        "epoch",
        "not_before_epoch",
        "expires_at_epoch",
        "payload_hash",
        "packet_hash",
    }
    if set(obj.keys()) != expected:
        raise ValueError("privileged_action_packet keys mismatch")
    if obj.get("schema") != PRIVILEGED_ACTION_PACKET_SCHEMA_V0:
        raise ValueError("privileged_action_packet schema mismatch")
    environment = _require_str(obj.get("environment"), name="privileged_action_packet.environment")
    if environment not in ENVIRONMENTS_V0:
        raise ValueError("privileged_action_packet environment is not allowed")
    action = _require_str(obj.get("action"), name="privileged_action_packet.action")
    if action not in ACTIONS_V0:
        raise ValueError("privileged_action_packet action is not allowed")
    _require_str(obj.get("target_kind"), name="privileged_action_packet.target_kind")
    _require_str(obj.get("target_hash"), name="privileged_action_packet.target_hash")
    _require_str(obj.get("policy_hash"), name="privileged_action_packet.policy_hash")
    _require_nonnegative_int(obj.get("nonce"), name="privileged_action_packet.nonce")
    epoch = _require_nonnegative_int(obj.get("epoch"), name="privileged_action_packet.epoch")
    not_before = _require_nonnegative_int(
        obj.get("not_before_epoch"),
        name="privileged_action_packet.not_before_epoch",
    )
    expires_at = _require_nonnegative_int(
        obj.get("expires_at_epoch"),
        name="privileged_action_packet.expires_at_epoch",
    )
    if expires_at < not_before:
        raise ValueError("privileged_action_packet expires_at_epoch precedes not_before_epoch")
    if epoch > expires_at:
        raise ValueError("privileged_action_packet epoch exceeds expires_at_epoch")
    _require_str(obj.get("payload_hash"), name="privileged_action_packet.payload_hash")
    if obj.get("packet_hash") != privileged_action_packet_content_hash_v0(obj):
        raise ValueError("privileged_action_packet hash mismatch")


def build_signature_envelope_v0(
    *,
    key_id: str,
    public_key: str,
    packet_hash: str,
    signature_scheme: str,
    signature: str,
) -> dict[str, Any]:
    envelope = {
        "schema": SIGNATURE_ENVELOPE_SCHEMA_V0,
        "key_id": key_id,
        "public_key": public_key,
        "packet_hash": packet_hash,
        "signature_scheme": signature_scheme,
        "signature": signature,
        "signature_envelope_hash": ZERO_ROOT_V0,
    }
    envelope["signature_envelope_hash"] = signature_envelope_content_hash_v0(envelope)
    validate_signature_envelope_v0(envelope)
    return envelope


def validate_signature_envelope_v0(envelope: Mapping[str, Any]) -> None:
    obj = _require_mapping(envelope, name="signature_envelope")
    expected = {
        "schema",
        "key_id",
        "public_key",
        "packet_hash",
        "signature_scheme",
        "signature",
        "signature_envelope_hash",
    }
    if set(obj.keys()) != expected:
        raise ValueError("signature_envelope keys mismatch")
    if obj.get("schema") != SIGNATURE_ENVELOPE_SCHEMA_V0:
        raise ValueError("signature_envelope schema mismatch")
    _require_str(obj.get("key_id"), name="signature_envelope.key_id")
    _require_str(obj.get("public_key"), name="signature_envelope.public_key")
    _require_str(obj.get("packet_hash"), name="signature_envelope.packet_hash")
    scheme = _require_str(obj.get("signature_scheme"), name="signature_envelope.signature_scheme")
    if scheme not in SIGNATURE_SCHEMES_V0:
        raise ValueError("signature_envelope signature_scheme is not supported")
    _require_str(obj.get("signature"), name="signature_envelope.signature")
    if obj.get("signature_envelope_hash") != signature_envelope_content_hash_v0(obj):
        raise ValueError("signature_envelope hash mismatch")


def _reject(reason: str) -> tuple[bool, str]:
    return False, reason


def _admission_decision(
    *,
    packet: Mapping[str, Any],
    policy: Mapping[str, Any],
    key_descriptors: list[Mapping[str, Any]],
    signature_envelopes: list[Mapping[str, Any]],
    transparency_log_hash: str | None,
    signature_verifier: SignatureVerifierV0 | None,
) -> tuple[bool, str, list[Mapping[str, Any]]]:
    try:
        validate_privileged_action_packet_v0(packet)
        validate_action_policy_v0(policy)
        for descriptor in key_descriptors:
            validate_key_descriptor_v0(descriptor)
        for envelope in signature_envelopes:
            validate_signature_envelope_v0(envelope)
    except Exception as exc:
        return False, f"malformed_input:{exc}", []

    if packet["action"] != policy["action"]:
        return (*_reject("policy_action_mismatch"), [])
    if packet["policy_hash"] != policy["policy_hash"]:
        return (*_reject("policy_hash_mismatch"), [])
    if packet["environment"] != "production":
        return (*_reject("packet_environment_not_production"), [])

    descriptors_by_key: dict[str, Mapping[str, Any]] = {}
    public_keys: set[str] = set()
    for descriptor in key_descriptors:
        key_id = str(descriptor["key_id"])
        if key_id in descriptors_by_key:
            return (*_reject("duplicate_key_id"), [])
        descriptors_by_key[key_id] = descriptor
        public_key = str(descriptor["public_key"])
        if public_key in public_keys:
            return (*_reject("duplicate_public_key"), [])
        public_keys.add(public_key)

    if signature_verifier is None:
        return (*_reject("missing_signature_verifier"), [])

    seen_signature_key_ids: set[str] = set()
    counted: list[Mapping[str, Any]] = []
    for envelope in signature_envelopes:
        key_id = str(envelope["key_id"])
        if key_id in seen_signature_key_ids:
            return (*_reject("duplicate_signature_envelope"), [])
        seen_signature_key_ids.add(key_id)
        if envelope["packet_hash"] != packet["packet_hash"]:
            return (*_reject("signature_packet_hash_mismatch"), [])
        descriptor = descriptors_by_key.get(key_id)
        if descriptor is None:
            return (*_reject("signature_key_unknown"), [])
        if envelope["public_key"] != descriptor["public_key"]:
            return (*_reject("signature_public_key_mismatch"), [])
        if not signature_verifier(packet, descriptor, envelope):
            return (*_reject("signature_verification_failed"), [])
        counted.append(descriptor)

    if any(descriptor["break_glass"] is True for descriptor in counted) and packet["action"] != "emergency_pause":
        return (*_reject("break_glass_scope_violation"), counted)
    role_signers = [descriptor for descriptor in counted if descriptor["role"] == policy["role"]]
    if len(role_signers) != len(counted):
        return (*_reject("wrong_role"), role_signers)
    if any(descriptor["environment"] != "production" for descriptor in role_signers):
        return (*_reject("testnet_key_for_production"), role_signers)
    if any(descriptor["status"] != "active" for descriptor in role_signers):
        return (*_reject("revoked_or_expired_key"), role_signers)
    if len(role_signers) < int(policy["threshold"]):
        return (*_reject("threshold_not_met"), role_signers)
    custodian_count = len({str(descriptor["custodian_id"]) for descriptor in role_signers})
    if custodian_count < int(policy["min_distinct_custodians"]):
        return (*_reject("distinct_custodian_threshold_not_met"), role_signers)
    if policy["hardware_required"] is True and any(
        descriptor["storage_class"] not in NON_SOFTWARE_STORAGE_CLASSES_V0 for descriptor in role_signers
    ):
        return (*_reject("non_software_custody_required"), role_signers)
    if policy["timelock_required"] is True and int(packet["epoch"]) < int(packet["not_before_epoch"]):
        return (*_reject("timelock_not_satisfied"), role_signers)
    if policy["transparency_required"] is True and not transparency_log_hash:
        return (*_reject("missing_transparency_log_hash"), role_signers)
    return True, "accepted", role_signers


def build_admission_receipt_v0(
    packet: Mapping[str, Any],
    policy: Mapping[str, Any],
    key_descriptors: list[Mapping[str, Any]],
    signature_envelopes: list[Mapping[str, Any]],
    *,
    transparency_log_hash: str | None,
    signature_verifier: SignatureVerifierV0 | None = None,
) -> dict[str, Any]:
    ok, reason, accepted = _admission_decision(
        packet=packet,
        policy=policy,
        key_descriptors=key_descriptors,
        signature_envelopes=signature_envelopes,
        transparency_log_hash=transparency_log_hash,
        signature_verifier=signature_verifier,
    )
    accepted_key_ids = sorted(str(descriptor["key_id"]) for descriptor in accepted)
    accepted_custodian_ids = sorted({str(descriptor["custodian_id"]) for descriptor in accepted})
    hardware_requirement_met = (
        policy.get("hardware_required") is not True
        or bool(accepted)
        and all(descriptor.get("storage_class") in NON_SOFTWARE_STORAGE_CLASSES_V0 for descriptor in accepted)
    )
    receipt = {
        "schema": ADMISSION_RECEIPT_SCHEMA_V0,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "reject_reason": "" if ok else reason,
        "environment": packet.get("environment"),
        "action": packet.get("action"),
        "packet_hash": packet.get("packet_hash"),
        "policy_hash": policy.get("policy_hash"),
        "accepted_key_ids": accepted_key_ids,
        "accepted_custodian_ids": accepted_custodian_ids,
        "accepted_signature_count": len(accepted_key_ids),
        "threshold": policy.get("threshold"),
        "distinct_custodian_count": len(accepted_custodian_ids),
        "min_distinct_custodians": policy.get("min_distinct_custodians"),
        "timelock_satisfied": (
            policy.get("timelock_required") is not True
            or isinstance(packet.get("epoch"), int)
            and isinstance(packet.get("not_before_epoch"), int)
            and int(packet["epoch"]) >= int(packet["not_before_epoch"])
        ),
        "hardware_requirement_met": hardware_requirement_met,
        "transparency_log_hash": transparency_log_hash,
        "receipt_hash": ZERO_ROOT_V0,
    }
    receipt["receipt_hash"] = admission_receipt_content_hash_v0(receipt)
    validate_admission_receipt_v0(receipt)
    return receipt


def validate_admission_receipt_v0(receipt: Mapping[str, Any]) -> None:
    obj = _require_mapping(receipt, name="admission_receipt")
    expected = {
        "schema",
        "ok",
        "status",
        "reject_reason",
        "environment",
        "action",
        "packet_hash",
        "policy_hash",
        "accepted_key_ids",
        "accepted_custodian_ids",
        "accepted_signature_count",
        "threshold",
        "distinct_custodian_count",
        "min_distinct_custodians",
        "timelock_satisfied",
        "hardware_requirement_met",
        "transparency_log_hash",
        "receipt_hash",
    }
    if set(obj.keys()) != expected:
        raise ValueError("admission_receipt keys mismatch")
    if obj.get("schema") != ADMISSION_RECEIPT_SCHEMA_V0:
        raise ValueError("admission_receipt schema mismatch")
    ok = _require_bool(obj.get("ok"), name="admission_receipt.ok")
    status = _require_str(obj.get("status"), name="admission_receipt.status")
    if status not in RECEIPT_STATUSES_V0:
        raise ValueError("admission_receipt status is not allowed")
    if ok and status != "accepted":
        raise ValueError("accepted admission_receipt status mismatch")
    if not ok and status != "rejected":
        raise ValueError("rejected admission_receipt status mismatch")
    reject_reason = (
        _require_str(obj.get("reject_reason"), name="admission_receipt.reject_reason")
        if not ok
        else obj.get("reject_reason")
    )
    if ok and reject_reason != "":
        raise ValueError("accepted admission_receipt reject_reason must be empty")
    environment = _require_str(obj.get("environment"), name="admission_receipt.environment")
    if environment not in ENVIRONMENTS_V0:
        raise ValueError("admission_receipt environment is not allowed")
    action = _require_str(obj.get("action"), name="admission_receipt.action")
    if action not in ACTIONS_V0:
        raise ValueError("admission_receipt action is not allowed")
    _require_str(obj.get("packet_hash"), name="admission_receipt.packet_hash")
    _require_str(obj.get("policy_hash"), name="admission_receipt.policy_hash")
    accepted_key_ids = _require_list(obj.get("accepted_key_ids"), name="admission_receipt.accepted_key_ids")
    accepted_custodian_ids = _require_list(
        obj.get("accepted_custodian_ids"),
        name="admission_receipt.accepted_custodian_ids",
    )
    for index, key_id in enumerate(accepted_key_ids):
        _require_str(key_id, name=f"admission_receipt.accepted_key_ids[{index}]")
    for index, custodian_id in enumerate(accepted_custodian_ids):
        _require_str(custodian_id, name=f"admission_receipt.accepted_custodian_ids[{index}]")
    if len(set(accepted_key_ids)) != len(accepted_key_ids):
        raise ValueError("admission_receipt accepted_key_ids must be distinct")
    if len(set(accepted_custodian_ids)) != len(accepted_custodian_ids):
        raise ValueError("admission_receipt accepted_custodian_ids must be distinct")
    if list(accepted_key_ids) != sorted(accepted_key_ids):
        raise ValueError("admission_receipt accepted_key_ids must be sorted")
    if list(accepted_custodian_ids) != sorted(accepted_custodian_ids):
        raise ValueError("admission_receipt accepted_custodian_ids must be sorted")
    signature_count = _require_nonnegative_int(
        obj.get("accepted_signature_count"),
        name="admission_receipt.accepted_signature_count",
    )
    if signature_count != len(accepted_key_ids):
        raise ValueError("admission_receipt accepted_signature_count mismatch")
    distinct_count = _require_nonnegative_int(
        obj.get("distinct_custodian_count"),
        name="admission_receipt.distinct_custodian_count",
    )
    if distinct_count != len(accepted_custodian_ids):
        raise ValueError("admission_receipt distinct_custodian_count mismatch")
    _require_positive_int(obj.get("threshold"), name="admission_receipt.threshold")
    _require_positive_int(obj.get("min_distinct_custodians"), name="admission_receipt.min_distinct_custodians")
    _require_bool(obj.get("timelock_satisfied"), name="admission_receipt.timelock_satisfied")
    _require_bool(obj.get("hardware_requirement_met"), name="admission_receipt.hardware_requirement_met")
    _require_optional_str(obj.get("transparency_log_hash"), name="admission_receipt.transparency_log_hash")
    if obj.get("receipt_hash") != admission_receipt_content_hash_v0(obj):
        raise ValueError("admission_receipt hash mismatch")


def validate_production_key_admission_receipt_v0(
    *,
    receipt: Mapping[str, Any],
    required_action: str,
) -> None:
    """Fail closed for externally supplied receipt summaries.

    A standalone receipt object is forgeable because its hash is self-computed and
    this validator has no cryptographic proof inputs (packet, descriptors,
    envelopes, signature verifier) to recompute a trusted admission decision.
    """

    validate_admission_receipt_v0(receipt)
    action = _require_str(required_action, name="required_action")
    if action not in ACTIONS_V0:
        raise ValueError("required_action is not allowed")
    raise ValueError(
        "production key-management admission receipt cannot be validated without full signed admission evidence"
    )


DEFAULT_ACTION_POLICIES_V0 = _load_default_action_policies()
