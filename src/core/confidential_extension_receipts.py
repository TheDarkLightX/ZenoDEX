"""
Deterministic receipts for TEE-attested confidential extensions.

This module is intentionally narrow:
- It binds a metered extension execution to an approved enclave measurement.
- It checks local accounting and attestation freshness.
- It does not implement remote attestation cryptography itself.

Production attestation verification remains an external step. The output of that step
is reduced here to an approved measurement allowlist plus bounded epoch freshness.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import AbstractSet, Any, Dict, Iterable, Tuple

from ..state.canonical import (
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)

MAX_FEE = 0x7FFF
MAX_BALANCE = 0xFFFF
MAX_EPOCH = 0xFFFFFFFF
MAX_ATTESTATION_AGE = 0xFF
CONFIDENTIAL_EXTENSION_RECEIPT_SCHEMA = "zenodex/confidential_extension_receipt/v2"
CONFIDENTIAL_EXTENSION_RECEIPT_HASH_DOMAIN = "zenodex.confidential_extension_receipt/v2"
CONFIDENTIAL_MEASUREMENT_REGISTRY_SCHEMA = "zenodex/confidential_measurement_registry/v1"
CONFIDENTIAL_MEASUREMENT_REGISTRY_HASH_DOMAIN = "zenodex.confidential_measurement_registry/v1"


def confidential_extension_receipt_hash(receipt_body: Dict[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes(CONFIDENTIAL_EXTENSION_RECEIPT_HASH_DOMAIN) + canonical_json_bytes(receipt_body))


def confidential_measurement_registry_hash(registry: Dict[str, Any]) -> str:
    unsigned = _measurement_registry_unsigned(registry)
    return sha256_hex(
        domain_sep_bytes(CONFIDENTIAL_MEASUREMENT_REGISTRY_HASH_DOMAIN)
        + canonical_json_bytes(unsigned)
    )


def _is_lower_hex(value: str, *, length: int) -> bool:
    return len(value) == length and all(ch in "0123456789abcdef" for ch in value)


def is_canonical_confidential_measurement(value: str) -> bool:
    if not isinstance(value, str) or not value:
        return False
    if value.startswith("nitro:"):
        parts = value.split(":")
        return (
            len(parts) == 5
            and parts[0] == "nitro"
            and parts[1] == "pcr0"
            and parts[3] == "pcr8"
            and _is_lower_hex(parts[2], length=96)
            and _is_lower_hex(parts[4], length=96)
        )
    if value.startswith("azure-sevsnp:"):
        parts = value.split(":")
        return (
            len(parts) == 3
            and parts[0] == "azure-sevsnp"
            and parts[1] == "hostdata"
            and _is_lower_hex(parts[2], length=64)
        )
    return True


def _to_measurement_set(values: Iterable[str] | AbstractSet[str]) -> set[str]:
    out = {str(v) for v in values}
    out.discard("")
    return out


def _require_nonempty_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_policy_digest(value: Any) -> str:
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name="policy_digest")


def _require_bounded_int(value: Any, *, name: str, upper: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > upper:
        raise ValueError(f"{name} must be a bounded int")
    return value


def _require_flag(value: Any, *, name: str) -> int:
    return _require_bounded_int(value, name=name, upper=1)


def _require_gate_flag(value: Any, *, name: str) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, int) and not isinstance(value, bool) and value in (0, 1):
        return bool(value)
    raise ValueError(f"{name} must be a bool or 0/1 int")


def _require_int_field(mapping: Dict[str, Any], key: str) -> int:
    value = mapping.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{key} must be an int")
    return value


def _measurement_registry_unsigned(registry: Dict[str, Any]) -> Dict[str, Any]:
    entries = registry.get("entries")
    if not isinstance(entries, list):
        raise ValueError("registry.entries must be a list")
    normalized_entries = []
    for entry in entries:
        if not isinstance(entry, dict):
            raise ValueError("registry entries must be objects")
        normalized_entries.append(
            {
                "provider_id": entry.get("provider_id"),
                "measurement": entry.get("measurement"),
                "policy_digest": entry.get("policy_digest"),
                "valid_from_epoch": entry.get("valid_from_epoch"),
                "valid_until_epoch": entry.get("valid_until_epoch"),
                "revoked": entry.get("revoked"),
            }
        )
    normalized_entries.sort(
        key=lambda entry: (
            str(entry["provider_id"]),
            str(entry["measurement"]),
            str(entry["policy_digest"]),
            int(entry["valid_from_epoch"]) if isinstance(entry["valid_from_epoch"], int) else -1,
            int(entry["valid_until_epoch"]) if isinstance(entry["valid_until_epoch"], int) else -1,
        )
    )
    return {
        "schema": registry.get("schema"),
        "registry_id": registry.get("registry_id"),
        "entries": normalized_entries,
    }


def verify_confidential_measurement_registry(
    registry: Dict[str, Any],
    *,
    current_epoch: int,
    policy_digest: str | None = None,
) -> Tuple[bool, str, set[str]]:
    if not isinstance(registry, dict):
        return False, "bad_registry_type", set()
    try:
        current_epoch_v = _require_bounded_int(current_epoch, name="current_epoch", upper=MAX_EPOCH)
        policy_digest_v = None if policy_digest is None else _require_policy_digest(policy_digest)
        if registry.get("schema") != CONFIDENTIAL_MEASUREMENT_REGISTRY_SCHEMA:
            return False, "bad_registry_schema", set()
        _require_nonempty_str(registry.get("registry_id"), name="registry_id")
        entries_obj = registry.get("entries")
        if not isinstance(entries_obj, list):
            return False, "bad_registry_entries", set()
        if "registry_hash" in registry:
            want_hash = registry.get("registry_hash")
            if not isinstance(want_hash, str) or want_hash != confidential_measurement_registry_hash(registry):
                return False, "registry_hash_mismatch", set()
        active: set[str] = set()
        seen_keys: set[tuple[str, str, str]] = set()
        for entry_obj in entries_obj:
            if not isinstance(entry_obj, dict):
                return False, "bad_registry_entry", set()
            provider_id = _require_nonempty_str(entry_obj.get("provider_id"), name="entry.provider_id")
            measurement = _require_nonempty_str(entry_obj.get("measurement"), name="entry.measurement")
            if not is_canonical_confidential_measurement(measurement):
                return False, "bad_registry_measurement", set()
            entry_policy_digest = _require_policy_digest(entry_obj.get("policy_digest"))
            valid_from = _require_bounded_int(
                entry_obj.get("valid_from_epoch"),
                name="entry.valid_from_epoch",
                upper=MAX_EPOCH,
            )
            valid_until = _require_bounded_int(
                entry_obj.get("valid_until_epoch"),
                name="entry.valid_until_epoch",
                upper=MAX_EPOCH,
            )
            if valid_until < valid_from:
                return False, "bad_registry_epoch_window", set()
            revoked = entry_obj.get("revoked")
            if not isinstance(revoked, bool):
                return False, "bad_registry_revocation_flag", set()
            key = (provider_id, measurement, entry_policy_digest)
            if key in seen_keys:
                return False, "duplicate_registry_measurement", set()
            seen_keys.add(key)
            if policy_digest_v is not None and entry_policy_digest != policy_digest_v:
                continue
            if revoked:
                continue
            if valid_from <= current_epoch_v <= valid_until:
                active.add(measurement)
        return True, "ok", active
    except (TypeError, ValueError):
        return False, "bad_registry_entry", set()


def confidential_measurement_registry_approves_receipt(
    registry: Dict[str, Any],
    *,
    provider_id: str,
    measurement: str,
    current_epoch: int,
    policy_digest: str,
) -> Tuple[bool, str]:
    ok, err, _active = verify_confidential_measurement_registry(
        registry,
        current_epoch=current_epoch,
        policy_digest=policy_digest,
    )
    if not ok:
        return False, err
    try:
        provider_id_v = _require_nonempty_str(provider_id, name="provider_id")
        measurement_v = _require_nonempty_str(measurement, name="measurement")
        if not is_canonical_confidential_measurement(measurement_v):
            return False, "bad_registry_measurement"
        policy_digest_v = _require_policy_digest(policy_digest)
        current_epoch_v = _require_bounded_int(current_epoch, name="current_epoch", upper=MAX_EPOCH)
        entries_obj = registry.get("entries")
        if not isinstance(entries_obj, list):
            return False, "bad_registry_entries"
        for entry_obj in entries_obj:
            if not isinstance(entry_obj, dict):
                return False, "bad_registry_entry"
            if entry_obj.get("provider_id") != provider_id_v:
                continue
            if entry_obj.get("measurement") != measurement_v:
                continue
            if _require_policy_digest(entry_obj.get("policy_digest")) != policy_digest_v:
                continue
            valid_from = _require_bounded_int(
                entry_obj.get("valid_from_epoch"),
                name="entry.valid_from_epoch",
                upper=MAX_EPOCH,
            )
            valid_until = _require_bounded_int(
                entry_obj.get("valid_until_epoch"),
                name="entry.valid_until_epoch",
                upper=MAX_EPOCH,
            )
            if bool(entry_obj.get("revoked")):
                continue
            if valid_from <= current_epoch_v <= valid_until:
                return True, "ok"
        return False, "measurement_not_active_for_provider"
    except (TypeError, ValueError):
        return False, "bad_registry_entry"


PRECHECK_OK = "Ok"
PRECHECK_BAD_SCHEMA = "BadSchema"
PRECHECK_MISSING_RECEIPT_HASH = "MissingReceiptHash"
PRECHECK_HASH_MISMATCH = "HashMismatch"
PRECHECK_BAD_EXTENSION_ID = "BadExtensionId"
PRECHECK_BAD_PROVIDER_ID = "BadProviderId"
PRECHECK_BAD_REQUEST_ID = "BadRequestId"
PRECHECK_BAD_POLICY_VERSION = "BadPolicyVersion"
PRECHECK_BAD_POLICY_DIGEST = "BadPolicyDigest"
PRECHECK_BAD_MEASUREMENT = "BadMeasurement"
PRECHECK_MEASUREMENT_NOT_APPROVED = "MeasurementNotApproved"
PRECHECK_BAD_HOST = "BadHost"
PRECHECK_BAD_ATTESTATION = "BadAttestation"
PRECHECK_BAD_ACCOUNTING = "BadAccounting"
PRECHECK_BAD_NUMERIC_FIELD = "BadNumericField"
PRECHECK_BAD_DO_EXECUTE = "BadDoExecute"
PRECHECK_BAD_POLICY_OK = "BadPolicyOk"
PRECHECK_BAD_NONCE_UNUSED = "BadNonceUnused"
PRECHECK_BAD_OUTPUT_BOUND_OK = "BadOutputBoundOk"


@dataclass(frozen=True)
class ConfidentialExtensionReceiptPrecheckOutcome:
    precheck_ok: bool
    reject_code: str
    checks: Dict[str, bool]


def evaluate_confidential_extension_receipt_precheck_gate(
    *,
    schema_ok: Any,
    receipt_hash_present: Any,
    hash_matches: Any,
    extension_id_ok: Any,
    provider_id_ok: Any,
    request_id_ok: Any,
    policy_version_ok: Any,
    policy_digest_ok: Any,
    measurement_format_ok: Any,
    measurement_approved: Any,
    host_object_ok: Any,
    attestation_object_ok: Any,
    accounting_object_ok: Any,
    numeric_fields_ok: Any,
    do_execute_flag_ok: Any,
    policy_ok_flag_ok: Any,
    nonce_unused_flag_ok: Any,
    output_bound_ok_flag_ok: Any,
) -> ConfidentialExtensionReceiptPrecheckOutcome:
    schema_ok_v = _require_gate_flag(schema_ok, name="schema_ok")
    receipt_hash_present_v = _require_gate_flag(receipt_hash_present, name="receipt_hash_present")
    hash_matches_v = _require_gate_flag(hash_matches, name="hash_matches")
    extension_id_ok_v = _require_gate_flag(extension_id_ok, name="extension_id_ok")
    provider_id_ok_v = _require_gate_flag(provider_id_ok, name="provider_id_ok")
    request_id_ok_v = _require_gate_flag(request_id_ok, name="request_id_ok")
    policy_version_ok_v = _require_gate_flag(policy_version_ok, name="policy_version_ok")
    policy_digest_ok_v = _require_gate_flag(policy_digest_ok, name="policy_digest_ok")
    measurement_format_ok_v = _require_gate_flag(measurement_format_ok, name="measurement_format_ok")
    measurement_approved_v = _require_gate_flag(measurement_approved, name="measurement_approved")
    host_object_ok_v = _require_gate_flag(host_object_ok, name="host_object_ok")
    attestation_object_ok_v = _require_gate_flag(attestation_object_ok, name="attestation_object_ok")
    accounting_object_ok_v = _require_gate_flag(accounting_object_ok, name="accounting_object_ok")
    numeric_fields_ok_v = _require_gate_flag(numeric_fields_ok, name="numeric_fields_ok")
    do_execute_flag_ok_v = _require_gate_flag(do_execute_flag_ok, name="do_execute_flag_ok")
    policy_ok_flag_ok_v = _require_gate_flag(policy_ok_flag_ok, name="policy_ok_flag_ok")
    nonce_unused_flag_ok_v = _require_gate_flag(nonce_unused_flag_ok, name="nonce_unused_flag_ok")
    output_bound_ok_flag_ok_v = _require_gate_flag(output_bound_ok_flag_ok, name="output_bound_ok_flag_ok")

    checks = {
        "schema_ok": schema_ok_v,
        "receipt_hash_present": receipt_hash_present_v,
        "hash_matches": hash_matches_v,
        "extension_id_ok": extension_id_ok_v,
        "provider_id_ok": provider_id_ok_v,
        "request_id_ok": request_id_ok_v,
        "policy_version_ok": policy_version_ok_v,
        "policy_digest_ok": policy_digest_ok_v,
        "measurement_format_ok": measurement_format_ok_v,
        "measurement_approved": measurement_approved_v,
        "host_object_ok": host_object_ok_v,
        "attestation_object_ok": attestation_object_ok_v,
        "accounting_object_ok": accounting_object_ok_v,
        "numeric_fields_ok": numeric_fields_ok_v,
        "do_execute_flag_ok": do_execute_flag_ok_v,
        "policy_ok_flag_ok": policy_ok_flag_ok_v,
        "nonce_unused_flag_ok": nonce_unused_flag_ok_v,
        "output_bound_ok_flag_ok": output_bound_ok_flag_ok_v,
    }

    if not schema_ok_v:
        reject_code = PRECHECK_BAD_SCHEMA
    elif not receipt_hash_present_v:
        reject_code = PRECHECK_MISSING_RECEIPT_HASH
    elif not hash_matches_v:
        reject_code = PRECHECK_HASH_MISMATCH
    elif not extension_id_ok_v:
        reject_code = PRECHECK_BAD_EXTENSION_ID
    elif not provider_id_ok_v:
        reject_code = PRECHECK_BAD_PROVIDER_ID
    elif not request_id_ok_v:
        reject_code = PRECHECK_BAD_REQUEST_ID
    elif not policy_version_ok_v:
        reject_code = PRECHECK_BAD_POLICY_VERSION
    elif not policy_digest_ok_v:
        reject_code = PRECHECK_BAD_POLICY_DIGEST
    elif not measurement_format_ok_v:
        reject_code = PRECHECK_BAD_MEASUREMENT
    elif not measurement_approved_v:
        reject_code = PRECHECK_MEASUREMENT_NOT_APPROVED
    elif not host_object_ok_v:
        reject_code = PRECHECK_BAD_HOST
    elif not attestation_object_ok_v:
        reject_code = PRECHECK_BAD_ATTESTATION
    elif not accounting_object_ok_v:
        reject_code = PRECHECK_BAD_ACCOUNTING
    elif not numeric_fields_ok_v:
        reject_code = PRECHECK_BAD_NUMERIC_FIELD
    elif not do_execute_flag_ok_v:
        reject_code = PRECHECK_BAD_DO_EXECUTE
    elif not policy_ok_flag_ok_v:
        reject_code = PRECHECK_BAD_POLICY_OK
    elif not nonce_unused_flag_ok_v:
        reject_code = PRECHECK_BAD_NONCE_UNUSED
    elif not output_bound_ok_flag_ok_v:
        reject_code = PRECHECK_BAD_OUTPUT_BOUND_OK
    else:
        reject_code = PRECHECK_OK

    return ConfidentialExtensionReceiptPrecheckOutcome(
        precheck_ok=bool(reject_code == PRECHECK_OK),
        reject_code=reject_code,
        checks=checks,
    )


def confidential_extension_receipt_precheck_error(
    outcome: ConfidentialExtensionReceiptPrecheckOutcome,
) -> str:
    mapping = {
        PRECHECK_BAD_SCHEMA: "bad_schema",
        PRECHECK_MISSING_RECEIPT_HASH: "missing_receipt_hash",
        PRECHECK_HASH_MISMATCH: "hash_mismatch",
        PRECHECK_BAD_EXTENSION_ID: "bad_extension_id",
        PRECHECK_BAD_PROVIDER_ID: "bad_provider_id",
        PRECHECK_BAD_REQUEST_ID: "bad_request_id",
        PRECHECK_BAD_POLICY_VERSION: "bad_policy_version",
        PRECHECK_BAD_POLICY_DIGEST: "bad_policy_digest",
        PRECHECK_BAD_MEASUREMENT: "bad_measurement",
        PRECHECK_MEASUREMENT_NOT_APPROVED: "measurement_not_approved",
        PRECHECK_BAD_HOST: "bad_host",
        PRECHECK_BAD_ATTESTATION: "bad_attestation",
        PRECHECK_BAD_ACCOUNTING: "bad_accounting",
        PRECHECK_BAD_NUMERIC_FIELD: "bad_numeric_field",
        PRECHECK_BAD_DO_EXECUTE: "bad_do_execute",
        PRECHECK_BAD_POLICY_OK: "bad_policy_ok",
        PRECHECK_BAD_NONCE_UNUSED: "bad_nonce_unused",
        PRECHECK_BAD_OUTPUT_BOUND_OK: "bad_output_bound_ok",
    }
    return mapping.get(outcome.reject_code, "ok")


@dataclass(frozen=True)
class ConfidentialExtensionReceiptGateOutcome:
    do_execute: int
    policy_ok: int
    nonce_unused: int
    output_bound_ok: int
    fresh_attestation_ok: bool
    host_guards_ok: bool
    accounting_ok: bool
    receipt_admissible: bool


def _fresh_attestation(*, current_epoch: int, attestation_epoch: int, max_attestation_age: int) -> bool:
    for value, upper in (
        (current_epoch, MAX_EPOCH),
        (attestation_epoch, MAX_EPOCH),
        (max_attestation_age, MAX_ATTESTATION_AGE),
    ):
        if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > upper:
            return False
    if attestation_epoch > current_epoch:
        return False
    return (current_epoch - attestation_epoch) <= max_attestation_age


def _accounting_ok(
    *,
    do_execute: int,
    fee_charged: int,
    receipt_fee: int,
    credit_before: int,
    credit_after: int,
    provider_balance_before: int,
    provider_balance_after: int,
) -> bool:
    for value, upper in (
        (fee_charged, MAX_FEE),
        (receipt_fee, MAX_FEE),
        (credit_before, MAX_BALANCE),
        (credit_after, MAX_BALANCE),
        (provider_balance_before, MAX_BALANCE),
        (provider_balance_after, MAX_BALANCE),
    ):
        if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > upper:
            return False
    if do_execute == 0:
        return (
            fee_charged == 0
            and receipt_fee == 0
            and credit_after == credit_before
            and provider_balance_after == provider_balance_before
        )
    return (
        fee_charged > 0
        and fee_charged == receipt_fee
        and credit_before >= fee_charged
        and credit_after == (credit_before - fee_charged)
        and provider_balance_after == (provider_balance_before + fee_charged)
        and provider_balance_after <= MAX_BALANCE
    )


def evaluate_confidential_extension_receipt_gate(
    *,
    do_execute: Any,
    policy_ok: Any,
    nonce_unused: Any,
    output_bound_ok: Any,
    current_epoch: Any,
    attestation_epoch: Any,
    max_attestation_age: Any,
    fee_charged: Any,
    receipt_fee: Any,
    credit_before: Any,
    credit_after: Any,
    provider_balance_before: Any,
    provider_balance_after: Any,
) -> ConfidentialExtensionReceiptGateOutcome:
    do_execute_v = _require_flag(do_execute, name="do_execute")
    policy_ok_v = _require_flag(policy_ok, name="policy_ok")
    nonce_unused_v = _require_flag(nonce_unused, name="nonce_unused")
    output_bound_ok_v = _require_flag(output_bound_ok, name="output_bound_ok")
    current_epoch_v = _require_bounded_int(current_epoch, name="current_epoch", upper=MAX_EPOCH)
    attestation_epoch_v = _require_bounded_int(attestation_epoch, name="attestation_epoch", upper=MAX_EPOCH)
    max_attestation_age_v = _require_bounded_int(
        max_attestation_age,
        name="max_attestation_age",
        upper=MAX_ATTESTATION_AGE,
    )
    fee_charged_v = _require_bounded_int(fee_charged, name="fee_charged", upper=MAX_FEE)
    receipt_fee_v = _require_bounded_int(receipt_fee, name="receipt_fee", upper=MAX_FEE)
    credit_before_v = _require_bounded_int(credit_before, name="credit_before", upper=MAX_BALANCE)
    credit_after_v = _require_bounded_int(credit_after, name="credit_after", upper=MAX_BALANCE)
    provider_balance_before_v = _require_bounded_int(
        provider_balance_before,
        name="provider_balance_before",
        upper=MAX_BALANCE,
    )
    provider_balance_after_v = _require_bounded_int(
        provider_balance_after,
        name="provider_balance_after",
        upper=MAX_BALANCE,
    )

    fresh_attestation_ok = _fresh_attestation(
        current_epoch=current_epoch_v,
        attestation_epoch=attestation_epoch_v,
        max_attestation_age=max_attestation_age_v,
    )
    host_guards_ok = bool(
        do_execute_v == 0
        or (policy_ok_v == 1 and nonce_unused_v == 1 and output_bound_ok_v == 1)
    )
    accounting_ok = _accounting_ok(
        do_execute=do_execute_v,
        fee_charged=fee_charged_v,
        receipt_fee=receipt_fee_v,
        credit_before=credit_before_v,
        credit_after=credit_after_v,
        provider_balance_before=provider_balance_before_v,
        provider_balance_after=provider_balance_after_v,
    )
    return ConfidentialExtensionReceiptGateOutcome(
        do_execute=do_execute_v,
        policy_ok=policy_ok_v,
        nonce_unused=nonce_unused_v,
        output_bound_ok=output_bound_ok_v,
        fresh_attestation_ok=fresh_attestation_ok,
        host_guards_ok=host_guards_ok,
        accounting_ok=accounting_ok,
        receipt_admissible=bool(fresh_attestation_ok and host_guards_ok and accounting_ok),
    )


def make_confidential_extension_receipt(
    *,
    extension_id: str,
    provider_id: str,
    request_id: str,
    policy_version: str,
    policy_digest: str,
    measurement: str,
    do_execute: int,
    policy_ok: int,
    nonce_unused: int,
    output_bound_ok: int,
    current_epoch: int,
    attestation_epoch: int,
    max_attestation_age: int,
    fee_charged: int,
    receipt_fee: int,
    credit_before: int,
    credit_after: int,
    provider_balance_before: int,
    provider_balance_after: int,
) -> Dict[str, Any]:
    extension_id = _require_nonempty_str(extension_id, name="extension_id")
    provider_id = _require_nonempty_str(provider_id, name="provider_id")
    request_id = _require_nonempty_str(request_id, name="request_id")
    policy_version = _require_nonempty_str(policy_version, name="policy_version")
    policy_digest = _require_policy_digest(policy_digest)
    measurement = _require_nonempty_str(measurement, name="measurement")
    if not is_canonical_confidential_measurement(measurement):
        raise ValueError("measurement must use a canonical built-in format")
    do_execute = _require_flag(do_execute, name="do_execute")
    policy_ok = _require_flag(policy_ok, name="policy_ok")
    nonce_unused = _require_flag(nonce_unused, name="nonce_unused")
    output_bound_ok = _require_flag(output_bound_ok, name="output_bound_ok")
    current_epoch = _require_bounded_int(current_epoch, name="current_epoch", upper=MAX_EPOCH)
    attestation_epoch = _require_bounded_int(attestation_epoch, name="attestation_epoch", upper=MAX_EPOCH)
    max_attestation_age = _require_bounded_int(max_attestation_age, name="max_attestation_age", upper=MAX_ATTESTATION_AGE)
    fee_charged = _require_bounded_int(fee_charged, name="fee_charged", upper=MAX_FEE)
    receipt_fee = _require_bounded_int(receipt_fee, name="receipt_fee", upper=MAX_FEE)
    credit_before = _require_bounded_int(credit_before, name="credit_before", upper=MAX_BALANCE)
    credit_after = _require_bounded_int(credit_after, name="credit_after", upper=MAX_BALANCE)
    provider_balance_before = _require_bounded_int(provider_balance_before, name="provider_balance_before", upper=MAX_BALANCE)
    provider_balance_after = _require_bounded_int(provider_balance_after, name="provider_balance_after", upper=MAX_BALANCE)
    try:
        gate = evaluate_confidential_extension_receipt_gate(
            do_execute=do_execute,
            policy_ok=policy_ok,
            nonce_unused=nonce_unused,
            output_bound_ok=output_bound_ok,
            current_epoch=current_epoch,
            attestation_epoch=attestation_epoch,
            max_attestation_age=max_attestation_age,
            fee_charged=fee_charged,
            receipt_fee=receipt_fee,
            credit_before=credit_before,
            credit_after=credit_after,
            provider_balance_before=provider_balance_before,
            provider_balance_after=provider_balance_after,
        )
    except (TypeError, ValueError):
        return False, "bad_numeric_field"
    if not gate.fresh_attestation_ok:
        raise ValueError("attestation must be fresh")
    if not gate.host_guards_ok:
        raise ValueError("executing receipt requires all host guards")
    if not gate.accounting_ok:
        raise ValueError("accounting must satisfy receipt invariants")
    body = {
        "schema": CONFIDENTIAL_EXTENSION_RECEIPT_SCHEMA,
        "extension_id": extension_id,
        "provider_id": provider_id,
        "request_id": request_id,
        "policy_version": policy_version,
        "policy_digest": policy_digest,
        "measurement": measurement,
        "host": {
            "do_execute": do_execute,
            "policy_ok": policy_ok,
            "nonce_unused": nonce_unused,
            "output_bound_ok": output_bound_ok,
        },
        "attestation": {
            "current_epoch": current_epoch,
            "attestation_epoch": attestation_epoch,
            "max_attestation_age": max_attestation_age,
        },
        "accounting": {
            "fee_charged": fee_charged,
            "receipt_fee": receipt_fee,
            "credit_before": credit_before,
            "credit_after": credit_after,
            "provider_balance_before": provider_balance_before,
            "provider_balance_after": provider_balance_after,
        },
    }
    return {"body": body, "receipt_hash": confidential_extension_receipt_hash(body)}


def verify_confidential_extension_receipt(
    receipt: Dict[str, Any],
    *,
    approved_measurements: Iterable[str] | AbstractSet[str],
) -> Tuple[bool, str]:
    if not isinstance(receipt, dict):
        return False, "bad_receipt_type"
    body = receipt.get("body")
    if not isinstance(body, dict):
        return False, "missing_body"

    want_hash = receipt.get("receipt_hash")
    host = body.get("host")
    attestation = body.get("attestation")
    accounting = body.get("accounting")
    schema_ok = body.get("schema") == CONFIDENTIAL_EXTENSION_RECEIPT_SCHEMA
    receipt_hash_present = isinstance(want_hash, str) and bool(want_hash)
    hash_matches = bool(
        receipt_hash_present and confidential_extension_receipt_hash(body) == want_hash
    )
    extension_id = body.get("extension_id")
    provider_id = body.get("provider_id")
    request_id = body.get("request_id")
    extension_id_ok = isinstance(extension_id, str) and bool(extension_id) and extension_id == extension_id.strip()
    provider_id_ok = isinstance(provider_id, str) and bool(provider_id) and provider_id == provider_id.strip()
    request_id_ok = isinstance(request_id, str) and bool(request_id) and request_id == request_id.strip()
    policy_version_ok = isinstance(body.get("policy_version"), str) and bool(body.get("policy_version"))
    policy_digest_ok = False
    try:
        policy_digest = body.get("policy_digest")
        policy_digest_ok = isinstance(policy_digest, str) and bool(policy_digest) and policy_digest == _require_policy_digest(policy_digest)
    except (TypeError, ValueError):
        policy_digest_ok = False
    measurement = body.get("measurement")
    measurement_format_ok = isinstance(measurement, str) and bool(measurement) and is_canonical_confidential_measurement(measurement)
    measurement_approved = bool(measurement_format_ok and measurement in _to_measurement_set(approved_measurements))
    host_object_ok = isinstance(host, dict)
    attestation_object_ok = isinstance(attestation, dict)
    accounting_object_ok = isinstance(accounting, dict)

    do_execute = policy_ok = nonce_unused = output_bound_ok = None
    current_epoch = attestation_epoch = max_attestation_age = None
    fee_charged = receipt_fee = credit_before = credit_after = None
    provider_balance_before = provider_balance_after = None
    numeric_fields_ok = False
    try:
        if host_object_ok and attestation_object_ok and accounting_object_ok:
            do_execute = _require_int_field(host, "do_execute")
            policy_ok = _require_int_field(host, "policy_ok")
            nonce_unused = _require_int_field(host, "nonce_unused")
            output_bound_ok = _require_int_field(host, "output_bound_ok")
            current_epoch = _require_int_field(attestation, "current_epoch")
            attestation_epoch = _require_int_field(attestation, "attestation_epoch")
            max_attestation_age = _require_int_field(attestation, "max_attestation_age")
            fee_charged = _require_int_field(accounting, "fee_charged")
            receipt_fee = _require_int_field(accounting, "receipt_fee")
            credit_before = _require_int_field(accounting, "credit_before")
            credit_after = _require_int_field(accounting, "credit_after")
            provider_balance_before = _require_int_field(accounting, "provider_balance_before")
            provider_balance_after = _require_int_field(accounting, "provider_balance_after")
            numeric_fields_ok = True
    except (TypeError, ValueError):
        numeric_fields_ok = False

    precheck = evaluate_confidential_extension_receipt_precheck_gate(
        schema_ok=schema_ok,
        receipt_hash_present=receipt_hash_present,
        hash_matches=hash_matches,
        extension_id_ok=extension_id_ok,
        provider_id_ok=provider_id_ok,
        request_id_ok=request_id_ok,
        policy_version_ok=policy_version_ok,
        policy_digest_ok=policy_digest_ok,
        measurement_format_ok=measurement_format_ok,
        measurement_approved=measurement_approved,
        host_object_ok=host_object_ok,
        attestation_object_ok=attestation_object_ok,
        accounting_object_ok=accounting_object_ok,
        numeric_fields_ok=numeric_fields_ok,
        do_execute_flag_ok=int(do_execute in (0, 1)),
        policy_ok_flag_ok=int(policy_ok in (0, 1)),
        nonce_unused_flag_ok=int(nonce_unused in (0, 1)),
        output_bound_ok_flag_ok=int(output_bound_ok in (0, 1)),
    )
    if not precheck.precheck_ok:
        return False, confidential_extension_receipt_precheck_error(precheck)

    try:
        gate = evaluate_confidential_extension_receipt_gate(
            do_execute=do_execute,
            policy_ok=policy_ok,
            nonce_unused=nonce_unused,
            output_bound_ok=output_bound_ok,
            current_epoch=current_epoch,
            attestation_epoch=attestation_epoch,
            max_attestation_age=max_attestation_age,
            fee_charged=fee_charged,
            receipt_fee=receipt_fee,
            credit_before=credit_before,
            credit_after=credit_after,
            provider_balance_before=provider_balance_before,
            provider_balance_after=provider_balance_after,
        )
    except (TypeError, ValueError):
        return False, "bad_numeric_field"

    if not gate.fresh_attestation_ok:
        return False, "stale_attestation"

    if not gate.host_guards_ok:
        return False, "attestation_guard_failed"

    if not gate.accounting_ok:
        return False, "accounting_guard_failed"
    return True, "ok"
