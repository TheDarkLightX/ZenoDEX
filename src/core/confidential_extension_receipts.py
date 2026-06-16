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

from typing import AbstractSet, Any, Dict, Iterable, Tuple, cast

from ..core import confidential_extension_receipt_gates as _receipt_gates
from ..core import confidential_measurement_registry as _measurement_registry
from ..state.canonical import (
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)

MAX_FEE = _receipt_gates.MAX_FEE
MAX_BALANCE = _receipt_gates.MAX_BALANCE
MAX_EPOCH = _receipt_gates.MAX_EPOCH
MAX_ATTESTATION_AGE = _receipt_gates.MAX_ATTESTATION_AGE
CONFIDENTIAL_EXTENSION_RECEIPT_SCHEMA = "zenodex/confidential_extension_receipt/v2"
CONFIDENTIAL_EXTENSION_RECEIPT_HASH_DOMAIN = "zenodex.confidential_extension_receipt/v2"

CONFIDENTIAL_MEASUREMENT_REGISTRY_HASH_DOMAIN = _measurement_registry.CONFIDENTIAL_MEASUREMENT_REGISTRY_HASH_DOMAIN
CONFIDENTIAL_MEASUREMENT_REGISTRY_SCHEMA = _measurement_registry.CONFIDENTIAL_MEASUREMENT_REGISTRY_SCHEMA
confidential_measurement_registry_approves_receipt = _measurement_registry.confidential_measurement_registry_approves_receipt
confidential_measurement_registry_hash = _measurement_registry.confidential_measurement_registry_hash
is_canonical_confidential_measurement = _measurement_registry.is_canonical_confidential_measurement
verify_confidential_measurement_registry = _measurement_registry.verify_confidential_measurement_registry
_to_measurement_set = _measurement_registry._to_measurement_set

PRECHECK_OK = _receipt_gates.PRECHECK_OK
PRECHECK_BAD_SCHEMA = _receipt_gates.PRECHECK_BAD_SCHEMA
PRECHECK_MISSING_RECEIPT_HASH = _receipt_gates.PRECHECK_MISSING_RECEIPT_HASH
PRECHECK_HASH_MISMATCH = _receipt_gates.PRECHECK_HASH_MISMATCH
PRECHECK_BAD_EXTENSION_ID = _receipt_gates.PRECHECK_BAD_EXTENSION_ID
PRECHECK_BAD_PROVIDER_ID = _receipt_gates.PRECHECK_BAD_PROVIDER_ID
PRECHECK_BAD_REQUEST_ID = _receipt_gates.PRECHECK_BAD_REQUEST_ID
PRECHECK_BAD_POLICY_VERSION = _receipt_gates.PRECHECK_BAD_POLICY_VERSION
PRECHECK_BAD_POLICY_DIGEST = _receipt_gates.PRECHECK_BAD_POLICY_DIGEST
PRECHECK_BAD_MEASUREMENT = _receipt_gates.PRECHECK_BAD_MEASUREMENT
PRECHECK_MEASUREMENT_NOT_APPROVED = _receipt_gates.PRECHECK_MEASUREMENT_NOT_APPROVED
PRECHECK_BAD_HOST = _receipt_gates.PRECHECK_BAD_HOST
PRECHECK_BAD_ATTESTATION = _receipt_gates.PRECHECK_BAD_ATTESTATION
PRECHECK_BAD_ACCOUNTING = _receipt_gates.PRECHECK_BAD_ACCOUNTING
PRECHECK_BAD_NUMERIC_FIELD = _receipt_gates.PRECHECK_BAD_NUMERIC_FIELD
PRECHECK_BAD_DO_EXECUTE = _receipt_gates.PRECHECK_BAD_DO_EXECUTE
PRECHECK_BAD_POLICY_OK = _receipt_gates.PRECHECK_BAD_POLICY_OK
PRECHECK_BAD_NONCE_UNUSED = _receipt_gates.PRECHECK_BAD_NONCE_UNUSED
PRECHECK_BAD_OUTPUT_BOUND_OK = _receipt_gates.PRECHECK_BAD_OUTPUT_BOUND_OK
ConfidentialExtensionReceiptPrecheckOutcome = _receipt_gates.ConfidentialExtensionReceiptPrecheckOutcome
ConfidentialExtensionReceiptGateOutcome = _receipt_gates.ConfidentialExtensionReceiptGateOutcome
_require_bounded_int = _receipt_gates._require_bounded_int
_require_flag = _receipt_gates._require_flag
_fresh_attestation = _receipt_gates._fresh_attestation
_accounting_ok = _receipt_gates._accounting_ok
evaluate_confidential_extension_receipt_precheck_gate = _receipt_gates.evaluate_confidential_extension_receipt_precheck_gate
confidential_extension_receipt_precheck_error = _receipt_gates.confidential_extension_receipt_precheck_error
evaluate_confidential_extension_receipt_gate = _receipt_gates.evaluate_confidential_extension_receipt_gate


def confidential_extension_receipt_hash(receipt_body: Dict[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes(CONFIDENTIAL_EXTENSION_RECEIPT_HASH_DOMAIN) + canonical_json_bytes(receipt_body))


def _require_nonempty_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_policy_digest(value: Any) -> str:
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name="policy_digest")


def _require_int_field(mapping: Dict[str, Any], key: str) -> int:
    value = mapping.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{key} must be an int")
    return value


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
    receipt: object,
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
    extension_id_ok = isinstance(body.get("extension_id"), str) and bool(body.get("extension_id"))
    provider_id_ok = isinstance(body.get("provider_id"), str) and bool(body.get("provider_id"))
    request_id_ok = isinstance(body.get("request_id"), str) and bool(body.get("request_id"))
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
            host_fields = cast(Dict[str, Any], host)
            attestation_fields = cast(Dict[str, Any], attestation)
            accounting_fields = cast(Dict[str, Any], accounting)
            do_execute = _require_int_field(host_fields, "do_execute")
            policy_ok = _require_int_field(host_fields, "policy_ok")
            nonce_unused = _require_int_field(host_fields, "nonce_unused")
            output_bound_ok = _require_int_field(host_fields, "output_bound_ok")
            current_epoch = _require_int_field(attestation_fields, "current_epoch")
            attestation_epoch = _require_int_field(attestation_fields, "attestation_epoch")
            max_attestation_age = _require_int_field(attestation_fields, "max_attestation_age")
            fee_charged = _require_int_field(accounting_fields, "fee_charged")
            receipt_fee = _require_int_field(accounting_fields, "receipt_fee")
            credit_before = _require_int_field(accounting_fields, "credit_before")
            credit_after = _require_int_field(accounting_fields, "credit_after")
            provider_balance_before = _require_int_field(accounting_fields, "provider_balance_before")
            provider_balance_after = _require_int_field(accounting_fields, "provider_balance_after")
            numeric_fields_ok = True
    except ValueError:
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

    if not gate.fresh_attestation_ok:
        return False, "stale_attestation"

    if not gate.host_guards_ok:
        return False, "attestation_guard_failed"

    if not gate.accounting_ok:
        return False, "accounting_guard_failed"
    return True, "ok"
