"""Bounded local/testnet runtime receipts for the mounted confidential surface.

These receipts do not prove private execution or TEE runtime confidentiality.
They only show that an admitted confidential request can produce a deterministic,
redacted public execution artifact inside the mounted API boundary.
"""

from __future__ import annotations

from typing import Any, Mapping

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex


CONFIDENTIAL_RUNTIME_EXECUTION_RECEIPT_SCHEMA_V1 = "zenodex/confidential_runtime_execution_receipt/v1"
_CONFIDENTIAL_RUNTIME_EXECUTION_RECEIPT_HASH_DOMAIN_V1 = "zenodex.confidential_runtime_execution_receipt/v1"
_CONFIDENTIAL_RUNTIME_EFFECT_HASH_DOMAIN_V1 = "zenodex.confidential_runtime_execution_effect/v1"
_SAFE_TOKEN_CHARS = frozenset("abcdefghijklmnopqrstuvwxyz0123456789._-")


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{name} must be an object")
    return value


def _require_nonempty_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{name} must be a non-empty string")
    return value.strip()


def _require_safe_token(value: Any, *, name: str, max_len: int = 64) -> str:
    token = _require_nonempty_str(value, name=name).lower()
    if len(token) > max_len or any(ch not in _SAFE_TOKEN_CHARS for ch in token):
        raise ValueError(f"{name} must be a safe token")
    return token


def _require_bounded_int(value: Any, *, name: str, lo: int = 0, hi: int = 0xFFFFFFFF) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < lo or value > hi:
        raise ValueError(f"{name} must be a bounded int")
    return int(value)


def _provider_family(measurement: str) -> str:
    if measurement.startswith("nitro:"):
        return "nitro"
    if measurement.startswith("azure-sevsnp:"):
        return "azure-sevsnp"
    return "custom"


def confidential_runtime_execution_receipt_hash_v1(body: Mapping[str, Any]) -> str:
    return sha256_hex(
        domain_sep_bytes(_CONFIDENTIAL_RUNTIME_EXECUTION_RECEIPT_HASH_DOMAIN_V1)
        + canonical_json_bytes(dict(body))
    )


def _public_effect_digest_v1(
    *,
    attestation_receipt_hash: str,
    execution_id: str,
    execution_kind: str,
    result_code: str,
) -> str:
    payload = {
        "attestation_receipt_hash": _require_nonempty_str(
            attestation_receipt_hash,
            name="attestation_receipt_hash",
        ),
        "execution_id": execution_id,
        "execution_kind": execution_kind,
        "result_code": result_code,
    }
    return sha256_hex(
        domain_sep_bytes(_CONFIDENTIAL_RUNTIME_EFFECT_HASH_DOMAIN_V1)
        + canonical_json_bytes(payload)
    )


def build_confidential_runtime_execution_receipt_v1(
    *,
    receipt: Mapping[str, Any],
    execution_id: str,
    execution_kind: str,
    result_code: str,
    operator_status_hash: str,
    approved_measurements_hash: str,
    external_verifier_binding_hash: str,
) -> dict[str, Any]:
    receipt_obj = _require_mapping(receipt, name="receipt")
    receipt_body = _require_mapping(receipt_obj.get("body"), name="receipt.body")
    host = _require_mapping(receipt_body.get("host"), name="receipt.body.host")
    accounting = _require_mapping(receipt_body.get("accounting"), name="receipt.body.accounting")
    attestation = _require_mapping(receipt_body.get("attestation"), name="receipt.body.attestation")

    attestation_receipt_hash = _require_nonempty_str(receipt_obj.get("receipt_hash"), name="receipt.receipt_hash")
    execution_id_v = _require_safe_token(execution_id, name="execution_id")
    execution_kind_v = _require_safe_token(execution_kind, name="execution_kind")
    result_code_v = _require_safe_token(result_code, name="result_code")
    extension_id = _require_nonempty_str(receipt_body.get("extension_id"), name="receipt.body.extension_id")
    provider_id = _require_nonempty_str(receipt_body.get("provider_id"), name="receipt.body.provider_id")
    request_id = _require_nonempty_str(receipt_body.get("request_id"), name="receipt.body.request_id")
    measurement = _require_nonempty_str(receipt_body.get("measurement"), name="receipt.body.measurement")
    operator_status_hash_v = _require_nonempty_str(operator_status_hash, name="operator_status_hash")
    approved_measurements_hash_v = _require_nonempty_str(
        approved_measurements_hash,
        name="approved_measurements_hash",
    )
    external_verifier_binding_hash_v = _require_nonempty_str(
        external_verifier_binding_hash,
        name="external_verifier_binding_hash",
    )
    current_epoch = _require_bounded_int(attestation.get("current_epoch"), name="receipt.body.attestation.current_epoch")
    attestation_epoch = _require_bounded_int(
        attestation.get("attestation_epoch"),
        name="receipt.body.attestation.attestation_epoch",
    )
    fee_charged = _require_bounded_int(accounting.get("fee_charged"), name="receipt.body.accounting.fee_charged")
    receipt_fee = _require_bounded_int(accounting.get("receipt_fee"), name="receipt.body.accounting.receipt_fee")
    if fee_charged != receipt_fee:
        raise ValueError("receipt fee mismatch")
    if host.get("do_execute") != 1:
        raise ValueError("receipt host must admit execution")
    if host.get("policy_ok") != 1:
        raise ValueError("receipt host policy guard must pass")
    if host.get("output_bound_ok") != 1:
        raise ValueError("receipt host output-bound guard must pass")

    body = {
        "schema": CONFIDENTIAL_RUNTIME_EXECUTION_RECEIPT_SCHEMA_V1,
        "attestation_receipt_hash": attestation_receipt_hash,
        "extension_id": extension_id,
        "provider_id": provider_id,
        "request_id": request_id,
        "execution_id": execution_id_v,
        "execution_kind": execution_kind_v,
        "result_code": result_code_v,
        "measurement_provider": _provider_family(measurement),
        "operator_status_hash": operator_status_hash_v,
        "approved_measurements_hash": approved_measurements_hash_v,
        "external_verifier_binding_hash": external_verifier_binding_hash_v,
        "attestation_epoch": attestation_epoch,
        "current_epoch": current_epoch,
        "units_charged": fee_charged,
        "result_redacted": True,
        "public_effect_digest": _public_effect_digest_v1(
            attestation_receipt_hash=attestation_receipt_hash,
            execution_id=execution_id_v,
            execution_kind=execution_kind_v,
            result_code=result_code_v,
        ),
        "public_summary": {
            "execution_admitted": True,
            "policy_ok": True,
            "output_bound_ok": True,
            "request_bound": True,
        },
    }
    return {
        "body": body,
        "receipt_hash": confidential_runtime_execution_receipt_hash_v1(body),
    }
