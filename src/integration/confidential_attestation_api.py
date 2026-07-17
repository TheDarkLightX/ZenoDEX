"""Mounted local/testnet API for confidential attestation receipts.

The API invokes a configured external verifier for cryptographic attestation
checks, then applies the in-repo deterministic receipt and allowlist gate.
"""

from __future__ import annotations

import json
import os
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

from ..core.confidential_extension_live_admission import (
    validate_confidential_extension_live_admission,
)
from ..core.confidential_extension_receipts import verify_confidential_extension_receipt
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.confidential_requests import ConfidentialRequestKey, ConfidentialRequestTable
from .confidential_attestation_verifier import (
    ConfidentialAttestationVerifierConfig,
    make_confidential_attestation_verifier,
    verify_and_make_confidential_extension_receipt,
)
from .confidential_feature_status import load_confidential_feature_status_from_env
from .confidential_runtime_receipts import build_confidential_runtime_execution_receipt_v1

MAX_POST_BODY = 96_000
ResponseT = Tuple[int, Dict[str, Any]]
StateTransitionResponseT = Tuple[int, Dict[str, Any], ConfidentialRequestTable | None]
_EXTERNAL_VERIFIER_BINDING_HASH_DOMAIN_V1 = "zenodex.confidential_external_verifier_binding/v1"


def _env_str(name: str, default: str) -> str:
    raw = os.environ.get(name)
    if raw is None:
        return default
    value = raw.strip()
    return value if value else default


def _env_bool(name: str, default: bool = False) -> bool:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return bool(default)
    return raw.strip().lower() in {"1", "true", "yes", "on"}


def _env_float(name: str, default: float, *, lo: float, hi: float) -> float:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return float(default)
    try:
        value = float(raw.strip())
    except Exception:
        return float(default)
    return min(max(value, lo), hi)


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return int(default)
    try:
        value = int(raw.strip())
    except Exception:
        return int(default)
    return min(max(value, lo), hi)


def _parse_json_body(body: Optional[bytes]) -> tuple[Optional[dict[str, Any]], Optional[str]]:
    if body is None or len(body) == 0:
        return None, "empty_body"
    if len(body) > MAX_POST_BODY:
        return None, "body_too_large"
    try:
        obj = json.loads(body)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None, "invalid_json"
    if not isinstance(obj, dict):
        return None, "expected_object"
    return obj, None


def _verifier_cmd_from_env() -> Sequence[str] | None:
    raw = _env_str("CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON", "")
    if not raw:
        return None
    try:
        obj = json.loads(raw)
    except Exception:
        return None
    if not isinstance(obj, list) or not obj:
        return None
    out: list[str] = []
    for item in obj:
        if not isinstance(item, str) or not item:
            return None
        out.append(item)
    return tuple(out)


def _verifier_config_from_env() -> ConfidentialAttestationVerifierConfig:
    return ConfidentialAttestationVerifierConfig(
        enabled=_env_bool("CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED", False),
        verifier_cmd=_verifier_cmd_from_env(),
        allow_path_lookup=_env_bool("CONFIDENTIAL_ATTESTATION_VERIFIER_ALLOW_PATH_LOOKUP", False),
        timeout_s=_env_float("CONFIDENTIAL_ATTESTATION_VERIFIER_TIMEOUT_S", 10.0, lo=0.05, hi=60.0),
        max_request_bytes=_env_int(
            "CONFIDENTIAL_ATTESTATION_VERIFIER_MAX_REQUEST_BYTES",
            256_000,
            lo=1,
            hi=1_000_000,
        ),
        max_stdout_bytes=_env_int(
            "CONFIDENTIAL_ATTESTATION_VERIFIER_MAX_STDOUT_BYTES",
            32_000,
            lo=1,
            hi=256_000,
        ),
        max_stderr_bytes=_env_int(
            "CONFIDENTIAL_ATTESTATION_VERIFIER_MAX_STDERR_BYTES",
            8_000,
            lo=1,
            hi=64_000,
        ),
    )


def _external_verifier_binding_hash(config: ConfidentialAttestationVerifierConfig) -> str:
    payload = {
        "enabled": bool(config.enabled),
        "verifier_cmd": list(config.verifier_cmd or ()),
        "allow_path_lookup": bool(config.allow_path_lookup),
        "timeout_s_millis": int(round(float(config.timeout_s) * 1000.0)),
        "max_request_bytes": int(config.max_request_bytes),
        "max_stdout_bytes": int(config.max_stdout_bytes),
        "max_stderr_bytes": int(config.max_stderr_bytes),
    }
    return sha256_hex(
        domain_sep_bytes(_EXTERNAL_VERIFIER_BINDING_HASH_DOMAIN_V1) + canonical_json_bytes(payload)
    )


def _request_mapping(body: Mapping[str, Any], *, name: str) -> Mapping[str, Any]:
    raw = body.get(name)
    if isinstance(raw, str):
        try:
            raw = json.loads(raw)
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            raise ValueError(f"bad_{name}") from exc
    if not isinstance(raw, Mapping):
        raise ValueError(f"{name} must be an object")
    return raw


def _request_str(body: Mapping[str, Any], *, name: str) -> str:
    value = body.get(name)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{name} must be a non-empty string")
    return value.strip()


def _request_int(body: Mapping[str, Any], *, name: str) -> int:
    value = body.get(name)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    return int(value)


def _status_payload() -> dict[str, Any]:
    status = load_confidential_feature_status_from_env()
    public_status = status.to_public_dict()
    verifier_cfg = _verifier_config_from_env()
    return {
        "enabled": True,
        "external_verifier_enabled": bool(verifier_cfg.enabled),
        "external_verifier_configured": bool(verifier_cfg.verifier_cmd),
        "approved_measurements_count": len(status.approved_measurements),
        "approved_measurements_hash": public_status.get("approved_measurements_hash"),
        "providers": public_status.get("providers", []),
        "max_attestation_age_epochs": int(status.max_attestation_age_epochs),
        "stage": str(status.stage),
        "status_hash": public_status.get("status_hash"),
        "external_verifier_binding_hash": _external_verifier_binding_hash(verifier_cfg),
        "endpoints": [
            "POST /api/confidential/attestation/verify",
            "POST /api/confidential/attestation/admit",
            "POST /api/confidential/attestation/execute",
        ],
    }


def _make_receipt_from_body(body: Mapping[str, Any]) -> tuple[dict[str, Any] | None, str | None]:
    try:
        attestation_payload = _request_mapping(body, name="attestation_payload")
        receipt, err = verify_and_make_confidential_extension_receipt(
            verifier=make_confidential_attestation_verifier(_verifier_config_from_env()),
            attestation_payload=attestation_payload,
            extension_id=_request_str(body, name="extension_id"),
            provider_id=_request_str(body, name="provider_id"),
            request_id=_request_str(body, name="request_id"),
            policy_version=_request_str(body, name="policy_version"),
            do_execute=_request_int(body, name="do_execute"),
            policy_ok=_request_int(body, name="policy_ok"),
            nonce_unused=_request_int(body, name="nonce_unused"),
            output_bound_ok=_request_int(body, name="output_bound_ok"),
            current_epoch=_request_int(body, name="current_epoch"),
            max_attestation_age=_request_int(body, name="max_attestation_age"),
            fee_charged=_request_int(body, name="fee_charged"),
            receipt_fee=_request_int(body, name="receipt_fee"),
            credit_before=_request_int(body, name="credit_before"),
            credit_after=_request_int(body, name="credit_after"),
            provider_balance_before=_request_int(body, name="provider_balance_before"),
            provider_balance_after=_request_int(body, name="provider_balance_after"),
        )
    except Exception as exc:
        return None, f"bad_request: {exc}"

    if err is not None or receipt is None:
        return None, str(err or "rejected")
    return receipt, None


def _verify_receipt_allowlist(receipt: dict[str, Any]) -> tuple[bool, str]:
    status = load_confidential_feature_status_from_env()
    return verify_confidential_extension_receipt(
        receipt,
        approved_measurements=status.approved_measurements,
    )


def _receipt_body(receipt: Mapping[str, Any]) -> Mapping[str, Any] | None:
    body = receipt.get("body")
    return body if isinstance(body, Mapping) else None


def _receipt_summary(receipt: Mapping[str, Any]) -> dict[str, Any]:
    receipt_body = _receipt_body(receipt)
    if receipt_body is None:
        return {}
    host = receipt_body.get("host")
    host_obj = host if isinstance(host, Mapping) else {}
    return {
        "receipt_hash": receipt.get("receipt_hash"),
        "measurement": receipt_body.get("measurement"),
        "provider_id": receipt_body.get("provider_id"),
        "request_id": receipt_body.get("request_id"),
        "policy_digest": receipt_body.get("policy_digest"),
        "execution_admitted": bool(host_obj.get("do_execute") == 1),
    }


def _execute_public_summary(receipt: Mapping[str, Any]) -> dict[str, Any]:
    summary = _receipt_summary(receipt)
    measurement = summary.get("measurement")
    measurement_provider = "custom"
    if isinstance(measurement, str):
        if measurement.startswith("nitro:"):
            measurement_provider = "nitro"
        elif measurement.startswith("azure-sevsnp:"):
            measurement_provider = "azure-sevsnp"
    return {
        "receipt_hash": summary.get("receipt_hash"),
        "measurement_provider": measurement_provider,
        "provider_id": summary.get("provider_id"),
        "request_id": summary.get("request_id"),
        "execution_admitted": summary.get("execution_admitted"),
    }


def _request_key_from_receipt(receipt: Mapping[str, Any]) -> ConfidentialRequestKey:
    body = _receipt_body(receipt)
    if body is None:
        raise ValueError("missing receipt body")
    return ConfidentialRequestKey(
        extension_id=str(body["extension_id"]),
        provider_id=str(body["provider_id"]),
        request_id=str(body["request_id"]),
    )


def _handle_verify(body: Mapping[str, Any]) -> ResponseT:
    receipt, err = _make_receipt_from_body(body)
    if err is not None or receipt is None:
        if err and err.startswith("bad_request: "):
            return 400, {
                "ok": False,
                "error": "bad_request",
                "details": err.removeprefix("bad_request: "),
            }
        return 502, {
            "ok": False,
            "error": "attestation_verifier_rejected",
            "details": str(err or "rejected"),
        }

    ok, gate_error = _verify_receipt_allowlist(receipt)
    if not ok:
        return 400, {"ok": False, "error": str(gate_error), "receipt_admissible": False}

    summary = _receipt_summary(receipt)
    if not summary:
        return 500, {"ok": False, "error": "bad_receipt_shape"}
    return 200, {
        "ok": True,
        "receipt_admissible": True,
        "receipt": receipt,
        **summary,
        "claim_scope": "local_testnet_external_verifier_receipt",
    }


def _handle_admit(
    body: Mapping[str, Any],
    *,
    request_table: ConfidentialRequestTable | None,
) -> StateTransitionResponseT:
    if request_table is None:
        return 503, {"ok": False, "error": "confidential_request_table_unavailable"}, None
    try:
        expected_policy_digest = _request_str(body, name="expected_policy_digest")
    except Exception as exc:
        return 400, {"ok": False, "error": "bad_request", "details": str(exc)}, request_table

    receipt, err = _make_receipt_from_body(body)
    if err is not None or receipt is None:
        if err and err.startswith("bad_request: "):
            return (
                400,
                {"ok": False, "error": "bad_request", "details": err.removeprefix("bad_request: ")},
                request_table,
            )
        return (
            502,
            {
                "ok": False,
                "error": "attestation_verifier_rejected",
                "details": str(err or "rejected"),
            },
            request_table,
        )

    status = load_confidential_feature_status_from_env()
    admitted, admission_error, updated = validate_confidential_extension_live_admission(
        receipt=receipt,
        approved_measurements=status.approved_measurements,
        expected_policy_digest=expected_policy_digest,
        request_table=request_table,
    )
    if not admitted or updated is None:
        return (
            400,
            {
                "ok": False,
                "error": str(admission_error or "admission_rejected"),
                "admission_ok": False,
                "request_consumed": False,
            },
            request_table,
        )

    key = _request_key_from_receipt(receipt)
    return (
        200,
        {
            "ok": True,
            "admission_ok": True,
            "receipt_admissible": True,
            "request_consumed": True,
            "request_key": {
                "extension_id": key.extension_id,
                "provider_id": key.provider_id,
                "request_id": key.request_id,
            },
            "receipt": receipt,
            **_receipt_summary(receipt),
            "claim_scope": "local_testnet_external_verifier_live_admission",
        },
        updated,
    )


def _handle_execute(
    body: Mapping[str, Any],
    *,
    request_table: ConfidentialRequestTable | None,
) -> StateTransitionResponseT:
    if request_table is None:
        return 503, {"ok": False, "error": "confidential_request_table_unavailable"}, None
    try:
        expected_policy_digest = _request_str(body, name="expected_policy_digest")
        execution_id = _request_str(body, name="execution_id")
        execution_kind = _request_str(body, name="execution_kind")
        result_code = _request_str(body, name="result_code")
    except Exception as exc:
        return 400, {"ok": False, "error": "bad_request", "details": str(exc)}, request_table

    receipt, err = _make_receipt_from_body(body)
    if err is not None or receipt is None:
        if err and err.startswith("bad_request: "):
            return (
                400,
                {"ok": False, "error": "bad_request", "details": err.removeprefix("bad_request: ")},
                request_table,
            )
        return (
            502,
            {
                "ok": False,
                "error": "attestation_verifier_rejected",
                "details": str(err or "rejected"),
            },
            request_table,
        )

    status = load_confidential_feature_status_from_env()
    public_status = status.to_public_dict()
    admitted, admission_error, updated = validate_confidential_extension_live_admission(
        receipt=receipt,
        approved_measurements=status.approved_measurements,
        expected_policy_digest=expected_policy_digest,
        request_table=request_table,
    )
    if not admitted or updated is None:
        return (
            400,
            {
                "ok": False,
                "error": str(admission_error or "admission_rejected"),
                "admission_ok": False,
                "execution_ok": False,
                "request_consumed": False,
            },
            request_table,
        )

    try:
        runtime_receipt = build_confidential_runtime_execution_receipt_v1(
            receipt=receipt,
            execution_id=execution_id,
            execution_kind=execution_kind,
            result_code=result_code,
            operator_status_hash=str(public_status.get("status_hash") or ""),
            approved_measurements_hash=str(public_status.get("approved_measurements_hash") or ""),
            external_verifier_binding_hash=_external_verifier_binding_hash(
                _verifier_config_from_env()
            ),
        )
    except Exception as exc:
        return (
            400,
            {
                "ok": False,
                "error": "bad_runtime_request",
                "details": str(exc),
                "admission_ok": True,
                "execution_ok": False,
                "request_consumed": False,
            },
            request_table,
        )

    key = _request_key_from_receipt(receipt)
    runtime_body = _receipt_body(runtime_receipt) or {}
    return (
        200,
        {
            "ok": True,
            "admission_ok": True,
            "execution_ok": True,
            "receipt_admissible": True,
            "request_consumed": True,
            "request_key": {
                "extension_id": key.extension_id,
                "provider_id": key.provider_id,
                "request_id": key.request_id,
            },
            **_execute_public_summary(receipt),
            "runtime_receipt": runtime_receipt,
            "runtime_receipt_hash": runtime_receipt.get("receipt_hash"),
            "execution_id": runtime_body.get("execution_id"),
            "execution_kind": runtime_body.get("execution_kind"),
            "result_code": runtime_body.get("result_code"),
            "operator_status_hash": runtime_body.get("operator_status_hash"),
            "approved_measurements_hash": runtime_body.get("approved_measurements_hash"),
            "external_verifier_binding_hash": runtime_body.get("external_verifier_binding_hash"),
            "public_effect_digest": runtime_body.get("public_effect_digest"),
            "result_redacted": bool(runtime_body.get("result_redacted") is True),
            "claim_scope": "local_testnet_external_verifier_bounded_runtime_receipt",
        },
        updated,
    )


def handle_confidential_attestation_request(
    method: str,
    path: str,
    raw_body: Optional[bytes],
    *,
    request_table: ConfidentialRequestTable | None = None,
) -> StateTransitionResponseT:
    """Return the HTTP response and the immutable replay-table candidate.

    Rejections return the exact input snapshot. A successful stateful request
    returns a new snapshot for the locked imperative shell to commit.
    """

    if method == "GET" and path == "/api/confidential/attestation/status":
        return 200, {"ok": True, "status": _status_payload()}, request_table

    if method == "POST" and path == "/api/confidential/attestation/verify":
        obj, err = _parse_json_body(raw_body)
        if err is not None or obj is None:
            return 400, {"ok": False, "error": str(err or "invalid_request")}, request_table
        status, response = _handle_verify(obj)
        return status, response, request_table

    if method == "POST" and path == "/api/confidential/attestation/admit":
        obj, err = _parse_json_body(raw_body)
        if err is not None or obj is None:
            return 400, {"ok": False, "error": str(err or "invalid_request")}, request_table
        return _handle_admit(obj, request_table=request_table)

    if method == "POST" and path == "/api/confidential/attestation/execute":
        obj, err = _parse_json_body(raw_body)
        if err is not None or obj is None:
            return 400, {"ok": False, "error": str(err or "invalid_request")}, request_table
        return _handle_execute(obj, request_table=request_table)

    return 404, {"ok": False, "error": "not_found"}, request_table
