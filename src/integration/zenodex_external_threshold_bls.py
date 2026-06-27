"""External threshold-BLS signer contract for production wallet backends.

This module does not implement threshold cryptography. It validates evidence and
signature receipts emitted by an external signer service such as a drand/kyber
or ssv-dkg based BLS threshold stack.
"""

from __future__ import annotations

import hashlib
import hmac
import json
import subprocess
from pathlib import Path
from typing import Any, Mapping, Sequence

from src.integration.zeno_key_manager import validate_tau_bls_public_key
from src.integration.zeno_key_manager_v0 import (
    BACKEND_THRESHOLD_BLS_EXTERNAL_SERVICE,
    KeyBackendDescriptor,
)
from src.integration.zeno_ledger_v0 import canonical_json_bytes_v0, hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x, hex_to_bytes_fixed

try:
    from py_ecc.bls import G2Basic

    _BLS_AVAILABLE = True
except Exception:  # pragma: no cover - optional dependency guard
    G2Basic = None
    _BLS_AVAILABLE = False


EXTERNAL_THRESHOLD_BLS_EVIDENCE_SCHEMA_V0 = "zenodex/external_threshold_bls/evidence/v0"
EXTERNAL_THRESHOLD_BLS_SIGN_REQUEST_SCHEMA_V0 = "zenodex/external_threshold_bls/sign_request/v0"
EXTERNAL_THRESHOLD_BLS_SIGNATURE_RECEIPT_SCHEMA_V0 = "zenodex/external_threshold_bls/signature_receipt/v0"

APPROVED_EXTERNAL_THRESHOLD_BLS_PROVIDER_STACKS_V0 = frozenset(
    {
        "drand-kyber-threshold-bls12-381-v1",
        "ssv-dkg-drand-threshold-bls12-381-v1",
    }
)

_EVIDENCE_KEYS_V0 = frozenset(
    {
        "schema",
        "backend_kind",
        "provider_stack",
        "service_id",
        "service_version",
        "binary_sha256",
        "public_key",
        "threshold",
        "participants",
        "dkg_transcript_hash",
        "audit_evidence",
        "no_raw_private_key_export",
        "dealerless_dkg",
        "production_security_claim",
        "evidence_hash",
    }
)
_PARTICIPANT_KEYS_V0 = frozenset({"participant_id", "public_share_key", "operator_key_hash"})
_AUDIT_EVIDENCE_KEYS_V0 = frozenset({"name", "report_uri", "report_hash", "scope"})
_SIGN_REQUEST_KEYS_V0 = frozenset(
    {"schema", "key_id", "evidence_hash", "payload_hash", "payload", "request_hash"}
)
_SIGNATURE_RECEIPT_KEYS_V0 = frozenset(
    {
        "schema",
        "backend_kind",
        "provider_stack",
        "service_id",
        "service_version",
        "evidence_hash",
        "payload_hash",
        "public_key",
        "threshold",
        "participant_ids",
        "partial_signature_hashes",
        "signature",
        "raw_private_key_reconstructed_for_signing",
        "production_security_claim",
        "receipt_hash",
    }
)


def _require_bls() -> None:
    if not _BLS_AVAILABLE:
        raise RuntimeError("py_ecc.bls is required to verify external threshold BLS receipts")


def _require_bls_basic() -> Any:
    _require_bls()
    if G2Basic is None:
        raise RuntimeError("py_ecc.bls is required to verify external threshold BLS receipts")
    return G2Basic


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be bool")
    return value


def _require_positive_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    return int(value)


def _require_sequence(value: object, *, name: str) -> Sequence[Any]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a sequence")
    return value


def _require_root(value: object, *, name: str) -> str:
    text = _require_str(value, name=name)
    canonical = canonical_hex_fixed_allow_0x(text, nbytes=32, name=name)
    if text != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_signature(value: object, *, name: str) -> str:
    text = _require_str(value, name=name)
    canonical = canonical_hex_fixed_allow_0x(text, nbytes=96, name=name)
    if text != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _payload_hash(payload: Mapping[str, Any]) -> str:
    return hash_v0("zeno_key_manager_signing_payload_v0", dict(payload))


def _bls_digest(payload: Mapping[str, Any]) -> bytes:
    return hashlib.sha256(
        canonical_json_bytes_v0(
            {
                "domain": "zenodex.zeno_key_manager.local_signing.v0",
                "payload": dict(payload),
            }
        )
    ).digest()


def _evidence_body(evidence: Mapping[str, Any]) -> dict[str, Any]:
    return {key: evidence[key] for key in sorted(_EVIDENCE_KEYS_V0 - {"evidence_hash"})}


def _sign_request_body(request: Mapping[str, Any]) -> dict[str, Any]:
    return {key: request[key] for key in sorted(_SIGN_REQUEST_KEYS_V0 - {"request_hash"})}


def _signature_receipt_body(receipt: Mapping[str, Any]) -> dict[str, Any]:
    return {key: receipt[key] for key in sorted(_SIGNATURE_RECEIPT_KEYS_V0 - {"receipt_hash"})}


def external_threshold_bls_payload_hash_v0(payload: Mapping[str, Any]) -> str:
    obj = _require_mapping(payload, name="payload")
    return _payload_hash(obj)


def validate_external_threshold_bls_evidence_v0(evidence: Mapping[str, Any]) -> None:
    obj = _require_mapping(evidence, name="evidence")
    if set(obj.keys()) != _EVIDENCE_KEYS_V0:
        raise ValueError("external threshold BLS evidence contains unsupported fields")
    if obj.get("schema") != EXTERNAL_THRESHOLD_BLS_EVIDENCE_SCHEMA_V0:
        raise ValueError("external threshold BLS evidence schema mismatch")
    if obj.get("backend_kind") != BACKEND_THRESHOLD_BLS_EXTERNAL_SERVICE:
        raise ValueError("external threshold BLS evidence backend_kind mismatch")
    provider_stack = _require_str(obj.get("provider_stack"), name="provider_stack")
    if provider_stack not in APPROVED_EXTERNAL_THRESHOLD_BLS_PROVIDER_STACKS_V0:
        raise ValueError("external threshold BLS provider_stack is not approved")
    _require_str(obj.get("service_id"), name="service_id")
    _require_str(obj.get("service_version"), name="service_version")
    _require_root(obj.get("binary_sha256"), name="binary_sha256")
    validate_tau_bls_public_key(_require_str(obj.get("public_key"), name="public_key"))
    threshold = _require_positive_int(obj.get("threshold"), name="threshold")
    participants = _require_sequence(obj.get("participants"), name="participants")
    if threshold > len(participants):
        raise ValueError("external threshold BLS threshold exceeds participant count")
    seen: set[str] = set()
    for index, raw in enumerate(participants):
        participant = _require_mapping(raw, name=f"participants[{index}]")
        if set(participant.keys()) != _PARTICIPANT_KEYS_V0:
            raise ValueError("external threshold BLS participant contains unsupported fields")
        participant_id = _require_str(participant.get("participant_id"), name=f"participants[{index}].participant_id")
        if participant_id in seen:
            raise ValueError("duplicate external threshold BLS participant_id")
        seen.add(participant_id)
        validate_tau_bls_public_key(_require_str(participant.get("public_share_key"), name="public_share_key"))
        _require_root(participant.get("operator_key_hash"), name="operator_key_hash")
    _require_root(obj.get("dkg_transcript_hash"), name="dkg_transcript_hash")
    audit_items = _require_sequence(obj.get("audit_evidence"), name="audit_evidence")
    if not audit_items:
        raise ValueError("external threshold BLS audit_evidence is required")
    for index, raw in enumerate(audit_items):
        audit = _require_mapping(raw, name=f"audit_evidence[{index}]")
        if set(audit.keys()) != _AUDIT_EVIDENCE_KEYS_V0:
            raise ValueError("external threshold BLS audit evidence contains unsupported fields")
        _require_str(audit.get("name"), name=f"audit_evidence[{index}].name")
        uri = _require_str(audit.get("report_uri"), name=f"audit_evidence[{index}].report_uri")
        if not (uri.startswith("https://") or uri.startswith("ipfs://")):
            raise ValueError("external threshold BLS audit report_uri must be https or ipfs")
        _require_root(audit.get("report_hash"), name=f"audit_evidence[{index}].report_hash")
        scope = _require_str(audit.get("scope"), name=f"audit_evidence[{index}].scope")
        if provider_stack not in scope:
            raise ValueError("external threshold BLS audit scope must bind provider_stack")
    if _require_bool(obj.get("no_raw_private_key_export"), name="no_raw_private_key_export") is not True:
        raise ValueError("external threshold BLS must not export raw private keys")
    if _require_bool(obj.get("dealerless_dkg"), name="dealerless_dkg") is not True:
        raise ValueError("external threshold BLS production evidence requires dealerless DKG")
    if _require_bool(obj.get("production_security_claim"), name="production_security_claim") is not True:
        raise ValueError("external threshold BLS evidence must claim production security")
    expected = hash_v0("zenodex_external_threshold_bls_evidence_v0", _evidence_body(obj))
    if not hmac.compare_digest(_require_root(obj.get("evidence_hash"), name="evidence_hash"), expected):
        raise ValueError("external threshold BLS evidence_hash mismatch")


def build_external_threshold_bls_evidence_v0(
    *,
    provider_stack: str,
    service_id: str,
    service_version: str,
    binary_sha256: str,
    public_key: str,
    threshold: int,
    participants: Sequence[Mapping[str, Any]],
    dkg_transcript_hash: str,
    audit_evidence: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    body = {
        "schema": EXTERNAL_THRESHOLD_BLS_EVIDENCE_SCHEMA_V0,
        "backend_kind": BACKEND_THRESHOLD_BLS_EXTERNAL_SERVICE,
        "provider_stack": provider_stack,
        "service_id": service_id,
        "service_version": service_version,
        "binary_sha256": binary_sha256,
        "public_key": public_key,
        "threshold": threshold,
        "participants": [dict(item) for item in participants],
        "dkg_transcript_hash": dkg_transcript_hash,
        "audit_evidence": [dict(item) for item in audit_evidence],
        "no_raw_private_key_export": True,
        "dealerless_dkg": True,
        "production_security_claim": True,
    }
    evidence = {**body, "evidence_hash": hash_v0("zenodex_external_threshold_bls_evidence_v0", body)}
    validate_external_threshold_bls_evidence_v0(evidence)
    return evidence


def build_external_threshold_bls_backend_descriptor_v0(
    *,
    key_id: str,
    backend_id: str,
    policy_hash: str,
    evidence: Mapping[str, Any],
) -> KeyBackendDescriptor:
    validate_external_threshold_bls_evidence_v0(evidence)
    return KeyBackendDescriptor(
        key_id=key_id,
        backend_kind=BACKEND_THRESHOLD_BLS_EXTERNAL_SERVICE,
        backend_id=backend_id,
        policy_hash=policy_hash,
        active=True,
        no_raw_private_key_exposure=True,
        metadata={
            "provider_stack": evidence["provider_stack"],
            "service_id": evidence["service_id"],
            "service_version": evidence["service_version"],
            "binary_sha256": evidence["binary_sha256"],
            "public_key": evidence["public_key"],
            "threshold": evidence["threshold"],
            "participants": len(evidence["participants"]),
            "dkg_transcript_hash": evidence["dkg_transcript_hash"],
            "external_threshold_bls_evidence_hash": evidence["evidence_hash"],
            "dealerless_dkg": True,
            "production_security_claim": True,
        },
    )


def build_external_threshold_bls_sign_request_v0(
    *,
    key_id: str,
    evidence_hash: str,
    payload: Mapping[str, Any],
) -> dict[str, Any]:
    obj = _require_mapping(payload, name="payload")
    body = {
        "schema": EXTERNAL_THRESHOLD_BLS_SIGN_REQUEST_SCHEMA_V0,
        "key_id": _require_str(key_id, name="key_id"),
        "evidence_hash": _require_root(evidence_hash, name="evidence_hash"),
        "payload_hash": _payload_hash(obj),
        "payload": dict(obj),
    }
    return {**body, "request_hash": hash_v0("zenodex_external_threshold_bls_sign_request_v0", body)}


def validate_external_threshold_bls_sign_request_v0(request: Mapping[str, Any]) -> None:
    obj = _require_mapping(request, name="request")
    if set(obj.keys()) != _SIGN_REQUEST_KEYS_V0:
        raise ValueError("external threshold BLS sign request contains unsupported fields")
    if obj.get("schema") != EXTERNAL_THRESHOLD_BLS_SIGN_REQUEST_SCHEMA_V0:
        raise ValueError("external threshold BLS sign request schema mismatch")
    _require_str(obj.get("key_id"), name="key_id")
    _require_root(obj.get("evidence_hash"), name="evidence_hash")
    payload = _require_mapping(obj.get("payload"), name="payload")
    if obj.get("payload_hash") != _payload_hash(payload):
        raise ValueError("external threshold BLS sign request payload_hash mismatch")
    expected = hash_v0("zenodex_external_threshold_bls_sign_request_v0", _sign_request_body(obj))
    if not hmac.compare_digest(_require_root(obj.get("request_hash"), name="request_hash"), expected):
        raise ValueError("external threshold BLS sign request hash mismatch")


def run_external_threshold_bls_signer_v0(
    *,
    command: Sequence[str],
    request: Mapping[str, Any],
    timeout_s: float = 30.0,
    max_stdout_bytes: int = 256_000,
) -> Mapping[str, Any]:
    validate_external_threshold_bls_sign_request_v0(request)
    if not isinstance(command, Sequence) or isinstance(command, (str, bytes, bytearray)) or not command:
        raise TypeError("command must be a non-empty sequence")
    argv = [_require_str(item, name=f"command[{index}]") for index, item in enumerate(command)]
    proc = subprocess.run(
        argv,
        input=canonical_json_bytes_v0(request),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout_s,
        check=False,
    )
    if proc.returncode != 0:
        detail = proc.stderr[:240].decode("utf-8", errors="replace")
        raise RuntimeError(f"external threshold BLS signer failed with {proc.returncode}: {detail}")
    if len(proc.stdout) > max_stdout_bytes:
        raise RuntimeError("external threshold BLS signer stdout too large")
    decoded = json.loads(proc.stdout.decode("utf-8"))
    return _require_mapping(decoded, name="external signer receipt")


def validate_external_threshold_bls_signer_artifact_v0(
    *,
    evidence: Mapping[str, Any],
    signer_artifact_path: Path,
) -> str:
    validate_external_threshold_bls_evidence_v0(evidence)
    artifact_hash = sha256_file_for_external_signer_v0(Path(signer_artifact_path))
    if not hmac.compare_digest(str(evidence["binary_sha256"]), artifact_hash):
        raise ValueError("external threshold BLS signer artifact hash mismatch")
    return artifact_hash


def build_external_threshold_bls_signature_receipt_v0(
    *,
    evidence: Mapping[str, Any],
    payload: Mapping[str, Any],
    participant_ids: Sequence[str],
    partial_signature_hashes: Sequence[str],
    signature: str,
) -> dict[str, Any]:
    validate_external_threshold_bls_evidence_v0(evidence)
    payload_obj = _require_mapping(payload, name="payload")
    ids = [_require_str(item, name=f"participant_ids[{index}]") for index, item in enumerate(participant_ids)]
    roots = [
        _require_root(item, name=f"partial_signature_hashes[{index}]")
        for index, item in enumerate(partial_signature_hashes)
    ]
    body = {
        "schema": EXTERNAL_THRESHOLD_BLS_SIGNATURE_RECEIPT_SCHEMA_V0,
        "backend_kind": BACKEND_THRESHOLD_BLS_EXTERNAL_SERVICE,
        "provider_stack": evidence["provider_stack"],
        "service_id": evidence["service_id"],
        "service_version": evidence["service_version"],
        "evidence_hash": evidence["evidence_hash"],
        "payload_hash": _payload_hash(payload_obj),
        "public_key": evidence["public_key"],
        "threshold": evidence["threshold"],
        "participant_ids": ids,
        "partial_signature_hashes": roots,
        "signature": _require_signature(signature, name="signature"),
        "raw_private_key_reconstructed_for_signing": False,
        "production_security_claim": True,
    }
    return {
        **body,
        "receipt_hash": hash_v0("zenodex_external_threshold_bls_signature_receipt_v0", body),
    }


def verify_external_threshold_bls_signature_receipt_v0(
    receipt: Mapping[str, Any],
    *,
    evidence: Mapping[str, Any],
    payload: Mapping[str, Any],
) -> tuple[bool, str | None]:
    try:
        bls = _require_bls_basic()
        validate_external_threshold_bls_evidence_v0(evidence)
        obj = _require_mapping(receipt, name="receipt")
        if set(obj.keys()) != _SIGNATURE_RECEIPT_KEYS_V0:
            return False, "external threshold BLS receipt contains unsupported fields"
        if obj.get("schema") != EXTERNAL_THRESHOLD_BLS_SIGNATURE_RECEIPT_SCHEMA_V0:
            return False, "external threshold BLS receipt schema mismatch"
        for key in ("backend_kind", "provider_stack", "service_id", "service_version", "evidence_hash", "public_key"):
            if obj.get(key) != evidence[key]:
                return False, f"external threshold BLS receipt {key} mismatch"
        if obj.get("threshold") != evidence["threshold"]:
            return False, "external threshold BLS receipt threshold mismatch"
        payload_obj = _require_mapping(payload, name="payload")
        if obj.get("payload_hash") != _payload_hash(payload_obj):
            return False, "external threshold BLS receipt payload_hash mismatch"
        participant_ids = _require_sequence(obj.get("participant_ids"), name="participant_ids")
        if len(participant_ids) < int(evidence["threshold"]):
            return False, "external threshold BLS receipt threshold not met"
        if len({str(item) for item in participant_ids}) != len(participant_ids):
            return False, "external threshold BLS receipt duplicate participant_id"
        known_ids = {str(item["participant_id"]) for item in evidence["participants"]}
        if not set(str(item) for item in participant_ids).issubset(known_ids):
            return False, "external threshold BLS receipt unknown participant_id"
        partial_hashes = _require_sequence(obj.get("partial_signature_hashes"), name="partial_signature_hashes")
        if len(partial_hashes) != len(participant_ids):
            return False, "external threshold BLS receipt partial hash count mismatch"
        for index, root in enumerate(partial_hashes):
            _require_root(root, name=f"partial_signature_hashes[{index}]")
        if obj.get("raw_private_key_reconstructed_for_signing") is not False:
            return False, "external threshold BLS receipt reconstructed raw private key"
        if obj.get("production_security_claim") is not True:
            return False, "external threshold BLS receipt missing production claim"
        expected = hash_v0("zenodex_external_threshold_bls_signature_receipt_v0", _signature_receipt_body(obj))
        if not hmac.compare_digest(_require_root(obj.get("receipt_hash"), name="receipt_hash"), expected):
            return False, "external threshold BLS receipt_hash mismatch"
        signature = _require_signature(obj.get("signature"), name="signature")
        ok = bool(
            bls.Verify(
                hex_to_bytes_fixed(str(evidence["public_key"]), nbytes=48, name="public_key"),
                _bls_digest(payload_obj),
                hex_to_bytes_fixed(signature, nbytes=96, name="signature"),
            )
        )
        return (True, None) if ok else (False, "external threshold BLS aggregate signature invalid")
    except Exception as exc:
        return False, f"external threshold BLS receipt invalid: {exc}"


def sha256_file_for_external_signer_v0(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return "0x" + digest.hexdigest()
