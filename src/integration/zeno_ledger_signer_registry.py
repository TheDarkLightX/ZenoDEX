"""Signer registry and quorum verification for ZenoLedger release artifacts."""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from src.integration.zeno_ledger_signature import (
    SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
    SUPPORTED_PAYLOAD_KINDS_V0,
    validate_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x

SIGNER_REGISTRY_SCHEMA_V0 = "zenodex/zeno_ledger/signer_registry/v0"
SIGNATURE_QUORUM_REPORT_SCHEMA_V0 = "zenodex/zeno_ledger/signature_quorum_report/v0"


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_positive_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    return int(value)


def _require_bls_public_key(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _signer_body(
    *,
    signer_id: str,
    key_id: str,
    public_key: str,
    weight: int = 1,
    status: str = "active",
) -> dict[str, Any]:
    status_value = _require_str(status, name="status")
    if status_value not in {"active", "revoked"}:
        raise ValueError("signer status must be active or revoked")
    body = {
        "signer_id": _require_str(signer_id, name="signer_id"),
        "key_id": _require_str(key_id, name="key_id"),
        "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
        "public_key": _require_bls_public_key(public_key, name="public_key"),
        "weight": _require_positive_int(weight, name="weight"),
        "status": status_value,
    }
    return {**body, "signer_hash": hash_v0("signer_registry_entry_v0", body)}


def build_signer_registry_v0(
    *,
    registry_id: str,
    payload_kind: str,
    threshold: int,
    signers: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    kind = _require_str(payload_kind, name="payload_kind")
    if kind not in SUPPORTED_PAYLOAD_KINDS_V0:
        raise ValueError("payload_kind is not supported")
    threshold_value = _require_positive_int(threshold, name="threshold")
    untrusted_signers: object = signers
    if not isinstance(untrusted_signers, Sequence) or isinstance(
        untrusted_signers, (str, bytes, bytearray)
    ):
        raise TypeError("signers must be a sequence")
    if not signers:
        raise ValueError("signer registry requires at least one signer")

    entries: list[dict[str, Any]] = []
    seen_identities: set[tuple[str, str]] = set()
    seen_public_keys: set[str] = set()
    active_weight = 0
    for index, raw in enumerate(signers):
        obj = _require_mapping(raw, name=f"signers[{index}]")
        entry = _signer_body(
            signer_id=_require_str(obj.get("signer_id"), name=f"signers[{index}].signer_id"),
            key_id=_require_str(obj.get("key_id"), name=f"signers[{index}].key_id"),
            public_key=_require_bls_public_key(obj.get("public_key"), name=f"signers[{index}].public_key"),
            weight=_require_positive_int(obj.get("weight", 1), name=f"signers[{index}].weight"),
            status=_require_str(obj.get("status", "active"), name=f"signers[{index}].status"),
        )
        identity = (entry["signer_id"], entry["key_id"])
        if identity in seen_identities:
            raise ValueError("duplicate signer_id/key_id")
        public_key = str(entry["public_key"])
        if public_key in seen_public_keys:
            raise ValueError("duplicate signer public_key")
        seen_identities.add(identity)
        seen_public_keys.add(public_key)
        if entry["status"] == "active":
            active_weight += int(entry["weight"])
        entries.append(entry)
    entries.sort(key=lambda item: (str(item["signer_id"]), str(item["key_id"])))
    if threshold_value > active_weight:
        raise ValueError("threshold exceeds active signer weight")

    body = {
        "schema": SIGNER_REGISTRY_SCHEMA_V0,
        "registry_id": _require_str(registry_id, name="registry_id"),
        "payload_kind": kind,
        "threshold": threshold_value,
        "signers": entries,
    }
    return {**body, "registry_hash": hash_v0("signer_registry_v0", body)}


def validate_signer_registry_v0(registry: Mapping[str, Any]) -> None:
    obj = _require_mapping(registry, name="registry")
    if obj.get("schema") != SIGNER_REGISTRY_SCHEMA_V0:
        raise ValueError("signer registry schema mismatch")
    expected = build_signer_registry_v0(
        registry_id=_require_str(obj.get("registry_id"), name="registry_id"),
        payload_kind=_require_str(obj.get("payload_kind"), name="payload_kind"),
        threshold=_require_positive_int(obj.get("threshold"), name="threshold"),
        signers=[
            _require_mapping(item, name=f"signers[{index}]")
            for index, item in enumerate(obj.get("signers", []))
        ],
    )
    if dict(obj) != expected:
        raise ValueError("signer registry binding mismatch")


def verify_signature_quorum_v0(
    *,
    registry: Mapping[str, Any],
    payload_kind: str,
    payload_hash: str,
    envelopes: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    validate_signer_registry_v0(registry)
    kind = _require_str(payload_kind, name="payload_kind")
    if kind != registry["payload_kind"]:
        raise ValueError("payload_kind does not match registry")
    untrusted_envelopes: object = envelopes
    if not isinstance(untrusted_envelopes, Sequence) or isinstance(
        untrusted_envelopes, (str, bytes, bytearray)
    ):
        raise TypeError("envelopes must be a sequence")
    if not envelopes:
        raise ValueError("at least one envelope is required")

    active_by_identity: dict[tuple[str, str], Mapping[str, Any]] = {}
    for raw_entry in registry["signers"]:
        entry = _require_mapping(raw_entry, name="registry.signer")
        if entry["status"] == "active":
            active_by_identity[(str(entry["signer_id"]), str(entry["key_id"]))] = entry

    accepted: list[dict[str, Any]] = []
    seen_identities: set[tuple[str, str]] = set()
    seen_public_keys: set[str] = set()
    weight = 0
    for index, raw_envelope in enumerate(envelopes):
        envelope = _require_mapping(raw_envelope, name=f"envelopes[{index}]")
        identity = (
            _require_str(envelope.get("signer_id"), name=f"envelopes[{index}].signer_id"),
            _require_str(envelope.get("key_id"), name=f"envelopes[{index}].key_id"),
        )
        if identity in seen_identities:
            raise ValueError("duplicate envelope signer_id/key_id")
        signer = active_by_identity.get(identity)
        if signer is None:
            raise ValueError("envelope signer is not active in registry")
        if envelope.get("algorithm") != SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0:
            raise ValueError("envelope algorithm is not allowed by registry")
        public_key = str(signer["public_key"])
        if public_key in seen_public_keys:
            raise ValueError("duplicate envelope signer public_key")
        validate_bls_signed_artifact_envelope_v0(
            envelope=envelope,
            expected_payload_kind=kind,
            expected_payload_hash=payload_hash,
            expected_public_key=public_key,
        )
        seen_identities.add(identity)
        seen_public_keys.add(public_key)
        signer_weight = int(signer["weight"])
        weight += signer_weight
        accepted.append(
            {
                "signer_id": identity[0],
                "key_id": identity[1],
                "weight": signer_weight,
                "envelope_hash": envelope["envelope_hash"],
            }
        )

    threshold = int(registry["threshold"])
    if weight < threshold:
        raise ValueError("signature quorum threshold not met")
    body = {
        "schema": SIGNATURE_QUORUM_REPORT_SCHEMA_V0,
        "registry_hash": registry["registry_hash"],
        "payload_kind": kind,
        "payload_hash": payload_hash,
        "threshold": threshold,
        "accepted_weight": weight,
        "accepted_signatures": accepted,
    }
    return {**body, "quorum_report_hash": hash_v0("signature_quorum_report_v0", body)}
