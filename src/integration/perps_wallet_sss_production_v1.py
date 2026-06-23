"""Production custodian ceremony for encrypted SSS backup.

This module implements the production hardening layer on top of the existing
encrypted SSS backup receipts. It provides:

- Custodian registration (guardians register BLS public keys)
- Backup ceremony quorum (guardians sign the backup hash)
- Live delivery verification (SMTP/cloud-drive/offline-export evidence)
- Production security claim elevation (only when all gates pass)
- Key rotation ceremony with quorum-signed invalidation

The module does NOT make the server a custodian. Encrypted share envelopes
remain transport artifacts. The custodian ceremony binds guardian BLS
signatures to the backup hash, proving that a quorum of independent
custodians attested to the backup's integrity before it was distributed.
"""

from __future__ import annotations

import time
from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from src.integration.perps_wallet_encrypted_sss_backup import (
    PERPS_WALLET_ENCRYPTED_SSS_BACKUP_SCHEMA_V1,
    build_perps_wallet_encrypted_sss_live_delivery_receipt_v1,
    perps_wallet_encrypted_sss_backup_hash_v1,
)
from src.integration.zeno_ledger_signature import (
    build_bls_signed_artifact_envelope_v0,
    validate_bls_signed_artifact_envelope_v0,
)

SSS_PRODUCTION_CEREMONY_SCHEMA_V1 = "zenodex/perps-wallet-sss-production-ceremony/v1"
SSS_CUSTODIAN_REGISTRY_SCHEMA_V1 = "zenodex/perps-wallet-sss-custodian-registry/v1"
SSS_KEY_ROTATION_CEREMONY_SCHEMA_V1 = "zenodex/perps-wallet-sss-key-rotation-ceremony/v1"

CEREMONY_PAYLOAD_KIND_V1 = "perps_wallet_sss_production_ceremony"
CUSTODIAN_REGISTRY_PAYLOAD_KIND_V1 = "perps_wallet_sss_custodian_registry"
KEY_ROTATION_PAYLOAD_KIND_V1 = "perps_wallet_sss_key_rotation_ceremony"

_MIN_CUSTODIANS = 3
_MIN_DISTINCT_CUSTODIANS = 3
_MAX_CUSTODIANS = 255


@dataclass(frozen=True)
class Custodian:
    custodian_id: str
    bls_public_key_hex: str
    role: str
    organization: str


def build_custodian_registry_v1(
    *,
    authority_id: str,
    chain_id: str,
    custodians: Sequence[Custodian],
    threshold: int,
    created_at_epoch: int,
) -> dict[str, Any]:
    if len(custodians) < _MIN_CUSTODIANS:
        raise ValueError(f"custodian registry requires at least {_MIN_CUSTODIANS} custodians")
    if len(custodians) > _MAX_CUSTODIANS:
        raise ValueError(f"custodian registry supports at most {_MAX_CUSTODIANS} custodians")
    if threshold < 2:
        raise ValueError("threshold must be at least 2")
    if threshold > len(custodians):
        raise ValueError("threshold must not exceed custodian count")
    ids = [c.custodian_id for c in custodians]
    if len(ids) != len(set(ids)):
        raise ValueError("custodian ids must be unique")
    orgs = [c.organization for c in custodians]
    if len(set(orgs)) < _MIN_DISTINCT_CUSTODIANS:
        raise ValueError(
            f"custodian registry requires at least {_MIN_DISTINCT_CUSTODIANS} distinct organizations"
        )
    keys = [c.bls_public_key_hex for c in custodians]
    if len(keys) != len(set(keys)):
        raise ValueError("custodian BLS public keys must be unique")

    registry: dict[str, Any] = {
        "schema": SSS_CUSTODIAN_REGISTRY_SCHEMA_V1,
        "authority_id": authority_id,
        "chain_id": chain_id,
        "threshold": threshold,
        "custodian_count": len(custodians),
        "custodians": [
            {
                "custodian_id": c.custodian_id,
                "bls_public_key": c.bls_public_key_hex,
                "role": c.role,
                "organization": c.organization,
            }
            for c in custodians
        ],
        "created_at_epoch": created_at_epoch,
        "production_security_claim": True,
    }
    return registry


def validate_custodian_registry_v1(
    registry: Mapping[str, Any],
    *,
    expected_authority_id: str | None = None,
    errors: list[str] | None = None,
) -> dict[str, Any]:
    errs = errors if errors is not None else []
    if registry.get("schema") != SSS_CUSTODIAN_REGISTRY_SCHEMA_V1:
        errs.append("custodian registry schema mismatch")
        return {"ok": False, "errors": errs}
    if expected_authority_id and registry.get("authority_id") != expected_authority_id:
        errs.append("custodian registry authority_id mismatch")
    threshold = registry.get("threshold")
    if not isinstance(threshold, int) or threshold < 2:
        errs.append("custodian registry threshold must be >= 2")
    custodians = registry.get("custodians")
    if not isinstance(custodians, list) or len(custodians) < _MIN_CUSTODIANS:
        errs.append(f"custodian registry requires at least {_MIN_CUSTODIANS} custodians")
        return {"ok": False, "errors": errs}
    ids = set()
    keys = set()
    orgs = set()
    for i, c in enumerate(custodians):
        if not isinstance(c, dict):
            errs.append(f"custodian[{i}] is not an object")
            continue
        cid = c.get("custodian_id")
        if not isinstance(cid, str) or not cid.strip():
            errs.append(f"custodian[{i}].custodian_id is missing")
        else:
            ids.add(cid)
        pk = c.get("bls_public_key")
        if not isinstance(pk, str) or not pk.startswith("0x") or len(pk) < 66:
            errs.append(f"custodian[{i}].bls_public_key is invalid")
        else:
            keys.add(pk)
        org = c.get("organization")
        if not isinstance(org, str) or not org.strip():
            errs.append(f"custodian[{i}].organization is missing")
        else:
            orgs.add(org)
    if len(ids) != len(custodians):
        errs.append("custodian ids must be unique")
    if len(keys) != len(custodians):
        errs.append("custodian BLS public keys must be unique")
    if len(orgs) < _MIN_DISTINCT_CUSTODIANS:
        errs.append(
            f"custodian registry requires at least {_MIN_DISTINCT_CUSTODIANS} distinct organizations"
        )
    if isinstance(threshold, int) and threshold > len(custodians):
        errs.append("threshold must not exceed custodian count")
    return {"ok": not errs, "errors": errs}


def collect_custodian_attestation_v1(
    *,
    custodian_id: str,
    private_key_hex: str,
    public_key_hex: str,
    backup_hash: str,
    authority_id: str,
    chain_id: str,
) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "schema": SSS_PRODUCTION_CEREMONY_SCHEMA_V1,
        "authority_id": authority_id,
        "chain_id": chain_id,
        "backup_hash": backup_hash,
        "attested_by": custodian_id,
        "attested_at_epoch": int(time.time()),
    }
    ceremony_hash = _ceremony_hash_v1(payload)
    envelope = build_bls_signed_artifact_envelope_v0(
        payload_kind=CEREMONY_PAYLOAD_KIND_V1,
        payload_hash=ceremony_hash,
        signer_id=custodian_id,
        key_id=f"{custodian_id}-bls",
        private_key_hex=private_key_hex,
    )
    payload["signature_envelope"] = envelope
    return payload


def _ceremony_hash_v1(payload: Mapping[str, Any]) -> str:
    from src.integration.zeno_ledger_v0 import hash_v0

    body = {k: v for k, v in dict(payload).items() if k != "signature_envelope"}
    return hash_v0(CEREMONY_PAYLOAD_KIND_V1, body)


def verify_custodian_attestation_v1(
    attestation: Mapping[str, Any],
    *,
    expected_backup_hash: str,
    expected_public_key: str,
    errors: list[str] | None = None,
) -> dict[str, Any]:
    errs = errors if errors is not None else []
    if attestation.get("schema") != SSS_PRODUCTION_CEREMONY_SCHEMA_V1:
        errs.append("custodian attestation schema mismatch")
    if attestation.get("backup_hash") != expected_backup_hash:
        errs.append("custodian attestation backup_hash mismatch")
    envelope = attestation.get("signature_envelope")
    if not isinstance(envelope, dict):
        errs.append("custodian attestation signature envelope is missing")
        return {"ok": False, "errors": errs}
    try:
        validate_bls_signed_artifact_envelope_v0(
            envelope=envelope,
            expected_payload_kind=CEREMONY_PAYLOAD_KIND_V1,
            expected_payload_hash=_ceremony_hash_v1(
                {k: v for k, v in dict(attestation).items() if k != "signature_envelope"}
            ),
            expected_public_key=expected_public_key,
        )
    except Exception as exc:
        errs.append(f"custodian attestation signature invalid: {exc}")
    return {"ok": not errs, "errors": errs}


def build_production_ceremony_v1(
    *,
    backup: Mapping[str, Any],
    registry: Mapping[str, Any],
    attestations: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    backup_hash = backup.get("backup_hash")
    if not backup_hash:
        raise ValueError("backup must have a backup_hash")
    if backup.get("schema") != PERPS_WALLET_ENCRYPTED_SSS_BACKUP_SCHEMA_V1:
        raise ValueError("backup schema mismatch")
    if registry.get("schema") != SSS_CUSTODIAN_REGISTRY_SCHEMA_V1:
        raise ValueError("registry schema mismatch")
    threshold = registry.get("threshold")
    if not isinstance(threshold, int) or threshold < 2:
        raise ValueError("registry threshold must be >= 2")
    custodian_map: dict[str, dict[str, Any]] = {}
    for c in registry.get("custodians", []):
        custodian_map[c["custodian_id"]] = c
    verified_attestations: list[dict[str, Any]] = []
    seen_custodians: set[str] = set()
    for att in attestations:
        cid = att.get("attested_by")
        if not isinstance(cid, str) or cid not in custodian_map:
            raise ValueError(f"attestation from unknown custodian: {cid}")
        if cid in seen_custodians:
            raise ValueError(f"duplicate attestation from custodian: {cid}")
        seen_custodians.add(cid)
        result = verify_custodian_attestation_v1(
            att,
            expected_backup_hash=backup_hash,
            expected_public_key=custodian_map[cid]["bls_public_key"],
        )
        if not result["ok"]:
            raise ValueError(f"custodian attestation from {cid} failed: {result['errors']}")
        verified_attestations.append(dict(att))
    if len(verified_attestations) < threshold:
        raise ValueError(
            f"production ceremony requires {threshold} attestations, got {len(verified_attestations)}"
        )
    ceremony: dict[str, Any] = {
        "schema": SSS_PRODUCTION_CEREMONY_SCHEMA_V1,
        "authority_id": registry.get("authority_id"),
        "chain_id": registry.get("chain_id"),
        "backup_hash": backup_hash,
        "registry_threshold": threshold,
        "attestation_count": len(verified_attestations),
        "attestations": verified_attestations,
        "quorum_satisfied": len(verified_attestations) >= threshold,
        "distinct_organizations": len(
            {custodian_map[a["attested_by"]]["organization"] for a in verified_attestations}
        ),
        "production_security_claim": True,
        "not_claimed": [
            "does_not_claim_server_side_key_custody",
            "does_not_claim_plaintext_share_storage",
            "does_not_claim_individual_custodian_trust",
        ],
    }
    return ceremony


def evaluate_production_ceremony_v1(
    ceremony: Mapping[str, Any],
    *,
    registry: Mapping[str, Any],
    backup: Mapping[str, Any],
    errors: list[str] | None = None,
) -> dict[str, Any]:
    errs = errors if errors is not None else []
    if ceremony.get("schema") != SSS_PRODUCTION_CEREMONY_SCHEMA_V1:
        errs.append("production ceremony schema mismatch")
        return {"ok": False, "errors": errs, "production_ready": False}
    if ceremony.get("backup_hash") != backup.get("backup_hash"):
        errs.append("production ceremony backup_hash does not match backup")
    if ceremony.get("authority_id") != registry.get("authority_id"):
        errs.append("production ceremony authority_id does not match registry")
    threshold = registry.get("threshold")
    attestations = ceremony.get("attestations", [])
    if not isinstance(attestations, list):
        errs.append("production ceremony attestations must be a list")
        return {"ok": False, "errors": errs, "production_ready": False}
    custodian_map: dict[str, dict[str, Any]] = {}
    for c in registry.get("custodians", []):
        custodian_map[c["custodian_id"]] = c
    seen: set[str] = set()
    for i, att in enumerate(attestations):
        cid = att.get("attested_by") if isinstance(att, dict) else None
        if not cid or cid not in custodian_map:
            errs.append(f"production ceremony attestation[{i}] from unknown custodian")
            continue
        if cid in seen:
            errs.append(f"production ceremony attestation[{i}] duplicate custodian: {cid}")
            continue
        seen.add(cid)
        result = verify_custodian_attestation_v1(
            att,
            expected_backup_hash=backup.get("backup_hash", ""),
            expected_public_key=custodian_map[cid]["bls_public_key"],
            errors=errs,
        )
    if isinstance(threshold, int) and len(seen) < threshold:
        errs.append(
            f"production ceremony has {len(seen)} attestations, needs {threshold}"
        )
    distinct_orgs = len(
        {custodian_map[cid]["organization"] for cid in seen if cid in custodian_map}
    )
    if distinct_orgs < _MIN_DISTINCT_CUSTODIANS:
        errs.append(
            f"production ceremony requires {_MIN_DISTINCT_CUSTODIANS} distinct organizations, got {distinct_orgs}"
        )
    if ceremony.get("quorum_satisfied") is not True:
        errs.append("production ceremony quorum_satisfied must be true")
    production_ready = not errs
    return {"ok": production_ready, "errors": errs, "production_ready": production_ready}


def build_key_rotation_ceremony_v1(
    *,
    authority_id: str,
    chain_id: str,
    old_key_id: str,
    new_key_id: str,
    old_backup_hash: str,
    new_backup_hash: str,
    registry: Mapping[str, Any],
    attestations: Sequence[Mapping[str, Any]],
    rotated_at_epoch: int,
) -> dict[str, Any]:
    threshold = registry.get("threshold")
    if not isinstance(threshold, int) or threshold < 2:
        raise ValueError("registry threshold must be >= 2")
    custodian_map: dict[str, dict[str, Any]] = {
        c["custodian_id"]: c for c in registry.get("custodians", [])
    }
    verified: list[dict[str, Any]] = []
    seen: set[str] = set()
    rotation_payload = {
        "authority_id": authority_id,
        "chain_id": chain_id,
        "old_key_id": old_key_id,
        "new_key_id": new_key_id,
        "old_backup_hash": old_backup_hash,
        "new_backup_hash": new_backup_hash,
        "rotated_at_epoch": rotated_at_epoch,
    }
    rotation_hash = _rotation_hash_v1(rotation_payload)
    for att in attestations:
        cid = att.get("attested_by")
        if not isinstance(cid, str) or cid not in custodian_map:
            raise ValueError(f"rotation attestation from unknown custodian: {cid}")
        if cid in seen:
            raise ValueError(f"duplicate rotation attestation: {cid}")
        seen.add(cid)
        envelope = att.get("signature_envelope")
        if not isinstance(envelope, dict):
            raise ValueError(f"rotation attestation from {cid} missing signature envelope")
        try:
            validate_bls_signed_artifact_envelope_v0(
                envelope=envelope,
                expected_payload_kind=KEY_ROTATION_PAYLOAD_KIND_V1,
                expected_payload_hash=rotation_hash,
                expected_public_key=custodian_map[cid]["bls_public_key"],
            )
        except Exception as exc:
            raise ValueError(f"rotation attestation from {cid} signature invalid: {exc}") from exc
        verified.append(dict(att))
    if len(verified) < threshold:
        raise ValueError(
            f"key rotation requires {threshold} attestations, got {len(verified)}"
        )
    ceremony: dict[str, Any] = {
        **rotation_payload,
        "schema": SSS_KEY_ROTATION_CEREMONY_SCHEMA_V1,
        "registry_threshold": threshold,
        "attestation_count": len(verified),
        "attestations": verified,
        "quorum_satisfied": len(verified) >= threshold,
        "old_key_invalidated": True,
        "production_security_claim": True,
    }
    return ceremony


def _rotation_hash_v1(payload: Mapping[str, Any]) -> str:
    from src.integration.zeno_ledger_v0 import hash_v0

    body = {k: v for k, v in dict(payload).items() if k != "signature_envelope"}
    return hash_v0(KEY_ROTATION_PAYLOAD_KIND_V1, body)


def evaluate_key_rotation_ceremony_v1(
    ceremony: Mapping[str, Any],
    *,
    registry: Mapping[str, Any],
    errors: list[str] | None = None,
) -> dict[str, Any]:
    errs = errors if errors is not None else []
    if ceremony.get("schema") != SSS_KEY_ROTATION_CEREMONY_SCHEMA_V1:
        errs.append("key rotation ceremony schema mismatch")
        return {"ok": False, "errors": errs, "rotation_ready": False}
    threshold = registry.get("threshold")
    custodian_map: dict[str, dict[str, Any]] = {
        c["custodian_id"]: c for c in registry.get("custodians", [])
    }
    attestations = ceremony.get("attestations", [])
    if not isinstance(attestations, list):
        errs.append("key rotation attestations must be a list")
        return {"ok": False, "errors": errs, "rotation_ready": False}
    rotation_payload = {
        "authority_id": ceremony.get("authority_id"),
        "chain_id": ceremony.get("chain_id"),
        "old_key_id": ceremony.get("old_key_id"),
        "new_key_id": ceremony.get("new_key_id"),
        "old_backup_hash": ceremony.get("old_backup_hash"),
        "new_backup_hash": ceremony.get("new_backup_hash"),
        "rotated_at_epoch": ceremony.get("rotated_at_epoch"),
    }
    rotation_hash = _rotation_hash_v1(rotation_payload)
    seen: set[str] = set()
    for i, att in enumerate(attestations):
        cid = att.get("attested_by") if isinstance(att, dict) else None
        if not cid or cid not in custodian_map:
            errs.append(f"key rotation attestation[{i}] from unknown custodian")
            continue
        if cid in seen:
            errs.append(f"key rotation attestation[{i}] duplicate custodian: {cid}")
            continue
        seen.add(cid)
        envelope = att.get("signature_envelope")
        if not isinstance(envelope, dict):
            errs.append(f"key rotation attestation[{i}] missing signature envelope")
            continue
        try:
            validate_bls_signed_artifact_envelope_v0(
                envelope=envelope,
                expected_payload_kind=KEY_ROTATION_PAYLOAD_KIND_V1,
                expected_payload_hash=rotation_hash,
                expected_public_key=custodian_map[cid]["bls_public_key"],
            )
        except Exception as exc:
            errs.append(f"key rotation attestation[{i}] signature invalid: {exc}")
    if isinstance(threshold, int) and len(seen) < threshold:
        errs.append(f"key rotation has {len(seen)} attestations, needs {threshold}")
    if ceremony.get("old_key_invalidated") is not True:
        errs.append("key rotation must invalidate old key")
    if ceremony.get("quorum_satisfied") is not True:
        errs.append("key rotation quorum_satisfied must be true")
    rotation_ready = not errs
    return {"ok": rotation_ready, "errors": errs, "rotation_ready": rotation_ready}
