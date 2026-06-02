"""Production-promotion evidence helpers for perps wallet custody.

The local public testnet can carry fixture custody evidence, but production
promotion requires a separate evidence object bound to a wallet authority hash.
This module only validates and hashes that evidence; it does not authorize
custody or settlement by itself.
"""

from __future__ import annotations

from typing import Any, Mapping

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex


HARDWARE_WALLET_EVIDENCE_SCHEMA_V1 = "zenodex/perps_wallet/production_hardware_wallet_evidence/v1"
_HARDWARE_WALLET_EVIDENCE_HASH_DOMAIN_V1 = "zenodex.perps_wallet.production_hardware_wallet_evidence/v1"
_MAX_EVIDENCE_AGE_SECONDS = 90 * 24 * 60 * 60


def attach_production_hardware_wallet_hash_v1(evidence: Mapping[str, Any]) -> dict[str, Any]:
    body = dict(evidence)
    body["evidence_hash"] = production_hardware_wallet_evidence_hash_v1(body)
    return body


def production_hardware_wallet_evidence_hash_v1(evidence: Mapping[str, Any]) -> str:
    body = {key: value for key, value in dict(evidence).items() if key != "evidence_hash"}
    return sha256_hex(
        domain_sep_bytes(_HARDWARE_WALLET_EVIDENCE_HASH_DOMAIN_V1)
        + canonical_json_bytes(body)
    )


def evaluate_production_hardware_wallet_evidence_v1(
    evidence: Mapping[str, Any] | None,
    *,
    wallet_authority_profile_hash: str | None,
    expected_device_pubkey: str | None = None,
    now: int | None = None,
) -> dict[str, Any]:
    gaps: list[str] = []
    body = dict(evidence or {})

    if evidence is None:
        gaps.append("production hardware wallet evidence missing")
    if body.get("schema") != HARDWARE_WALLET_EVIDENCE_SCHEMA_V1:
        gaps.append("production hardware wallet evidence schema mismatch")
    if not _nonempty_str(wallet_authority_profile_hash):
        gaps.append("production hardware wallet evidence wallet authority hash missing")
    elif body.get("profile_wallet_authority_hash") != wallet_authority_profile_hash:
        gaps.append("production hardware wallet evidence wallet authority hash mismatch")

    expected_hash = production_hardware_wallet_evidence_hash_v1(body)
    observed_hash = body.get("evidence_hash")
    if observed_hash != expected_hash:
        gaps.append("production hardware wallet evidence hash mismatch")

    for field in ("device_id", "device_model", "device_firmware_version"):
        if not _nonempty_str(body.get(field)):
            gaps.append(f"production hardware wallet evidence {field} missing")

    _require_mapping_fields(
        body.get("device_attestation"),
        label="device_attestation",
        fields=("pubkey", "challenge", "signature"),
        gaps=gaps,
    )
    attestation = body.get("device_attestation")
    if (
        expected_device_pubkey is not None
        and isinstance(attestation, Mapping)
        and attestation.get("pubkey") != expected_device_pubkey
    ):
        gaps.append("production hardware wallet evidence device attestation pubkey mismatch")
    _require_mapping_fields(
        body.get("os_prompt_capture"),
        label="os_prompt_capture",
        fields=("kind", "hash", "captured_at"),
        gaps=gaps,
    )
    _require_mapping_fields(
        body.get("device_approval_tx"),
        label="device_approval_tx",
        fields=("tx_payload_hash", "approval_signature", "captured_at"),
        gaps=gaps,
    )

    issued_at = body.get("issued_at")
    if not isinstance(issued_at, int) or isinstance(issued_at, bool) or issued_at <= 0:
        gaps.append("production hardware wallet evidence issued_at must be a positive integer")
    elif now is not None:
        if issued_at > int(now):
            gaps.append("production hardware wallet evidence issued_at is in the future")
        elif int(now) - issued_at > _MAX_EVIDENCE_AGE_SECONDS:
            gaps.append("production hardware wallet evidence is stale")

    production_ready = not gaps
    return {
        "schema": "zenodex/perps_wallet/production_hardware_wallet_evidence_status/v1",
        "ok": production_ready,
        "status": "ready" if production_ready else "blocked",
        "production_ready": production_ready,
        "evidence_hash": observed_hash if isinstance(observed_hash, str) else expected_hash,
        "expected_evidence_hash": expected_hash,
        "wallet_authority_profile_hash": wallet_authority_profile_hash,
        "gaps": gaps,
        "production_security_claim": production_ready,
    }


def _require_mapping_fields(
    value: object,
    *,
    label: str,
    fields: tuple[str, ...],
    gaps: list[str],
) -> None:
    if not isinstance(value, Mapping):
        gaps.append(f"production hardware wallet evidence {label} missing")
        return
    for field in fields:
        item = value.get(field)
        if field == "captured_at":
            if not isinstance(item, int) or isinstance(item, bool) or item <= 0:
                gaps.append(f"production hardware wallet evidence {label}.{field} missing")
        elif not _nonempty_str(item):
            gaps.append(f"production hardware wallet evidence {label}.{field} missing")


def _nonempty_str(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())
