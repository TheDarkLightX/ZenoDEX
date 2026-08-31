"""Encrypted SSS backup receipts for the perps wallet authority lane.

This module models optional backup and recovery evidence. It does not make the
server a custodian: encrypted share envelopes are transport artifacts, and the
status explicitly distinguishes local-testnet fixture readiness from a
production security claim.
"""

from __future__ import annotations

import base64
import hashlib
import json
import secrets
from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF

from src.integration.perps_wallet_authority import evaluate_perps_wallet_authority_profile_v1
from src.integration.bls_intent_signing import bls_pubkey_hex_from_privkey
from src.integration.zeno_ledger_signature import validate_bls_signed_artifact_envelope_v0
from src.integration.zeno_ledger_v0 import hash_v0


PERPS_WALLET_ENCRYPTED_SSS_BACKUP_SCHEMA_V1 = "zenodex/perps-wallet-encrypted-sss-backup/v1"
PERPS_WALLET_ENCRYPTED_SSS_BACKUP_STATUS_SCHEMA_V1 = (
    "zenodex/perps-wallet-encrypted-sss-backup-status/v1"
)
PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_SCHEMA_V1 = (
    "zenodex/perps-wallet-encrypted-sss-recipient-keys/v1"
)
PERPS_WALLET_ENCRYPTED_SSS_AUDIT_EVIDENCE_SCHEMA_V1 = (
    "zenodex/perps-wallet-encrypted-sss-audit-evidence/v1"
)
PERPS_WALLET_ENCRYPTED_SSS_AUDIT_PAYLOAD_KIND_V1 = "perps_wallet_encrypted_sss_audit_evidence"
SHAMIR_GF256_ALGORITHM_V1 = "shamir-gf256-v1"
AEAD_AES_256_GCM = "AES-256-GCM"
KDF_HKDF_SHA256 = "HKDF-SHA256"

_BACKUP_NON_HASH_FIELDS = frozenset({"backup_hash"})
_ENVELOPE_NON_HASH_FIELDS = frozenset({"envelope_hash"})
_DELIVERY_NON_HASH_FIELDS = frozenset({"delivery_hash"})
_AUDIT_NON_HASH_FIELDS = frozenset({"audit_hash", "signature_envelope"})
_DRILL_NON_HASH_FIELDS = frozenset({"drill_hash"})
_HOSTILE_SUITE_NON_HASH_FIELDS = frozenset({"suite_hash"})
_REQUIRED_PROVIDER_KINDS = frozenset({"recovery_email", "cloud_drive", "offline_export"})
_LIVE_DELIVERY_MODES = frozenset({"smtp", "dropbox", "box", "offline_export"})
_FORBIDDEN_RAW_FIELD_FRAGMENTS = (
    "privkey",
    "private_key",
    "privatekey",
    "raw_private_key",
    "mnemonic",
    "seed_phrase",
    "seedphrase",
    "raw_share",
    "share_plaintext",
    "plaintext_share_bytes",
    "key_material_hex",
)


@dataclass(frozen=True)
class SssBackupRecipient:
    recipient_id: str
    provider_kind: str
    provider_id: str
    transport_kind: str
    destination_hash: str
    recipient_root_key: bytes


def split_secret_shamir_gf256(
    secret_material: bytes,
    *,
    threshold: int,
    share_count: int,
    coefficient_seed: bytes | None = None,
) -> list[tuple[int, bytes]]:
    """Split bytes into Shamir shares over GF(256)."""

    if not secret_material:
        raise ValueError("secret_material must be non-empty")
    if threshold < 2:
        raise ValueError("threshold must be at least 2")
    if share_count < threshold:
        raise ValueError("share_count must be >= threshold")
    if share_count > 255:
        raise ValueError("share_count must be <= 255")
    if coefficient_seed is None:
        coefficient_seed = secrets.token_bytes(32)
    if not coefficient_seed:
        raise ValueError("coefficient_seed must be non-empty")

    shares = bytearray(secret_material_len := len(secret_material))
    del shares
    out = [(x, bytearray(secret_material_len)) for x in range(1, share_count + 1)]
    for byte_index, value in enumerate(secret_material):
        coefficients = [value]
        for degree in range(1, threshold):
            coef = _derive_coefficient(coefficient_seed, byte_index=byte_index, degree=degree)
            if degree == threshold - 1 and coef == 0:
                coef = 1
            coefficients.append(coef)
        for x, share_bytes in out:
            share_bytes[byte_index] = _eval_poly_gf256(coefficients, x)
    return [(x, bytes(share_bytes)) for x, share_bytes in out]


def recover_secret_shamir_gf256(shares: Sequence[tuple[int, bytes]]) -> bytes:
    """Recover the secret from Shamir shares by interpolating at x=0."""

    if not shares:
        raise ValueError("shares must be non-empty")
    seen_x: set[int] = set()
    share_len: int | None = None
    for x, share in shares:
        if not isinstance(x, int) or isinstance(x, bool) or x <= 0 or x > 255:
            raise ValueError("share x coordinate must be in 1..255")
        if x in seen_x:
            raise ValueError("duplicate share x coordinate")
        seen_x.add(x)
        if share_len is None:
            share_len = len(share)
        elif len(share) != share_len:
            raise ValueError("all shares must have the same length")
    if share_len is None or share_len == 0:
        raise ValueError("shares must be non-empty")

    recovered = bytearray(share_len)
    for byte_index in range(share_len):
        value = 0
        for i, (xi, share_i) in enumerate(shares):
            coefficient = 1
            for j, (xj, _) in enumerate(shares):
                if i == j:
                    continue
                denominator = xi ^ xj
                if denominator == 0:
                    raise ValueError("duplicate share x coordinate")
                coefficient = _gf_mul(coefficient, _gf_div(xj, denominator))
            value ^= _gf_mul(share_i[byte_index], coefficient)
        recovered[byte_index] = value
    return bytes(recovered)


def build_perps_wallet_encrypted_sss_backup_v1(
    *,
    authority_id: str,
    chain_id: str,
    wallet_authority_hash: str,
    subject_key_id: str,
    secret_material: bytes,
    recipients: Sequence[SssBackupRecipient],
    threshold: int = 3,
    created_at_epoch: int = 13,
    drill_epoch: int = 14,
    backup_id: str = "perps-wallet-a-localtest-encrypted-sss-v1",
    coefficient_seed: bytes | None = None,
    encryption_salt: bytes | None = None,
) -> dict[str, Any]:
    if len(recipients) < threshold:
        raise ValueError("recipient count must be >= threshold")
    if threshold < 2:
        raise ValueError("threshold must be at least 2")

    shares = split_secret_shamir_gf256(
        secret_material,
        threshold=threshold,
        share_count=len(recipients),
        coefficient_seed=coefficient_seed,
    )
    if encryption_salt is None:
        encryption_salt = secrets.token_bytes(32)
    if not encryption_salt:
        raise ValueError("encryption_salt must be non-empty")
    key_fingerprint = _sha256_hex(secret_material)
    envelopes = [
        _encrypt_share_envelope(
            backup_id=backup_id,
            chain_id=chain_id,
            wallet_authority_hash=wallet_authority_hash,
            subject_key_id=subject_key_id,
            recipient=recipient,
            share_index=index,
            x=x,
            share_bytes=share_bytes,
            encryption_salt=encryption_salt,
        )
        for index, ((x, share_bytes), recipient) in enumerate(zip(shares, recipients, strict=True), start=1)
    ]

    selected = envelopes[:threshold]
    selected_recipients = list(recipients[:threshold])
    recovered = recover_secret_shamir_gf256(
        [
            (
                int(envelope["x"]),
                _decrypt_share_envelope(
                    backup_id=backup_id,
                    wallet_authority_hash=wallet_authority_hash,
                    envelope=envelope,
                    recipient_root_key=recipient.recipient_root_key,
                ),
            )
            for envelope, recipient in zip(selected, selected_recipients, strict=True)
        ]
    )
    insufficient_recovered = recover_secret_shamir_gf256(
        [
            (
                int(envelope["x"]),
                _decrypt_share_envelope(
                    backup_id=backup_id,
                    wallet_authority_hash=wallet_authority_hash,
                    envelope=envelope,
                    recipient_root_key=recipient.recipient_root_key,
                ),
            )
            for envelope, recipient in zip(selected[:-1], selected_recipients[:-1], strict=True)
        ]
    )
    tampered_ciphertext_rejected = _tampered_ciphertext_rejected(
        backup_id=backup_id,
        wallet_authority_hash=wallet_authority_hash,
        envelope=selected[0],
        recipient_root_key=selected_recipients[0].recipient_root_key,
    )
    wrong_recipient_key_rejected = _wrong_recipient_key_rejected(
        backup_id=backup_id,
        wallet_authority_hash=wallet_authority_hash,
        envelope=selected[0],
        wrong_key=selected_recipients[1].recipient_root_key,
    )
    duplicate_share_rejected = _duplicate_share_rejected(selected[0])

    storage_provider_kinds = sorted({recipient.provider_kind for recipient in recipients})
    delivery_evidence = [_delivery_receipt_for_envelope(envelope) for envelope in envelopes]
    recovery_drill = {
        "drill_id": "local-testnet-encrypted-sss-recovery-drill-1",
        "performed_at_epoch": drill_epoch,
        "selected_share_ids": [str(envelope["share_id"]) for envelope in selected],
        "selected_provider_kinds": sorted({str(envelope["provider_kind"]) for envelope in selected}),
        "threshold_satisfied": True,
        "reconstituted_key_matches": recovered == secret_material,
        "reconstituted_key_fingerprint": key_fingerprint,
        "new_key_rotation_required": True,
        "old_key_invalidated_on_completion": True,
    }
    recovery_drill["drill_hash"] = perps_wallet_encrypted_sss_recovery_drill_hash_v1(recovery_drill)
    hostile_share_tests: dict[str, Any] = {
        "insufficient_shares_rejected": insufficient_recovered != secret_material,
        "tampered_ciphertext_rejected": tampered_ciphertext_rejected,
        "wrong_recipient_key_rejected": wrong_recipient_key_rejected,
        "duplicate_share_rejected": duplicate_share_rejected,
    }
    hostile_share_tests["suite_hash"] = perps_wallet_encrypted_sss_hostile_suite_hash_v1(hostile_share_tests)

    backup: dict[str, Any] = {
        "schema": PERPS_WALLET_ENCRYPTED_SSS_BACKUP_SCHEMA_V1,
        "authority_id": authority_id,
        "chain_id": chain_id,
        "wallet_authority_hash": wallet_authority_hash,
        "subject_key_id": subject_key_id,
        "backup_id": backup_id,
        "created_at_epoch": created_at_epoch,
        "sss": {
            "algorithm": SHAMIR_GF256_ALGORITHM_V1,
            "threshold": threshold,
            "share_count": len(envelopes),
            "x_coordinates": [int(envelope["x"]) for envelope in envelopes],
        },
        "encryption": {
            "library": "cryptography",
            "aead": AEAD_AES_256_GCM,
            "kdf": KDF_HKDF_SHA256,
            "key_derivation": "per-recipient local-testnet fixture root",
        },
        "storage_policy": {
            "min_provider_kinds": 3,
            "requires_recovery_email": True,
            "requires_cloud_drive": True,
            "requires_offline_export": True,
        },
        "storage_provider_kinds": storage_provider_kinds,
        "envelopes": envelopes,
        "delivery_evidence": delivery_evidence,
        "recovery_drill": recovery_drill,
        "hostile_share_tests": hostile_share_tests,
        "raw_material_exposure": {
            "key_material_exposed": False,
            "share_material_exposed": False,
            "server_can_reconstitute": False,
        },
        "audit_evidence": {
            "audit_required_for_production": True,
            "external_audit_ready": False,
            "audit_status": "local-fixture-unaudited",
            "audit_report_hash": None,
        },
        "production_security_claim": False,
        "audit_status": "local-fixture-unaudited",
        "not_claimed": [
            "does_not_claim_server_side_custody",
            "does_not_claim_plaintext_share_storage",
            "does_not_claim_external_email_delivery",
            "does_not_claim_dropbox_or_box_account_delivery",
            "does_not_claim_audited_production_sss_custody",
        ],
    }
    backup["backup_hash"] = perps_wallet_encrypted_sss_backup_hash_v1(backup)
    return backup


def build_perps_wallet_encrypted_sss_recipient_keys_v1(
    *,
    backup: Mapping[str, Any],
    recipients: Sequence[SssBackupRecipient],
) -> dict[str, Any]:
    """Build private local replay keys for encrypted SSS fixture evaluation.

    This artifact is intentionally separate from the public backup/status
    receipts. It is mounted into the local API so the evaluator can decrypt and
    replay the recovery drill instead of trusting self-attested booleans.
    """

    body = {
        "schema": PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_SCHEMA_V1,
        "backup_id": backup.get("backup_id"),
        "backup_hash": backup.get("backup_hash"),
        "wallet_authority_hash": backup.get("wallet_authority_hash"),
        "subject_key_id": backup.get("subject_key_id"),
        "keys": [
            {
                "recipient_id": recipient.recipient_id,
                "provider_kind": recipient.provider_kind,
                "provider_id": recipient.provider_id,
                "transport_kind": recipient.transport_kind,
                "destination_hash": recipient.destination_hash,
                "recipient_root_key_b64": _b64(recipient.recipient_root_key),
                "recipient_root_key_sha256": _sha256_hex(recipient.recipient_root_key),
            }
            for recipient in recipients
        ],
        "production_security_claim": False,
        "not_claimed": [
            "local_replay_keys_are_not_public_config",
            "does_not_claim_production_recipient_key_custody",
        ],
    }
    body["keyset_hash"] = hash_v0("perps_wallet_encrypted_sss_recipient_keys_v1", body)
    return body


def recipient_root_keys_from_fixture_v1(keys_fixture: Mapping[str, Any]) -> dict[str, bytes]:
    obj = dict(keys_fixture)
    if obj.get("schema") != PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_SCHEMA_V1:
        raise ValueError("encrypted SSS recipient keys schema mismatch")
    expected_hash = obj.get("keyset_hash")
    body = {key: value for key, value in obj.items() if key != "keyset_hash"}
    if expected_hash != hash_v0("perps_wallet_encrypted_sss_recipient_keys_v1", body):
        raise ValueError("encrypted SSS recipient keys hash mismatch")
    if obj.get("production_security_claim") is not False:
        raise ValueError("encrypted SSS recipient keys must not claim production custody")
    raw_keys = _require_list(obj.get("keys"), name="keys")
    out: dict[str, bytes] = {}
    for index, item in enumerate(raw_keys):
        entry = _require_mapping(item, name=f"keys[{index}]")
        recipient_id = _require_nonempty_str(entry.get("recipient_id"), name=f"keys[{index}].recipient_id")
        root_key = _b64decode(
            _require_nonempty_str(
                entry.get("recipient_root_key_b64"),
                name=f"keys[{index}].recipient_root_key_b64",
            ),
            name=f"keys[{index}].recipient_root_key_b64",
        )
        if len(root_key) != 32:
            raise ValueError(f"keys[{index}].recipient_root_key_b64 must decode to 32 bytes")
        if entry.get("recipient_root_key_sha256") != _sha256_hex(root_key):
            raise ValueError(f"keys[{index}].recipient root key hash mismatch")
        if recipient_id in out:
            raise ValueError(f"duplicate encrypted SSS recipient key: {recipient_id}")
        out[recipient_id] = root_key
    if not out:
        raise ValueError("encrypted SSS recipient keys fixture is empty")
    return out


def perps_wallet_encrypted_sss_envelope_hash_v1(envelope: Mapping[str, Any]) -> str:
    return hash_v0(
        "perps_wallet_encrypted_sss_envelope_v1",
        {key: value for key, value in dict(envelope).items() if key not in _ENVELOPE_NON_HASH_FIELDS},
    )


def perps_wallet_encrypted_sss_delivery_hash_v1(delivery: Mapping[str, Any]) -> str:
    return hash_v0(
        "perps_wallet_encrypted_sss_delivery_v1",
        {key: value for key, value in dict(delivery).items() if key not in _DELIVERY_NON_HASH_FIELDS},
    )


def perps_wallet_encrypted_sss_audit_subject_hash_v1(backup: Mapping[str, Any]) -> str:
    return hash_v0(
        "perps_wallet_encrypted_sss_audit_subject_v1",
        {
            key: value
            for key, value in dict(backup).items()
            if key not in {"backup_hash", "audit_evidence"}
        },
    )


def perps_wallet_encrypted_sss_audit_evidence_hash_v1(audit_evidence: Mapping[str, Any]) -> str:
    return hash_v0(
        "perps_wallet_encrypted_sss_audit_evidence_v1",
        {key: value for key, value in dict(audit_evidence).items() if key not in _AUDIT_NON_HASH_FIELDS},
    )


def perps_wallet_encrypted_sss_recovery_drill_hash_v1(drill: Mapping[str, Any]) -> str:
    return hash_v0(
        "perps_wallet_encrypted_sss_recovery_drill_v1",
        {key: value for key, value in dict(drill).items() if key not in _DRILL_NON_HASH_FIELDS},
    )


def perps_wallet_encrypted_sss_hostile_suite_hash_v1(suite: Mapping[str, Any]) -> str:
    return hash_v0(
        "perps_wallet_encrypted_sss_hostile_suite_v1",
        {key: value for key, value in dict(suite).items() if key not in _HOSTILE_SUITE_NON_HASH_FIELDS},
    )


def perps_wallet_encrypted_sss_backup_hash_v1(backup: Mapping[str, Any]) -> str:
    return hash_v0(
        "perps_wallet_encrypted_sss_backup_v1",
        {key: value for key, value in dict(backup).items() if key not in _BACKUP_NON_HASH_FIELDS},
    )


def evaluate_perps_wallet_encrypted_sss_backup_v1(
    profile: Mapping[str, Any] | None,
    backup: Mapping[str, Any] | None,
    *,
    expected_chain_id: str | None = None,
    recipient_root_keys: Mapping[str, bytes] | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    if backup is None:
        errors.append("encrypted SSS backup artifact is missing")
        return _status(errors=errors, profile=profile, backup=None)

    obj = dict(backup)

    authority_status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=expected_chain_id)
    if authority_status.get("production_wallet_authority") is not True:
        errors.append("wallet authority profile is not ready")

    _reject_forbidden_raw_fields(obj, errors=errors)
    if obj.get("schema") != PERPS_WALLET_ENCRYPTED_SSS_BACKUP_SCHEMA_V1:
        errors.append("encrypted SSS backup schema mismatch")
    if expected_chain_id is not None and obj.get("chain_id") != expected_chain_id:
        errors.append("encrypted SSS backup chain_id mismatch")
    if profile is not None and obj.get("wallet_authority_hash") != profile.get("wallet_authority_hash"):
        errors.append("encrypted SSS backup wallet_authority_hash mismatch")
    if obj.get("backup_hash") != perps_wallet_encrypted_sss_backup_hash_v1(obj):
        errors.append("encrypted SSS backup hash mismatch")

    threshold = 0
    share_count = 0
    try:
        sss = _require_mapping(obj.get("sss"), name="sss")
        if sss.get("algorithm") != SHAMIR_GF256_ALGORITHM_V1:
            errors.append("encrypted SSS backup algorithm mismatch")
        threshold = _require_positive_int(sss.get("threshold"), name="sss.threshold")
        share_count = _require_positive_int(sss.get("share_count"), name="sss.share_count")
        if threshold < 2:
            errors.append("encrypted SSS backup threshold must be at least 2")
        if share_count < threshold:
            errors.append("encrypted SSS backup share_count must be >= threshold")
        x_coordinates = _require_int_list(sss.get("x_coordinates"), name="sss.x_coordinates")
        if len(x_coordinates) != share_count:
            errors.append("encrypted SSS x_coordinates length must equal share_count")
        if len(set(x_coordinates)) != len(x_coordinates):
            errors.append("encrypted SSS x_coordinates must be unique")
    except Exception as exc:
        errors.append(str(exc))

    provider_kinds: set[str] = set()
    provider_ids: set[str] = set()
    envelope_ids: set[str] = set()
    envelope_by_id: dict[str, Mapping[str, Any]] = {}
    envelope_by_share_id: dict[str, Mapping[str, Any]] = {}
    share_ids: set[str] = set()
    xs: set[int] = set()
    try:
        envelopes = _require_list(obj.get("envelopes"), name="envelopes")
        if share_count and len(envelopes) != share_count:
            errors.append("encrypted SSS envelope count must equal share_count")
        for index, item in enumerate(envelopes):
            envelope = _require_mapping(item, name=f"envelopes[{index}]")
            _validate_envelope(envelope, errors=errors)
            for key in ("backup_id", "chain_id", "wallet_authority_hash", "subject_key_id"):
                if envelope.get(key) != obj.get(key):
                    errors.append(f"encrypted SSS envelope {key} mismatch")
            envelope_ids.add(str(envelope.get("envelope_id")))
            envelope_by_id[str(envelope.get("envelope_id"))] = envelope
            share_id = str(envelope.get("share_id"))
            share_ids.add(share_id)
            envelope_by_share_id[share_id] = envelope
            provider_kinds.add(str(envelope.get("provider_kind")))
            provider_ids.add(str(envelope.get("provider_id")))
            if isinstance(envelope.get("x"), int):
                xs.add(int(envelope["x"]))
        if len(envelope_ids) != len(envelopes):
            errors.append("encrypted SSS envelope ids must be unique")
        if len(share_ids) != len(envelopes):
            errors.append("encrypted SSS share ids must be unique")
        if len(xs) != len(envelopes):
            errors.append("encrypted SSS x coordinates must be unique per envelope")
    except Exception as exc:
        errors.append(str(exc))

    try:
        storage_policy = _require_mapping(obj.get("storage_policy"), name="storage_policy")
        min_provider_kinds = _require_positive_int(
            storage_policy.get("min_provider_kinds"), name="storage_policy.min_provider_kinds"
        )
        if len(provider_kinds) < min_provider_kinds:
            errors.append("encrypted SSS backup does not meet provider-kind diversity")
        if storage_policy.get("requires_recovery_email") is True and "recovery_email" not in provider_kinds:
            errors.append("encrypted SSS backup is missing a recovery email provider")
        if storage_policy.get("requires_cloud_drive") is True and "cloud_drive" not in provider_kinds:
            errors.append("encrypted SSS backup is missing a cloud-drive provider")
        if storage_policy.get("requires_offline_export") is True and "offline_export" not in provider_kinds:
            errors.append("encrypted SSS backup is missing an offline export provider")
        if not _REQUIRED_PROVIDER_KINDS.issubset(provider_kinds):
            errors.append("encrypted SSS backup is missing required provider kinds")
    except Exception as exc:
        errors.append(str(exc))

    provider_delivery_ready = False
    live_provider_delivery_ready = False
    delivery_modes: set[str] = set()
    try:
        delivery_errors: list[str] = []
        delivered_envelope_ids: set[str] = set()
        delivered_provider_kinds: set[str] = set()
        delivery_evidence = _require_list(obj.get("delivery_evidence"), name="delivery_evidence")
        if len(delivery_evidence) != len(envelope_by_id):
            delivery_errors.append("encrypted SSS delivery evidence count must equal envelope count")
        for index, item in enumerate(delivery_evidence):
            delivery = _require_mapping(item, name=f"delivery_evidence[{index}]")
            _validate_delivery_receipt(delivery, envelope_by_id=envelope_by_id, errors=delivery_errors)
            mode = str(delivery.get("delivery_mode"))
            if mode:
                delivery_modes.add(mode)
            if delivery.get("delivery_status") == "delivered":
                delivered_envelope_ids.add(str(delivery.get("envelope_id")))
                delivered_provider_kinds.add(str(delivery.get("provider_kind")))
        if delivered_envelope_ids != envelope_ids:
            delivery_errors.append("encrypted SSS delivery evidence must cover every envelope")
        if not _REQUIRED_PROVIDER_KINDS.issubset(delivered_provider_kinds):
            delivery_errors.append("encrypted SSS delivery evidence is missing required provider kinds")
        provider_delivery_ready = not delivery_errors
        live_provider_delivery_ready = provider_delivery_ready and bool(delivery_modes) and delivery_modes.issubset(
            _LIVE_DELIVERY_MODES
        )
        errors.extend(delivery_errors)
    except Exception as exc:
        errors.append(str(exc))

    recovery_drill_ready = False
    selected_share_ids: list[str] = []
    drill_fingerprint: str | None = None
    try:
        drill = _require_mapping(obj.get("recovery_drill"), name="recovery_drill")
        selected_share_ids = _require_str_list(drill.get("selected_share_ids"), name="recovery_drill.selected_share_ids")
        raw_drill_fingerprint = drill.get("reconstituted_key_fingerprint")
        drill_fingerprint = raw_drill_fingerprint if _is_root_hash(raw_drill_fingerprint) else None
        if len(selected_share_ids) < threshold:
            errors.append("encrypted SSS recovery drill selected fewer than threshold shares")
        if not set(selected_share_ids).issubset(share_ids):
            errors.append("encrypted SSS recovery drill references unknown share ids")
        if drill.get("threshold_satisfied") is not True:
            errors.append("encrypted SSS recovery drill did not satisfy threshold")
        if drill.get("reconstituted_key_matches") is not True:
            errors.append("encrypted SSS recovery drill did not reconstitute the key")
        if drill.get("new_key_rotation_required") is not True:
            errors.append("encrypted SSS recovery drill does not require new-key rotation")
        if drill.get("old_key_invalidated_on_completion") is not True:
            errors.append("encrypted SSS recovery drill does not invalidate the old key")
        if drill.get("drill_hash") != perps_wallet_encrypted_sss_recovery_drill_hash_v1(drill):
            errors.append("encrypted SSS recovery drill hash mismatch")
        recovery_drill_ready = not any(error.startswith("encrypted SSS recovery drill") for error in errors)
    except Exception as exc:
        errors.append(str(exc))

    replay_recovery_ready = False
    subject_public_key_matches = False
    replay_hostile_tests_ready = False
    replay_errors: list[str] = []
    try:
        replay = _replay_recovery_drill(
            profile=profile,
            backup=obj,
            selected_share_ids=selected_share_ids,
            envelope_by_share_id=envelope_by_share_id,
            recipient_root_keys=recipient_root_keys,
        )
        replay_recovery_ready = replay["replay_recovery_ready"]
        subject_public_key_matches = replay["subject_public_key_matches"]
        replay_errors.extend(replay["errors"])
        replay_hostile = _replay_hostile_share_tests(
            profile=profile,
            backup=obj,
            selected_share_ids=selected_share_ids,
            envelope_by_share_id=envelope_by_share_id,
            recipient_root_keys=recipient_root_keys,
            threshold=threshold,
            drill_fingerprint=drill_fingerprint,
        )
        replay_hostile_tests_ready = replay_hostile["replay_hostile_tests_ready"]
        replay_errors.extend(replay_hostile["errors"])
    except Exception as exc:
        replay_errors.append(f"encrypted SSS replay failed: {exc}")
    if replay_errors:
        errors.extend(replay_errors)

    hostile_share_tests_ready = False
    try:
        hostile = _require_mapping(obj.get("hostile_share_tests"), name="hostile_share_tests")
        for key in (
            "insufficient_shares_rejected",
            "tampered_ciphertext_rejected",
            "wrong_recipient_key_rejected",
            "duplicate_share_rejected",
        ):
            if hostile.get(key) is not True:
                errors.append(f"encrypted SSS hostile-share test failed: {key}")
        if hostile.get("suite_hash") != perps_wallet_encrypted_sss_hostile_suite_hash_v1(hostile):
            errors.append("encrypted SSS hostile-share suite hash mismatch")
        hostile_share_tests_ready = not any(error.startswith("encrypted SSS hostile-share") for error in errors)
    except Exception as exc:
        errors.append(str(exc))

    raw_material_absent = False
    try:
        exposure = _require_mapping(obj.get("raw_material_exposure"), name="raw_material_exposure")
        raw_material_absent = (
            exposure.get("key_material_exposed") is False
            and exposure.get("share_material_exposed") is False
            and exposure.get("server_can_reconstitute") is False
        )
        if not raw_material_absent:
            errors.append("encrypted SSS backup exposes raw key/share material or server-side reconstitution")
    except Exception as exc:
        errors.append(str(exc))

    raw_audit_status = obj.get("audit_status")
    audit_status = raw_audit_status if isinstance(raw_audit_status, str) else "unknown"
    external_audit_ready = False
    try:
        audit_evidence = _require_mapping(obj.get("audit_evidence"), name="audit_evidence")
        external_audit_ready = audit_evidence.get("external_audit_ready") is True
        raw_evidence_audit_status = audit_evidence.get("audit_status")
        if isinstance(raw_evidence_audit_status, str):
            audit_status = raw_evidence_audit_status
        if audit_status not in {
            "local-fixture-unaudited",
            "external-audit-in-progress",
            "external-audit-completed",
        }:
            errors.append("encrypted SSS audit status is unsupported")
        audit_report_hash = audit_evidence.get("audit_report_hash")
        if external_audit_ready and not _is_root_hash(audit_report_hash):
            errors.append("encrypted SSS audit evidence is ready but audit_report_hash is invalid")
        if external_audit_ready and audit_status != "external-audit-completed":
            errors.append("encrypted SSS external audit readiness requires completed audit status")
        if not external_audit_ready and audit_status == "external-audit-completed":
            errors.append("encrypted SSS audit status cannot be completed when audit is not ready")
        if external_audit_ready:
            _validate_external_audit_evidence(audit_evidence, backup=obj, errors=errors)
    except Exception as exc:
        errors.append(str(exc))

    if obj.get("production_security_claim") is not False:
        errors.append("encrypted SSS backup must not make a production security claim in local-testnet")

    return _status(
        errors=errors,
        profile=profile,
        backup=obj,
        threshold=threshold,
        share_count=share_count,
        provider_kinds=sorted(provider_kinds),
        provider_ids=sorted(provider_ids),
        provider_delivery_ready=provider_delivery_ready,
        live_provider_delivery_ready=live_provider_delivery_ready,
        delivery_modes=sorted(delivery_modes),
        recovery_drill_ready=recovery_drill_ready,
        hostile_share_tests_ready=hostile_share_tests_ready,
        raw_material_absent=raw_material_absent,
        external_audit_ready=external_audit_ready,
        audit_status=audit_status,
        replay_recovery_ready=replay_recovery_ready,
        subject_public_key_matches=subject_public_key_matches,
        replay_hostile_tests_ready=replay_hostile_tests_ready,
    )


def _validate_external_audit_evidence(
    audit_evidence: Mapping[str, Any],
    *,
    backup: Mapping[str, Any],
    errors: list[str],
) -> None:
    if audit_evidence.get("schema") != PERPS_WALLET_ENCRYPTED_SSS_AUDIT_EVIDENCE_SCHEMA_V1:
        errors.append("encrypted SSS external audit evidence schema mismatch")
    for key in (
        "audit_id",
        "auditor_id",
        "auditor_public_key",
        "audit_subject_hash",
        "audit_report_hash",
        "wallet_authority_hash",
        "findings_status",
        "audit_hash",
    ):
        if not isinstance(audit_evidence.get(key), str) or not str(audit_evidence.get(key)).strip():
            errors.append(f"encrypted SSS external audit evidence missing string field: {key}")
    for key in ("audit_subject_hash", "audit_report_hash", "wallet_authority_hash"):
        if not _is_root_hash(audit_evidence.get(key)):
            errors.append(f"encrypted SSS external audit evidence {key} is invalid")
    issued_at_epoch = audit_evidence.get("issued_at_epoch")
    if not isinstance(issued_at_epoch, int) or isinstance(issued_at_epoch, bool) or issued_at_epoch < 0:
        errors.append("encrypted SSS external audit evidence issued_at_epoch must be a non-negative int")
    if audit_evidence.get("findings_status") not in {"no-critical-open", "remediated"}:
        errors.append("encrypted SSS external audit evidence findings_status is unsupported")
    if audit_evidence.get("wallet_authority_hash") != backup.get("wallet_authority_hash"):
        errors.append("encrypted SSS external audit evidence wallet_authority_hash mismatch")
    if audit_evidence.get("audit_subject_hash") != perps_wallet_encrypted_sss_audit_subject_hash_v1(backup):
        errors.append("encrypted SSS external audit evidence subject hash mismatch")
    if audit_evidence.get("audit_hash") != perps_wallet_encrypted_sss_audit_evidence_hash_v1(audit_evidence):
        errors.append("encrypted SSS external audit evidence hash mismatch")
    envelope = audit_evidence.get("signature_envelope")
    if not isinstance(envelope, Mapping):
        errors.append("encrypted SSS external audit evidence signature envelope is missing")
        return
    try:
        validate_bls_signed_artifact_envelope_v0(
            envelope=envelope,
            expected_payload_kind=PERPS_WALLET_ENCRYPTED_SSS_AUDIT_PAYLOAD_KIND_V1,
            expected_payload_hash=str(audit_evidence.get("audit_hash")),
            expected_public_key=str(audit_evidence.get("auditor_public_key")),
        )
    except Exception as exc:
        errors.append(f"encrypted SSS external audit evidence signature invalid: {exc}")


def _status(
    *,
    errors: Sequence[str],
    profile: Mapping[str, Any] | None,
    backup: Mapping[str, Any] | None,
    threshold: int = 0,
    share_count: int = 0,
    provider_kinds: Sequence[str] | None = None,
    provider_ids: Sequence[str] | None = None,
    provider_delivery_ready: bool = False,
    live_provider_delivery_ready: bool = False,
    delivery_modes: Sequence[str] | None = None,
    recovery_drill_ready: bool = False,
    hostile_share_tests_ready: bool = False,
    raw_material_absent: bool = False,
    external_audit_ready: bool = False,
    audit_status: str = "unknown",
    replay_recovery_ready: bool = False,
    subject_public_key_matches: bool = False,
    replay_hostile_tests_ready: bool = False,
) -> dict[str, Any]:
    ready = not errors
    body: dict[str, Any] = {
        "schema": PERPS_WALLET_ENCRYPTED_SSS_BACKUP_STATUS_SCHEMA_V1,
        "ok": ready,
        "encrypted_sss_backup_ready": ready,
        "status": "ready" if ready else "blocked",
        "errors": list(errors),
        "wallet_authority_hash": None if profile is None else profile.get("wallet_authority_hash"),
        "backup_hash": None if backup is None else backup.get("backup_hash"),
        "backup_id": None if backup is None else backup.get("backup_id"),
        "subject_key_id": None if backup is None else backup.get("subject_key_id"),
        "sss_implemented": True,
        "sss_algorithm": SHAMIR_GF256_ALGORITHM_V1,
        "threshold": threshold,
        "share_count": share_count,
        "storage_provider_kinds": list(provider_kinds or []),
        "storage_provider_ids": list(provider_ids or []),
        "provider_delivery_ready": provider_delivery_ready,
        "live_provider_delivery_ready": live_provider_delivery_ready,
        "delivery_modes": list(delivery_modes or []),
        "requires_recovery_email": True,
        "requires_cloud_drive": True,
        "requires_offline_export": True,
        "recovery_drill_ready": recovery_drill_ready,
        "replay_recovery_ready": replay_recovery_ready,
        "subject_public_key_matches": subject_public_key_matches,
        "hostile_share_tests_ready": hostile_share_tests_ready,
        "replay_hostile_tests_ready": replay_hostile_tests_ready,
        "raw_material_absent": raw_material_absent,
        "server_side_reconstitution": False,
        "recovery_model": "guardian-threshold-social-recovery-plus-encrypted-sss-backup",
        "custody_path": "optional encrypted backup; not on-chain or server-side custody",
        "external_audit_ready": external_audit_ready,
        "audit_required_for_production": True,
        "production_security_claim": False,
        "audit_status": audit_status,
    }
    body["status_hash"] = hash_v0("perps_wallet_encrypted_sss_backup_status_v1", body)
    return body


def _replay_recovery_drill(
    *,
    profile: Mapping[str, Any] | None,
    backup: Mapping[str, Any],
    selected_share_ids: Sequence[str],
    envelope_by_share_id: Mapping[str, Mapping[str, Any]],
    recipient_root_keys: Mapping[str, bytes] | None,
) -> dict[str, Any]:
    errors: list[str] = []
    if not recipient_root_keys:
        return {
            "replay_recovery_ready": False,
            "subject_public_key_matches": False,
            "errors": ["encrypted SSS trusted recipient replay keys are missing"],
        }
    threshold = _require_positive_int(_require_mapping(backup.get("sss"), name="sss").get("threshold"), name="sss.threshold")
    if len(selected_share_ids) < threshold:
        errors.append("encrypted SSS replay selected fewer than threshold shares")
    decrypted_shares: list[tuple[int, bytes]] = []
    for share_id in selected_share_ids[:threshold]:
        envelope = envelope_by_share_id.get(str(share_id))
        if envelope is None:
            errors.append(f"encrypted SSS replay references unknown share id: {share_id}")
            continue
        recipient_id = str(envelope.get("recipient_id") or "")
        root_key = recipient_root_keys.get(recipient_id)
        if root_key is None:
            errors.append(f"encrypted SSS replay key missing for recipient: {recipient_id}")
            continue
        try:
            decrypted_shares.append(
                (
                    int(envelope["x"]),
                    _decrypt_share_envelope(
                        backup_id=str(backup["backup_id"]),
                        wallet_authority_hash=str(backup["wallet_authority_hash"]),
                        envelope=envelope,
                        recipient_root_key=root_key,
                    ),
                )
            )
        except (InvalidTag, ValueError, KeyError, TypeError) as exc:
            errors.append(f"encrypted SSS replay decrypt failed for {share_id}: {exc}")
    if errors:
        return {
            "replay_recovery_ready": False,
            "subject_public_key_matches": False,
            "errors": errors,
        }
    recovered = recover_secret_shamir_gf256(decrypted_shares)
    drill = _require_mapping(backup.get("recovery_drill"), name="recovery_drill")
    if drill.get("reconstituted_key_fingerprint") != _sha256_hex(recovered):
        errors.append("encrypted SSS replay recovered key fingerprint mismatch")
    subject_public_key = _subject_public_key(profile, str(backup.get("subject_key_id") or ""))
    try:
        recovered_public_key = "0x" + bls_pubkey_hex_from_privkey(recovered)
    except Exception as exc:
        errors.append(f"encrypted SSS replay recovered key is not a valid BLS key: {exc}")
        recovered_public_key = None
    subject_public_key_matches = recovered_public_key is not None and subject_public_key == recovered_public_key
    if not subject_public_key_matches:
        errors.append("encrypted SSS replay recovered key does not match subject public key")
    return {
        "replay_recovery_ready": not errors,
        "subject_public_key_matches": subject_public_key_matches,
        "errors": errors,
    }


def _replay_hostile_share_tests(
    *,
    profile: Mapping[str, Any] | None,
    backup: Mapping[str, Any],
    selected_share_ids: Sequence[str],
    envelope_by_share_id: Mapping[str, Mapping[str, Any]],
    recipient_root_keys: Mapping[str, bytes] | None,
    threshold: int,
    drill_fingerprint: str | None,
) -> dict[str, Any]:
    errors: list[str] = []
    if not recipient_root_keys:
        return {
            "replay_hostile_tests_ready": False,
            "errors": ["encrypted SSS hostile replay keys are missing"],
        }
    selected_envelopes = [
        envelope_by_share_id[str(share_id)]
        for share_id in selected_share_ids[:threshold]
        if str(share_id) in envelope_by_share_id
    ]
    if len(selected_envelopes) < threshold:
        return {
            "replay_hostile_tests_ready": False,
            "errors": ["encrypted SSS hostile replay selected fewer than threshold envelopes"],
        }
    first = selected_envelopes[0]
    first_root = recipient_root_keys.get(str(first.get("recipient_id") or ""))
    if first_root is None:
        return {
            "replay_hostile_tests_ready": False,
            "errors": ["encrypted SSS hostile replay missing first recipient key"],
        }
    if not _tampered_ciphertext_rejected(
        backup_id=str(backup["backup_id"]),
        wallet_authority_hash=str(backup["wallet_authority_hash"]),
        envelope=first,
        recipient_root_key=first_root,
    ):
        errors.append("encrypted SSS hostile replay accepted tampered ciphertext")
    wrong_root = next(
        (key for recipient_id, key in recipient_root_keys.items() if recipient_id != first.get("recipient_id")),
        None,
    )
    if wrong_root is None:
        errors.append("encrypted SSS hostile replay needs a second recipient key")
    elif not _wrong_recipient_key_rejected(
        backup_id=str(backup["backup_id"]),
        wallet_authority_hash=str(backup["wallet_authority_hash"]),
        envelope=first,
        wrong_key=wrong_root,
    ):
        errors.append("encrypted SSS hostile replay accepted wrong recipient key")
    if not _duplicate_share_rejected(first):
        errors.append("encrypted SSS hostile replay accepted duplicate share")
    insufficient_shares: list[tuple[int, bytes]] = []
    for envelope in selected_envelopes[: max(0, threshold - 1)]:
        root = recipient_root_keys.get(str(envelope.get("recipient_id") or ""))
        if root is None:
            errors.append("encrypted SSS hostile replay missing recipient key for insufficient-share check")
            continue
        insufficient_shares.append(
            (
                int(envelope["x"]),
                _decrypt_share_envelope(
                    backup_id=str(backup["backup_id"]),
                    wallet_authority_hash=str(backup["wallet_authority_hash"]),
                    envelope=envelope,
                    recipient_root_key=root,
                ),
            )
        )
    if len(insufficient_shares) >= threshold:
        errors.append("encrypted SSS hostile replay used too many insufficient shares")
    elif insufficient_shares:
        recovered = recover_secret_shamir_gf256(insufficient_shares)
        recovered_fingerprint = _sha256_hex(recovered)
        subject_public_key = _subject_public_key(profile, str(backup.get("subject_key_id") or ""))
        try:
            recovered_public_key = "0x" + bls_pubkey_hex_from_privkey(recovered)
        except Exception:
            recovered_public_key = None
        if recovered_fingerprint == drill_fingerprint or recovered_public_key == subject_public_key:
            errors.append("encrypted SSS hostile replay recovered subject key from insufficient shares")
    else:
        errors.append("encrypted SSS hostile replay has no insufficient shares to test")
    return {
        "replay_hostile_tests_ready": not errors,
        "errors": errors,
    }


def _encrypt_share_envelope(
    *,
    backup_id: str,
    chain_id: str,
    wallet_authority_hash: str,
    subject_key_id: str,
    recipient: SssBackupRecipient,
    share_index: int,
    x: int,
    share_bytes: bytes,
    encryption_salt: bytes,
) -> dict[str, Any]:
    share_id = f"share-{share_index:02d}"
    envelope_id = f"{backup_id}:{share_id}:{recipient.recipient_id}"
    aad = _envelope_aad(
        backup_id=backup_id,
        chain_id=chain_id,
        wallet_authority_hash=wallet_authority_hash,
        subject_key_id=subject_key_id,
        envelope_id=envelope_id,
        share_id=share_id,
        x=x,
        recipient=recipient,
    )
    aad_bytes = _canonical_json_bytes(aad)
    envelope_salt = hashlib.blake2b(
        encryption_salt
        + b"|zenodex-localtest-sss-envelope-salt-v1|"
        + envelope_id.encode("utf-8"),
        digest_size=32,
    ).digest()
    key, nonce = _derive_aead_material(
        recipient.recipient_root_key,
        backup_id=backup_id,
        envelope_id=envelope_id,
        wallet_authority_hash=wallet_authority_hash,
        envelope_salt=envelope_salt,
    )
    ciphertext = AESGCM(key).encrypt(nonce, share_bytes, aad_bytes)
    envelope = {
        **aad,
        "envelope_salt_b64": _b64(envelope_salt),
        "nonce_b64": _b64(nonce),
        "ciphertext_b64": _b64(ciphertext),
        "aad_hash": hash_v0("perps_wallet_encrypted_sss_envelope_aad_v1", aad),
        "share_sha256": _sha256_hex(share_bytes),
    }
    envelope["envelope_hash"] = perps_wallet_encrypted_sss_envelope_hash_v1(envelope)
    return envelope


def _delivery_receipt_for_envelope(envelope: Mapping[str, Any]) -> dict[str, Any]:
    delivery = {
        "schema": "zenodex/perps-wallet-encrypted-sss-delivery/v1",
        "envelope_id": envelope["envelope_id"],
        "share_id": envelope["share_id"],
        "provider_kind": envelope["provider_kind"],
        "provider_id": envelope["provider_id"],
        "destination_hash": envelope["destination_hash"],
        "envelope_hash": envelope["envelope_hash"],
        "delivery_mode": "local_fixture",
        "delivery_status": "delivered",
        "delivered_at_epoch": 13,
        "receipt_reference": f"local-fixture-delivery:{envelope['share_id']}",
    }
    delivery["delivery_hash"] = perps_wallet_encrypted_sss_delivery_hash_v1(delivery)
    return delivery


def build_perps_wallet_encrypted_sss_live_delivery_receipt_v1(
    envelope: Mapping[str, Any],
    *,
    delivery_mode: str,
    delivered_at_epoch: int,
    receipt_reference: str,
    provider_response_hash: str,
    smtp_message_id: str | None = None,
    provider_file_id: str | None = None,
    provider_revision: str | None = None,
    offline_export_manifest_hash: str | None = None,
) -> dict[str, Any]:
    if delivery_mode not in _LIVE_DELIVERY_MODES:
        raise ValueError("delivery_mode must be a live encrypted SSS delivery mode")
    delivery: dict[str, Any] = {
        "schema": "zenodex/perps-wallet-encrypted-sss-delivery/v1",
        "envelope_id": envelope["envelope_id"],
        "share_id": envelope["share_id"],
        "provider_kind": envelope["provider_kind"],
        "provider_id": envelope["provider_id"],
        "destination_hash": envelope["destination_hash"],
        "envelope_hash": envelope["envelope_hash"],
        "delivery_mode": delivery_mode,
        "delivery_status": "delivered",
        "delivered_at_epoch": delivered_at_epoch,
        "receipt_reference": receipt_reference,
        "provider_response_hash": provider_response_hash,
    }
    if smtp_message_id is not None:
        delivery["smtp_message_id"] = smtp_message_id
    if provider_file_id is not None:
        delivery["provider_file_id"] = provider_file_id
    if provider_revision is not None:
        delivery["provider_revision"] = provider_revision
    if offline_export_manifest_hash is not None:
        delivery["offline_export_manifest_hash"] = offline_export_manifest_hash
    delivery["delivery_hash"] = perps_wallet_encrypted_sss_delivery_hash_v1(delivery)
    return delivery


def _decrypt_share_envelope(
    *,
    backup_id: str,
    wallet_authority_hash: str,
    envelope: Mapping[str, Any],
    recipient_root_key: bytes,
) -> bytes:
    envelope_id = str(envelope["envelope_id"])
    key, _nonce = _derive_aead_material(
        recipient_root_key,
        backup_id=backup_id,
        envelope_id=envelope_id,
        wallet_authority_hash=wallet_authority_hash,
        envelope_salt=_b64decode(str(envelope["envelope_salt_b64"]), name="envelope_salt_b64"),
    )
    aad = {
        key: envelope[key]
        for key in (
            "backup_id",
            "chain_id",
            "wallet_authority_hash",
            "subject_key_id",
            "envelope_id",
            "share_id",
            "x",
            "recipient_id",
            "provider_kind",
            "provider_id",
            "transport_kind",
            "destination_hash",
        )
    }
    plaintext = AESGCM(key).decrypt(
        _b64decode(str(envelope["nonce_b64"]), name="nonce_b64"),
        _b64decode(str(envelope["ciphertext_b64"]), name="ciphertext_b64"),
        _canonical_json_bytes(aad),
    )
    if _sha256_hex(plaintext) != envelope.get("share_sha256"):
        raise ValueError("share hash mismatch")
    return plaintext


def _envelope_aad(
    *,
    backup_id: str,
    chain_id: str,
    wallet_authority_hash: str,
    subject_key_id: str,
    envelope_id: str,
    share_id: str,
    x: int,
    recipient: SssBackupRecipient,
) -> dict[str, Any]:
    return {
        "backup_id": backup_id,
        "chain_id": chain_id,
        "wallet_authority_hash": wallet_authority_hash,
        "subject_key_id": subject_key_id,
        "envelope_id": envelope_id,
        "share_id": share_id,
        "x": x,
        "recipient_id": recipient.recipient_id,
        "provider_kind": recipient.provider_kind,
        "provider_id": recipient.provider_id,
        "transport_kind": recipient.transport_kind,
        "destination_hash": recipient.destination_hash,
    }


def _validate_envelope(envelope: Mapping[str, Any], *, errors: list[str]) -> None:
    for key in (
        "backup_id",
        "chain_id",
        "wallet_authority_hash",
        "subject_key_id",
        "envelope_id",
        "share_id",
        "recipient_id",
        "provider_kind",
        "provider_id",
        "transport_kind",
        "destination_hash",
        "envelope_salt_b64",
        "nonce_b64",
        "ciphertext_b64",
        "aad_hash",
        "share_sha256",
        "envelope_hash",
    ):
        if not isinstance(envelope.get(key), str) or not str(envelope.get(key)).strip():
            errors.append(f"encrypted SSS envelope missing string field: {key}")
    x = envelope.get("x")
    if not isinstance(x, int) or isinstance(x, bool) or x <= 0 or x > 255:
        errors.append("encrypted SSS envelope x must be in 1..255")
    if not _is_root_hash(envelope.get("aad_hash")):
        errors.append("encrypted SSS envelope aad_hash is invalid")
    else:
        aad = {
            key: envelope.get(key)
            for key in (
                "backup_id",
                "chain_id",
                "wallet_authority_hash",
                "subject_key_id",
                "envelope_id",
                "share_id",
                "x",
                "recipient_id",
                "provider_kind",
                "provider_id",
                "transport_kind",
                "destination_hash",
            )
        }
        if envelope.get("aad_hash") != hash_v0("perps_wallet_encrypted_sss_envelope_aad_v1", aad):
            errors.append("encrypted SSS envelope aad_hash mismatch")
    if not _is_root_hash(envelope.get("share_sha256")):
        errors.append("encrypted SSS envelope share_sha256 is invalid")
    if envelope.get("envelope_hash") != perps_wallet_encrypted_sss_envelope_hash_v1(envelope):
        errors.append("encrypted SSS envelope hash mismatch")
    try:
        envelope_salt = _b64decode(str(envelope.get("envelope_salt_b64")), name="envelope_salt_b64")
        if len(envelope_salt) != 32:
            errors.append("encrypted SSS envelope salt must be 32 bytes")
    except Exception as exc:
        errors.append(str(exc))
    try:
        nonce = _b64decode(str(envelope.get("nonce_b64")), name="nonce_b64")
        if len(nonce) != 12:
            errors.append("encrypted SSS envelope nonce must be 12 bytes")
    except Exception as exc:
        errors.append(str(exc))
    try:
        ciphertext = _b64decode(str(envelope.get("ciphertext_b64")), name="ciphertext_b64")
        if not ciphertext:
            errors.append("encrypted SSS envelope ciphertext must be non-empty")
    except Exception as exc:
        errors.append(str(exc))


def _validate_delivery_receipt(
    delivery: Mapping[str, Any],
    *,
    envelope_by_id: Mapping[str, Mapping[str, Any]],
    errors: list[str],
) -> None:
    if delivery.get("schema") != "zenodex/perps-wallet-encrypted-sss-delivery/v1":
        errors.append("encrypted SSS delivery evidence schema mismatch")
    for key in (
        "envelope_id",
        "share_id",
        "provider_kind",
        "provider_id",
        "destination_hash",
        "envelope_hash",
        "delivery_mode",
        "delivery_status",
        "receipt_reference",
        "delivery_hash",
    ):
        if not isinstance(delivery.get(key), str) or not str(delivery.get(key)).strip():
            errors.append(f"encrypted SSS delivery evidence missing string field: {key}")
    if delivery.get("delivery_mode") not in {"local_fixture", *tuple(_LIVE_DELIVERY_MODES)}:
        errors.append("encrypted SSS delivery evidence has unsupported delivery_mode")
    if delivery.get("delivery_status") != "delivered":
        errors.append("encrypted SSS delivery evidence is not delivered")
    delivered_at_epoch = delivery.get("delivered_at_epoch")
    if not isinstance(delivered_at_epoch, int) or isinstance(delivered_at_epoch, bool) or delivered_at_epoch < 0:
        errors.append("encrypted SSS delivery evidence delivered_at_epoch must be a non-negative int")
    if not _is_root_hash(delivery.get("destination_hash")):
        errors.append("encrypted SSS delivery evidence destination_hash is invalid")
    if not _is_root_hash(delivery.get("envelope_hash")):
        errors.append("encrypted SSS delivery evidence envelope_hash is invalid")
    mode = delivery.get("delivery_mode")
    if mode in _LIVE_DELIVERY_MODES:
        if not _is_root_hash(delivery.get("provider_response_hash")):
            errors.append("encrypted SSS live delivery evidence provider_response_hash is invalid")
        if mode == "smtp" and not isinstance(delivery.get("smtp_message_id"), str):
            errors.append("encrypted SSS smtp delivery evidence missing smtp_message_id")
        if mode in {"dropbox", "box"}:
            if not isinstance(delivery.get("provider_file_id"), str) or not str(delivery.get("provider_file_id")).strip():
                errors.append("encrypted SSS cloud delivery evidence missing provider_file_id")
            if not isinstance(delivery.get("provider_revision"), str) or not str(delivery.get("provider_revision")).strip():
                errors.append("encrypted SSS cloud delivery evidence missing provider_revision")
        if mode == "offline_export" and not _is_root_hash(delivery.get("offline_export_manifest_hash")):
            errors.append("encrypted SSS offline export delivery evidence manifest hash is invalid")
    if delivery.get("delivery_hash") != perps_wallet_encrypted_sss_delivery_hash_v1(delivery):
        errors.append("encrypted SSS delivery evidence hash mismatch")

    envelope = envelope_by_id.get(str(delivery.get("envelope_id")))
    if envelope is None:
        errors.append("encrypted SSS delivery evidence references unknown envelope")
        return
    for key in ("share_id", "provider_kind", "provider_id", "destination_hash", "envelope_hash"):
        if delivery.get(key) != envelope.get(key):
            errors.append(f"encrypted SSS delivery evidence {key} mismatch")


def _tampered_ciphertext_rejected(
    *,
    backup_id: str,
    wallet_authority_hash: str,
    envelope: Mapping[str, Any],
    recipient_root_key: bytes,
) -> bool:
    tampered = dict(envelope)
    raw = bytearray(_b64decode(str(tampered["ciphertext_b64"]), name="ciphertext_b64"))
    raw[0] ^= 0x01
    tampered["ciphertext_b64"] = _b64(bytes(raw))
    try:
        _decrypt_share_envelope(
            backup_id=backup_id,
            wallet_authority_hash=wallet_authority_hash,
            envelope=tampered,
            recipient_root_key=recipient_root_key,
        )
    except (InvalidTag, ValueError):
        return True
    return False


def _wrong_recipient_key_rejected(
    *,
    backup_id: str,
    wallet_authority_hash: str,
    envelope: Mapping[str, Any],
    wrong_key: bytes,
) -> bool:
    try:
        _decrypt_share_envelope(
            backup_id=backup_id,
            wallet_authority_hash=wallet_authority_hash,
            envelope=envelope,
            recipient_root_key=wrong_key,
        )
    except (InvalidTag, ValueError):
        return True
    return False


def _duplicate_share_rejected(envelope: Mapping[str, Any]) -> bool:
    share = b"\x00" * 32
    try:
        recover_secret_shamir_gf256([(int(envelope["x"]), share), (int(envelope["x"]), share)])
    except ValueError:
        return True
    return False


def _derive_coefficient(seed: bytes, *, byte_index: int, degree: int) -> int:
    return hashlib.blake2b(
        seed
        + byte_index.to_bytes(4, "big")
        + degree.to_bytes(2, "big")
        + b"|zenodex-shamir-gf256-coefficient-v1",
        digest_size=1,
    ).digest()[0]


def _eval_poly_gf256(coefficients: Sequence[int], x: int) -> int:
    out = 0
    power = 1
    for coefficient in coefficients:
        out ^= _gf_mul(coefficient, power)
        power = _gf_mul(power, x)
    return out


def _gf_mul(a: int, b: int) -> int:
    a &= 0xFF
    b &= 0xFF
    out = 0
    while b:
        if b & 1:
            out ^= a
        carry = a & 0x80
        a = (a << 1) & 0xFF
        if carry:
            a ^= 0x1B
        b >>= 1
    return out


def _gf_pow(a: int, power: int) -> int:
    out = 1
    base = a
    while power:
        if power & 1:
            out = _gf_mul(out, base)
        base = _gf_mul(base, base)
        power >>= 1
    return out


def _gf_inv(a: int) -> int:
    if a == 0:
        raise ZeroDivisionError("cannot invert 0 in GF(256)")
    return _gf_pow(a, 254)


def _gf_div(a: int, b: int) -> int:
    return _gf_mul(a, _gf_inv(b))


def _derive_aead_material(
    root_key: bytes,
    *,
    backup_id: str,
    envelope_id: str,
    wallet_authority_hash: str,
    envelope_salt: bytes,
) -> tuple[bytes, bytes]:
    context = _length_prefixed_context(
        b"zenodex-perps-wallet-encrypted-sss-aead-context-v2",
        backup_id.encode("utf-8"),
        envelope_id.encode("utf-8"),
        wallet_authority_hash.encode("utf-8"),
        envelope_salt,
    )
    expanded = HKDF(
        algorithm=hashes.SHA256(),
        length=44,
        salt=hashlib.sha256(context).digest(),
        info=context,
    ).derive(root_key)
    return expanded[:32], expanded[32:]


def _derive_aead_key(
    root_key: bytes,
    *,
    backup_id: str,
    envelope_id: str,
    wallet_authority_hash: str,
    envelope_salt: bytes,
) -> bytes:
    key, _nonce = _derive_aead_material(
        root_key,
        backup_id=backup_id,
        envelope_id=envelope_id,
        wallet_authority_hash=wallet_authority_hash,
        envelope_salt=envelope_salt,
    )
    return key


def _derive_nonce(
    root_key: bytes,
    *,
    backup_id: str,
    envelope_id: str,
    wallet_authority_hash: str,
    envelope_salt: bytes,
) -> bytes:
    _key, nonce = _derive_aead_material(
        root_key,
        backup_id=backup_id,
        envelope_id=envelope_id,
        wallet_authority_hash=wallet_authority_hash,
        envelope_salt=envelope_salt,
    )
    return nonce


def _length_prefixed_context(domain: bytes, *parts: bytes) -> bytes:
    out = bytearray()
    for part in (domain, *parts):
        out.extend(len(part).to_bytes(4, "big"))
        out.extend(part)
    return bytes(out)


def _canonical_json_bytes(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def _b64(value: bytes) -> str:
    return base64.b64encode(value).decode("ascii")


def _b64decode(value: str, *, name: str) -> bytes:
    try:
        return base64.b64decode(value.encode("ascii"), validate=True)
    except Exception as exc:
        raise ValueError(f"{name} must be valid base64: {exc}") from None


def _sha256_hex(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _is_root_hash(value: object) -> bool:
    if not isinstance(value, str) or len(value) != 66 or not value.startswith("0x"):
        return False
    try:
        int(value[2:], 16)
    except ValueError:
        return False
    return True


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_nonempty_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise TypeError(f"{name} must be a non-empty string")
    return value


def _require_list(value: object, *, name: str) -> list[Any]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    return value


def _require_str_list(value: object, *, name: str) -> list[str]:
    raw = _require_list(value, name=name)
    out: list[str] = []
    for index, item in enumerate(raw):
        if not isinstance(item, str) or not item.strip():
            raise TypeError(f"{name}[{index}] must be a non-empty string")
        out.append(item)
    return out


def _require_int_list(value: object, *, name: str) -> list[int]:
    raw = _require_list(value, name=name)
    out: list[int] = []
    for index, item in enumerate(raw):
        if not isinstance(item, int) or isinstance(item, bool):
            raise TypeError(f"{name}[{index}] must be an int")
        out.append(item)
    return out


def _require_positive_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise TypeError(f"{name} must be a positive int")
    return value


def _subject_public_key(profile: Mapping[str, Any] | None, subject_key_id: str) -> str | None:
    if profile is None:
        return None
    key_manager = profile.get("key_manager")
    if not isinstance(key_manager, Mapping):
        return None
    key_refs = key_manager.get("key_refs")
    if not isinstance(key_refs, list):
        return None
    for item in key_refs:
        if not isinstance(item, Mapping):
            continue
        if item.get("key_id") == subject_key_id and item.get("status") == "active":
            public_key = item.get("public_key")
            return public_key if isinstance(public_key, str) else None
    return None


def _reject_forbidden_raw_fields(value: object, *, errors: list[str], path: str = "backup") -> None:
    if isinstance(value, Mapping):
        for key, item in value.items():
            key_str = str(key).lower()
            if any(fragment in key_str for fragment in _FORBIDDEN_RAW_FIELD_FRAGMENTS):
                errors.append(f"encrypted SSS backup contains forbidden raw-material field: {path}.{key}")
            _reject_forbidden_raw_fields(item, errors=errors, path=f"{path}.{key}")
        return
    if isinstance(value, list):
        for index, item in enumerate(value):
            _reject_forbidden_raw_fields(item, errors=errors, path=f"{path}[{index}]")
