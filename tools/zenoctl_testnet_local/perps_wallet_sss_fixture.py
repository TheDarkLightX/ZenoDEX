"""Encrypted-SSS construction and private keys for local-testnet fixtures only.

The shipped wallet runtime must never construct these artifacts or load this
aggregate recipient-key set: possessing every recipient root key would make the
server able to reconstruct the protected wallet key. Local tests use it solely
to generate deterministic evidence and replay recovery and hostile-share checks.
"""

from __future__ import annotations

import base64
import binascii
import hashlib
import json
import secrets
from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from cryptography.hazmat.primitives.ciphers.aead import AESGCM

from src.integration.perps_wallet_encrypted_sss_backup import (
    AEAD_AES_256_GCM,
    KDF_HKDF_SHA256,
    PERPS_WALLET_ENCRYPTED_SSS_BACKUP_SCHEMA_V1,
    SHAMIR_GF256_ALGORITHM_V1,
    _decrypt_share_envelope,
    _derive_aead_material,
    _duplicate_share_rejected,
    _tampered_ciphertext_rejected,
    _wrong_recipient_key_rejected,
    perps_wallet_encrypted_sss_backup_hash_v1,
    perps_wallet_encrypted_sss_delivery_hash_v1,
    perps_wallet_encrypted_sss_envelope_hash_v1,
    perps_wallet_encrypted_sss_hostile_suite_hash_v1,
    perps_wallet_encrypted_sss_recovery_drill_hash_v1,
    recover_secret_shamir_gf256,
)
from src.integration.zeno_ledger_v0 import hash_v0

PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_FIXTURE_SCHEMA_V1 = (
    "zenodex/perps-wallet-encrypted-sss-recipient-keys/v1"
)


@dataclass(frozen=True)
class SssBackupRecipient:
    """A fixture-only recipient carrying local deterministic root material."""

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
    """Split fixture bytes into Shamir shares over GF(256)."""

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

    secret_material_len = len(secret_material)
    out = [(x, bytearray(secret_material_len)) for x in range(1, share_count + 1)]
    for byte_index, value in enumerate(secret_material):
        coefficients = [value]
        for degree in range(1, threshold):
            coefficient = _derive_coefficient(
                coefficient_seed,
                byte_index=byte_index,
                degree=degree,
            )
            if degree == threshold - 1 and coefficient == 0:
                coefficient = 1
            coefficients.append(coefficient)
        for x, share_bytes in out:
            share_bytes[byte_index] = _eval_poly_gf256(coefficients, x)
    return [(x, bytes(share_bytes)) for x, share_bytes in out]


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
    """Construct deterministic local-testnet evidence; never call in runtime."""

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
        for index, ((x, share_bytes), recipient) in enumerate(
            zip(shares, recipients, strict=True),
            start=1,
        )
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
            for envelope, recipient in zip(
                selected[:-1],
                selected_recipients[:-1],
                strict=True,
            )
        ]
    )
    storage_provider_kinds = sorted({recipient.provider_kind for recipient in recipients})
    delivery_evidence = [_local_fixture_delivery_receipt(envelope) for envelope in envelopes]
    recovery_drill = {
        "drill_id": "local-testnet-encrypted-sss-recovery-drill-1",
        "performed_at_epoch": drill_epoch,
        "selected_share_ids": [str(envelope["share_id"]) for envelope in selected],
        "selected_provider_kinds": sorted(
            {str(envelope["provider_kind"]) for envelope in selected}
        ),
        "threshold_satisfied": True,
        "reconstituted_key_matches": recovered == secret_material,
        "reconstituted_key_fingerprint": key_fingerprint,
        "new_key_rotation_required": True,
        "old_key_invalidated_on_completion": True,
    }
    recovery_drill["drill_hash"] = perps_wallet_encrypted_sss_recovery_drill_hash_v1(
        recovery_drill
    )
    hostile_share_tests: dict[str, Any] = {
        "insufficient_shares_rejected": insufficient_recovered != secret_material,
        "tampered_ciphertext_rejected": _tampered_ciphertext_rejected(
            backup_id=backup_id,
            wallet_authority_hash=wallet_authority_hash,
            envelope=selected[0],
            recipient_root_key=selected_recipients[0].recipient_root_key,
        ),
        "wrong_recipient_key_rejected": _wrong_recipient_key_rejected(
            backup_id=backup_id,
            wallet_authority_hash=wallet_authority_hash,
            envelope=selected[0],
            wrong_key=selected_recipients[1].recipient_root_key,
        ),
        "duplicate_share_rejected": _duplicate_share_rejected(selected[0]),
    }
    hostile_share_tests["suite_hash"] = perps_wallet_encrypted_sss_hostile_suite_hash_v1(
        hostile_share_tests
    )

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


def build_perps_wallet_encrypted_sss_recipient_keys_fixture_v1(
    *,
    backup: Mapping[str, Any],
    recipients: Sequence[SssBackupRecipient],
) -> dict[str, Any]:
    """Build a private, explicitly non-production local replay key set."""
    body = {
        "schema": PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_FIXTURE_SCHEMA_V1,
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
                "recipient_root_key_b64": base64.b64encode(recipient.recipient_root_key).decode("ascii"),
                "recipient_root_key_sha256": hashlib.sha256(recipient.recipient_root_key).hexdigest(),
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
    """Parse a local replay key set; never call this from shipped runtime code."""
    obj = dict(keys_fixture)
    if obj.get("schema") != PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_FIXTURE_SCHEMA_V1:
        raise ValueError("encrypted SSS recipient keys schema mismatch")
    expected_hash = obj.get("keyset_hash")
    body = {key: value for key, value in obj.items() if key != "keyset_hash"}
    if expected_hash != hash_v0("perps_wallet_encrypted_sss_recipient_keys_v1", body):
        raise ValueError("encrypted SSS recipient keys hash mismatch")
    if obj.get("production_security_claim") is not False:
        raise ValueError("encrypted SSS recipient keys must not claim production custody")
    raw_keys = obj.get("keys")
    if not isinstance(raw_keys, list):
        raise ValueError("keys must be a list")
    out: dict[str, bytes] = {}
    for index, item in enumerate(raw_keys):
        if not isinstance(item, Mapping):
            raise ValueError(f"keys[{index}] must be an object")
        recipient_id = item.get("recipient_id")
        if not isinstance(recipient_id, str) or not recipient_id:
            raise ValueError(f"keys[{index}].recipient_id must be a non-empty string")
        encoded = item.get("recipient_root_key_b64")
        if not isinstance(encoded, str) or not encoded:
            raise ValueError(f"keys[{index}].recipient_root_key_b64 must be a non-empty string")
        try:
            root_key = base64.b64decode(encoded.encode("ascii"), validate=True)
        except (UnicodeEncodeError, binascii.Error) as exc:
            raise ValueError(f"keys[{index}].recipient_root_key_b64 is invalid base64") from exc
        if len(root_key) != 32:
            raise ValueError(f"keys[{index}].recipient_root_key_b64 must decode to 32 bytes")
        if item.get("recipient_root_key_sha256") != hashlib.sha256(root_key).hexdigest():
            raise ValueError(f"keys[{index}].recipient root key hash mismatch")
        if recipient_id in out:
            raise ValueError(f"duplicate encrypted SSS recipient key: {recipient_id}")
        out[recipient_id] = root_key
    if not out:
        raise ValueError("encrypted SSS recipient keys fixture is empty")
    return out


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
    ciphertext = AESGCM(key).encrypt(nonce, share_bytes, _canonical_json_bytes(aad))
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


def _local_fixture_delivery_receipt(envelope: Mapping[str, Any]) -> dict[str, Any]:
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


def _canonical_json_bytes(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode(
        "utf-8"
    )


def _b64(value: bytes) -> str:
    return base64.b64encode(value).decode("ascii")


def _sha256_hex(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()
