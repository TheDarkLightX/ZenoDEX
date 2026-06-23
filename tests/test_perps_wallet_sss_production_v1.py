"""Tests for production SSS custodian ceremony and key rotation.

Verifies that the production hardening layer correctly:
- Registers custodians with BLS keys and distinct organizations
- Collects and verifies custodian attestations on backup hashes
- Builds production ceremonies with quorum enforcement
- Rejects ceremonies with insufficient quorum or duplicate custodians
- Performs key rotation with quorum-signed invalidation
- Elevates production_security_claim only when all gates pass
"""

from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.perps_wallet_encrypted_sss_backup import (
    SssBackupRecipient,
    build_perps_wallet_encrypted_sss_backup_v1,
    evaluate_perps_wallet_encrypted_sss_backup_v1,
    perps_wallet_encrypted_sss_backup_hash_v1,
)
from src.integration.perps_wallet_sss_production_v1 import (
    Custodian,
    build_custodian_registry_v1,
    build_key_rotation_ceremony_v1,
    build_production_ceremony_v1,
    collect_custodian_attestation_v1,
    evaluate_key_rotation_ceremony_v1,
    evaluate_production_ceremony_v1,
    validate_custodian_registry_v1,
    verify_custodian_attestation_v1,
)
from src.integration.zeno_ledger_signature import bls_public_key_hex_from_private_key_v0


def _make_recipients() -> list[SssBackupRecipient]:
    return [
        SssBackupRecipient(
            recipient_id=f"recipient-{i}",
            provider_kind=kind,
            provider_id=f"provider-{i}",
            transport_kind="email" if kind == "recovery_email" else "api",
            destination_hash=f"0x{'ab' * 32}",
            recipient_root_key=bytes(32 + i for _ in range(32)),
        )
        for i, kind in enumerate(["recovery_email", "cloud_drive", "offline_export"])
    ]


def _make_custodians() -> tuple[list[Custodian], list[str]]:
    privkeys = ["0x" + bytes([0x09 * (i + 1)] * 32).hex() for i in range(4)]
    pubkeys = [bls_public_key_hex_from_private_key_v0(pk) for pk in privkeys]
    custodians = [
        Custodian(
            custodian_id=f"custodian-{i}",
            bls_public_key_hex=pubkeys[i],
            role="treasury" if i == 0 else "verifier",
            organization=f"org-{i}",
        )
        for i in range(4)
    ]
    return custodians, privkeys


def _build_test_backup(production_mode: bool = False) -> dict:
    return build_perps_wallet_encrypted_sss_backup_v1(
        authority_id="authority-test-v1",
        chain_id="zeno-ledger-localtest-v0",
        wallet_authority_hash=f"0x{'cd' * 32}",
        subject_key_id="subject-key-a",
        secret_material=bytes(range(32)),
        recipients=_make_recipients(),
        threshold=3,
        created_at_epoch=100,
        drill_epoch=101,
        production_mode=production_mode,
    )


def test_custodian_registry_requires_minimum_three_custodians() -> None:
    with pytest.raises(ValueError, match="at least 3 custodians"):
        build_custodian_registry_v1(
            authority_id="a",
            chain_id="c",
            custodians=[Custodian("c1", "0x" + "ab" * 48, "r", "o1")],
            threshold=1,
            created_at_epoch=1,
        )


def test_custodian_registry_requires_distinct_organizations() -> None:
    custodians, _ = _make_custodians()
    same_org = [
        Custodian(c.custodian_id, c.bls_public_key_hex, c.role, "same-org")
        for c in custodians[:4]
    ]
    with pytest.raises(ValueError, match="distinct organizations"):
        build_custodian_registry_v1(
            authority_id="a",
            chain_id="c",
            custodians=same_org,
            threshold=3,
            created_at_epoch=1,
        )


def test_custodian_registry_rejects_threshold_below_three() -> None:
    custodians, _ = _make_custodians()
    with pytest.raises(ValueError, match="threshold must be at least 3"):
        build_custodian_registry_v1(
            authority_id="a",
            chain_id="c",
            custodians=custodians,
            threshold=2,
            created_at_epoch=1,
        )


def test_custodian_registry_validation_rejects_threshold_below_three() -> None:
    custodians, _ = _make_custodians()
    registry = build_custodian_registry_v1(
        authority_id="auth-1",
        chain_id="chain-1",
        custodians=custodians,
        threshold=3,
        created_at_epoch=100,
    )
    malformed = {**registry, "threshold": 2}

    result = validate_custodian_registry_v1(malformed, expected_authority_id="auth-1")

    assert result["ok"] is False
    assert "custodian registry threshold must be >= 3" in result["errors"]


def test_custodian_registry_rejects_duplicate_keys() -> None:
    custodians, _ = _make_custodians()
    dup_key = [
        Custodian(c.custodian_id, custodians[0].bls_public_key_hex, c.role, c.organization)
        for c in custodians
    ]
    with pytest.raises(ValueError, match="BLS public keys must be unique"):
        build_custodian_registry_v1(
            authority_id="a",
            chain_id="c",
            custodians=dup_key,
            threshold=3,
            created_at_epoch=1,
        )


def test_custodian_registry_builds_and_validates_successfully() -> None:
    custodians, _ = _make_custodians()
    registry = build_custodian_registry_v1(
        authority_id="auth-1",
        chain_id="chain-1",
        custodians=custodians,
        threshold=3,
        created_at_epoch=100,
    )
    assert registry["schema"] == "zenodex/perps-wallet-sss-custodian-registry/v1"
    assert registry["threshold"] == 3
    assert registry["custodian_count"] == 4
    assert registry["production_security_claim"] is True
    result = validate_custodian_registry_v1(registry, expected_authority_id="auth-1")
    assert result["ok"], result["errors"]


def test_custodian_attestation_verifies_against_correct_public_key() -> None:
    custodians, privkeys = _make_custodians()
    backup = _build_test_backup()
    attestation = collect_custodian_attestation_v1(
        custodian_id="custodian-0",
        private_key_hex=privkeys[0],
        public_key_hex=custodians[0].bls_public_key_hex,
        backup_hash=backup["backup_hash"],
        authority_id="auth-1",
        chain_id="chain-1",
    )
    result = verify_custodian_attestation_v1(
        attestation,
        expected_backup_hash=backup["backup_hash"],
        expected_public_key=custodians[0].bls_public_key_hex,
    )
    assert result["ok"], result["errors"]


def test_custodian_attestation_rejects_wrong_backup_hash() -> None:
    custodians, privkeys = _make_custodians()
    attestation = collect_custodian_attestation_v1(
        custodian_id="custodian-0",
        private_key_hex=privkeys[0],
        public_key_hex=custodians[0].bls_public_key_hex,
        backup_hash="0x" + "aa" * 32,
        authority_id="auth-1",
        chain_id="chain-1",
    )
    result = verify_custodian_attestation_v1(
        attestation,
        expected_backup_hash="0x" + "bb" * 32,
        expected_public_key=custodians[0].bls_public_key_hex,
    )
    assert not result["ok"]


def test_production_ceremony_requires_quorum_attestations() -> None:
    custodians, privkeys = _make_custodians()
    registry = build_custodian_registry_v1(
        authority_id="auth-1",
        chain_id="chain-1",
        custodians=custodians,
        threshold=3,
        created_at_epoch=100,
    )
    backup = _build_test_backup(production_mode=True)
    attestations = [
        collect_custodian_attestation_v1(
            custodian_id=custodians[i].custodian_id,
            private_key_hex=privkeys[i],
            public_key_hex=custodians[i].bls_public_key_hex,
            backup_hash=backup["backup_hash"],
            authority_id="auth-1",
            chain_id="chain-1",
        )
        for i in range(2)
    ]
    with pytest.raises(ValueError, match="requires 3 attestations, got 2"):
        build_production_ceremony_v1(backup=backup, registry=registry, attestations=attestations)


def test_production_ceremony_builds_with_sufficient_quorum() -> None:
    custodians, privkeys = _make_custodians()
    registry = build_custodian_registry_v1(
        authority_id="auth-1",
        chain_id="chain-1",
        custodians=custodians,
        threshold=3,
        created_at_epoch=100,
    )
    backup = _build_test_backup(production_mode=True)
    attestations = [
        collect_custodian_attestation_v1(
            custodian_id=custodians[i].custodian_id,
            private_key_hex=privkeys[i],
            public_key_hex=custodians[i].bls_public_key_hex,
            backup_hash=backup["backup_hash"],
            authority_id="auth-1",
            chain_id="chain-1",
        )
        for i in range(3)
    ]
    ceremony = build_production_ceremony_v1(backup=backup, registry=registry, attestations=attestations)
    assert ceremony["quorum_satisfied"] is True
    assert ceremony["attestation_count"] == 3
    assert ceremony["production_security_claim"] is True
    assert ceremony["distinct_organizations"] == 3


def test_production_ceremony_rejects_duplicate_custodian_attestations() -> None:
    custodians, privkeys = _make_custodians()
    registry = build_custodian_registry_v1(
        authority_id="auth-1",
        chain_id="chain-1",
        custodians=custodians,
        threshold=3,
        created_at_epoch=100,
    )
    backup = _build_test_backup(production_mode=True)
    att = collect_custodian_attestation_v1(
        custodian_id="custodian-0",
        private_key_hex=privkeys[0],
        public_key_hex=custodians[0].bls_public_key_hex,
        backup_hash=backup["backup_hash"],
        authority_id="auth-1",
        chain_id="chain-1",
    )
    with pytest.raises(ValueError, match="duplicate attestation"):
        build_production_ceremony_v1(backup=backup, registry=registry, attestations=[att, att, att])


def test_production_ceremony_evaluation_succeeds_with_valid_attestations() -> None:
    custodians, privkeys = _make_custodians()
    registry = build_custodian_registry_v1(
        authority_id="auth-1",
        chain_id="chain-1",
        custodians=custodians,
        threshold=3,
        created_at_epoch=100,
    )
    backup = _build_test_backup(production_mode=True)
    attestations = [
        collect_custodian_attestation_v1(
            custodian_id=custodians[i].custodian_id,
            private_key_hex=privkeys[i],
            public_key_hex=custodians[i].bls_public_key_hex,
            backup_hash=backup["backup_hash"],
            authority_id="auth-1",
            chain_id="chain-1",
        )
        for i in range(3)
    ]
    ceremony = build_production_ceremony_v1(backup=backup, registry=registry, attestations=attestations)
    result = evaluate_production_ceremony_v1(ceremony, registry=registry, backup=backup)
    assert result["ok"], result["errors"]
    assert result["production_ready"] is True


def test_key_rotation_ceremony_builds_and_validates() -> None:
    custodians, privkeys = _make_custodians()
    registry = build_custodian_registry_v1(
        authority_id="auth-1",
        chain_id="chain-1",
        custodians=custodians,
        threshold=3,
        created_at_epoch=100,
    )
    old_backup = _build_test_backup(production_mode=True)
    new_backup = _build_test_backup(production_mode=True)
    rotation_payload = {
        "authority_id": "auth-1",
        "chain_id": "chain-1",
        "old_key_id": "key-old-v1",
        "new_key_id": "key-new-v1",
        "old_backup_hash": old_backup["backup_hash"],
        "new_backup_hash": new_backup["backup_hash"],
        "rotated_at_epoch": 200,
    }
    from src.integration.perps_wallet_sss_production_v1 import _rotation_hash_v1
    rotation_hash = _rotation_hash_v1(rotation_payload)
    from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0
    attestations = []
    for i in range(3):
        envelope = build_bls_signed_artifact_envelope_v0(
            payload_kind="perps_wallet_sss_key_rotation_ceremony",
            payload_hash=rotation_hash,
            signer_id=custodians[i].custodian_id,
            key_id=f"{custodians[i].custodian_id}-bls",
            private_key_hex=privkeys[i],
        )
        attestations.append({
            "attested_by": custodians[i].custodian_id,
            "signature_envelope": envelope,
        })
    ceremony = build_key_rotation_ceremony_v1(
        authority_id="auth-1",
        chain_id="chain-1",
        old_key_id="key-old-v1",
        new_key_id="key-new-v1",
        old_backup_hash=old_backup["backup_hash"],
        new_backup_hash=new_backup["backup_hash"],
        registry=registry,
        attestations=attestations,
        rotated_at_epoch=200,
    )
    assert ceremony["quorum_satisfied"] is True
    assert ceremony["old_key_invalidated"] is True
    assert ceremony["production_security_claim"] is True
    assert ceremony["distinct_organizations"] == 3
    result = evaluate_key_rotation_ceremony_v1(ceremony, registry=registry)
    assert result["ok"], result["errors"]
    assert result["rotation_ready"] is True


def test_key_rotation_ceremony_rejects_insufficient_quorum() -> None:
    custodians, privkeys = _make_custodians()
    registry = build_custodian_registry_v1(
        authority_id="auth-1",
        chain_id="chain-1",
        custodians=custodians,
        threshold=3,
        created_at_epoch=100,
    )
    old_backup = _build_test_backup(production_mode=True)
    new_backup = _build_test_backup(production_mode=True)
    rotation_payload = {
        "authority_id": "auth-1",
        "chain_id": "chain-1",
        "old_key_id": "key-old-v1",
        "new_key_id": "key-new-v1",
        "old_backup_hash": old_backup["backup_hash"],
        "new_backup_hash": new_backup["backup_hash"],
        "rotated_at_epoch": 200,
    }
    from src.integration.perps_wallet_sss_production_v1 import _rotation_hash_v1
    rotation_hash = _rotation_hash_v1(rotation_payload)
    from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0
    attestations = []
    for i in range(2):
        envelope = build_bls_signed_artifact_envelope_v0(
            payload_kind="perps_wallet_sss_key_rotation_ceremony",
            payload_hash=rotation_hash,
            signer_id=custodians[i].custodian_id,
            key_id=f"{custodians[i].custodian_id}-bls",
            private_key_hex=privkeys[i],
        )
        attestations.append({
            "attested_by": custodians[i].custodian_id,
            "signature_envelope": envelope,
        })
    with pytest.raises(ValueError, match="requires 3 attestations, got 2"):
        build_key_rotation_ceremony_v1(
            authority_id="auth-1",
            chain_id="chain-1",
            old_key_id="key-old-v1",
            new_key_id="key-new-v1",
            old_backup_hash=old_backup["backup_hash"],
            new_backup_hash=new_backup["backup_hash"],
            registry=registry,
            attestations=attestations,
            rotated_at_epoch=200,
        )


def test_backup_production_mode_does_not_self_claim_production_security() -> None:
    backup = _build_test_backup(production_mode=True)
    assert backup["production_security_claim"] is False
    assert backup["audit_status"] == "external-audit-in-progress"
    assert backup["audit_evidence"]["external_audit_ready"] is False


def test_backup_production_claim_does_not_require_custodian_ceremony() -> None:
    backup = _build_test_backup(production_mode=True)
    backup["production_security_claim"] = True

    result = evaluate_perps_wallet_encrypted_sss_backup_v1(profile=None, backup=backup)

    assert result["ok"] is False
    assert "encrypted SSS backup claims production security but external audit is not ready" in result["errors"]
    assert "encrypted SSS backup claims production security but has no production ceremony" not in result["errors"]


def test_backup_attached_invalid_custodian_ceremony_still_fails_closed() -> None:
    backup = _build_test_backup(production_mode=True)
    backup["production_security_claim"] = True
    backup["production_ceremony"] = {}

    result = evaluate_perps_wallet_encrypted_sss_backup_v1(profile=None, backup=backup)

    assert result["ok"] is False
    assert "encrypted SSS backup has invalid production ceremony evidence" in result["errors"]


def test_backup_local_mode_keeps_production_security_claim_false() -> None:
    backup = _build_test_backup(production_mode=False)
    assert backup["production_security_claim"] is False
    assert backup["audit_status"] == "local-fixture-unaudited"


def test_backup_hash_is_stable_after_attaching_production_metadata() -> None:
    custodians, privkeys = _make_custodians()
    registry = build_custodian_registry_v1(
        authority_id="auth-1",
        chain_id="chain-1",
        custodians=custodians,
        threshold=3,
        created_at_epoch=100,
    )
    backup = _build_test_backup(production_mode=True)
    attestations = [
        collect_custodian_attestation_v1(
            custodian_id=custodians[i].custodian_id,
            private_key_hex=privkeys[i],
            public_key_hex=custodians[i].bls_public_key_hex,
            backup_hash=backup["backup_hash"],
            authority_id="auth-1",
            chain_id="chain-1",
        )
        for i in range(3)
    ]
    ceremony = build_production_ceremony_v1(
        backup=backup,
        registry=registry,
        attestations=attestations,
    )
    original_hash = backup["backup_hash"]

    backup["custodian_registry"] = registry
    backup["production_ceremony"] = ceremony
    backup["production_security_claim"] = True
    backup["audit_status"] = "external-audit-completed"

    assert perps_wallet_encrypted_sss_backup_hash_v1(backup) == original_hash
