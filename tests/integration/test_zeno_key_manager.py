from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.integration import zeno_key_manager
from src.integration.zeno_key_manager import (
    KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
    KEY_ENVIRONMENT_TEE_ATTESTED,
    KEY_ORIGIN_TAU_NET_IMPORT,
    KEY_STATUS_ACTIVE,
    KEY_STATUS_REVOKED,
    KEY_STATUS_ROTATED,
    KeyEnvironmentPolicy,
    KeyExecutionEnvironment,
    KeyRef,
    KeyUsePolicy,
    LocalInMemoryBlsSigner,
    RecoveryGuardian,
    SignRequestContext,
    SocialRecoveryPolicy,
    TauNetKeyImportEvidence,
    ZenoKeyManager,
    generate_tau_testnet_compatible_private_key_hex,
    import_tau_net_key_ref,
    import_tau_net_key_ref_with_evidence,
    validate_tau_bls_public_key,
)

PUBKEY_A = "0x" + "11" * 48
PUBKEY_B = "0x" + "22" * 48
PUBKEY_C = "0x" + "33" * 48
ROOT_A = "0x" + "aa" * 32
ROOT_B = "0x" + "bb" * 32
ROOT_C = "0x" + "cc" * 32


def test_key_ref_public_json_roundtrips_without_private_key_material() -> None:
    ref = KeyRef(
        key_id="local-release-1",
        public_key=PUBKEY_A,
        metadata={"label": "release key"},
    )

    payload = ref.public_dict()
    encoded = json.dumps(payload, sort_keys=True)

    assert "private_key" not in encoded
    assert "secret_hex" not in encoded
    assert KeyRef.from_public_dict(payload) == ref


def test_key_ref_rejects_secret_fields_in_metadata_and_payload_shape() -> None:
    with pytest.raises(ValueError, match="private key material"):
        KeyRef(key_id="bad", public_key=PUBKEY_A, metadata={"nested": {"private_key_hex": "0x" + "01" * 32}})

    payload = KeyRef(key_id="ok", public_key=PUBKEY_A).public_dict()
    payload["private_key_hex"] = "0x" + "01" * 32
    with pytest.raises(ValueError, match="unsupported fields"):
        KeyRef.from_public_dict(payload)


def test_tau_net_import_validates_public_key_metadata_only() -> None:
    imported = import_tau_net_key_ref(
        key_id="tau-import-1",
        tau_public_key=PUBKEY_B[2:],
        tau_account_id="tau-account-7",
    )

    assert imported.origin == KEY_ORIGIN_TAU_NET_IMPORT
    assert imported.public_key == PUBKEY_B
    assert imported.metadata == {"tau_account_id": "tau-account-7", "import_mode": "public_key_only"}

    with pytest.raises(ValueError, match="all-zero public key"):
        validate_tau_bls_public_key("0x" + "00" * 48)


def test_tau_net_import_with_challenge_bound_evidence() -> None:
    evidence = TauNetKeyImportEvidence(
        key_id="tau-import-2",
        tau_public_key=PUBKEY_B,
        tau_chain_id="tau-testnet-1",
        tau_account_id="agrs-account-1",
        challenge_hash=ROOT_A,
        challenge_signature_hash=ROOT_B,
        policy_hash=ROOT_C,
        verified_at_epoch=10,
        expires_at_epoch=20,
    )

    imported = import_tau_net_key_ref_with_evidence(
        evidence=evidence,
        current_epoch=12,
        metadata={"label": "AGRS testnet key"},
    )
    encoded = json.dumps(imported.public_dict(), sort_keys=True)

    assert imported.origin == KEY_ORIGIN_TAU_NET_IMPORT
    assert imported.metadata["import_mode"] == "challenge_bound_public_key"
    assert imported.metadata["tau_chain_id"] == "tau-testnet-1"
    assert imported.metadata["tau_account_id"] == "agrs-account-1"
    assert imported.metadata["policy_hash"] == ROOT_C
    assert "tau_import_evidence_hash" in imported.metadata
    assert "private_key" not in encoded

    bad_evidence = TauNetKeyImportEvidence(
        key_id="tau-import-3",
        tau_public_key=PUBKEY_B,
        tau_chain_id="tau-testnet-1",
        challenge_hash=ROOT_A,
        challenge_signature_hash=ROOT_B,
        policy_hash=ROOT_C,
        verified_at_epoch=10,
        expires_at_epoch=20,
        challenge_signature_ok=False,
    )

    with pytest.raises(PermissionError, match="tau_import_challenge_signature_not_verified"):
        import_tau_net_key_ref_with_evidence(evidence=bad_evidence, current_epoch=12)

    with pytest.raises(PermissionError, match="tau_import_evidence_expired"):
        import_tau_net_key_ref_with_evidence(evidence=evidence, current_epoch=21)


def test_policy_evaluation_is_explicit_and_fail_closed_for_status_scope_and_window() -> None:
    ref = KeyRef(key_id="k1", public_key=PUBKEY_A, status=KEY_STATUS_REVOKED)
    policy = KeyUsePolicy(
        allowed_payload_kinds=("checkpoint",),
        allowed_chain_ids=("zeno-ledger-prod",),
        allowed_purposes=("sign",),
        valid_from_epoch=10,
        valid_until_epoch=20,
    )
    context = SignRequestContext(
        payload_kind="tau_export_packet",
        chain_id="zeno-ledger-dev",
        purpose="recover",
        current_epoch=25,
    )

    decision = policy.evaluate(key_ref=ref, context=context)

    assert decision.ok is False
    assert decision.errors == (
        "key_revoked",
        "payload_kind_not_allowed",
        "chain_id_not_allowed",
        "purpose_not_allowed",
        "policy_expired",
    )


def test_key_manager_rotation_and_revocation_update_public_refs() -> None:
    manager = ZenoKeyManager(key_refs=[KeyRef(key_id="old", public_key=PUBKEY_A)])
    old, new = manager.rotate_key(
        old_key_id="old",
        new_key_ref=KeyRef(key_id="new", public_key=PUBKEY_B, replaces_key_id="old", version=2),
    )

    assert old.status == KEY_STATUS_ROTATED
    assert new.status == KEY_STATUS_ACTIVE
    assert manager.key_ref("old").status == KEY_STATUS_ROTATED
    assert manager.key_ref("new").replaces_key_id == "old"

    revoked = manager.revoke_key("new")
    assert revoked.status == KEY_STATUS_REVOKED
    assert manager.public_dict()["schema"] == zeno_key_manager.KEY_MANAGER_SCHEMA_V0


def test_rotated_key_is_not_sign_usable_by_default() -> None:
    ref = KeyRef(key_id="old", public_key=PUBKEY_A, status=KEY_STATUS_ROTATED)
    policy = KeyUsePolicy(
        allowed_payload_kinds=("checkpoint",),
        allowed_chain_ids=("zeno-ledger-prod",),
    )
    context = SignRequestContext(
        payload_kind="checkpoint",
        chain_id="zeno-ledger-prod",
        purpose="sign",
        current_epoch=1,
    )

    decision = policy.evaluate(key_ref=ref, context=context)

    assert decision.ok is False
    assert decision.errors == ("key_rotated",)


def test_phone_environment_requires_user_presence_and_rollback_protection() -> None:
    environment = KeyExecutionEnvironment(
        environment_id="iphone-secure-enclave-1",
        environment_kind=KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
        chain_id="zeno-ledger-prod",
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    )
    policy = KeyEnvironmentPolicy(
        allowed_environment_kinds=(KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,),
        expected_chain_id="zeno-ledger-prod",
        expected_policy_hash=ROOT_A,
        expected_challenge_hash=ROOT_B,
    )

    assert policy.evaluate(environment=environment, current_epoch=12).ok is True
    assert "environment_hash" in environment.public_dict()

    missing_presence = KeyExecutionEnvironment(
        environment_id="iphone-secure-enclave-1",
        environment_kind=KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
        chain_id="zeno-ledger-prod",
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        local_user_presence_confirmed=False,
        rollback_protection_confirmed=True,
    )
    decision = policy.evaluate(environment=missing_presence, current_epoch=12)

    assert decision.ok is False
    assert decision.errors == ("local_user_presence_missing",)


def test_tee_environment_requires_attestation_measurement_and_freshness() -> None:
    environment = KeyExecutionEnvironment(
        environment_id="tee-key-use-1",
        environment_kind=KEY_ENVIRONMENT_TEE_ATTESTED,
        chain_id="zeno-ledger-prod",
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        attestation_hash=ROOT_C,
        tee_measurement_hash=ROOT_B,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    )
    policy = KeyEnvironmentPolicy(
        allowed_environment_kinds=(KEY_ENVIRONMENT_TEE_ATTESTED,),
        expected_chain_id="zeno-ledger-prod",
        expected_policy_hash=ROOT_A,
        expected_challenge_hash=ROOT_B,
        require_attestation=True,
        require_tee_measurement=True,
    )

    assert policy.evaluate(environment=environment, current_epoch=15).ok is True

    expired = policy.evaluate(environment=environment, current_epoch=21)
    assert expired.ok is False
    assert expired.errors == ("environment_expired",)

    missing_measurement = KeyExecutionEnvironment(
        environment_id="tee-key-use-2",
        environment_kind=KEY_ENVIRONMENT_TEE_ATTESTED,
        chain_id="zeno-ledger-prod",
        policy_hash=ROOT_A,
        challenge_hash=ROOT_B,
        issued_at_epoch=10,
        expires_at_epoch=20,
        attestation_hash=ROOT_C,
        local_user_presence_confirmed=True,
        rollback_protection_confirmed=True,
    )
    decision = policy.evaluate(environment=missing_measurement, current_epoch=15)

    assert decision.ok is False
    assert decision.errors == ("tee_measurement_missing",)


def test_social_recovery_policy_evaluates_threshold_and_delay_without_crypto_claims() -> None:
    policy = SocialRecoveryPolicy(
        policy_id="recover-local-1",
        subject_key_id="subject",
        threshold=2,
        delay_epochs=3,
        guardians=(
            RecoveryGuardian(guardian_id="g1", public_key=PUBKEY_A, weight=1),
            RecoveryGuardian(guardian_id="g2", public_key=PUBKEY_B, weight=1),
            RecoveryGuardian(guardian_id="g3", public_key=PUBKEY_C, weight=1, status=KEY_STATUS_REVOKED),
        ),
    )

    early = policy.evaluate(approvals=("g1", "g2"), requested_at_epoch=10, current_epoch=12)
    ready = policy.evaluate(approvals=("g1", "g2", "g3"), requested_at_epoch=10, current_epoch=13)

    assert early["threshold_ok"] is True
    assert early["delay_ok"] is False
    assert early["ok"] is False
    assert ready["ok"] is True
    assert ready["accepted_weight"] == 2
    assert ready["rejected_approvals"] == ["g3"]


def test_module_has_no_network_client_imports() -> None:
    source = Path(zeno_key_manager.__file__).read_text(encoding="utf-8")

    assert "import socket" not in source
    assert "requests" not in source
    assert "urllib" not in source
    assert "http.client" not in source


def test_local_signer_rejects_inconsistent_bls_dependency_state(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(zeno_key_manager, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(zeno_key_manager, "G2Basic", None)

    with pytest.raises(RuntimeError, match="py_ecc\\.bls is required for local BLS signing"):
        LocalInMemoryBlsSigner.from_private_key_hex(
            key_id="local-bls-1",
            private_key_hex="0x" + ("00" * 31) + "01",
        )


def test_local_key_generation_rejects_inconsistent_bls_dependency_state(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(zeno_key_manager, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(zeno_key_manager, "G2Basic", None)

    with pytest.raises(RuntimeError, match="py_ecc\\.bls is required for local BLS signing"):
        generate_tau_testnet_compatible_private_key_hex()


def test_local_signing_rejects_lost_bls_dependency_without_assert(monkeypatch: pytest.MonkeyPatch) -> None:
    signer = object.__new__(LocalInMemoryBlsSigner)
    signer.key_ref = KeyRef(key_id="local-bls-1", public_key=PUBKEY_A)
    signer._sk = 1
    policy = KeyUsePolicy(
        allowed_payload_kinds=("checkpoint",),
        allowed_chain_ids=("zeno-ledger-prod",),
    )
    context = SignRequestContext(
        payload_kind="checkpoint",
        chain_id="zeno-ledger-prod",
        purpose="sign",
        current_epoch=2,
    )
    monkeypatch.setattr(zeno_key_manager, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(zeno_key_manager, "G2Basic", None)

    with pytest.raises(RuntimeError, match="py_ecc\\.bls is required for local BLS signing"):
        signer.sign({"checkpoint_hash": ROOT_A}, policy=policy, context=context)


@pytest.mark.skipif(not zeno_key_manager._BLS_AVAILABLE, reason="py_ecc not installed")
def test_local_in_memory_signer_requires_policy_approval_and_keeps_secret_out_of_record() -> None:
    private_key_hex = "0x" + ("00" * 31) + "01"
    signer = LocalInMemoryBlsSigner.from_private_key_hex(
        key_id="local-bls-1",
        private_key_hex=private_key_hex,
        metadata={"label": "local"},
    )
    policy = KeyUsePolicy(
        allowed_payload_kinds=("checkpoint",),
        allowed_chain_ids=("zeno-ledger-prod",),
        valid_until_epoch=10,
    )
    context = SignRequestContext(
        payload_kind="checkpoint",
        chain_id="zeno-ledger-prod",
        purpose="sign",
        current_epoch=2,
    )

    record = signer.sign({"checkpoint_hash": "0x" + "44" * 32}, policy=policy, context=context)
    encoded = json.dumps(record, sort_keys=True)

    assert record["signature"].startswith("0x")
    assert private_key_hex not in encoded
    assert "private_key" not in encoded

    denied = SignRequestContext(
        payload_kind="checkpoint",
        chain_id="zeno-ledger-prod",
        purpose="sign",
        current_epoch=11,
    )
    with pytest.raises(PermissionError, match="policy_expired"):
        signer.sign({"checkpoint_hash": "0x" + "44" * 32}, policy=policy, context=denied)
