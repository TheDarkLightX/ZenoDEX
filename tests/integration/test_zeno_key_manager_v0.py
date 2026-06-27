from __future__ import annotations

import json

import pytest

import src.integration.zeno_key_manager as key_manager_mod
from src.integration.zeno_key_import_v0 import (
    build_tau_import_challenge_v0,
    import_tau_bls_key_descriptor_v0,
    key_ref_from_tau_import_receipt_v0,
)
from src.integration.zeno_key_manager import (
    KEY_STATUS_REVOKED,
    KeyRef,
    KeyUsePolicy,
    RecoveryGuardian,
    SignRequestContext,
    SocialRecoveryPolicy,
    TauNetKeyImportEvidence,
)
from src.integration.zeno_key_manager_v0 import (
    BACKEND_TAU_BLS_IMPORT,
    KeyBackendDescriptor,
    SignAdmissionRequest,
    evaluate_sign_admission_v0,
)
from src.integration.zeno_key_recovery_v0 import evaluate_recovery_rotation_v0
from tools import zeno_key_manager as zeno_key_manager_cli


PUBKEY_A = "0x" + "11" * 48
PUBKEY_B = "0x" + "22" * 48
ROOT_A = "0x" + "aa" * 32
ROOT_B = "0x" + "bb" * 32
ROOT_C = "0x" + "cc" * 32


def _sign_request(payload: dict[str, object], *, seen_nonces: tuple[int, ...] = ()) -> SignAdmissionRequest:
    key_ref = KeyRef(key_id="tau-user-main", public_key=PUBKEY_A)
    backend = KeyBackendDescriptor(
        key_id=key_ref.key_id,
        backend_kind=BACKEND_TAU_BLS_IMPORT,
        backend_id="tau-wallet-local",
        policy_hash=ROOT_A,
    )
    policy = KeyUsePolicy(
        allowed_payload_kinds=("checkpoint",),
        allowed_chain_ids=("tau-testnet-1",),
    )
    context = SignRequestContext(
        payload_kind="checkpoint",
        chain_id="tau-testnet-1",
        purpose="sign",
        current_epoch=5,
    )
    return SignAdmissionRequest(
        key_ref=key_ref,
        backend=backend,
        policy=policy,
        context=context,
        payload=payload,
        seen_nonces=seen_nonces,
    )


def test_sign_admission_accepts_domain_chain_nonce_bound_payload() -> None:
    receipt = evaluate_sign_admission_v0(
        _sign_request({"domain": "zenodex.ledger.checkpoint.v0", "chain_id": "tau-testnet-1", "nonce": 7})
    )

    assert receipt["ok"] is True
    assert receipt["receipt_hash"].startswith("0x")


def test_sign_admission_rejects_secret_fields_and_reused_nonce() -> None:
    receipt = evaluate_sign_admission_v0(
        _sign_request(
            {"domain": "zenodex.ledger.checkpoint.v0", "chain_id": "tau-testnet-1", "nonce": 7},
            seen_nonces=(7,),
        )
    )

    assert receipt["ok"] is False
    assert "payload_nonce_reused" in receipt["errors"]

    try:
        _sign_request({"domain": "x", "chain_id": "tau-testnet-1", "nonce": 8, "private_key": "bad"})
    except ValueError as exc:
        assert "private key material" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("secret field was accepted")


def test_tau_import_receipt_imports_public_descriptor_without_private_key() -> None:
    challenge = build_tau_import_challenge_v0(
        key_id="tau-user-main",
        tau_chain_id="tau-testnet-1",
        policy_hash=ROOT_A,
        nonce="n1",
    )
    evidence = TauNetKeyImportEvidence(
        key_id="tau-user-main",
        tau_public_key=PUBKEY_A,
        tau_chain_id="tau-testnet-1",
        tau_account_id="agrs-1",
        challenge_hash=challenge["challenge_hash"],
        challenge_signature_hash=ROOT_B,
        policy_hash=ROOT_A,
        verified_at_epoch=1,
        expires_at_epoch=10,
    )

    receipt = import_tau_bls_key_descriptor_v0(evidence=evidence, current_epoch=5, metadata={"label": "AGRS"})
    encoded = json.dumps(receipt, sort_keys=True)
    key_ref = key_ref_from_tau_import_receipt_v0(receipt)

    assert receipt["raw_private_key_imported"] is False
    assert key_ref.public_key == PUBKEY_A
    assert "private_key_hex" not in encoded
    assert "secret_hex" not in encoded


def test_recovery_rotation_receipt_requires_threshold_delay_and_key_binding() -> None:
    policy = SocialRecoveryPolicy(
        policy_id="recover-main",
        subject_key_id="old",
        threshold=2,
        delay_epochs=3,
        guardians=(
            RecoveryGuardian(guardian_id="g1", public_key=PUBKEY_A),
            RecoveryGuardian(guardian_id="g2", public_key=PUBKEY_B),
        ),
    )
    new_key = KeyRef(key_id="new", public_key=PUBKEY_B, replaces_key_id="old")

    early = evaluate_recovery_rotation_v0(
        policy=policy,
        approvals=("g1", "g2"),
        requested_at_epoch=10,
        current_epoch=12,
        new_key_ref=new_key,
        recovery_nonce="r1",
    )
    ready = evaluate_recovery_rotation_v0(
        policy=policy,
        approvals=("g1", "g2"),
        requested_at_epoch=10,
        current_epoch=13,
        new_key_ref=new_key,
        recovery_nonce="r1",
    )
    revoked_new = evaluate_recovery_rotation_v0(
        policy=policy,
        approvals=("g1", "g2"),
        requested_at_epoch=10,
        current_epoch=13,
        new_key_ref=KeyRef(key_id="new", public_key=PUBKEY_B, status=KEY_STATUS_REVOKED, replaces_key_id="old"),
        recovery_nonce="r1",
    )

    assert early["ok"] is False
    assert "recovery_policy_not_satisfied" in early["errors"]
    assert ready["ok"] is True
    assert revoked_new["ok"] is False
    assert "new_key_not_active" in revoked_new["errors"]


def test_zeno_key_manager_cli_tau_challenge(capsys) -> None:
    rc = zeno_key_manager_cli.main(
        [
            "tau-challenge",
            "--key-ref",
            "tau-user-main",
            "--tau-chain-id",
            "tau-testnet-1",
            "--policy-hash",
            ROOT_A,
            "--nonce",
            "n1",
        ]
    )

    assert rc == 0
    packet = json.loads(capsys.readouterr().out)
    assert packet["schema"] == "zenodex/zeno_key_manager/tau_import_challenge/v0"
    assert packet["challenge_hash"].startswith("0x")


def test_local_bls_keygen_fails_closed_when_g2basic_binding_is_missing(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(key_manager_mod, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(key_manager_mod, "G2Basic", None)

    with pytest.raises(RuntimeError, match="py_ecc\\.bls is required for local BLS signing"):
        key_manager_mod.generate_tau_testnet_compatible_private_key_hex()
