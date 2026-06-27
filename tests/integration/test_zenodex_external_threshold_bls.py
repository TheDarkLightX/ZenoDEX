from __future__ import annotations

import pytest

import src.integration.zenodex_external_threshold_bls as threshold_bls


ROOT_A = "0x" + "aa" * 32
ROOT_B = "0x" + "bb" * 32
ROOT_C = "0x" + "cc" * 32
PUBKEY_A = "0x" + "11" * 48
PUBKEY_B = "0x" + "22" * 48
SIGNATURE_A = "0x" + "33" * 96


def _threshold_evidence() -> dict[str, object]:
    return threshold_bls.build_external_threshold_bls_evidence_v0(
        provider_stack="ssv-dkg-drand-threshold-bls12-381-v1",
        service_id="wallet-threshold-service",
        service_version="1.0.0",
        binary_sha256=ROOT_A,
        public_key=PUBKEY_A,
        threshold=2,
        participants=[
            {
                "participant_id": "alice",
                "public_share_key": PUBKEY_A,
                "operator_key_hash": ROOT_B,
            },
            {
                "participant_id": "bob",
                "public_share_key": PUBKEY_B,
                "operator_key_hash": ROOT_C,
            },
        ],
        dkg_transcript_hash=ROOT_B,
        audit_evidence=[
            {
                "name": "threshold-bls-audit",
                "report_uri": "https://example.com/threshold-bls-audit.pdf",
                "report_hash": ROOT_C,
                "scope": "ssv-dkg-drand-threshold-bls12-381-v1 external threshold BLS stack",
            }
        ],
    )


def test_external_threshold_bls_verify_fails_closed_when_g2basic_binding_is_missing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    evidence = _threshold_evidence()
    payload = {"domain": "zenodex.governance.action.v0", "nonce": 1}
    receipt = threshold_bls.build_external_threshold_bls_signature_receipt_v0(
        evidence=evidence,
        payload=payload,
        participant_ids=("alice", "bob"),
        partial_signature_hashes=(ROOT_A, ROOT_B),
        signature=SIGNATURE_A,
    )
    monkeypatch.setattr(threshold_bls, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(threshold_bls, "G2Basic", None)

    ok, error = threshold_bls.verify_external_threshold_bls_signature_receipt_v0(
        receipt,
        evidence=evidence,
        payload=payload,
    )

    assert ok is False
    assert error == (
        "external threshold BLS receipt invalid: "
        "py_ecc.bls is required to verify external threshold BLS receipts"
    )
