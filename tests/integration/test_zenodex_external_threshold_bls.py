from __future__ import annotations

import pytest

from src.integration import zenodex_external_threshold_bls as threshold_bls
from src.integration.zenodex_external_threshold_bls import (
    build_external_threshold_bls_evidence_v0,
    build_external_threshold_bls_signature_receipt_v0,
    verify_external_threshold_bls_signature_receipt_v0,
)

PUBKEY_A = "0x" + "11" * 48
PUBKEY_B = "0x" + "22" * 48
ROOT_A = "0x" + "aa" * 32
ROOT_B = "0x" + "bb" * 32
ROOT_C = "0x" + "cc" * 32


def _evidence() -> dict[str, object]:
    return build_external_threshold_bls_evidence_v0(
        provider_stack="ssv-dkg-drand-threshold-bls12-381-v1",
        service_id="wallet-threshold-service",
        service_version="1.0.0",
        binary_sha256=ROOT_A,
        public_key=PUBKEY_A,
        threshold=2,
        participants=[
            {"participant_id": "alice", "public_share_key": PUBKEY_A, "operator_key_hash": ROOT_B},
            {"participant_id": "bob", "public_share_key": PUBKEY_B, "operator_key_hash": ROOT_C},
        ],
        dkg_transcript_hash=ROOT_B,
        audit_evidence=[
            {
                "name": "threshold-bls-audit",
                "report_uri": "https://example.invalid/threshold-bls-audit",
                "report_hash": ROOT_C,
                "scope": "ssv-dkg-drand-threshold-bls12-381-v1 external threshold BLS signer",
            }
        ],
    )


def test_external_threshold_receipt_rejects_lost_bls_dependency_without_assert(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    evidence = _evidence()
    payload = {"checkpoint_hash": ROOT_A}
    receipt = build_external_threshold_bls_signature_receipt_v0(
        evidence=evidence,
        payload=payload,
        participant_ids=("alice", "bob"),
        partial_signature_hashes=(ROOT_A, ROOT_B),
        signature="0x" + "11" * 96,
    )
    monkeypatch.setattr(threshold_bls, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(threshold_bls, "G2Basic", None)

    ok, reason = verify_external_threshold_bls_signature_receipt_v0(receipt, evidence=evidence, payload=payload)

    assert ok is False
    assert reason == (
        "external threshold BLS receipt invalid: "
        "py_ecc.bls is required to verify external threshold BLS receipts"
    )
