from __future__ import annotations

import pytest

import src.integration.zeno_ledger_signature as sig
import src.integration.zenodex_external_threshold_bls as ext_bls
from src.integration.zenodex_external_threshold_bls import (
    build_external_threshold_bls_evidence_v0,
    build_external_threshold_bls_signature_receipt_v0,
    verify_external_threshold_bls_signature_receipt_v0,
)

pytestmark = pytest.mark.skipif(not sig._BLS_AVAILABLE, reason="py_ecc BLS dependency unavailable")

ROOT_A = "0x" + "aa" * 32
ROOT_B = "0x" + "bb" * 32
ROOT_C = "0x" + "cc" * 32
SK1 = "0x" + ("01" * 32)


def _evidence() -> dict[str, object]:
    public_key = sig.bls_public_key_hex_from_private_key_v0(SK1)
    return build_external_threshold_bls_evidence_v0(
        provider_stack="ssv-dkg-drand-threshold-bls12-381-v1",
        service_id="wallet-threshold-service",
        service_version="1.0.0",
        binary_sha256=ROOT_A,
        public_key=public_key,
        threshold=1,
        participants=[
            {
                "participant_id": "alice",
                "public_share_key": public_key,
                "operator_key_hash": ROOT_B,
            },
        ],
        dkg_transcript_hash=ROOT_B,
        audit_evidence=[
            {
                "name": "ssv-dkg-drand-kudelski-and-chainsecurity-references",
                "report_uri": "https://docs.drand.love/blog/2023/05/26/tlock-security-assessment/",
                "report_hash": ROOT_C,
                "scope": "ssv-dkg-drand-threshold-bls12-381-v1 external threshold BLS stack",
            }
        ],
    )


def test_external_threshold_bls_verifier_dependency_guard_is_explicit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    evidence = _evidence()
    payload = {"kind": "governance_action", "payload_hash": ROOT_A}
    receipt = build_external_threshold_bls_signature_receipt_v0(
        evidence=evidence,
        payload=payload,
        participant_ids=["alice"],
        partial_signature_hashes=[ROOT_B],
        signature="0x" + "00" * 96,
    )

    monkeypatch.setattr(ext_bls, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(ext_bls, "G2Basic", None)

    ok, err = verify_external_threshold_bls_signature_receipt_v0(
        receipt,
        evidence=evidence,
        payload=payload,
    )

    assert ok is False
    assert err == "external threshold BLS receipt invalid: py_ecc.bls is required to verify external threshold BLS receipts"
