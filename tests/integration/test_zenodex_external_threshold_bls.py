from __future__ import annotations

import pytest

from src.integration import zenodex_external_threshold_bls as threshold_bls


def test_external_threshold_bls_rejects_inconsistent_bls_dependency(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(threshold_bls, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(threshold_bls, "G2Basic", None)

    ok, err = threshold_bls.verify_external_threshold_bls_signature_receipt_v0(
        {},
        evidence={},
        payload={},
    )

    assert ok is False
    assert (
        err
        == "external threshold BLS receipt invalid: py_ecc.bls is required to verify external threshold BLS receipts"
    )


def test_external_threshold_bls_rejects_malformed_evidence_without_broad_exception(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class RejectingBls:
        @staticmethod
        def Verify(*_args: object, **_kwargs: object) -> bool:
            return False

    monkeypatch.setattr(threshold_bls, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(threshold_bls, "G2Basic", RejectingBls)

    ok, err = threshold_bls.verify_external_threshold_bls_signature_receipt_v0(
        {},
        evidence={},
        payload={},
    )

    assert ok is False
    assert (
        err
        == "external threshold BLS receipt invalid: external threshold BLS evidence contains unsupported fields"
    )
