from __future__ import annotations

import pytest

import src.core.confidential_extension_receipts as receipts_mod
from src.core.confidential_extension_receipts import (
    confidential_extension_receipt_hash,
    make_confidential_extension_receipt,
    verify_confidential_extension_receipt,
)

NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
POLICY_DIGEST = "0x" + ("d" * 64)
APPROVED = {f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"}


def _valid_receipt() -> dict[str, object]:
    return make_confidential_extension_receipt(
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-1",
        policy_version="tee-policy-v1",
        policy_digest=POLICY_DIGEST,
        measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        attestation_epoch=8,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )


def _body(receipt: dict[str, object]) -> dict[str, object]:
    body = receipt["body"]
    assert isinstance(body, dict)
    return body


def test_confidential_receipt_invalid_policy_digest_stays_bad_policy_digest() -> None:
    receipt = _valid_receipt()
    body = _body(receipt)
    body["policy_digest"] = "not-a-digest"
    receipt["receipt_hash"] = confidential_extension_receipt_hash(body)

    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)

    assert ok is False
    assert err == "bad_policy_digest"


def test_confidential_receipt_policy_digest_helper_bug_propagates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    receipt = _valid_receipt()

    def broken_policy_digest(value: object) -> str:
        raise RuntimeError("policy digest helper bug")

    monkeypatch.setattr(receipts_mod, "_require_policy_digest", broken_policy_digest)
    with pytest.raises(RuntimeError, match="policy digest helper bug"):
        verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)


def test_confidential_receipt_invalid_numeric_field_stays_bad_numeric_field() -> None:
    receipt = _valid_receipt()
    body = _body(receipt)
    host = body["host"]
    assert isinstance(host, dict)
    host["do_execute"] = True
    receipt["receipt_hash"] = confidential_extension_receipt_hash(body)

    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)

    assert ok is False
    assert err == "bad_numeric_field"


def test_confidential_receipt_numeric_helper_bug_propagates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    receipt = _valid_receipt()

    def broken_int_field(mapping: dict[str, object], key: str) -> int:
        raise RuntimeError("numeric helper bug")

    monkeypatch.setattr(receipts_mod, "_require_int_field", broken_int_field)
    with pytest.raises(RuntimeError, match="numeric helper bug"):
        verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
