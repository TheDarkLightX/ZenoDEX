from __future__ import annotations

from src.core.confidential_extension_receipts import (
    confidential_extension_receipt_hash,
    make_confidential_extension_receipt,
    verify_confidential_extension_receipt,
)


APPROVED = {"nitro:pcr0:abc123"}


def _valid_receipt() -> dict:
    return make_confidential_extension_receipt(
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-1",
        policy_version="tee-policy-v1",
        measurement="nitro:pcr0:abc123",
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


def test_confidential_extension_receipt_roundtrip_is_deterministic() -> None:
    r1 = _valid_receipt()
    r2 = _valid_receipt()
    ok, err = verify_confidential_extension_receipt(r1, approved_measurements=APPROVED)
    assert ok, err
    assert r1 == r2


def test_confidential_extension_receipt_rejects_unapproved_measurement() -> None:
    receipt = _valid_receipt()
    receipt["body"]["measurement"] = "nitro:pcr0:zzz"
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "measurement_not_approved"


def test_confidential_extension_receipt_rejects_stale_attestation_bva() -> None:
    receipt = _valid_receipt()
    receipt["body"]["attestation"]["current_epoch"] = 11
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "stale_attestation"


def test_confidential_extension_receipt_hash_mismatch_rejected() -> None:
    receipt = _valid_receipt()
    receipt["body"]["host"]["nonce_unused"] = 0
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "hash_mismatch"


def test_confidential_extension_receipt_accounting_mismatch_rejected() -> None:
    receipt = _valid_receipt()
    receipt["body"]["accounting"]["receipt_fee"] = 6
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "accounting_guard_failed"


def test_confidential_extension_receipt_no_execute_path_preserves_balances() -> None:
    receipt = make_confidential_extension_receipt(
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-2",
        policy_version="tee-policy-v1",
        measurement="nitro:pcr0:abc123",
        do_execute=0,
        policy_ok=0,
        nonce_unused=0,
        output_bound_ok=0,
        current_epoch=10,
        attestation_epoch=10,
        max_attestation_age=2,
        fee_charged=0,
        receipt_fee=0,
        credit_before=40,
        credit_after=40,
        provider_balance_before=9,
        provider_balance_after=9,
    )
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert ok, err
