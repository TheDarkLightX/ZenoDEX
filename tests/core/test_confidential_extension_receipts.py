from __future__ import annotations

import pytest

import src.core.confidential_extension_receipts as receipt_module
from src.core.confidential_extension_receipts import (
    confidential_extension_receipt_hash,
    make_confidential_extension_receipt,
    verify_confidential_extension_receipt,
)

NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
POLICY_DIGEST = "0x" + ("d" * 64)
APPROVED = {f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"}


def _valid_receipt() -> dict:
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


def test_confidential_extension_receipt_roundtrip_is_deterministic() -> None:
    r1 = _valid_receipt()
    r2 = _valid_receipt()
    ok, err = verify_confidential_extension_receipt(r1, approved_measurements=APPROVED)
    assert ok, err
    assert r1 == r2


def test_confidential_extension_receipt_rejects_unapproved_measurement() -> None:
    receipt = _valid_receipt()
    receipt["body"]["measurement"] = f"nitro:pcr0:{'c' * 96}:pcr8:{'d' * 96}"
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
        policy_digest=POLICY_DIGEST,
        measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
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


def test_confidential_extension_receipt_constructor_rejects_impossible_execute_state() -> None:
    try:
        make_confidential_extension_receipt(
            extension_id="route-premium-v1",
            provider_id="provider-1",
            request_id="req-3",
            policy_version="tee-policy-v1",
            policy_digest=POLICY_DIGEST,
            measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
            do_execute=1,
            policy_ok=1,
            nonce_unused=0,
            output_bound_ok=1,
            current_epoch=10,
            attestation_epoch=10,
            max_attestation_age=2,
            fee_charged=1,
            receipt_fee=1,
            credit_before=40,
            credit_after=39,
            provider_balance_before=9,
            provider_balance_after=10,
        )
    except ValueError as exc:
        assert str(exc) == "executing receipt requires all host guards"
    else:
        raise AssertionError("expected impossible execute-state rejection")




def test_confidential_extension_receipt_rejects_out_of_range_numeric_field_fail_closed() -> None:
    receipt = _valid_receipt()
    receipt["body"]["attestation"]["current_epoch"] = 0x100000000
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "bad_numeric_field"
def test_confidential_extension_receipt_rejects_noncanonical_numeric_encoding() -> None:
    receipt = _valid_receipt()
    receipt["body"]["host"]["policy_ok"] = "1"
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "bad_numeric_field"


def test_confidential_extension_receipt_numeric_internal_fault_is_not_masked(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def broken(_mapping: dict, _key: str) -> int:
        raise RuntimeError("numeric parser fault")

    monkeypatch.setattr(receipt_module, "_require_int_field", broken)

    with pytest.raises(RuntimeError, match="numeric parser fault"):
        verify_confidential_extension_receipt(_valid_receipt(), approved_measurements=APPROVED)


def test_confidential_extension_receipt_rejects_noncanonical_policy_digest() -> None:
    receipt = _valid_receipt()
    receipt["body"]["policy_digest"] = "0x1"
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "bad_policy_digest"


def test_confidential_extension_receipt_policy_digest_internal_fault_is_not_masked(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def broken(_value: object) -> str:
        raise RuntimeError("policy digest verifier fault")

    monkeypatch.setattr(receipt_module, "_require_policy_digest", broken)

    with pytest.raises(RuntimeError, match="policy digest verifier fault"):
        verify_confidential_extension_receipt(_valid_receipt(), approved_measurements=APPROVED)


def test_confidential_extension_receipt_hash_mismatch_precedes_later_header_failures() -> None:
    receipt = _valid_receipt()
    receipt["body"]["policy_digest"] = "0x1"
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "hash_mismatch"


def test_confidential_extension_receipt_rejects_bad_do_execute_flag_after_numeric_parse() -> None:
    receipt = _valid_receipt()
    receipt["body"]["host"]["do_execute"] = 2
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "bad_do_execute"


def test_confidential_extension_receipt_rejects_bad_policy_ok_flag_after_do_execute() -> None:
    receipt = _valid_receipt()
    receipt["body"]["host"]["policy_ok"] = 2
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "bad_policy_ok"


def test_confidential_extension_receipt_rejects_empty_extension_id() -> None:
    receipt = _valid_receipt()
    receipt["body"]["extension_id"] = ""
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "bad_extension_id"


def test_confidential_extension_receipt_rejects_whitespace_only_request_id() -> None:
    receipt = _valid_receipt()
    receipt["body"]["request_id"] = " "
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "bad_request_id"


def test_confidential_extension_receipt_rejects_padded_request_id() -> None:
    receipt = _valid_receipt()
    receipt["body"]["request_id"] = "req-1 "
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])
    ok, err = verify_confidential_extension_receipt(receipt, approved_measurements=APPROVED)
    assert not ok
    assert err == "bad_request_id"
