from __future__ import annotations

from typing import Any

import pytest

from src.core.burn_receipts import burn_receipt_hash, make_burn_receipt, verify_burn_receipt


def _make_valid_receipt() -> dict[str, Any]:
    return make_burn_receipt(
        asset_id="TDEX",
        batch_id="batch-1",
        nullifier="n-1",
        tx_ref="tx-1",
        policy_version="burn-policy-v1",
        do_burn=1,
        receipt_bound=1,
        nullifier_unused=1,
        policy_ok=1,
        burn_amount=20,
        receipt_amount=20,
        burn_budget=30,
        supply_before=1000,
        supply_after=980,
        batch_burn_sum_before=50,
        batch_burn_sum_after=70,
    )


def test_burn_receipt_roundtrip_and_hash_is_deterministic() -> None:
    r1 = _make_valid_receipt()
    r2 = _make_valid_receipt()
    ok, err = verify_burn_receipt(r1)
    assert ok, err
    assert r1 == r2


def test_burn_receipt_replay_flag_fails_closed() -> None:
    receipt = _make_valid_receipt()
    receipt["body"]["host"]["nullifier_unused"] = 0
    receipt["receipt_hash"] = burn_receipt_hash(receipt["body"])
    ok, err = verify_burn_receipt(receipt)
    assert not ok
    assert err == "replay_guard_failed"


def test_burn_receipt_hash_mismatch_is_rejected() -> None:
    receipt = _make_valid_receipt()
    receipt["body"]["host"]["nullifier_unused"] = 0
    ok, err = verify_burn_receipt(receipt)
    assert not ok
    assert err == "hash_mismatch"


def test_burn_receipt_float_body_field_fails_closed() -> None:
    receipt = _make_valid_receipt()
    receipt["body"]["accounting"]["burn_amount"] = 20.0

    ok, err = verify_burn_receipt(receipt)

    assert not ok
    assert err == "bad_body_encoding"


def test_burn_receipt_non_string_body_key_fails_closed() -> None:
    receipt = _make_valid_receipt()
    receipt["body"][1] = "non-string key"

    ok, err = verify_burn_receipt(receipt)

    assert not ok
    assert err == "bad_body_encoding"


def test_burn_receipt_amount_mismatch_rejected_after_rehash() -> None:
    receipt = _make_valid_receipt()
    receipt["body"]["accounting"]["receipt_amount"] = 19
    receipt["receipt_hash"] = burn_receipt_hash(receipt["body"])
    ok, err = verify_burn_receipt(receipt)
    assert not ok
    assert err == "amount_guard_failed"


def test_burn_receipt_no_burn_path_preserves_state() -> None:
    receipt = make_burn_receipt(
        asset_id="TDEX",
        batch_id="batch-2",
        nullifier="n-2",
        tx_ref="tx-2",
        policy_version="burn-policy-v1",
        do_burn=0,
        receipt_bound=0,
        nullifier_unused=0,
        policy_ok=0,
        burn_amount=0,
        receipt_amount=0,
        burn_budget=30,
        supply_before=1000,
        supply_after=1000,
        batch_burn_sum_before=70,
        batch_burn_sum_after=70,
    )
    ok, err = verify_burn_receipt(receipt)
    assert ok, err


def test_burn_receipt_bool_numeric_field_is_rejected() -> None:
    receipt = _make_valid_receipt()
    receipt["body"]["host"]["do_burn"] = True
    receipt["receipt_hash"] = burn_receipt_hash(receipt["body"])

    ok, err = verify_burn_receipt(receipt)

    assert not ok
    assert err == "bad_numeric_field"


def test_burn_receipt_expected_numeric_coercion_failures_are_bad_numeric_field() -> None:
    receipt = _make_valid_receipt()
    receipt["body"]["accounting"]["burn_amount"] = "not-a-number"
    receipt["receipt_hash"] = burn_receipt_hash(receipt["body"])

    ok, err = verify_burn_receipt(receipt)

    assert not ok
    assert err == "bad_numeric_field"


def test_burn_receipt_unexpected_numeric_coercion_bug_propagates() -> None:
    class BrokenInt(str):
        def __new__(cls) -> "BrokenInt":
            return super().__new__(cls, "5")

        def __int__(self) -> int:
            raise RuntimeError("numeric parser bug")

    receipt = _make_valid_receipt()
    receipt["body"]["accounting"]["burn_amount"] = BrokenInt()
    receipt["receipt_hash"] = burn_receipt_hash(receipt["body"])

    with pytest.raises(RuntimeError, match="numeric parser bug"):
        verify_burn_receipt(receipt)
