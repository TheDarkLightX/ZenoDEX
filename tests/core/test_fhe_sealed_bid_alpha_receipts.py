from __future__ import annotations

from src.core.fhe_sealed_bid_alpha import (
    FHECipherBid,
    compile_fhe_sealed_bid_alpha_plan,
    fhe_sealed_bid_alpha_receipt_hash,
    verify_fhe_sealed_bid_alpha_plan,
)
from src.core.sealed_bid_auction import RevealedSealedBid


def _valid_alpha_receipt() -> dict:
    return compile_fhe_sealed_bid_alpha_plan(
        auction_id="alpha-1",
        units_for_sale=1,
        bids=[RevealedSealedBid("alice", "c1", 2, 100)],
        cipher_bids=[FHECipherBid("alice", "c1", "q1", "p1")],
        key_id="approved-key",
    )


def _verify_alpha(receipt: dict) -> tuple[bool, str]:
    return verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids=["approved-key"],
        trusted_plain_bids=[RevealedSealedBid("alice", "c1", 2, 100)],
    )


def test_alpha_plan_receipt_verifies_with_trusted_plaintext() -> None:
    ok, reason = _verify_alpha(_valid_alpha_receipt())

    assert ok
    assert reason == "ok"


def test_alpha_plan_rejects_noncanonical_budget_number() -> None:
    receipt = _valid_alpha_receipt()
    receipt["body"]["budget"]["bid_count"] = "1"
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])

    ok, reason = _verify_alpha(receipt)

    assert not ok
    assert reason == "bad_budget_numeric"


def test_alpha_plan_rejects_noncanonical_public_result_number() -> None:
    receipt = _valid_alpha_receipt()
    receipt["body"]["public_result"]["units_for_sale"] = "1"
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])

    ok, reason = _verify_alpha(receipt)

    assert not ok
    assert reason == "bad_public_result_numeric"


def test_alpha_plan_rejects_bool_fill_number() -> None:
    receipt = _valid_alpha_receipt()
    receipt["body"]["public_result"]["fills"][0]["filled_quantity"] = True
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])

    ok, reason = _verify_alpha(receipt)

    assert not ok
    assert reason == "bad_fill_numeric"


def test_alpha_plan_rejects_malformed_cipher_bid_with_stable_reason() -> None:
    receipt = _valid_alpha_receipt()
    receipt["body"]["cipher_bids"][0] = "not-a-cipher-bid"
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])

    ok, reason = _verify_alpha(receipt)

    assert not ok
    assert reason == "bad_cipher_bid"
