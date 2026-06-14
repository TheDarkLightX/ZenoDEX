from __future__ import annotations

import pytest

from src.core.fhe_sealed_bid_alpha import (
    FHECipherBid,
    compile_fhe_sealed_bid_alpha_plan,
    fhe_sealed_bid_alpha_receipt_hash,
    verify_fhe_sealed_bid_alpha_plan,
)
from src.core.sealed_bid_auction import RevealedSealedBid


class _ExplodingInt(int):
    def __int__(self) -> int:
        raise RuntimeError("fhe alpha numeric conversion fault")


def _plain_bids() -> tuple[RevealedSealedBid, ...]:
    return (
        RevealedSealedBid("alice", "commitment-a", 4, 105),
        RevealedSealedBid("bob", "commitment-b", 5, 100),
    )


def _cipher_bids() -> tuple[FHECipherBid, ...]:
    return (
        FHECipherBid("alice", "commitment-a", "ct:q:alice", "ct:p:alice"),
        FHECipherBid("bob", "commitment-b", "ct:q:bob", "ct:p:bob"),
    )


def _plan() -> dict:
    return compile_fhe_sealed_bid_alpha_plan(
        auction_id="fhe-alpha-test",
        units_for_sale=5,
        bids=_plain_bids(),
        cipher_bids=_cipher_bids(),
        key_id="fhe-key-1",
    )


def _rehash(receipt: dict) -> dict:
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])
    return receipt


def test_fhe_alpha_plan_accepts_trusted_plaintext_replay() -> None:
    ok, err = verify_fhe_sealed_bid_alpha_plan(
        _plan(),
        approved_key_ids={"fhe-key-1"},
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is True
    assert err == "ok"


def test_fhe_alpha_plan_rejects_expected_budget_numeric_failure() -> None:
    receipt = _plan()
    receipt["body"]["budget"]["bid_count"] = None
    _rehash(receipt)

    ok, err = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids={"fhe-key-1"},
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is False
    assert err == "bad_budget_numeric"


def test_fhe_alpha_plan_rejects_expected_estimate_domain_failure() -> None:
    receipt = _plan()
    receipt["body"]["budget"]["decrypt_outputs"] = 0
    _rehash(receipt)

    ok, err = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids={"fhe-key-1"},
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is False
    assert err == "decrypt_outputs out of range"


def test_fhe_alpha_plan_propagates_unexpected_budget_numeric_fault() -> None:
    receipt = _plan()
    receipt["body"]["budget"]["bid_count"] = _ExplodingInt(2)
    _rehash(receipt)

    with pytest.raises(RuntimeError, match="fhe alpha numeric conversion fault"):
        verify_fhe_sealed_bid_alpha_plan(
            receipt,
            approved_key_ids={"fhe-key-1"},
            trusted_plain_bids=_plain_bids(),
        )


def test_fhe_alpha_plan_propagates_unexpected_public_result_numeric_fault() -> None:
    receipt = _plan()
    receipt["body"]["public_result"]["units_for_sale"] = _ExplodingInt(5)
    _rehash(receipt)

    with pytest.raises(RuntimeError, match="fhe alpha numeric conversion fault"):
        verify_fhe_sealed_bid_alpha_plan(
            receipt,
            approved_key_ids={"fhe-key-1"},
            trusted_plain_bids=_plain_bids(),
        )


def test_fhe_alpha_plan_propagates_unexpected_fill_numeric_fault() -> None:
    receipt = _plan()
    receipt["body"]["public_result"]["fills"][0]["filled_quantity"] = _ExplodingInt(4)
    _rehash(receipt)

    with pytest.raises(RuntimeError, match="fhe alpha numeric conversion fault"):
        verify_fhe_sealed_bid_alpha_plan(
            receipt,
            approved_key_ids={"fhe-key-1"},
            trusted_plain_bids=_plain_bids(),
        )
