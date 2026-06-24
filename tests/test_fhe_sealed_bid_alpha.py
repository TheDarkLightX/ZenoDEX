from __future__ import annotations

import pytest

import src.core.fhe_sealed_bid_alpha as alpha
from src.core.fhe_sealed_bid_alpha import (
    FHECipherBid,
    compile_fhe_sealed_bid_alpha_plan,
    fhe_sealed_bid_alpha_receipt_hash,
    verify_fhe_sealed_bid_alpha_plan,
)
from src.core.sealed_bid_auction import RevealedSealedBid


def _plain_bids() -> tuple[RevealedSealedBid, ...]:
    return (
        RevealedSealedBid("alice", "c1", 2, 100),
        RevealedSealedBid("bob", "c2", 1, 90),
    )


def _cipher_bids() -> tuple[FHECipherBid, ...]:
    return (
        FHECipherBid("alice", "c1", "ct:q:alice", "ct:p:alice"),
        FHECipherBid("bob", "c2", "ct:q:bob", "ct:p:bob"),
    )


def _receipt() -> dict:
    return compile_fhe_sealed_bid_alpha_plan(
        auction_id="alpha-test",
        units_for_sale=2,
        bids=_plain_bids(),
        cipher_bids=_cipher_bids(),
        key_id="alpha-key",
    )


def _rehash(receipt: dict) -> None:
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])


def test_alpha_plan_receipt_verifies_with_trusted_plaintext() -> None:
    ok, reason = verify_fhe_sealed_bid_alpha_plan(
        _receipt(),
        approved_key_ids=["alpha-key"],
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is True
    assert reason == "ok"


def test_alpha_plan_rejects_bool_budget_numeric_field() -> None:
    receipt = _receipt()
    receipt["body"]["budget"]["bid_count"] = True
    _rehash(receipt)

    ok, reason = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids=["alpha-key"],
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is False
    assert reason == "bad_budget_numeric"


def test_alpha_plan_rejects_bool_public_result_numeric_field() -> None:
    receipt = _receipt()
    receipt["body"]["public_result"]["total_filled"] = True
    _rehash(receipt)

    ok, reason = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids=["alpha-key"],
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is False
    assert reason == "bad_public_result_numeric"


def test_alpha_plan_rejects_bool_fill_numeric_field() -> None:
    receipt = _receipt()
    receipt["body"]["public_result"]["fills"][0]["filled_quantity"] = True
    _rehash(receipt)

    ok, reason = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids=["alpha-key"],
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is False
    assert reason == "bad_fill_numeric"


def test_alpha_plan_rejects_malformed_cipher_bid_item() -> None:
    receipt = _receipt()
    receipt["body"]["cipher_bids"][0] = "bad-cipher-item"
    _rehash(receipt)

    ok, reason = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids=["alpha-key"],
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is False
    assert reason == "bad_cipher_bid"


def test_alpha_plan_surfaces_numeric_helper_fault(monkeypatch) -> None:
    receipt = _receipt()

    def fail_int_field(_mapping: object, _field_name: str) -> int:
        raise RuntimeError("alpha numeric helper bug")

    monkeypatch.setattr(alpha, "_receipt_int_field", fail_int_field)

    with pytest.raises(RuntimeError, match="alpha numeric helper bug"):
        verify_fhe_sealed_bid_alpha_plan(
            receipt,
            approved_key_ids=["alpha-key"],
            trusted_plain_bids=_plain_bids(),
        )


def test_alpha_plan_surfaces_plaintext_replay_fault(monkeypatch) -> None:
    receipt = _receipt()

    def fail_replay(*, units_for_sale: int, bids: object) -> object:
        del units_for_sale, bids
        raise RuntimeError("alpha replay bug")

    monkeypatch.setattr(alpha, "settle_uniform_price_sealed_bids", fail_replay)

    with pytest.raises(RuntimeError, match="alpha replay bug"):
        verify_fhe_sealed_bid_alpha_plan(
            receipt,
            approved_key_ids=["alpha-key"],
            trusted_plain_bids=_plain_bids(),
        )
