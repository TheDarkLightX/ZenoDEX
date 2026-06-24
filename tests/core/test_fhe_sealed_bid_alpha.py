from __future__ import annotations

import pytest

import src.core.fhe_sealed_bid_alpha as fhe_alpha
from src.core.fhe_sealed_bid_alpha import (
    FHECipherBid,
    compile_fhe_sealed_bid_alpha_plan,
    fhe_sealed_bid_alpha_receipt_hash,
    verify_fhe_sealed_bid_alpha_plan,
)
from src.core.sealed_bid_auction import RevealedSealedBid


APPROVED_KEYS = {"fhe-key-1"}


def _plain_bids() -> tuple[RevealedSealedBid, ...]:
    return (
        RevealedSealedBid(bidder_id="alice", commitment="commit-a", quantity=2, limit_price=10),
        RevealedSealedBid(bidder_id="bob", commitment="commit-b", quantity=3, limit_price=8),
    )


def _cipher_bids() -> tuple[FHECipherBid, ...]:
    return (
        FHECipherBid(
            bidder_id="alice",
            commitment="commit-a",
            quantity_handle="q-a",
            price_handle="p-a",
        ),
        FHECipherBid(
            bidder_id="bob",
            commitment="commit-b",
            quantity_handle="q-b",
            price_handle="p-b",
        ),
    )


def _valid_plan() -> dict:
    return compile_fhe_sealed_bid_alpha_plan(
        auction_id="auction-1",
        units_for_sale=4,
        bids=_plain_bids(),
        cipher_bids=_cipher_bids(),
        key_id="fhe-key-1",
    )


def test_fhe_sealed_bid_alpha_plan_roundtrip() -> None:
    ok, err = verify_fhe_sealed_bid_alpha_plan(
        _valid_plan(),
        approved_key_ids=APPROVED_KEYS,
        trusted_plain_bids=_plain_bids(),
    )

    assert ok, err


def test_fhe_sealed_bid_alpha_rejects_bad_budget_numeric() -> None:
    receipt = _valid_plan()
    receipt["body"]["budget"]["bid_count"] = "bad"
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])

    ok, err = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids=APPROVED_KEYS,
        trusted_plain_bids=_plain_bids(),
    )

    assert not ok
    assert err == "bad_budget_numeric"


def test_fhe_sealed_bid_alpha_does_not_swallow_cipher_validator_bug(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    receipt = _valid_plan()

    def broken_validator(_cipher_bids: object) -> tuple[FHECipherBid, ...]:
        raise RuntimeError("unexpected cipher validator bug")

    monkeypatch.setattr(fhe_alpha, "_validate_cipher_bids", broken_validator)
    with pytest.raises(RuntimeError, match="unexpected cipher validator bug"):
        verify_fhe_sealed_bid_alpha_plan(
            receipt,
            approved_key_ids=APPROVED_KEYS,
            trusted_plain_bids=_plain_bids(),
        )


def test_fhe_sealed_bid_alpha_does_not_swallow_estimator_bug(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    receipt = _valid_plan()

    def broken_estimator(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("unexpected estimator bug")

    monkeypatch.setattr(fhe_alpha, "estimate_fhe_uniform_price_ops", broken_estimator)
    with pytest.raises(RuntimeError, match="unexpected estimator bug"):
        verify_fhe_sealed_bid_alpha_plan(
            receipt,
            approved_key_ids=APPROVED_KEYS,
            trusted_plain_bids=_plain_bids(),
        )


def test_fhe_sealed_bid_alpha_does_not_swallow_settlement_replay_bug(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    receipt = _valid_plan()

    def broken_settlement(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("unexpected settlement replay bug")

    monkeypatch.setattr(fhe_alpha, "settle_uniform_price_sealed_bids", broken_settlement)
    with pytest.raises(RuntimeError, match="unexpected settlement replay bug"):
        verify_fhe_sealed_bid_alpha_plan(
            receipt,
            approved_key_ids=APPROVED_KEYS,
            trusted_plain_bids=_plain_bids(),
        )
