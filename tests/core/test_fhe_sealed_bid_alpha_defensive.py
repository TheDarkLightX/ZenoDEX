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

APPROVED_KEY_IDS = {"fhe-key-1"}


def _plain_bids() -> list[RevealedSealedBid]:
    return [
        RevealedSealedBid("alice", "c1", 3, 10),
        RevealedSealedBid("bob", "c2", 4, 9),
        RevealedSealedBid("carol", "c3", 2, 11),
    ]


def _cipher_bids() -> list[FHECipherBid]:
    return [
        FHECipherBid("alice", "c1", "ct:q:alice", "ct:p:alice"),
        FHECipherBid("bob", "c2", "ct:q:bob", "ct:p:bob"),
        FHECipherBid("carol", "c3", "ct:q:carol", "ct:p:carol"),
    ]


def _receipt() -> dict[str, object]:
    return compile_fhe_sealed_bid_alpha_plan(
        auction_id="auction-1",
        units_for_sale=5,
        bids=_plain_bids(),
        cipher_bids=_cipher_bids(),
        key_id="fhe-key-1",
    )


def _body(receipt: dict[str, object]) -> dict[str, object]:
    body = receipt["body"]
    assert isinstance(body, dict)
    return body


def _retag(receipt: dict[str, object]) -> None:
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(_body(receipt))


def test_fhe_plan_bool_budget_field_is_bad_budget_numeric() -> None:
    receipt = _receipt()
    budget = _body(receipt)["budget"]
    assert isinstance(budget, dict)
    budget["bid_count"] = True
    _retag(receipt)

    ok, err = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids=APPROVED_KEY_IDS,
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is False
    assert err == "bad_budget_numeric"


def test_fhe_plan_numeric_string_budget_field_is_bad_budget_numeric() -> None:
    receipt = _receipt()
    budget = _body(receipt)["budget"]
    assert isinstance(budget, dict)
    budget["bid_count"] = "3"
    _retag(receipt)

    ok, err = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids=APPROVED_KEY_IDS,
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is False
    assert err == "bad_budget_numeric"


def test_fhe_plan_bool_public_result_field_is_bad_public_result_numeric() -> None:
    receipt = _receipt()
    public_result = _body(receipt)["public_result"]
    assert isinstance(public_result, dict)
    public_result["clearing_price"] = True
    _retag(receipt)

    ok, err = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids=APPROVED_KEY_IDS,
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is False
    assert err == "bad_public_result_numeric"


def test_fhe_plan_numeric_string_public_result_field_is_bad_public_result_numeric() -> None:
    receipt = _receipt()
    public_result = _body(receipt)["public_result"]
    assert isinstance(public_result, dict)
    public_result["clearing_price"] = "10"
    _retag(receipt)

    ok, err = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids=APPROVED_KEY_IDS,
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is False
    assert err == "bad_public_result_numeric"


def test_fhe_plan_bool_fill_field_is_bad_fill_numeric() -> None:
    receipt = _receipt()
    public_result = _body(receipt)["public_result"]
    assert isinstance(public_result, dict)
    fills = public_result["fills"]
    assert isinstance(fills, list)
    first_fill = fills[0]
    assert isinstance(first_fill, dict)
    first_fill["filled_quantity"] = True
    _retag(receipt)

    ok, err = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids=APPROVED_KEY_IDS,
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is False
    assert err == "bad_fill_numeric"


def test_fhe_plan_numeric_string_fill_field_is_bad_fill_numeric() -> None:
    receipt = _receipt()
    public_result = _body(receipt)["public_result"]
    assert isinstance(public_result, dict)
    fills = public_result["fills"]
    assert isinstance(fills, list)
    first_fill = fills[0]
    assert isinstance(first_fill, dict)
    first_fill["filled_quantity"] = "3"
    _retag(receipt)

    ok, err = verify_fhe_sealed_bid_alpha_plan(
        receipt,
        approved_key_ids=APPROVED_KEY_IDS,
        trusted_plain_bids=_plain_bids(),
    )

    assert ok is False
    assert err == "bad_fill_numeric"


def test_fhe_plan_cipher_validation_helper_bug_propagates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def broken_validate(cipher_bids: object) -> tuple[FHECipherBid, ...]:
        raise RuntimeError("cipher validation bug")

    monkeypatch.setattr(fhe_alpha, "_validate_cipher_bids", broken_validate)
    with pytest.raises(RuntimeError, match="cipher validation bug"):
        verify_fhe_sealed_bid_alpha_plan(
            _receipt(),
            approved_key_ids=APPROVED_KEY_IDS,
            trusted_plain_bids=_plain_bids(),
        )


def test_fhe_plan_numeric_helper_bug_propagates(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_receipt_int(value: object) -> int:
        raise RuntimeError("numeric helper bug")

    monkeypatch.setattr(fhe_alpha, "_receipt_int", broken_receipt_int)
    with pytest.raises(RuntimeError, match="numeric helper bug"):
        verify_fhe_sealed_bid_alpha_plan(
            _receipt(),
            approved_key_ids=APPROVED_KEY_IDS,
            trusted_plain_bids=_plain_bids(),
        )


def test_fhe_plan_estimator_bug_propagates(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_estimator(*, bid_count: int, decrypt_outputs: int | None = None) -> object:
        raise RuntimeError("estimator bug")

    monkeypatch.setattr(fhe_alpha, "estimate_fhe_uniform_price_ops", broken_estimator)
    with pytest.raises(RuntimeError, match="estimator bug"):
        verify_fhe_sealed_bid_alpha_plan(
            _receipt(),
            approved_key_ids=APPROVED_KEY_IDS,
            trusted_plain_bids=_plain_bids(),
        )


def test_fhe_plan_trusted_plain_iter_type_error_stays_bad_trusted_plain_bids() -> None:
    class BadPlainBids:
        def __iter__(self):
            raise TypeError("bad plain bids")

    ok, err = verify_fhe_sealed_bid_alpha_plan(
        _receipt(),
        approved_key_ids=APPROVED_KEY_IDS,
        trusted_plain_bids=BadPlainBids(),
    )

    assert ok is False
    assert err == "bad_trusted_plain_bids"


def test_fhe_plan_trusted_plain_iter_runtime_bug_propagates() -> None:
    class BrokenPlainBids:
        def __iter__(self):
            raise RuntimeError("plain bid iterator bug")

    with pytest.raises(RuntimeError, match="plain bid iterator bug"):
        verify_fhe_sealed_bid_alpha_plan(
            _receipt(),
            approved_key_ids=APPROVED_KEY_IDS,
            trusted_plain_bids=BrokenPlainBids(),
        )
