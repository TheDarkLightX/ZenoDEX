from __future__ import annotations

import pytest

import src.core.sealed_bid_auction as sealed_bid_auction
from src.core.sealed_bid_auction import (
    CheckedSealedBidBatch,
    SealedBidReveal,
    make_sealed_bid_commit_receipt,
    reveal_matches_commitment,
    sealed_bid_reveal_hash,
    settle_checked_second_price_sealed_bid,
    settle_checked_uniform_price_sealed_bids,
    settle_committed_uniform_price_sealed_bids,
    verify_sealed_bid_reveals_for_batch,
    verify_commit_receipt,
)


def _commit(batch_id: str, bidder_id: str, quantity: int, limit_price: int, nonce: str, *, units_for_sale: int = 10):
    commitment = sealed_bid_reveal_hash(quantity=quantity, limit_price=limit_price, nonce=nonce)
    return make_sealed_bid_commit_receipt(
        batch_id=batch_id,
        bidder_id=bidder_id,
        commitment=commitment,
        commit_epoch=1,
        reveal_deadline_epoch=3,
        units_for_sale=units_for_sale,
    )


def _reveal(bidder_id: str, quantity: int, limit_price: int, nonce: str) -> SealedBidReveal:
    return SealedBidReveal(
        bidder_id=bidder_id,
        commitment=sealed_bid_reveal_hash(quantity=quantity, limit_price=limit_price, nonce=nonce),
        quantity=quantity,
        limit_price=limit_price,
        nonce=nonce,
    )


def test_commit_receipt_hides_private_fields() -> None:
    commitment = sealed_bid_reveal_hash(quantity=4, limit_price=105, nonce="n1")
    receipt = make_sealed_bid_commit_receipt(
        batch_id="b1",
        bidder_id="alice",
        commitment=commitment,
        commit_epoch=1,
        reveal_deadline_epoch=2,
        units_for_sale=10,
    )
    ok, err = verify_commit_receipt(receipt)
    assert ok, err
    assert "quantity" not in receipt["body"]
    assert "limit_price" not in receipt["body"]
    assert "nonce" not in receipt["body"]


def test_commit_receipt_rejects_non_canonical_numeric_fields() -> None:
    commitment = sealed_bid_reveal_hash(quantity=4, limit_price=105, nonce="n1")
    receipt = make_sealed_bid_commit_receipt(
        batch_id="b1",
        bidder_id="alice",
        commitment=commitment,
        commit_epoch=1,
        reveal_deadline_epoch=2,
        units_for_sale=10,
    )
    bad_bool = {"body": {**receipt["body"], "commit_epoch": True}, "receipt_hash": receipt["receipt_hash"]}
    bad_string = {"body": {**receipt["body"], "units_for_sale": "10"}, "receipt_hash": receipt["receipt_hash"]}

    assert verify_commit_receipt(bad_bool) == (False, "bad_numeric_field")
    assert verify_commit_receipt(bad_string) == (False, "bad_numeric_field")


def test_commit_receipt_rejects_unknown_body_fields() -> None:
    commitment = sealed_bid_reveal_hash(quantity=4, limit_price=105, nonce="n1")
    receipt = make_sealed_bid_commit_receipt(
        batch_id="b1",
        bidder_id="alice",
        commitment=commitment,
        commit_epoch=1,
        reveal_deadline_epoch=2,
        units_for_sale=10,
    )
    body = {**receipt["body"], "ignored_semantics": "unsafe"}
    tampered = {
        "body": body,
        "receipt_hash": receipt["receipt_hash"],
    }

    assert verify_commit_receipt(tampered) == (False, "unknown_commit_field")


def test_commit_receipt_rejects_private_leak_before_unknown_field() -> None:
    commitment = sealed_bid_reveal_hash(quantity=4, limit_price=105, nonce="n1")
    receipt = make_sealed_bid_commit_receipt(
        batch_id="b1",
        bidder_id="alice",
        commitment=commitment,
        commit_epoch=1,
        reveal_deadline_epoch=2,
        units_for_sale=10,
    )
    leaked = {
        "body": {**receipt["body"], "quantity": 4},
        "receipt_hash": receipt["receipt_hash"],
    }

    assert verify_commit_receipt(leaked) == (False, "private_field_leaked_quantity")


def test_commit_receipt_constructor_rejects_non_canonical_fields() -> None:
    commitment = sealed_bid_reveal_hash(quantity=4, limit_price=105, nonce="n1")

    with pytest.raises(ValueError, match="^batch_id must be non-empty$"):
        make_sealed_bid_commit_receipt(
            batch_id="",
            bidder_id="alice",
            commitment=commitment,
            commit_epoch=1,
            reveal_deadline_epoch=2,
            units_for_sale=10,
        )
    with pytest.raises(ValueError, match="^commit_epoch out of range$"):
        make_sealed_bid_commit_receipt(
            batch_id="b1",
            bidder_id="alice",
            commitment=commitment,
            commit_epoch=True,  # type: ignore[arg-type]
            reveal_deadline_epoch=2,
            units_for_sale=10,
        )
    with pytest.raises(ValueError, match="^bad_epoch_window$"):
        make_sealed_bid_commit_receipt(
            batch_id="b1",
            bidder_id="alice",
            commitment=commitment,
            commit_epoch=3,
            reveal_deadline_epoch=2,
            units_for_sale=10,
        )


def test_reveal_matches_commitment_and_rejects_mismatch() -> None:
    commitment = sealed_bid_reveal_hash(quantity=4, limit_price=105, nonce="n1")
    assert reveal_matches_commitment(commitment=commitment, quantity=4, limit_price=105, nonce="n1")
    assert not reveal_matches_commitment(commitment=commitment, quantity=5, limit_price=105, nonce="n1")


def test_uniform_price_settlement_is_deterministic_under_reordering() -> None:
    receipts = [
        _commit("batch-1", "alice", 4, 105, "n1"),
        _commit("batch-1", "bob", 5, 103, "n2"),
        _commit("batch-1", "carol", 7, 100, "n3"),
    ]
    reveals = [
        _reveal("alice", 4, 105, "n1"),
        _reveal("bob", 5, 103, "n2"),
        _reveal("carol", 7, 100, "n3"),
    ]
    checked1 = verify_sealed_bid_reveals_for_batch(
        batch_id="batch-1",
        units_for_sale=10,
        commit_receipts=receipts,
        reveals=reveals,
        current_epoch=2,
    )
    checked2 = verify_sealed_bid_reveals_for_batch(
        batch_id="batch-1",
        units_for_sale=10,
        commit_receipts=list(reversed(receipts)),
        reveals=list(reversed(reveals)),
        current_epoch=2,
    )
    s1 = settle_checked_uniform_price_sealed_bids(checked_batch=checked1)
    s2 = settle_checked_uniform_price_sealed_bids(checked_batch=checked2)

    assert s1 == s2
    assert s1.clearing_price == 100
    assert s1.total_filled == 10
    assert [(f.bidder_id, f.filled_quantity, f.paid_price) for f in s1.fills] == [
        ("alice", 4, 100),
        ("bob", 5, 100),
        ("carol", 1, 100),
    ]


def test_uniform_price_boundary_exact_units() -> None:
    receipts = [
        _commit("batch-2", "alice", 3, 110, "m1", units_for_sale=5),
        _commit("batch-2", "bob", 4, 110, "m2", units_for_sale=5),
        _commit("batch-2", "carol", 4, 108, "m3", units_for_sale=5),
    ]
    reveals = [
        _reveal("alice", 3, 110, "m1"),
        _reveal("bob", 4, 110, "m2"),
        _reveal("carol", 4, 108, "m3"),
    ]
    checked = verify_sealed_bid_reveals_for_batch(
        batch_id="batch-2",
        units_for_sale=5,
        commit_receipts=receipts,
        reveals=reveals,
        current_epoch=2,
    )
    s = settle_checked_uniform_price_sealed_bids(checked_batch=checked)

    assert s.clearing_price == 110
    assert s.total_filled == 5
    assert [(f.bidder_id, f.filled_quantity) for f in s.fills] == [("bob", 4), ("alice", 1)]


def test_checked_settlement_requires_checked_batch_type() -> None:
    with pytest.raises(ValueError, match="^checked_batch must be a CheckedSealedBidBatch$"):
        settle_checked_uniform_price_sealed_bids(checked_batch=object())  # type: ignore[arg-type]

    with pytest.raises(ValueError, match="^CheckedSealedBidBatch must be constructed by verifier$"):
        CheckedSealedBidBatch(batch_id="batch-1", units_for_sale=1, bids=(), _token=object())


def test_second_price_single_item_charges_second_highest_bid() -> None:
    receipts = [
        _commit("vickrey-1", "alice", 1, 105, "n1", units_for_sale=1),
        _commit("vickrey-1", "bob", 1, 130, "n2", units_for_sale=1),
        _commit("vickrey-1", "carol", 1, 119, "n3", units_for_sale=1),
    ]
    reveals = [
        _reveal("carol", 1, 119, "n3"),
        _reveal("bob", 1, 130, "n2"),
        _reveal("alice", 1, 105, "n1"),
    ]
    checked = verify_sealed_bid_reveals_for_batch(
        batch_id="vickrey-1",
        units_for_sale=1,
        commit_receipts=receipts,
        reveals=reveals,
        current_epoch=2,
    )

    settlement = settle_checked_second_price_sealed_bid(checked_batch=checked)

    assert settlement.clearing_price == 119
    assert settlement.total_filled == 1
    assert [(f.bidder_id, f.filled_quantity, f.paid_price) for f in settlement.fills] == [("bob", 1, 119)]
    assert settlement.price_witness is not None
    assert settlement.price_witness.pricing_rule == "second_price_single_item_v1"
    assert settlement.price_witness.reserve_price == 0
    assert settlement.price_witness.threshold_price == 119
    assert settlement.price_witness.winner_bidder_id == "bob"
    assert settlement.price_witness.winner_limit_price == 130
    assert settlement.price_witness.runner_up_bidder_id == "carol"
    assert settlement.price_witness.runner_up_limit_price == 119
    assert settlement.price_witness.eligible_bid_count == 3


def test_second_price_single_item_is_deterministic_under_reordering() -> None:
    receipts = [
        _commit("vickrey-2", "alice", 1, 105, "n1", units_for_sale=1),
        _commit("vickrey-2", "bob", 1, 130, "n2", units_for_sale=1),
        _commit("vickrey-2", "carol", 1, 119, "n3", units_for_sale=1),
    ]
    reveals = [
        _reveal("alice", 1, 105, "n1"),
        _reveal("bob", 1, 130, "n2"),
        _reveal("carol", 1, 119, "n3"),
    ]
    checked1 = verify_sealed_bid_reveals_for_batch(
        batch_id="vickrey-2",
        units_for_sale=1,
        commit_receipts=receipts,
        reveals=reveals,
        current_epoch=2,
    )
    checked2 = verify_sealed_bid_reveals_for_batch(
        batch_id="vickrey-2",
        units_for_sale=1,
        commit_receipts=list(reversed(receipts)),
        reveals=list(reversed(reveals)),
        current_epoch=2,
    )

    assert settle_checked_second_price_sealed_bid(checked_batch=checked1) == settle_checked_second_price_sealed_bid(
        checked_batch=checked2
    )


def test_second_price_single_item_reserve_and_tie_boundaries() -> None:
    tied_receipts = [
        _commit("vickrey-3", "alice", 1, 110, "n1", units_for_sale=1),
        _commit("vickrey-3", "bob", 1, 110, "n2", units_for_sale=1),
        _commit("vickrey-3", "carol", 1, 90, "n3", units_for_sale=1),
    ]
    tied_reveals = [
        _reveal("alice", 1, 110, "n1"),
        _reveal("bob", 1, 110, "n2"),
        _reveal("carol", 1, 90, "n3"),
    ]
    tied = verify_sealed_bid_reveals_for_batch(
        batch_id="vickrey-3",
        units_for_sale=1,
        commit_receipts=tied_receipts,
        reveals=tied_reveals,
        current_epoch=2,
    )
    tied_settlement = settle_checked_second_price_sealed_bid(checked_batch=tied)

    assert tied_settlement.clearing_price == 110
    assert tied_settlement.total_filled == 1
    assert tied_settlement.fills[0].bidder_id in {"alice", "bob"}
    assert tied_settlement.price_witness is not None
    assert tied_settlement.price_witness.threshold_price == 110
    assert tied_settlement.price_witness.runner_up_limit_price == 110

    reserve_receipt = [_commit("vickrey-4", "alice", 1, 105, "n1", units_for_sale=1)]
    reserve_reveal = [_reveal("alice", 1, 105, "n1")]
    checked = verify_sealed_bid_reveals_for_batch(
        batch_id="vickrey-4",
        units_for_sale=1,
        commit_receipts=reserve_receipt,
        reveals=reserve_reveal,
        current_epoch=2,
    )

    accepted = settle_checked_second_price_sealed_bid(checked_batch=checked, reserve_price=100)
    rejected = settle_checked_second_price_sealed_bid(checked_batch=checked, reserve_price=106)
    assert accepted.clearing_price == 100
    assert accepted.price_witness is not None
    assert accepted.price_witness.threshold_price == 100
    assert accepted.price_witness.runner_up_bidder_id is None
    assert rejected.total_filled == 0
    assert rejected.price_witness is not None
    assert rejected.price_witness.threshold_price == 106
    assert rejected.price_witness.eligible_bid_count == 0


def test_second_price_single_item_rejects_wrong_scope_and_bad_reserve() -> None:
    multi_receipts = [
        _commit("batch-2", "alice", 3, 110, "m1", units_for_sale=5),
        _commit("batch-2", "bob", 4, 110, "m2", units_for_sale=5),
    ]
    multi_reveals = [
        _reveal("alice", 3, 110, "m1"),
        _reveal("bob", 4, 110, "m2"),
    ]
    multi_checked = verify_sealed_bid_reveals_for_batch(
        batch_id="batch-2",
        units_for_sale=5,
        commit_receipts=multi_receipts,
        reveals=multi_reveals,
        current_epoch=2,
    )
    single_checked = verify_sealed_bid_reveals_for_batch(
        batch_id="vickrey-5",
        units_for_sale=1,
        commit_receipts=[_commit("vickrey-5", "alice", 1, 110, "n1", units_for_sale=1)],
        reveals=[_reveal("alice", 1, 110, "n1")],
        current_epoch=2,
    )

    with pytest.raises(ValueError, match="^second-price settlement requires units_for_sale == 1$"):
        settle_checked_second_price_sealed_bid(checked_batch=multi_checked)
    with pytest.raises(ValueError, match="^reserve_price out of range$"):
        settle_checked_second_price_sealed_bid(checked_batch=single_checked, reserve_price=True)  # type: ignore[arg-type]


def test_raw_uniform_settlement_is_not_public_api() -> None:
    assert not hasattr(sealed_bid_auction, "settle_uniform_price_sealed_bids")


def test_committed_settlement_binds_reveals_to_commit_receipts() -> None:
    receipts = [
        _commit("batch-1", "alice", 4, 105, "n1"),
        _commit("batch-1", "bob", 5, 103, "n2"),
        _commit("batch-1", "carol", 7, 100, "n3"),
    ]
    reveals = [
        _reveal("carol", 7, 100, "n3"),
        _reveal("alice", 4, 105, "n1"),
        _reveal("bob", 5, 103, "n2"),
    ]

    settlement = settle_committed_uniform_price_sealed_bids(
        batch_id="batch-1",
        units_for_sale=10,
        commit_receipts=list(reversed(receipts)),
        reveals=reveals,
        current_epoch=2,
    )

    assert settlement.clearing_price == 100
    assert settlement.total_filled == 10
    assert [(f.bidder_id, f.filled_quantity, f.paid_price) for f in settlement.fills] == [
        ("alice", 4, 100),
        ("bob", 5, 100),
        ("carol", 1, 100),
    ]


def test_committed_reveal_rejects_wrong_nonce_payload() -> None:
    receipt = _commit("batch-1", "alice", 4, 105, "n1")
    reveal = SealedBidReveal(
        bidder_id="alice",
        commitment=receipt["body"]["commitment"],
        quantity=4,
        limit_price=105,
        nonce="changed",
    )

    with pytest.raises(ValueError, match="^reveal_commitment_mismatch$"):
        verify_sealed_bid_reveals_for_batch(
            batch_id="batch-1",
            units_for_sale=10,
            commit_receipts=[receipt],
            reveals=[reveal],
            current_epoch=2,
        )


def test_committed_reveal_rejects_bidder_reassignment() -> None:
    receipt = _commit("batch-1", "alice", 4, 105, "n1")
    reveal = SealedBidReveal(
        bidder_id="bob",
        commitment=receipt["body"]["commitment"],
        quantity=4,
        limit_price=105,
        nonce="n1",
    )

    with pytest.raises(ValueError, match="^reveal_without_commit$"):
        verify_sealed_bid_reveals_for_batch(
            batch_id="batch-1",
            units_for_sale=10,
            commit_receipts=[receipt],
            reveals=[reveal],
            current_epoch=2,
        )


def test_committed_reveal_rejects_batch_inventory_and_deadline_drift() -> None:
    wrong_batch = _commit("batch-2", "alice", 4, 105, "n1")
    wrong_inventory = _commit("batch-1", "bob", 5, 103, "n2", units_for_sale=11)
    expired = _commit("batch-1", "carol", 7, 100, "n3")

    cases = [
        ([wrong_batch], "commit_batch_mismatch"),
        ([wrong_inventory], "commit_units_for_sale_mismatch"),
        ([expired], "reveal_deadline_passed"),
    ]
    for receipts, expected in cases:
        with pytest.raises(ValueError, match=f"^{expected}$"):
            verify_sealed_bid_reveals_for_batch(
                batch_id="batch-1",
                units_for_sale=10,
                commit_receipts=receipts,
                reveals=[],
                current_epoch=4 if expected == "reveal_deadline_passed" else 2,
            )


def test_committed_reveal_rejects_duplicate_commit_and_reveal_keys() -> None:
    receipt = _commit("batch-1", "alice", 4, 105, "n1")
    reveal = _reveal("alice", 4, 105, "n1")

    with pytest.raises(ValueError, match="^duplicate_commit_key$"):
        verify_sealed_bid_reveals_for_batch(
            batch_id="batch-1",
            units_for_sale=10,
            commit_receipts=[receipt, receipt],
            reveals=[reveal],
            current_epoch=2,
        )

    with pytest.raises(ValueError, match="^duplicate_reveal_key$"):
        verify_sealed_bid_reveals_for_batch(
            batch_id="batch-1",
            units_for_sale=10,
            commit_receipts=[receipt],
            reveals=[reveal, reveal],
            current_epoch=2,
        )


def test_committed_reveal_rejects_copied_commitment_by_other_bidder() -> None:
    alice = _commit("batch-1", "alice", 4, 105, "n1")
    copied = make_sealed_bid_commit_receipt(
        batch_id="batch-1",
        bidder_id="bob",
        commitment=alice["body"]["commitment"],
        commit_epoch=1,
        reveal_deadline_epoch=3,
        units_for_sale=10,
    )

    with pytest.raises(ValueError, match="^duplicate_commitment$"):
        verify_sealed_bid_reveals_for_batch(
            batch_id="batch-1",
            units_for_sale=10,
            commit_receipts=[alice, copied],
            reveals=[_reveal("alice", 4, 105, "n1")],
            current_epoch=2,
        )


def test_committed_reveal_rejects_non_canonical_reveal_fields() -> None:
    receipt = _commit("batch-1", "alice", 4, 105, "n1")
    bad_quantity = SealedBidReveal(
        bidder_id="alice",
        commitment=receipt["body"]["commitment"],
        quantity=True,  # type: ignore[arg-type]
        limit_price=105,
        nonce="n1",
    )
    bad_nonce = SealedBidReveal(
        bidder_id="alice",
        commitment=receipt["body"]["commitment"],
        quantity=4,
        limit_price=105,
        nonce="",
    )

    with pytest.raises(ValueError, match="^quantity out of range$"):
        verify_sealed_bid_reveals_for_batch(
            batch_id="batch-1",
            units_for_sale=10,
            commit_receipts=[receipt],
            reveals=[bad_quantity],
            current_epoch=2,
        )
    with pytest.raises(ValueError, match="^reveal nonce must be non-empty$"):
        verify_sealed_bid_reveals_for_batch(
            batch_id="batch-1",
            units_for_sale=10,
            commit_receipts=[receipt],
            reveals=[bad_nonce],
            current_epoch=2,
        )
