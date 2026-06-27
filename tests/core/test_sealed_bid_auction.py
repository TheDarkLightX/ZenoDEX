from __future__ import annotations

from src.core.sealed_bid_auction import (
    RevealedSealedBid,
    make_sealed_bid_commit_receipt,
    reveal_matches_commitment,
    sealed_bid_reveal_hash,
    settle_uniform_price_sealed_bids,
    verify_commit_receipt,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex


def _commit_receipt_hash(body: dict) -> str:
    return sha256_hex(domain_sep_bytes("zenodex.sealed_bid_commit/v1") + canonical_json_bytes(body))


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


def test_commit_receipt_rejects_noncanonical_numeric_encoding() -> None:
    commitment = sealed_bid_reveal_hash(quantity=4, limit_price=105, nonce="n1")
    receipt = make_sealed_bid_commit_receipt(
        batch_id="b1",
        bidder_id="alice",
        commitment=commitment,
        commit_epoch=1,
        reveal_deadline_epoch=2,
        units_for_sale=10,
    )
    receipt["body"]["commit_epoch"] = "1"
    receipt["receipt_hash"] = _commit_receipt_hash(receipt["body"])

    ok, err = verify_commit_receipt(receipt)

    assert not ok
    assert err == "bad_numeric_field"


def test_reveal_matches_commitment_and_rejects_mismatch() -> None:
    commitment = sealed_bid_reveal_hash(quantity=4, limit_price=105, nonce="n1")
    assert reveal_matches_commitment(commitment=commitment, quantity=4, limit_price=105, nonce="n1")
    assert not reveal_matches_commitment(commitment=commitment, quantity=5, limit_price=105, nonce="n1")


def test_uniform_price_settlement_is_deterministic_under_reordering() -> None:
    bids = [
        RevealedSealedBid("alice", sealed_bid_reveal_hash(quantity=4, limit_price=105, nonce="n1"), 4, 105),
        RevealedSealedBid("bob", sealed_bid_reveal_hash(quantity=5, limit_price=103, nonce="n2"), 5, 103),
        RevealedSealedBid("carol", sealed_bid_reveal_hash(quantity=7, limit_price=100, nonce="n3"), 7, 100),
    ]
    s1 = settle_uniform_price_sealed_bids(units_for_sale=10, bids=bids)
    s2 = settle_uniform_price_sealed_bids(units_for_sale=10, bids=list(reversed(bids)))
    assert s1 == s2
    assert s1.clearing_price == 100
    assert s1.total_filled == 10
    assert [(f.bidder_id, f.filled_quantity, f.paid_price) for f in s1.fills] == [
        ("alice", 4, 100),
        ("bob", 5, 100),
        ("carol", 1, 100),
    ]


def test_uniform_price_boundary_exact_units() -> None:
    bids = [
        RevealedSealedBid("alice", sealed_bid_reveal_hash(quantity=3, limit_price=110, nonce="m1"), 3, 110),
        RevealedSealedBid("bob", sealed_bid_reveal_hash(quantity=4, limit_price=110, nonce="m2"), 4, 110),
        RevealedSealedBid("carol", sealed_bid_reveal_hash(quantity=4, limit_price=108, nonce="m3"), 4, 108),
    ]
    s = settle_uniform_price_sealed_bids(units_for_sale=5, bids=bids)
    assert s.clearing_price == 110
    assert s.total_filled == 5
    assert [(f.bidder_id, f.filled_quantity) for f in s.fills] == [("bob", 4), ("alice", 1)]
