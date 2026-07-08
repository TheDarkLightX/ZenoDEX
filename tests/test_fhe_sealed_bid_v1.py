"""Tests for FHE sealed-bid auction settlement v1.

Copyright (c) DarkLightX/Dana Edwards. All rights reserved.
"""

from __future__ import annotations

import pytest

from src.core.fhe_sealed_bid_v1 import (
    SCHEME_FALLBACK,
    SCHEME_FHE,
    EncryptedBid,
    PaillierKeyPair,
    compare_encrypted,
    encrypt_bid,
    fhe_sealed_bid_v1_receipt_hash,
    generate_paillier_keypair,
    make_fhe_sealed_bid_v1_receipt,
    settle_fhe_sealed_bids,
    settle_sealed_bids_with_fhe,
    verify_fhe_sealed_bid_v1_receipt,
    _decrypt_value,
    _encrypt_value,
    _homomorphic_add,
    _homomorphic_scalar_mul,
    _homomorphic_sub,
)
from src.core.sealed_bid_auction import MAX_PRICE, RevealedSealedBid, settle_uniform_price_sealed_bids

_TEST_KEY_BITS = 64


@pytest.fixture(scope="module")
def key_pair() -> PaillierKeyPair:
    return generate_paillier_keypair(key_bits=_TEST_KEY_BITS, key_id="test-fhe-v1")


def _enc_bids(kp, specs):
    """Build encrypted bids from (bidder, commitment, qty, price)."""
    return [encrypt_bid(public_key=kp.public_key, bidder_id=b, commitment=c,
                        quantity=q, limit_price=p) for b, c, q, p in specs]


def _revealed(specs):
    return [RevealedSealedBid(bidder_id=b, commitment=c, quantity=q, limit_price=p)
            for b, c, q, p in specs]


# ── Paillier primitives ────────────────────────────────────────────────


class TestPaillierPrimitives:
    def test_encrypt_decrypt_round_trip_recovers_plaintext(self, key_pair):
        pk, sk = key_pair.public_key, key_pair.private_key
        for m in [0, 1, 42, 65535, 1000000]:
            assert _decrypt_value(sk, _encrypt_value(pk, m)) == m

    def test_homomorphic_add_sub_and_scalar_mul(self, key_pair):
        pk, sk = key_pair.public_key, key_pair.private_key
        assert _decrypt_value(sk, _homomorphic_add(pk, _encrypt_value(pk, 30), _encrypt_value(pk, 12))) == 42
        assert _decrypt_value(sk, _homomorphic_sub(pk, _encrypt_value(pk, 50), _encrypt_value(pk, 20))) == 30
        assert _decrypt_value(sk, _homomorphic_scalar_mul(pk, _encrypt_value(pk, 7), 6)) == 42

    def test_encryption_is_probabilistic(self, key_pair):
        pk = key_pair.public_key
        assert _encrypt_value(pk, 42) != _encrypt_value(pk, 42)


class TestComparisonOracle:
    def test_compare_returns_correct_sign_for_all_orderings(self, key_pair):
        pk, sk = key_pair.public_key, key_pair.private_key
        assert compare_encrypted(sk, pk, _encrypt_value(pk, 100), _encrypt_value(pk, 50)).value == 1
        assert compare_encrypted(sk, pk, _encrypt_value(pk, 30), _encrypt_value(pk, 80)).value == -1
        assert compare_encrypted(sk, pk, _encrypt_value(pk, 55), _encrypt_value(pk, 55)).value == 0


# ── Encrypted bid submission ───────────────────────────────────────────


class TestEncryptedBidSubmission:
    def test_encrypt_bid_produces_valid_distinct_ciphertexts(self, key_pair):
        bid = encrypt_bid(public_key=key_pair.public_key, bidder_id="alice",
                          commitment="c1", quantity=5, limit_price=100)
        assert bid.bidder_id == "alice"
        assert bid.price_ciphertext > 1
        assert bid.quantity_ciphertext > 1
        assert bid.price_ciphertext != bid.quantity_ciphertext

    def test_encrypt_bid_round_trip_recovers_values(self, key_pair):
        bid = encrypt_bid(public_key=key_pair.public_key, bidder_id="bob",
                          commitment="c2", quantity=3, limit_price=77)
        assert _decrypt_value(key_pair.private_key, bid.quantity_ciphertext) == 3
        assert _decrypt_value(key_pair.private_key, bid.price_ciphertext) == 77

    def test_encrypt_bid_rejects_invalid_inputs(self, key_pair):
        with pytest.raises(ValueError, match="bidder_id"):
            encrypt_bid(public_key=key_pair.public_key, bidder_id="", commitment="c", quantity=1, limit_price=1)
        with pytest.raises(ValueError, match="limit_price"):
            encrypt_bid(public_key=key_pair.public_key, bidder_id="a", commitment="c", quantity=1, limit_price=MAX_PRICE + 1)


# ── Homomorphic settlement ─────────────────────────────────────────────


class TestHomomorphicSettlement:
    def test_clearing_price_matches_plaintext_settlement(self, key_pair):
        specs = [("alice", "c1", 4, 105), ("bob", "c2", 3, 103)]
        result = settle_fhe_sealed_bids(auction_id="a1", units_for_sale=5,
                                        encrypted_bids=_enc_bids(key_pair, specs), key_pair=key_pair)
        plain = settle_uniform_price_sealed_bids(units_for_sale=5, bids=_revealed(specs))
        assert result.clearing_price == plain.clearing_price
        assert result.total_filled == plain.total_filled
        assert len(result.fills) == len(plain.fills)

    def test_clearing_price_is_marginal_bid_price(self, key_pair):
        specs = [("alice", "c1", 4, 110), ("bob", "c2", 3, 100), ("carol", "c3", 2, 90)]
        result = settle_fhe_sealed_bids(auction_id="a2", units_for_sale=5,
                                        encrypted_bids=_enc_bids(key_pair, specs), key_pair=key_pair)
        assert result.clearing_price == 100
        assert result.total_filled == 5
        assert all(f.paid_price == 100 for f in result.fills)

    def test_settlement_fills_all_when_supply_exceeds_demand(self, key_pair):
        specs = [("alice", "c1", 2, 50), ("bob", "c2", 2, 40)]
        result = settle_fhe_sealed_bids(auction_id="a3", units_for_sale=10,
                                        encrypted_bids=_enc_bids(key_pair, specs), key_pair=key_pair)
        assert result.clearing_price == 40
        assert result.total_filled == 4

    def test_tie_prices_broken_by_commitment_order(self, key_pair):
        specs = [("alice", "zzz", 2, 100), ("bob", "aaa", 2, 100)]
        result = settle_fhe_sealed_bids(auction_id="a4", units_for_sale=3,
                                        encrypted_bids=_enc_bids(key_pair, specs), key_pair=key_pair)
        assert result.fills[0].bidder_id == "bob"
        assert result.clearing_price == 100

    def test_settlement_rejects_too_many_and_duplicate_bids(self, key_pair):
        many = _enc_bids(key_pair, [(f"b{i}", f"c{i}", 1, 100) for i in range(9)])
        with pytest.raises(ValueError, match="bid count"):
            settle_fhe_sealed_bids(auction_id="a5", units_for_sale=5, encrypted_bids=many, key_pair=key_pair)
        dups = _enc_bids(key_pair, [("a", "c", 1, 100), ("a", "c", 1, 100)])
        with pytest.raises(ValueError, match="duplicate"):
            settle_fhe_sealed_bids(auction_id="a6", units_for_sale=5, encrypted_bids=dups, key_pair=key_pair)


# ── Production security claim ──────────────────────────────────────────


class TestProductionSecurityClaim:
    def test_fhe_sets_production_claim_false_for_weak_keys(self, key_pair):
        """Test keys (64-bit) must not get production security claim."""
        result = settle_fhe_sealed_bids(auction_id="a7", units_for_sale=2,
                                        encrypted_bids=_enc_bids(key_pair, [("a", "c", 2, 100)]), key_pair=key_pair)
        assert result.production_security_claim is False
        assert result.scheme == SCHEME_FHE

    def test_fhe_sets_production_claim_true_for_strong_keys(self):
        """Keys with key_bits >= 1024 get production security claim."""
        strong_key = generate_paillier_keypair(key_bits=1024, key_id="prod-fhe-v1")
        result = settle_fhe_sealed_bids(auction_id="a7b", units_for_sale=2,
                                        encrypted_bids=_enc_bids(strong_key, [("a", "c", 2, 100)]),
                                        key_pair=strong_key)
        assert result.production_security_claim is True
        assert result.scheme == SCHEME_FHE

    def test_decrypt_count_minimal_only_winning_bids_plus_clearing_price(self, key_pair):
        specs = [("a", "c1", 2, 100), ("b", "c2", 2, 90), ("c", "c3", 2, 80)]
        result = settle_fhe_sealed_bids(auction_id="a8", units_for_sale=4,
                                        encrypted_bids=_enc_bids(key_pair, specs), key_pair=key_pair)
        # 2 winning quantities + 1 clearing price = 3; carol never decrypted
        assert result.decrypt_count == 3

    def test_comparison_count_matches_selection_sort(self, key_pair):
        result = settle_fhe_sealed_bids(auction_id="a9", units_for_sale=2,
                                        encrypted_bids=_enc_bids(key_pair, [("a", "c1", 1, 100), ("b", "c2", 1, 90), ("c", "c3", 1, 80)]),
                                        key_pair=key_pair)
        assert result.comparison_count == 3  # 2 + 1 for 3-item selection sort


# ── Commit/reveal fallback ─────────────────────────────────────────────


class TestCommitRevealFallback:
    def test_fallback_when_no_key_pair_uses_commit_reveal_scheme(self):
        specs = [("alice", "c1", 4, 105), ("bob", "c2", 3, 103)]
        result = settle_sealed_bids_with_fhe(auction_id="a10", units_for_sale=5, revealed_bids=_revealed(specs))
        assert result.scheme == SCHEME_FALLBACK
        assert result.production_security_claim is False
        assert result.key_id == ""

    def test_fallback_clearing_price_matches_plaintext(self):
        specs = [("alice", "c1", 4, 105), ("bob", "c2", 3, 103)]
        result = settle_sealed_bids_with_fhe(auction_id="a11", units_for_sale=5, revealed_bids=_revealed(specs))
        plain = settle_uniform_price_sealed_bids(units_for_sale=5, bids=_revealed(specs))
        assert result.clearing_price == plain.clearing_price

    def test_unified_entry_raises_when_neither_path_provided(self):
        with pytest.raises(ValueError, match="either"):
            settle_sealed_bids_with_fhe(auction_id="a12", units_for_sale=5)


# ── Receipt verification ───────────────────────────────────────────────


class TestReceiptVerification:
    def test_fhe_receipt_verifies_with_trusted_plaintext(self, key_pair):
        specs = [("alice", "c1", 4, 105), ("bob", "c2", 3, 103)]
        result = settle_fhe_sealed_bids(auction_id="a13", units_for_sale=5,
                                        encrypted_bids=_enc_bids(key_pair, specs), key_pair=key_pair)
        receipt = make_fhe_sealed_bid_v1_receipt(auction_id="a13", units_for_sale=5, result=result)
        ok, reason = verify_fhe_sealed_bid_v1_receipt(receipt, approved_key_ids=["test-fhe-v1"],
                                                       trusted_plain_bids=_revealed(specs))
        assert ok is True
        assert reason == "ok"

    def test_fhe_receipt_rejects_unapproved_key_id(self, key_pair):
        specs = [("alice", "c1", 2, 100)]
        result = settle_fhe_sealed_bids(auction_id="a14", units_for_sale=2,
                                        encrypted_bids=_enc_bids(key_pair, specs), key_pair=key_pair)
        receipt = make_fhe_sealed_bid_v1_receipt(auction_id="a14", units_for_sale=2, result=result)
        ok, reason = verify_fhe_sealed_bid_v1_receipt(receipt, approved_key_ids=["other"],
                                                       trusted_plain_bids=_revealed(specs))
        assert ok is False
        assert reason == "key_not_approved"

    def test_fallback_receipt_verifies_with_empty_key_id(self):
        specs = [("alice", "c1", 2, 100)]
        result = settle_sealed_bids_with_fhe(auction_id="a15", units_for_sale=2, revealed_bids=_revealed(specs))
        receipt = make_fhe_sealed_bid_v1_receipt(auction_id="a15", units_for_sale=2, result=result)
        ok, reason = verify_fhe_sealed_bid_v1_receipt(receipt, approved_key_ids=[], trusted_plain_bids=_revealed(specs))
        assert ok is True

    def test_receipt_detects_tampered_clearing_price(self, key_pair):
        specs = [("alice", "c1", 2, 100)]
        result = settle_fhe_sealed_bids(auction_id="a16", units_for_sale=2,
                                        encrypted_bids=_enc_bids(key_pair, specs), key_pair=key_pair)
        receipt = make_fhe_sealed_bid_v1_receipt(auction_id="a16", units_for_sale=2, result=result)
        receipt["body"]["public_result"]["clearing_price"] = 999
        for fill in receipt["body"]["public_result"]["fills"]:
            fill["paid_price"] = 999
        receipt["receipt_hash"] = fhe_sealed_bid_v1_receipt_hash(receipt["body"])
        ok, reason = verify_fhe_sealed_bid_v1_receipt(receipt, approved_key_ids=["test-fhe-v1"],
                                                       trusted_plain_bids=_revealed(specs))
        assert ok is False
        assert reason == "public_result_mismatch"
