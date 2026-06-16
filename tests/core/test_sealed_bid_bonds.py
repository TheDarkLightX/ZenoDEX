from __future__ import annotations

import pytest

from src.core.sealed_bid_bonds import (
    BondedSealedBidCommit,
    SealedBidRevealRef,
    settle_sealed_bid_non_reveal_bonds,
)


def test_sealed_bid_bond_refund_and_slash_conservation() -> None:
    outcome = settle_sealed_bid_non_reveal_bonds(
        commits=[
            BondedSealedBidCommit("alice", "c1", 5),
            BondedSealedBidCommit("bob", "c2", 5),
            BondedSealedBidCommit("carol", "c3", 5),
        ],
        reveals=[SealedBidRevealRef("alice", "c1"), SealedBidRevealRef("bob", "c2")],
    )
    assert outcome.total_bonded == 15
    assert outcome.total_refunded == 10
    assert outcome.total_slashed == 5
    assert outcome.total_bonded == outcome.total_refunded + outcome.total_slashed
    assert outcome.refunded_bid_count == 2
    assert outcome.slashed_bid_count == 1


def test_sealed_bid_bond_duplicate_commit_fails_closed() -> None:
    with pytest.raises(ValueError, match="duplicate_commit_key"):
        settle_sealed_bid_non_reveal_bonds(
            commits=[
                BondedSealedBidCommit("alice", "c1", 5),
                BondedSealedBidCommit("alice", "c1", 5),
            ],
            reveals=[],
        )


def test_sealed_bid_bond_duplicate_reveal_fails_closed() -> None:
    with pytest.raises(ValueError, match="duplicate_reveal_key"):
        settle_sealed_bid_non_reveal_bonds(
            commits=[BondedSealedBidCommit("alice", "c1", 5)],
            reveals=[SealedBidRevealRef("alice", "c1"), SealedBidRevealRef("alice", "c1")],
        )


def test_sealed_bid_bond_reveal_without_commit_fails_closed() -> None:
    with pytest.raises(ValueError, match="reveal_without_commit"):
        settle_sealed_bid_non_reveal_bonds(
            commits=[BondedSealedBidCommit("alice", "c1", 5)],
            reveals=[SealedBidRevealRef("bob", "c2")],
        )


def test_sealed_bid_bond_decisions_are_canonical_commitment_then_bidder_order() -> None:
    outcome = settle_sealed_bid_non_reveal_bonds(
        commits=[
            BondedSealedBidCommit("carol", "c2", 7),
            BondedSealedBidCommit("bob", "c1", 5),
            BondedSealedBidCommit("alice", "c1", 3),
        ],
        reveals=[SealedBidRevealRef("alice", "c1")],
    )

    assert [(decision.commitment, decision.bidder_id) for decision in outcome.decisions] == [
        ("c1", "alice"),
        ("c1", "bob"),
        ("c2", "carol"),
    ]
    assert [decision.refunded for decision in outcome.decisions] == [3, 0, 0]
    assert [decision.slashed for decision in outcome.decisions] == [0, 5, 7]


@pytest.mark.parametrize(
    "bond_amount,expect_error",
    [
        (0, True),
        (1, False),
        (0xFFFF, False),
        (0x10000, True),
    ],
)
def test_sealed_bid_bond_amount_bva(bond_amount: int, expect_error: bool) -> None:
    kwargs = {
        "commits": [BondedSealedBidCommit("alice", "c1", bond_amount)],
        "reveals": [],
    }
    if expect_error:
        with pytest.raises(ValueError, match="bond_amount out of range"):
            settle_sealed_bid_non_reveal_bonds(**kwargs)
    else:
        outcome = settle_sealed_bid_non_reveal_bonds(**kwargs)
        assert outcome.total_bonded == bond_amount
        assert outcome.total_slashed == bond_amount
        assert outcome.total_refunded == 0


def test_sealed_bid_bond_exhaustive_small_bva() -> None:
    bidder_ids = ["a", "b", "c"]
    checked = 0
    for commit_count in range(0, 4):
        commits = [BondedSealedBidCommit(bidder_ids[i], f"c{i}", bond_amount=((i % 3) + 1)) for i in range(commit_count)]
        max_mask = 1 << commit_count
        for mask in range(max_mask):
            reveals = [SealedBidRevealRef(bidder_ids[i], f"c{i}") for i in range(commit_count) if (mask >> i) & 1]
            outcome = settle_sealed_bid_non_reveal_bonds(commits=commits, reveals=reveals)
            expected_refunded = sum(commits[i].bond_amount for i in range(commit_count) if (mask >> i) & 1)
            expected_slashed = sum(commits[i].bond_amount for i in range(commit_count) if ((mask >> i) & 1) == 0)
            assert outcome.total_refunded == expected_refunded
            assert outcome.total_slashed == expected_slashed
            assert outcome.total_bonded == expected_refunded + expected_slashed
            checked += 1
    assert checked == 15
