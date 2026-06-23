"""Deterministic non-reveal bond accounting for sealed-bid auctions."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

MAX_BOND = 0xFFFF


@dataclass(frozen=True)
class BondedSealedBidCommit:
    bidder_id: str
    commitment: str
    bond_amount: int


@dataclass(frozen=True)
class SealedBidRevealRef:
    bidder_id: str
    commitment: str


@dataclass(frozen=True)
class SealedBidBondDecision:
    bidder_id: str
    commitment: str
    bond_amount: int
    refunded: int
    slashed: int


@dataclass(frozen=True)
class SealedBidBondOutcome:
    total_bonded: int
    total_refunded: int
    total_slashed: int
    refunded_bid_count: int
    slashed_bid_count: int
    decisions: tuple[SealedBidBondDecision, ...]


def settle_sealed_bid_non_reveal_bonds(
    *,
    commits: Iterable[BondedSealedBidCommit],
    reveals: Iterable[SealedBidRevealRef],
) -> SealedBidBondOutcome:
    normalized_commits: list[BondedSealedBidCommit] = []
    seen_commit_keys: set[tuple[str, str]] = set()
    for commit in commits:
        if not isinstance(commit.bidder_id, str) or not commit.bidder_id:
            raise ValueError("bidder_id must be non-empty")
        if not isinstance(commit.commitment, str) or not commit.commitment:
            raise ValueError("commitment must be non-empty")
        if not isinstance(commit.bond_amount, int) or isinstance(commit.bond_amount, bool) or commit.bond_amount <= 0 or commit.bond_amount > MAX_BOND:
            raise ValueError("bond_amount out of range")
        key = (str(commit.bidder_id), str(commit.commitment))
        if key in seen_commit_keys:
            raise ValueError("duplicate_commit_key")
        seen_commit_keys.add(key)
        normalized_commits.append(commit)

    reveal_keys: set[tuple[str, str]] = set()
    for reveal in reveals:
        if not isinstance(reveal.bidder_id, str) or not reveal.bidder_id:
            raise ValueError("reveal bidder_id must be non-empty")
        if not isinstance(reveal.commitment, str) or not reveal.commitment:
            raise ValueError("reveal commitment must be non-empty")
        key = (str(reveal.bidder_id), str(reveal.commitment))
        if key in reveal_keys:
            raise ValueError("duplicate_reveal_key")
        reveal_keys.add(key)

    unknown_reveals = sorted(key for key in reveal_keys if key not in seen_commit_keys)
    if unknown_reveals:
        raise ValueError("reveal_without_commit")

    decisions: list[SealedBidBondDecision] = []
    total_bonded = 0
    total_refunded = 0
    total_slashed = 0
    refunded_bid_count = 0
    slashed_bid_count = 0

    ordered = sorted(normalized_commits, key=lambda c: (str(c.commitment), str(c.bidder_id)))
    for commit in ordered:
        key = (str(commit.bidder_id), str(commit.commitment))
        revealed = key in reveal_keys
        refunded = int(commit.bond_amount) if revealed else 0
        slashed = 0 if revealed else int(commit.bond_amount)
        decisions.append(
            SealedBidBondDecision(
                bidder_id=str(commit.bidder_id),
                commitment=str(commit.commitment),
                bond_amount=int(commit.bond_amount),
                refunded=int(refunded),
                slashed=int(slashed),
            )
        )
        total_bonded += int(commit.bond_amount)
        total_refunded += int(refunded)
        total_slashed += int(slashed)
        refunded_bid_count += int(1 if revealed else 0)
        slashed_bid_count += int(0 if revealed else 1)

    return SealedBidBondOutcome(
        total_bonded=int(total_bonded),
        total_refunded=int(total_refunded),
        total_slashed=int(total_slashed),
        refunded_bid_count=int(refunded_bid_count),
        slashed_bid_count=int(slashed_bid_count),
        decisions=tuple(decisions),
    )
