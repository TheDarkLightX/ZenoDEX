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


def _commit_key_from_parts(*, bidder_id: str, commitment: str) -> tuple[str, str]:
    return (str(bidder_id), str(commitment))


def _validate_bond_amount(bond_amount: int) -> None:
    if (
        not isinstance(bond_amount, int)
        or isinstance(bond_amount, bool)
        or bond_amount <= 0
        or bond_amount > MAX_BOND
    ):
        raise ValueError("bond_amount out of range")


def _normalize_commits(
    commits: Iterable[BondedSealedBidCommit],
) -> tuple[list[BondedSealedBidCommit], set[tuple[str, str]]]:
    normalized_commits: list[BondedSealedBidCommit] = []
    seen_commit_keys: set[tuple[str, str]] = set()
    for commit in commits:
        if not isinstance(commit.bidder_id, str) or not commit.bidder_id:
            raise ValueError("bidder_id must be non-empty")
        if not isinstance(commit.commitment, str) or not commit.commitment:
            raise ValueError("commitment must be non-empty")
        _validate_bond_amount(commit.bond_amount)
        key = _commit_key_from_parts(
            bidder_id=commit.bidder_id,
            commitment=commit.commitment,
        )
        if key in seen_commit_keys:
            raise ValueError("duplicate_commit_key")
        seen_commit_keys.add(key)
        normalized_commits.append(commit)
    return normalized_commits, seen_commit_keys


def _collect_reveal_keys(reveals: Iterable[SealedBidRevealRef]) -> set[tuple[str, str]]:
    reveal_keys: set[tuple[str, str]] = set()
    for reveal in reveals:
        if not isinstance(reveal.bidder_id, str) or not reveal.bidder_id:
            raise ValueError("reveal bidder_id must be non-empty")
        if not isinstance(reveal.commitment, str) or not reveal.commitment:
            raise ValueError("reveal commitment must be non-empty")
        key = _commit_key_from_parts(
            bidder_id=reveal.bidder_id,
            commitment=reveal.commitment,
        )
        if key in reveal_keys:
            raise ValueError("duplicate_reveal_key")
        reveal_keys.add(key)
    return reveal_keys


def _reject_unknown_reveals(
    *,
    reveal_keys: set[tuple[str, str]],
    seen_commit_keys: set[tuple[str, str]],
) -> None:
    unknown_reveals = sorted(key for key in reveal_keys if key not in seen_commit_keys)
    if unknown_reveals:
        raise ValueError("reveal_without_commit")


def _bond_decision(
    *, commit: BondedSealedBidCommit, reveal_keys: set[tuple[str, str]]
) -> SealedBidBondDecision:
    key = _commit_key_from_parts(
        bidder_id=commit.bidder_id,
        commitment=commit.commitment,
    )
    revealed = key in reveal_keys
    refunded = int(commit.bond_amount) if revealed else 0
    slashed = 0 if revealed else int(commit.bond_amount)
    return SealedBidBondDecision(
        bidder_id=str(commit.bidder_id),
        commitment=str(commit.commitment),
        bond_amount=int(commit.bond_amount),
        refunded=int(refunded),
        slashed=int(slashed),
    )


def _build_bond_outcome(decisions: list[SealedBidBondDecision]) -> SealedBidBondOutcome:
    total_bonded = sum(decision.bond_amount for decision in decisions)
    total_refunded = sum(decision.refunded for decision in decisions)
    total_slashed = sum(decision.slashed for decision in decisions)
    refunded_bid_count = sum(1 for decision in decisions if decision.refunded)
    slashed_bid_count = sum(1 for decision in decisions if decision.slashed)
    return SealedBidBondOutcome(
        total_bonded=int(total_bonded),
        total_refunded=int(total_refunded),
        total_slashed=int(total_slashed),
        refunded_bid_count=int(refunded_bid_count),
        slashed_bid_count=int(slashed_bid_count),
        decisions=tuple(decisions),
    )


def settle_sealed_bid_non_reveal_bonds(
    *,
    commits: Iterable[BondedSealedBidCommit],
    reveals: Iterable[SealedBidRevealRef],
) -> SealedBidBondOutcome:
    normalized_commits, seen_commit_keys = _normalize_commits(commits)
    reveal_keys = _collect_reveal_keys(reveals)
    _reject_unknown_reveals(
        reveal_keys=reveal_keys,
        seen_commit_keys=seen_commit_keys,
    )

    ordered = sorted(normalized_commits, key=lambda c: (str(c.commitment), str(c.bidder_id)))
    decisions = [_bond_decision(commit=commit, reveal_keys=reveal_keys) for commit in ordered]
    return _build_bond_outcome(decisions)
