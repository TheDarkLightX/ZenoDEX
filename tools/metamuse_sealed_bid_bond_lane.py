from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from src.core.sealed_bid_bonds import (
    BondedSealedBidCommit,
    SealedBidRevealRef,
    settle_sealed_bid_non_reveal_bonds,
)


@dataclass(frozen=True)
class BondLaneCommit:
    bidder_id: str
    commitment: str
    bond_amount: int

    def to_json(self) -> dict[str, Any]:
        return {
            "bidder_id": str(self.bidder_id),
            "commitment": str(self.commitment),
            "bond_amount": int(self.bond_amount),
        }


@dataclass(frozen=True)
class BondLaneCase:
    commits: tuple[BondLaneCommit, ...]
    reveals: tuple[tuple[str, str], ...]
    expected_refunded: int
    expected_slashed: int
    expected_refund_count: int
    expected_slash_count: int

    def to_json(self) -> dict[str, Any]:
        return {
            "commits": [c.to_json() for c in self.commits],
            "reveals": [
                {"bidder_id": str(bidder_id), "commitment": str(commitment)}
                for bidder_id, commitment in self.reveals
            ],
            "expected_refunded": int(self.expected_refunded),
            "expected_slashed": int(self.expected_slashed),
            "expected_refund_count": int(self.expected_refund_count),
            "expected_slash_count": int(self.expected_slash_count),
        }


SEALED_BID_BOND_CURATED_CASES: tuple[BondLaneCase, ...] = (
    BondLaneCase(
        commits=(
            BondLaneCommit("alice", "c1", 5),
            BondLaneCommit("bob", "c2", 5),
            BondLaneCommit("carol", "c3", 5),
        ),
        reveals=(("alice", "c1"), ("bob", "c2")),
        expected_refunded=10,
        expected_slashed=5,
        expected_refund_count=2,
        expected_slash_count=1,
    ),
    BondLaneCase(
        commits=(
            BondLaneCommit("alice", "d1", 7),
            BondLaneCommit("bob", "d2", 7),
        ),
        reveals=tuple(),
        expected_refunded=0,
        expected_slashed=14,
        expected_refund_count=0,
        expected_slash_count=2,
    ),
    BondLaneCase(
        commits=(
            BondLaneCommit("alice", "e1", 3),
        ),
        reveals=(("alice", "e1"),),
        expected_refunded=3,
        expected_slashed=0,
        expected_refund_count=1,
        expected_slash_count=0,
    ),
)


STIMULI_BANK: tuple[dict[str, Any], ...] = (
    {
        "stimulus_id": "auction.griefing_bond",
        "family": "adversarial_game",
        "prompt": "If users can commit and disappear for free, they can jam the auction. What deterministic bond rule removes free non-reveal griefing?",
        "design_shift": "Refund revealed bids, slash unrevealed bids one-for-one.",
    },
    {
        "stimulus_id": "accounting.conservation",
        "family": "potential_function",
        "prompt": "How do we keep the bond pool auditable under refunds and slashes?",
        "design_shift": "Track exact bonded = refunded + slashed conservation.",
    },
    {
        "stimulus_id": "ux.fail_closed",
        "family": "control",
        "prompt": "Which edge cases should reject outright instead of silently guessing?",
        "design_shift": "Reject duplicate commits, duplicate reveals, and reveal-without-commit.",
    },
)


LANE_SPEC: dict[str, Any] = {
    "lane_id": "sealed_bid_non_reveal_bond_v1",
    "title": "Sealed Bid Non-Reveal Bond",
    "representation": "bonded commit/reveal accounting",
    "abstraction_level": "bounded griefing-defense experiment",
    "goal": "eliminate free non-reveal griefing while preserving deterministic bond conservation",
    "obligations": [
        "revealed bids refund exactly their bond",
        "unrevealed bids are fully slashed",
        "bond conservation holds exactly",
    ],
    "invariants": [
        "total bonded = total refunded + total slashed",
        "unknown or duplicate reveals fail closed",
        "duplicate commit keys fail closed",
    ],
    "baseline_families": [
        {
            "name": "no_bond_commit_reveal",
            "why": "simplest sealed-bid UX",
            "failure_mode": "non-reveal griefing is free",
        },
        {
            "name": "manual_offchain_reputation",
            "why": "operational fallback for trusted small groups",
            "failure_mode": "not credibly neutral or automatic",
        },
    ],
    "reformulation_axes": [
        "economic penalty instead of social enforcement",
        "exact accounting instead of heuristic fines",
        "per-commit bond with deterministic refund/slash outcome",
    ],
    "performance_descriptors": {
        "asymptotic_profile": "O(n log n) by deterministic sort over commits",
        "invariant_family": ["bond_conservation", "no_free_non_reveal", "fail_closed_duplicates"],
        "failure_envelope": ["duplicate_commit", "duplicate_reveal", "reveal_without_commit"],
        "certificate_shape": ["curated_bond_corpus", "small_exhaustive_enumeration"],
    },
    "stimulus_ids": ["auction.griefing_bond", "accounting.conservation", "ux.fail_closed"],
    "hypotheses": [
        {
            "hypothesis_id": "sealed_bid_non_reveal_bond_v1",
            "mechanism_change": "Require a per-commit bond and refund it only on reveal; slash it otherwise.",
            "representation_shift_used": "restrict",
            "expected_metric_delta": [3, 1, 2, 0, 2],
            "null_hypothesis": "Bond accounting leaks value or still permits a free non-reveal path in bounded cases.",
            "falsification_recipe": "sealed_bid_bond_surface_safe",
            "support_recipe": "sealed_bid_bond_exhaustive_small",
            "formal_obligations": [
                "refund/slash totals equal total bonded",
                "unknown or duplicate reveals reject",
                "every unrevealed commitment is slashed",
            ],
            "risk_modes": ["bond too small for external damage", "strategic reveal timing around deadlines"],
            "status": "proposed",
        }
    ],
}


def verify_bond_case(case: BondLaneCase) -> tuple[bool, dict[str, Any]]:
    outcome = settle_sealed_bid_non_reveal_bonds(
        commits=[BondedSealedBidCommit(c.bidder_id, c.commitment, c.bond_amount) for c in case.commits],
        reveals=[SealedBidRevealRef(bidder_id, commitment) for bidder_id, commitment in case.reveals],
    )
    ok = (
        int(outcome.total_refunded) == int(case.expected_refunded)
        and int(outcome.total_slashed) == int(case.expected_slashed)
        and int(outcome.refunded_bid_count) == int(case.expected_refund_count)
        and int(outcome.slashed_bid_count) == int(case.expected_slash_count)
        and int(outcome.total_bonded) == int(outcome.total_refunded + outcome.total_slashed)
    )
    return ok, {
        "total_bonded": int(outcome.total_bonded),
        "total_refunded": int(outcome.total_refunded),
        "total_slashed": int(outcome.total_slashed),
        "refunded_bid_count": int(outcome.refunded_bid_count),
        "slashed_bid_count": int(outcome.slashed_bid_count),
    }


def lane_packet() -> dict[str, Any]:
    return {
        **LANE_SPEC,
        "stimuli": [stim for stim in STIMULI_BANK if stim["stimulus_id"] in set(LANE_SPEC["stimulus_ids"])],
        "curated_corpus": [case.to_json() for case in SEALED_BID_BOND_CURATED_CASES],
    }
