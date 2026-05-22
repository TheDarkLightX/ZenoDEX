from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from src.core.sealed_bid_auction import (
    RevealedSealedBid,
    make_sealed_bid_commit_receipt,
    reveal_matches_commitment,
    sealed_bid_reveal_hash,
    settle_uniform_price_sealed_bids,
    verify_commit_receipt,
)


@dataclass(frozen=True)
class SealedBidLaneBid:
    bidder_id: str
    quantity: int
    limit_price: int
    nonce: str

    @property
    def commitment(self) -> str:
        return sealed_bid_reveal_hash(quantity=self.quantity, limit_price=self.limit_price, nonce=self.nonce)

    def to_json(self) -> dict[str, Any]:
        return {
            "bidder_id": str(self.bidder_id),
            "quantity": int(self.quantity),
            "limit_price": int(self.limit_price),
            "commitment": str(self.commitment),
        }


@dataclass(frozen=True)
class SealedBidLaneCase:
    batch_id: str
    units_for_sale: int
    bids: tuple[SealedBidLaneBid, ...]
    expected_clearing_price: int
    expected_fill_vector: tuple[tuple[str, int], ...]

    def to_json(self) -> dict[str, Any]:
        return {
            "batch_id": str(self.batch_id),
            "units_for_sale": int(self.units_for_sale),
            "bids": [b.to_json() for b in self.bids],
            "expected_clearing_price": int(self.expected_clearing_price),
            "expected_fill_vector": [
                {"bidder_id": str(bidder_id), "filled_quantity": int(filled_quantity)}
                for bidder_id, filled_quantity in self.expected_fill_vector
            ],
        }


SEALED_BID_CURATED_CASES: tuple[SealedBidLaneCase, ...] = (
    SealedBidLaneCase(
        batch_id="batch-sb-1",
        units_for_sale=10,
        bids=(
            SealedBidLaneBid("alice", 4, 105, "n1"),
            SealedBidLaneBid("bob", 5, 103, "n2"),
            SealedBidLaneBid("carol", 7, 100, "n3"),
            SealedBidLaneBid("dave", 2, 98, "n4"),
        ),
        expected_clearing_price=100,
        expected_fill_vector=(("alice", 4), ("bob", 5), ("carol", 1)),
    ),
    SealedBidLaneCase(
        batch_id="batch-sb-2",
        units_for_sale=5,
        bids=(
            SealedBidLaneBid("alice", 3, 110, "m1"),
            SealedBidLaneBid("bob", 4, 110, "m2"),
            SealedBidLaneBid("carol", 4, 108, "m3"),
        ),
        expected_clearing_price=110,
        expected_fill_vector=(("bob", 4), ("alice", 1)),
    ),
)


STIMULI_BANK: tuple[dict[str, Any], ...] = (
    {
        "stimulus_id": "auction.commit_reveal",
        "family": "adversarial_game",
        "prompt": "If bids leak before the deadline, users must shade or delay. What is the minimum commit/reveal surface that hides price and size until reveal?",
        "design_shift": "Use public commitment receipts and delay price/size revelation until the reveal phase.",
    },
    {
        "stimulus_id": "auction.uniform_price",
        "family": "market",
        "prompt": "Which deterministic rule gives users one-shot bidding UX while reducing timing games?",
        "design_shift": "Uniform-price settlement with deterministic tie-breaks on commitment.",
    },
    {
        "stimulus_id": "privacy.public_surface",
        "family": "certificate",
        "prompt": "Which fields must stay off the public commit receipt to preserve sealed-bid UX while still enabling audits?",
        "design_shift": "Keep quantity, limit price, and nonce out of the commit receipt body.",
    },
)


LANE_SPEC: dict[str, Any] = {
    "lane_id": "sealed_bid_private_state_v1",
    "title": "Sealed Bid Private State",
    "representation": "commit/reveal one-sided uniform-price auction",
    "abstraction_level": "bounded UX experiment with deterministic settlement and public commitments",
    "goal": "hide bid size and price until reveal while keeping settlement deterministic and auditable",
    "obligations": [
        "public commit receipts must not leak quantity, limit price, or nonce",
        "reveals must bind to prior commitments",
        "settlement must be deterministic under input reordering",
    ],
    "invariants": [
        "highest limit prices fill first",
        "all accepted bids pay the same clearing price",
        "commit receipts expose commitments only, not private bid state",
    ],
    "baseline_families": [
        {
            "name": "open_orderbook_batch",
            "why": "default public UX exposes bid size and price immediately",
            "failure_mode": "information leakage invites undercutting and timing games",
        },
        {
            "name": "private_rfq_offchain",
            "why": "common way to hide quotes before matching",
            "failure_mode": "less publicly auditable and harder to replay deterministically",
        },
    ],
    "reformulation_axes": [
        "commit/reveal instead of open bidding",
        "uniform price instead of continuous undercutting",
        "public commitment receipts plus deterministic reveal settlement",
    ],
    "performance_descriptors": {
        "asymptotic_profile": "O(n log n) settlement after O(1) commitment verification per bid",
        "invariant_family": ["private_commit_surface", "commit_reveal_binding", "uniform_price_determinism"],
        "failure_envelope": ["late_reveal", "mismatched_commitment", "public_field_leakage"],
        "certificate_shape": ["curated_commit_reveal_corpus", "deterministic_fill_vector"],
    },
    "stimulus_ids": ["auction.commit_reveal", "auction.uniform_price", "privacy.public_surface"],
    "hypotheses": [
        {
            "hypothesis_id": "sealed_bid_private_state_v1",
            "mechanism_change": "Replace open bid disclosure with commitment receipts and deterministic uniform-price reveal settlement.",
            "representation_shift_used": "restrict",
            "expected_metric_delta": [2, 1, 3, 0, 2],
            "null_hypothesis": "The commit surface leaks bid state or the reveal settlement is not deterministic on the curated corpus.",
            "falsification_recipe": "sealed_bid_private_state_surface_safe",
            "support_recipe": "sealed_bid_uniform_price_model",
            "formal_obligations": [
                "commit receipts omit quantity, limit price, and nonce",
                "reveal binds to commitment",
                "deterministic clearing price and fill vector for fixed inputs",
            ],
            "risk_modes": ["griefing via non-reveal", "thin liquidity in small batches"],
            "status": "proposed",
        }
    ],
}


def verify_sealed_bid_case(case: SealedBidLaneCase) -> tuple[bool, dict[str, Any]]:
    receipts = []
    revealed = []
    for bid in case.bids:
        receipt = make_sealed_bid_commit_receipt(
            batch_id=case.batch_id,
            bidder_id=bid.bidder_id,
            commitment=bid.commitment,
            commit_epoch=1,
            reveal_deadline_epoch=2,
            units_for_sale=case.units_for_sale,
        )
        ok, err = verify_commit_receipt(receipt)
        if not ok:
            return False, {"reason": err, "bidder_id": bid.bidder_id}
        if not reveal_matches_commitment(
            commitment=bid.commitment,
            quantity=bid.quantity,
            limit_price=bid.limit_price,
            nonce=bid.nonce,
        ):
            return False, {"reason": "reveal_mismatch", "bidder_id": bid.bidder_id}
        receipts.append(receipt)
        revealed.append(RevealedSealedBid(bidder_id=bid.bidder_id, commitment=bid.commitment, quantity=bid.quantity, limit_price=bid.limit_price))

    settlement = settle_uniform_price_sealed_bids(units_for_sale=case.units_for_sale, bids=revealed)
    fill_vector = tuple((fill.bidder_id, int(fill.filled_quantity)) for fill in settlement.fills)
    ok = int(settlement.clearing_price) == int(case.expected_clearing_price) and fill_vector == case.expected_fill_vector
    return ok, {
        "clearing_price": int(settlement.clearing_price),
        "fill_vector": list(fill_vector),
        "expected_clearing_price": int(case.expected_clearing_price),
        "expected_fill_vector": list(case.expected_fill_vector),
        "receipt_count": len(receipts),
    }


def lane_packet() -> dict[str, Any]:
    return {
        **LANE_SPEC,
        "stimuli": [stim for stim in STIMULI_BANK if stim["stimulus_id"] in set(LANE_SPEC["stimulus_ids"])],
        "curated_corpus": [case.to_json() for case in SEALED_BID_CURATED_CASES],
    }
