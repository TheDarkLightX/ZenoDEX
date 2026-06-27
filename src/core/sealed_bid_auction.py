"""Deterministic sealed-bid commit/reveal auction experiment.

This is a bounded UX-oriented primitive for private-state experiments:
- public commit receipts expose only a commitment, not bid size/price/nonce
- reveals are verified against the commitment
- settlement is deterministic and uniform-price for a fixed sell inventory

Scope is deliberately narrow and one-sided (buyers bid for a fixed inventory).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Iterable, Tuple

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .domain_limits import is_strict_int

MAX_UNITS = 0xFFFF
MAX_PRICE = 0xFFFF


def _receipt_int(value: Any) -> int | None:
    if not is_strict_int(value):
        return None
    return value


@dataclass(frozen=True)
class RevealedSealedBid:
    bidder_id: str
    commitment: str
    quantity: int
    limit_price: int


@dataclass(frozen=True)
class SealedBidFill:
    bidder_id: str
    commitment: str
    filled_quantity: int
    paid_price: int


@dataclass(frozen=True)
class SealedBidSettlement:
    clearing_price: int
    total_filled: int
    fills: tuple[SealedBidFill, ...]


def sealed_bid_reveal_hash(*, quantity: int, limit_price: int, nonce: str) -> str:
    if not isinstance(quantity, int) or isinstance(quantity, bool) or quantity <= 0 or quantity > MAX_UNITS:
        raise ValueError("quantity out of range")
    if not isinstance(limit_price, int) or isinstance(limit_price, bool) or limit_price <= 0 or limit_price > MAX_PRICE:
        raise ValueError("limit_price out of range")
    if not isinstance(nonce, str) or not nonce:
        raise ValueError("nonce must be a non-empty string")
    body = {
        "schema": "zenodex/sealed_bid_reveal/v1",
        "quantity": int(quantity),
        "limit_price": int(limit_price),
        "nonce": str(nonce),
    }
    return sha256_hex(domain_sep_bytes("zenodex.sealed_bid_reveal/v1") + canonical_json_bytes(body))


def make_sealed_bid_commit_receipt(
    *,
    batch_id: str,
    bidder_id: str,
    commitment: str,
    commit_epoch: int,
    reveal_deadline_epoch: int,
    units_for_sale: int,
) -> Dict[str, Any]:
    if not isinstance(commitment, str) or not commitment:
        raise ValueError("commitment must be non-empty")
    body = {
        "schema": "zenodex/sealed_bid_commit/v1",
        "batch_id": str(batch_id),
        "bidder_id": str(bidder_id),
        "commitment": str(commitment),
        "commit_epoch": int(commit_epoch),
        "reveal_deadline_epoch": int(reveal_deadline_epoch),
        "units_for_sale": int(units_for_sale),
    }
    receipt_hash = sha256_hex(domain_sep_bytes("zenodex.sealed_bid_commit/v1") + canonical_json_bytes(body))
    return {"body": body, "receipt_hash": receipt_hash}


def verify_commit_receipt(receipt: Dict[str, Any]) -> Tuple[bool, str]:
    if not isinstance(receipt, dict):
        return False, "bad_receipt_type"
    body = receipt.get("body")
    if not isinstance(body, dict):
        return False, "missing_body"
    if body.get("schema") != "zenodex/sealed_bid_commit/v1":
        return False, "bad_schema"
    for key in ("batch_id", "bidder_id", "commitment"):
        val = body.get(key)
        if not isinstance(val, str) or not val:
            return False, f"bad_{key}"
    for key in ("quantity", "limit_price", "nonce"):
        if key in body:
            return False, f"private_field_leaked_{key}"
    commit_epoch = _receipt_int(body.get("commit_epoch"))
    reveal_deadline_epoch = _receipt_int(body.get("reveal_deadline_epoch"))
    units_for_sale = _receipt_int(body.get("units_for_sale"))
    if commit_epoch is None or reveal_deadline_epoch is None or units_for_sale is None:
        return False, "bad_numeric_field"
    if commit_epoch < 0 or reveal_deadline_epoch < commit_epoch:
        return False, "bad_epoch_window"
    if units_for_sale < 0 or units_for_sale > MAX_UNITS:
        return False, "bad_units_for_sale"
    want = receipt.get("receipt_hash")
    if not isinstance(want, str) or not want:
        return False, "missing_receipt_hash"
    got = sha256_hex(domain_sep_bytes("zenodex.sealed_bid_commit/v1") + canonical_json_bytes(body))
    if got != want:
        return False, "hash_mismatch"
    return True, "ok"


def reveal_matches_commitment(*, commitment: str, quantity: int, limit_price: int, nonce: str) -> bool:
    try:
        return str(commitment) == sealed_bid_reveal_hash(quantity=quantity, limit_price=limit_price, nonce=nonce)
    except (TypeError, ValueError, OverflowError):
        return False


def settle_uniform_price_sealed_bids(
    *,
    units_for_sale: int,
    bids: Iterable[RevealedSealedBid],
) -> SealedBidSettlement:
    if not isinstance(units_for_sale, int) or isinstance(units_for_sale, bool) or units_for_sale < 0 or units_for_sale > MAX_UNITS:
        raise ValueError("units_for_sale out of range")

    normalized: list[RevealedSealedBid] = []
    for bid in bids:
        if not isinstance(bid.bidder_id, str) or not bid.bidder_id:
            raise ValueError("bidder_id must be non-empty")
        if not isinstance(bid.commitment, str) or not bid.commitment:
            raise ValueError("commitment must be non-empty")
        if not isinstance(bid.quantity, int) or isinstance(bid.quantity, bool) or bid.quantity <= 0 or bid.quantity > MAX_UNITS:
            raise ValueError("quantity out of range")
        if not isinstance(bid.limit_price, int) or isinstance(bid.limit_price, bool) or bid.limit_price <= 0 or bid.limit_price > MAX_PRICE:
            raise ValueError("limit_price out of range")
        normalized.append(bid)

    ordered = sorted(normalized, key=lambda b: (-int(b.limit_price), str(b.commitment), str(b.bidder_id)))
    remaining = int(units_for_sale)
    fills: list[SealedBidFill] = []
    clearing_price = 0
    total_filled = 0
    for bid in ordered:
        if remaining <= 0:
            break
        fill_qty = min(int(bid.quantity), remaining)
        if fill_qty <= 0:
            continue
        clearing_price = int(bid.limit_price)
        total_filled += int(fill_qty)
        remaining -= int(fill_qty)
        fills.append(
            SealedBidFill(
                bidder_id=str(bid.bidder_id),
                commitment=str(bid.commitment),
                filled_quantity=int(fill_qty),
                paid_price=0,
            )
        )

    if clearing_price > 0:
        fills = [
            SealedBidFill(
                bidder_id=f.bidder_id,
                commitment=f.commitment,
                filled_quantity=int(f.filled_quantity),
                paid_price=int(clearing_price),
            )
            for f in fills
        ]

    return SealedBidSettlement(
        clearing_price=int(clearing_price),
        total_filled=int(total_filled),
        fills=tuple(fills),
    )
