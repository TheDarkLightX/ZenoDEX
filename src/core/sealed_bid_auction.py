"""Deterministic sealed-bid commit/reveal auction experiment.

This is a bounded UX-oriented primitive for private-state experiments:
- public commit receipts expose only a commitment, not bid size/price/nonce
- reveals are verified against the commitment
- settlement is deterministic and uniform-price for a fixed sell inventory

Scope is deliberately narrow and one-sided (buyers bid for a fixed inventory).
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import groupby
from typing import Any, Dict, Iterable, Tuple

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

MAX_UNITS = 0xFFFF
MAX_PRICE = 0xFFFF


def _receipt_int(value: Any) -> int:
    if isinstance(value, bool):
        raise TypeError("bool is not a sealed-bid receipt integer")
    if not isinstance(value, int):
        raise TypeError("sealed-bid receipt integer must be an int")
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
        "commit_epoch": _receipt_int(commit_epoch),
        "reveal_deadline_epoch": _receipt_int(reveal_deadline_epoch),
        "units_for_sale": _receipt_int(units_for_sale),
    }
    receipt_hash = sha256_hex(domain_sep_bytes("zenodex.sealed_bid_commit/v1") + canonical_json_bytes(body))
    return {"body": body, "receipt_hash": receipt_hash}


def verify_commit_receipt(receipt: object) -> Tuple[bool, str]:
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
    try:
        commit_epoch = _receipt_int(body.get("commit_epoch"))
        reveal_deadline_epoch = _receipt_int(body.get("reveal_deadline_epoch"))
        units_for_sale = _receipt_int(body.get("units_for_sale"))
    except (TypeError, ValueError, OverflowError):
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
    except ValueError:
        return False


def _sealed_bid_output_key(bid: RevealedSealedBid) -> tuple[str, str]:
    return (str(bid.bidder_id), str(bid.commitment))


def _validate_revealed_bid(bid: RevealedSealedBid) -> RevealedSealedBid:
    if not isinstance(bid.bidder_id, str) or not bid.bidder_id:
        raise ValueError("bidder_id must be non-empty")
    if not isinstance(bid.commitment, str) or not bid.commitment:
        raise ValueError("commitment must be non-empty")
    if not isinstance(bid.quantity, int) or isinstance(bid.quantity, bool) or bid.quantity <= 0 or bid.quantity > MAX_UNITS:
        raise ValueError("quantity out of range")
    if (
        not isinstance(bid.limit_price, int)
        or isinstance(bid.limit_price, bool)
        or bid.limit_price <= 0
        or bid.limit_price > MAX_PRICE
    ):
        raise ValueError("limit_price out of range")
    return bid


def _pro_rata_marginal_bucket(
    *, remaining: int, bucket: tuple[RevealedSealedBid, ...]
) -> tuple[tuple[tuple[RevealedSealedBid, int], ...], int]:
    """Allocate an oversubscribed same-price bucket by largest remainder."""
    total_requested = sum(int(bid.quantity) for bid in bucket)
    if remaining <= 0 or total_requested <= 0:
        return (), 0

    allocations: list[tuple[int, RevealedSealedBid, int, int]] = []
    allocated = 0
    for index, bid in enumerate(bucket):
        numerator = int(bid.quantity) * int(remaining)
        base = numerator // total_requested
        remainder = numerator % total_requested
        allocated += base
        allocations.append((index, bid, int(base), int(remainder)))

    leftover = int(remaining) - int(allocated)
    if leftover > 0:
        ranked = sorted(allocations, key=lambda item: (-item[3], _sealed_bid_output_key(item[1]), item[0]))
        bonus_indices = {item[0] for item in ranked[:leftover]}
    else:
        bonus_indices = set()

    result = []
    total = 0
    for index, bid, base, _remainder in allocations:
        fill_qty = int(base) + (1 if index in bonus_indices else 0)
        if fill_qty <= 0:
            continue
        result.append((bid, fill_qty))
        total += fill_qty
    return tuple(result), int(total)


def settle_uniform_price_sealed_bids(
    *,
    units_for_sale: int,
    bids: Iterable[RevealedSealedBid],
) -> SealedBidSettlement:
    if not isinstance(units_for_sale, int) or isinstance(units_for_sale, bool) or units_for_sale < 0 or units_for_sale > MAX_UNITS:
        raise ValueError("units_for_sale out of range")

    normalized = [_validate_revealed_bid(bid) for bid in bids]

    remaining = int(units_for_sale)
    fill_entries: list[tuple[RevealedSealedBid, int]] = []
    clearing_price = 0
    total_filled = 0

    ordered = tuple(sorted(normalized, key=lambda bid: (-int(bid.limit_price), _sealed_bid_output_key(bid))))
    for price, group in groupby(ordered, key=lambda bid: int(bid.limit_price)):
        if remaining <= 0:
            break
        bucket = tuple(group)
        bucket_quantity = sum(int(bid.quantity) for bid in bucket)
        if bucket_quantity <= 0:
            continue

        clearing_price = int(price)
        if bucket_quantity <= remaining:
            fill_entries.extend((bid, int(bid.quantity)) for bid in bucket)
            total_filled += int(bucket_quantity)
            remaining -= int(bucket_quantity)
            continue

        marginal_fills, marginal_total = _pro_rata_marginal_bucket(remaining=remaining, bucket=bucket)
        fill_entries.extend(marginal_fills)
        total_filled += int(marginal_total)
        remaining = 0

    fills = tuple(
        SealedBidFill(
            bidder_id=str(bid.bidder_id),
            commitment=str(bid.commitment),
            filled_quantity=int(fill_qty),
            paid_price=int(clearing_price) if clearing_price > 0 else 0,
        )
        for bid, fill_qty in sorted(fill_entries, key=lambda item: (-int(item[0].limit_price), _sealed_bid_output_key(item[0])))
    )

    return SealedBidSettlement(
        clearing_price=int(clearing_price),
        total_filled=int(total_filled),
        fills=fills,
    )
