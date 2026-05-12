"""Deterministic sealed-bid commit/reveal auction experiment.

This is a bounded UX-oriented primitive for private-state experiments:
- public commit receipts expose only a commitment, not bid size/price/nonce
- reveals are verified against the commitment
- settlement is deterministic and uniform-price for a fixed sell inventory

Scope is deliberately narrow and one-sided (buyers bid for a fixed inventory).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, Mapping, Tuple

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

MAX_UNITS = 0xFFFF
MAX_PRICE = 0xFFFF
_CHECKED_BATCH_TOKEN = object()


def _require_non_empty_str(value: object, error: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(error)
    return value


def _require_int_range(value: object, error: str, *, minimum: int, maximum: int) -> int:
    if (
        not isinstance(value, int)
        or isinstance(value, bool)
        or value < minimum
        or value > maximum
    ):
        raise ValueError(error)
    return int(value)


def _require_non_negative_int(value: object, error: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(error)
    return int(value)


@dataclass(frozen=True)
class RevealedSealedBid:
    bidder_id: str
    commitment: str
    quantity: int
    limit_price: int


@dataclass(frozen=True)
class SealedBidReveal:
    bidder_id: str
    commitment: str
    quantity: int
    limit_price: int
    nonce: str


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


@dataclass(frozen=True)
class CheckedSealedBidBatch:
    batch_id: str
    units_for_sale: int
    bids: tuple[RevealedSealedBid, ...]
    _token: object = field(repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._token is not _CHECKED_BATCH_TOKEN:
            raise ValueError("CheckedSealedBidBatch must be constructed by verifier")


def sealed_bid_reveal_hash(*, quantity: int, limit_price: int, nonce: str) -> str:
    quantity_int = _require_int_range(
        quantity,
        "quantity out of range",
        minimum=1,
        maximum=MAX_UNITS,
    )
    limit_price_int = _require_int_range(
        limit_price,
        "limit_price out of range",
        minimum=1,
        maximum=MAX_PRICE,
    )
    nonce_str = _require_non_empty_str(nonce, "nonce must be a non-empty string")
    body = {
        "schema": "zenodex/sealed_bid_reveal/v1",
        "quantity": quantity_int,
        "limit_price": limit_price_int,
        "nonce": nonce_str,
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
    batch_id_str = _require_non_empty_str(batch_id, "batch_id must be non-empty")
    bidder_id_str = _require_non_empty_str(bidder_id, "bidder_id must be non-empty")
    commitment_str = _require_non_empty_str(commitment, "commitment must be non-empty")
    commit_epoch_int = _require_non_negative_int(commit_epoch, "commit_epoch out of range")
    reveal_deadline_epoch_int = _require_non_negative_int(
        reveal_deadline_epoch,
        "reveal_deadline_epoch out of range",
    )
    if reveal_deadline_epoch_int < commit_epoch_int:
        raise ValueError("bad_epoch_window")
    units_for_sale_int = _require_int_range(
        units_for_sale,
        "units_for_sale out of range",
        minimum=0,
        maximum=MAX_UNITS,
    )
    body = {
        "schema": "zenodex/sealed_bid_commit/v1",
        "batch_id": batch_id_str,
        "bidder_id": bidder_id_str,
        "commitment": commitment_str,
        "commit_epoch": commit_epoch_int,
        "reveal_deadline_epoch": reveal_deadline_epoch_int,
        "units_for_sale": units_for_sale_int,
    }
    receipt_hash = sha256_hex(domain_sep_bytes("zenodex.sealed_bid_commit/v1") + canonical_json_bytes(body))
    return {"body": body, "receipt_hash": receipt_hash}


def verify_commit_receipt(receipt: Dict[str, Any]) -> Tuple[bool, str]:
    if not isinstance(receipt, dict):
        return False, "bad_receipt_type"
    body = receipt.get("body")
    if not isinstance(body, dict):
        return False, "missing_body"
    for key in ("quantity", "limit_price", "nonce"):
        if key in body:
            return False, f"private_field_leaked_{key}"
    allowed_body_keys = {
        "schema",
        "batch_id",
        "bidder_id",
        "commitment",
        "commit_epoch",
        "reveal_deadline_epoch",
        "units_for_sale",
    }
    for key in body:
        if key not in allowed_body_keys:
            return False, "unknown_commit_field"
    if body.get("schema") != "zenodex/sealed_bid_commit/v1":
        return False, "bad_schema"
    for key in ("batch_id", "bidder_id", "commitment"):
        val = body.get(key)
        if not isinstance(val, str) or not val:
            return False, f"bad_{key}"
    commit_epoch = body.get("commit_epoch")
    reveal_deadline_epoch = body.get("reveal_deadline_epoch")
    units_for_sale = body.get("units_for_sale")
    for value in (commit_epoch, reveal_deadline_epoch, units_for_sale):
        if not isinstance(value, int) or isinstance(value, bool):
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
    except Exception:
        return False


def _commit_body(receipt: Mapping[str, Any]) -> Mapping[str, Any]:
    receipt_dict = dict(receipt)
    ok, err = verify_commit_receipt(receipt_dict)
    if not ok:
        raise ValueError(err)
    body = receipt_dict.get("body")
    if not isinstance(body, Mapping):
        raise ValueError("missing_body")
    return body


def verify_sealed_bid_reveals_for_batch(
    *,
    batch_id: str,
    units_for_sale: int,
    commit_receipts: Iterable[Mapping[str, Any]],
    reveals: Iterable[SealedBidReveal],
    current_epoch: int | None = None,
) -> CheckedSealedBidBatch:
    """Verify reveal payloads against public commit receipts.

    This keeps the private auction execution path small: the uniform-price
    settler consumes only checked reveals whose commitment, batch, inventory,
    bidder, and nonce have already been bound.
    """

    if not isinstance(batch_id, str) or not batch_id:
        raise ValueError("batch_id must be non-empty")
    units_for_sale_int = _require_int_range(
        units_for_sale,
        "units_for_sale out of range",
        minimum=0,
        maximum=MAX_UNITS,
    )
    current_epoch_int: int | None = None
    if current_epoch is not None:
        current_epoch_int = _require_non_negative_int(
            current_epoch,
            "current_epoch must be a non-negative int",
        )

    commit_keys: set[tuple[str, str]] = set()
    commitments_seen: set[str] = set()
    commit_by_key: dict[tuple[str, str], Mapping[str, Any]] = {}
    for receipt in commit_receipts:
        if not isinstance(receipt, Mapping):
            raise ValueError("commit receipt must be an object")
        body = _commit_body(receipt)
        if str(body["batch_id"]) != batch_id:
            raise ValueError("commit_batch_mismatch")
        if int(body["units_for_sale"]) != units_for_sale_int:
            raise ValueError("commit_units_for_sale_mismatch")
        if current_epoch_int is not None and current_epoch_int > int(body["reveal_deadline_epoch"]):
            raise ValueError("reveal_deadline_passed")
        commitment = str(body["commitment"])
        key = (str(body["bidder_id"]), commitment)
        if key in commit_keys:
            raise ValueError("duplicate_commit_key")
        if commitment in commitments_seen:
            raise ValueError("duplicate_commitment")
        commit_keys.add(key)
        commitments_seen.add(commitment)
        commit_by_key[key] = body

    reveal_keys: set[tuple[str, str]] = set()
    checked: list[RevealedSealedBid] = []
    for reveal in reveals:
        if not isinstance(reveal, SealedBidReveal):
            raise ValueError("reveal must be a SealedBidReveal")
        if not isinstance(reveal.bidder_id, str) or not reveal.bidder_id:
            raise ValueError("reveal bidder_id must be non-empty")
        if not isinstance(reveal.commitment, str) or not reveal.commitment:
            raise ValueError("reveal commitment must be non-empty")
        if not isinstance(reveal.nonce, str) or not reveal.nonce:
            raise ValueError("reveal nonce must be non-empty")
        quantity = _require_int_range(
            reveal.quantity,
            "quantity out of range",
            minimum=1,
            maximum=MAX_UNITS,
        )
        limit_price = _require_int_range(
            reveal.limit_price,
            "limit_price out of range",
            minimum=1,
            maximum=MAX_PRICE,
        )
        key = (str(reveal.bidder_id), str(reveal.commitment))
        if key in reveal_keys:
            raise ValueError("duplicate_reveal_key")
        reveal_keys.add(key)
        if key not in commit_by_key:
            raise ValueError("reveal_without_commit")
        if not reveal_matches_commitment(
            commitment=str(reveal.commitment),
            quantity=quantity,
            limit_price=limit_price,
            nonce=str(reveal.nonce),
        ):
            raise ValueError("reveal_commitment_mismatch")
        checked.append(
            RevealedSealedBid(
                bidder_id=str(reveal.bidder_id),
                commitment=str(reveal.commitment),
                quantity=quantity,
                limit_price=limit_price,
            )
        )

    return CheckedSealedBidBatch(
        batch_id=batch_id,
        units_for_sale=units_for_sale_int,
        bids=tuple(sorted(checked, key=lambda bid: (str(bid.commitment), str(bid.bidder_id)))),
        _token=_CHECKED_BATCH_TOKEN,
    )


def settle_checked_uniform_price_sealed_bids(
    *,
    checked_batch: CheckedSealedBidBatch,
) -> SealedBidSettlement:
    if not isinstance(checked_batch, CheckedSealedBidBatch):
        raise ValueError("checked_batch must be a CheckedSealedBidBatch")
    return _settle_uniform_price_checked_bids(
        units_for_sale=checked_batch.units_for_sale,
        bids=checked_batch.bids,
    )


def settle_committed_uniform_price_sealed_bids(
    *,
    batch_id: str,
    units_for_sale: int,
    commit_receipts: Iterable[Mapping[str, Any]],
    reveals: Iterable[SealedBidReveal],
    current_epoch: int | None = None,
) -> SealedBidSettlement:
    checked_batch = verify_sealed_bid_reveals_for_batch(
        batch_id=batch_id,
        units_for_sale=units_for_sale,
        commit_receipts=commit_receipts,
        reveals=reveals,
        current_epoch=current_epoch,
    )
    return settle_checked_uniform_price_sealed_bids(checked_batch=checked_batch)


def _settle_uniform_price_checked_bids(
    *,
    units_for_sale: int,
    bids: Iterable[RevealedSealedBid],
) -> SealedBidSettlement:
    units_for_sale_int = _require_int_range(
        units_for_sale,
        "units_for_sale out of range",
        minimum=0,
        maximum=MAX_UNITS,
    )

    normalized: list[RevealedSealedBid] = []
    for bid in bids:
        if not isinstance(bid, RevealedSealedBid):
            raise ValueError("bid must be a RevealedSealedBid")
        if not isinstance(bid.bidder_id, str) or not bid.bidder_id:
            raise ValueError("bidder_id must be non-empty")
        if not isinstance(bid.commitment, str) or not bid.commitment:
            raise ValueError("commitment must be non-empty")
        quantity = _require_int_range(
            bid.quantity,
            "quantity out of range",
            minimum=1,
            maximum=MAX_UNITS,
        )
        limit_price = _require_int_range(
            bid.limit_price,
            "limit_price out of range",
            minimum=1,
            maximum=MAX_PRICE,
        )
        normalized.append(
            RevealedSealedBid(
                bidder_id=bid.bidder_id,
                commitment=bid.commitment,
                quantity=quantity,
                limit_price=limit_price,
            )
        )

    ordered = sorted(normalized, key=lambda b: (-int(b.limit_price), str(b.commitment), str(b.bidder_id)))
    remaining = units_for_sale_int
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
