"""Experimental FHE sealed-bid alpha planner.

This module does not implement FHE cryptography.
It provides a deterministic, fail-closed planning surface for a very small
sealed-bid auction lane that could be backed by an external FHE stack such as
Zama's FHEVM.

Design constraints:
- alpha only: max 8 bids
- one-sided uniform-price auction
- euint32-style arithmetic budget assumptions
- async decryption only
- explicit fallback to commit/reveal
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Iterable, Tuple

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .domain_limits import is_strict_int
from .sealed_bid_auction import (
    MAX_PRICE,
    RevealedSealedBid,
    SealedBidSettlement,
    settle_uniform_price_sealed_bids,
)

MAX_ALPHA_BIDS = 8
MAX_ALPHA_UNITS = 63
MAX_ALPHA_DECRYPT_OUTPUTS = MAX_ALPHA_BIDS + 2
ZAMA_DEVNET_HCU_TX_CAP = 20_000_000
ZAMA_DEVNET_HCU_DEPTH_CAP = 5_000_000

# Conservative euint32 HCU posture derived from current public Zama docs.
EUINT32_COMPARE_HCU = 118_000
EUINT32_SELECT_HCU = 55_000
EUINT32_ADD_HCU = 125_000


def _receipt_int(value: Any) -> int | None:
    if not is_strict_int(value):
        return None
    return value


@dataclass(frozen=True)
class FHECipherBid:
    bidder_id: str
    commitment: str
    quantity_handle: str
    price_handle: str


@dataclass(frozen=True)
class FHEOperationEstimate:
    bid_count: int
    compare_ops: int
    select_ops: int
    add_ops: int
    sort_layers: int
    decrypt_outputs: int
    estimated_hcu: int
    estimated_depth_hcu: int


def fhe_sealed_bid_alpha_receipt_hash(body: Dict[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes("zenodex.fhe_sealed_bid_alpha_plan/v1") + canonical_json_bytes(body))


def _next_power_of_two(value: int) -> int:
    n = 1
    while n < value:
        n <<= 1
    return n


def _bitonic_sort_comparator_upper_bound(bid_count: int) -> tuple[int, int]:
    if bid_count <= 1:
        return 0, 0
    n = _next_power_of_two(int(bid_count))
    log_n = n.bit_length() - 1
    comparators = (n * log_n * (log_n + 1)) // 4
    layers = (log_n * (log_n + 1)) // 2
    return int(comparators), int(layers)


def _validate_cipher_bids(cipher_bids: Iterable[FHECipherBid]) -> tuple[FHECipherBid, ...]:
    normalized: list[FHECipherBid] = []
    seen_commit_keys: set[tuple[str, str]] = set()
    seen_handles: set[str] = set()
    for bid in cipher_bids:
        if not isinstance(bid.bidder_id, str) or not bid.bidder_id:
            raise ValueError("bidder_id must be non-empty")
        if not isinstance(bid.commitment, str) or not bid.commitment:
            raise ValueError("commitment must be non-empty")
        for handle, name in ((bid.quantity_handle, "quantity_handle"), (bid.price_handle, "price_handle")):
            if not isinstance(handle, str) or not handle:
                raise ValueError(f"{name} must be non-empty")
            if handle in seen_handles:
                raise ValueError("duplicate_cipher_handle")
            seen_handles.add(handle)
        key = (str(bid.bidder_id), str(bid.commitment))
        if key in seen_commit_keys:
            raise ValueError("duplicate_commit_key")
        seen_commit_keys.add(key)
        normalized.append(bid)
    return tuple(normalized)


def estimate_fhe_uniform_price_ops(*, bid_count: int, decrypt_outputs: int | None = None) -> FHEOperationEstimate:
    if not isinstance(bid_count, int) or isinstance(bid_count, bool) or bid_count <= 0 or bid_count > MAX_ALPHA_BIDS:
        raise ValueError("bid_count out of range")
    effective_decrypt_outputs = int(bid_count + 2 if decrypt_outputs is None else decrypt_outputs)
    if (
        not isinstance(effective_decrypt_outputs, int)
        or isinstance(effective_decrypt_outputs, bool)
        or effective_decrypt_outputs <= 0
        or effective_decrypt_outputs > MAX_ALPHA_DECRYPT_OUTPUTS
    ):
        raise ValueError("decrypt_outputs out of range")

    sort_compare_ops, sort_layers = _bitonic_sort_comparator_upper_bound(int(bid_count))
    prefix_compare_ops = int(bid_count)
    prefix_select_ops = int(bid_count)
    prefix_add_ops = int(max(0, bid_count - 1))
    compare_ops = int(sort_compare_ops + prefix_compare_ops)
    select_ops = int((sort_compare_ops * 2) + prefix_select_ops)
    add_ops = int(prefix_add_ops + bid_count)
    estimated_hcu = (
        compare_ops * EUINT32_COMPARE_HCU
        + select_ops * EUINT32_SELECT_HCU
        + add_ops * EUINT32_ADD_HCU
    )
    estimated_depth_hcu = (
        sort_layers * (EUINT32_COMPARE_HCU + (2 * EUINT32_SELECT_HCU))
        + (bid_count * EUINT32_ADD_HCU)
    )
    return FHEOperationEstimate(
        bid_count=int(bid_count),
        compare_ops=int(compare_ops),
        select_ops=int(select_ops),
        add_ops=int(add_ops),
        sort_layers=int(sort_layers),
        decrypt_outputs=int(effective_decrypt_outputs),
        estimated_hcu=int(estimated_hcu),
        estimated_depth_hcu=int(estimated_depth_hcu),
    )


def compile_fhe_sealed_bid_alpha_plan(
    *,
    auction_id: str,
    units_for_sale: int,
    bids: Iterable[RevealedSealedBid],
    cipher_bids: Iterable[FHECipherBid],
    key_id: str,
    fallback_policy: str = "commit_reveal_v1",
    oracle_mode: str = "async_decrypt",
) -> Dict[str, Any]:
    if not isinstance(auction_id, str) or not auction_id:
        raise ValueError("auction_id must be non-empty")
    if not isinstance(key_id, str) or not key_id:
        raise ValueError("key_id must be non-empty")
    if str(fallback_policy) != "commit_reveal_v1":
        raise ValueError("fallback_policy must be commit_reveal_v1")
    if str(oracle_mode) != "async_decrypt":
        raise ValueError("oracle_mode must be async_decrypt")
    if not isinstance(units_for_sale, int) or isinstance(units_for_sale, bool) or units_for_sale <= 0 or units_for_sale > MAX_ALPHA_UNITS:
        raise ValueError("units_for_sale out of range")

    plain_bids = tuple(bids)
    cipher_surface = _validate_cipher_bids(cipher_bids)
    if len(plain_bids) == 0 or len(plain_bids) > MAX_ALPHA_BIDS:
        raise ValueError("plain bid count out of range")
    if len(plain_bids) != len(cipher_surface):
        raise ValueError("plain and cipher bid count mismatch")
    for bid in plain_bids:
        if int(bid.quantity) > MAX_ALPHA_UNITS:
            raise ValueError("bid quantity exceeds alpha cap")

    plain_keys = {(str(b.bidder_id), str(b.commitment)) for b in plain_bids}
    cipher_keys = {(str(b.bidder_id), str(b.commitment)) for b in cipher_surface}
    if plain_keys != cipher_keys:
        raise ValueError("plain and cipher bid surface mismatch")

    settlement = settle_uniform_price_sealed_bids(units_for_sale=units_for_sale, bids=plain_bids)
    estimate = estimate_fhe_uniform_price_ops(
        bid_count=len(plain_bids),
        decrypt_outputs=len(settlement.fills) + 2,
    )

    body = {
        "schema": "zenodex/fhe_sealed_bid_alpha_plan/v1",
        "auction_id": str(auction_id),
        "scheme": "zama-fhevm-alpha",
        "key_id": str(key_id),
        "oracle_mode": str(oracle_mode),
        "fallback_policy": str(fallback_policy),
        "result_verification_mode": "trusted_plaintext_replay_v1",
        "limits": {
            "max_alpha_bids": int(MAX_ALPHA_BIDS),
            "max_units": int(MAX_ALPHA_UNITS),
            "max_price": int(MAX_PRICE),
            "max_decrypt_outputs": int(MAX_ALPHA_DECRYPT_OUTPUTS),
            "hcu_cap": int(ZAMA_DEVNET_HCU_TX_CAP),
            "depth_hcu_cap": int(ZAMA_DEVNET_HCU_DEPTH_CAP),
        },
        "budget": {
            "bid_count": int(estimate.bid_count),
            "compare_ops": int(estimate.compare_ops),
            "select_ops": int(estimate.select_ops),
            "add_ops": int(estimate.add_ops),
            "sort_layers": int(estimate.sort_layers),
            "decrypt_outputs": int(estimate.decrypt_outputs),
            "estimated_hcu": int(estimate.estimated_hcu),
            "estimated_depth_hcu": int(estimate.estimated_depth_hcu),
        },
        "cipher_bids": [
            {
                "bidder_id": str(b.bidder_id),
                "commitment": str(b.commitment),
                "quantity_handle": str(b.quantity_handle),
                "price_handle": str(b.price_handle),
            }
            for b in cipher_surface
        ],
        "public_result": _settlement_to_public_result(settlement=settlement, units_for_sale=units_for_sale),
    }
    return {"body": body, "receipt_hash": fhe_sealed_bid_alpha_receipt_hash(body)}


def _settlement_to_public_result(*, settlement: SealedBidSettlement, units_for_sale: int) -> Dict[str, Any]:
    return {
        "units_for_sale": int(units_for_sale),
        "clearing_price": int(settlement.clearing_price),
        "total_filled": int(settlement.total_filled),
        "fill_count": int(len(settlement.fills)),
        "fills": [
            {
                "bidder_id": str(fill.bidder_id),
                "commitment": str(fill.commitment),
                "filled_quantity": int(fill.filled_quantity),
                "paid_price": int(fill.paid_price),
            }
            for fill in settlement.fills
        ],
    }


def verify_fhe_sealed_bid_alpha_plan(
    receipt: Dict[str, Any],
    *,
    approved_key_ids: Iterable[str],
    trusted_plain_bids: Iterable[RevealedSealedBid] | None = None,
) -> Tuple[bool, str]:
    if not isinstance(receipt, dict):
        return False, "bad_receipt_type"
    body = receipt.get("body")
    if not isinstance(body, dict):
        return False, "missing_body"
    if body.get("schema") != "zenodex/fhe_sealed_bid_alpha_plan/v1":
        return False, "bad_schema"

    want_hash = receipt.get("receipt_hash")
    if not isinstance(want_hash, str) or not want_hash:
        return False, "missing_receipt_hash"
    if fhe_sealed_bid_alpha_receipt_hash(body) != want_hash:
        return False, "hash_mismatch"

    if body.get("scheme") != "zama-fhevm-alpha":
        return False, "bad_scheme"
    if body.get("oracle_mode") != "async_decrypt":
        return False, "bad_oracle_mode"
    if body.get("fallback_policy") != "commit_reveal_v1":
        return False, "bad_fallback_policy"
    if body.get("result_verification_mode") != "trusted_plaintext_replay_v1":
        return False, "bad_result_verification_mode"
    auction_id = body.get("auction_id")
    if not isinstance(auction_id, str) or not auction_id:
        return False, "bad_auction_id"

    key_id = body.get("key_id")
    if not isinstance(key_id, str) or not key_id:
        return False, "bad_key_id"
    if key_id not in {str(x) for x in approved_key_ids if str(x)}:
        return False, "key_not_approved"

    cipher_bids_raw = body.get("cipher_bids")
    if not isinstance(cipher_bids_raw, list):
        return False, "bad_cipher_bids"
    if not all(isinstance(item, dict) for item in cipher_bids_raw):
        return False, "bad_cipher_bid"
    try:
        cipher_bids = _validate_cipher_bids(
            FHECipherBid(
                bidder_id=item.get("bidder_id"),
                commitment=item.get("commitment"),
                quantity_handle=item.get("quantity_handle"),
                price_handle=item.get("price_handle"),
            )
            for item in cipher_bids_raw
        )
    except ValueError as exc:
        return False, str(exc)
    if len(cipher_bids) == 0 or len(cipher_bids) > MAX_ALPHA_BIDS:
        return False, "cipher_bid_count_out_of_range"

    budget = body.get("budget")
    if not isinstance(budget, dict):
        return False, "bad_budget"
    bid_count = _receipt_int(budget.get("bid_count"))
    decrypt_outputs = _receipt_int(budget.get("decrypt_outputs"))
    compare_ops = _receipt_int(budget.get("compare_ops"))
    select_ops = _receipt_int(budget.get("select_ops"))
    add_ops = _receipt_int(budget.get("add_ops"))
    sort_layers = _receipt_int(budget.get("sort_layers"))
    estimated_hcu = _receipt_int(budget.get("estimated_hcu"))
    estimated_depth_hcu = _receipt_int(budget.get("estimated_depth_hcu"))
    if (
        bid_count is None
        or decrypt_outputs is None
        or compare_ops is None
        or select_ops is None
        or add_ops is None
        or sort_layers is None
        or estimated_hcu is None
        or estimated_depth_hcu is None
    ):
        return False, "bad_budget_numeric"

    if bid_count != len(cipher_bids):
        return False, "budget_bid_count_mismatch"
    try:
        expected = estimate_fhe_uniform_price_ops(bid_count=bid_count, decrypt_outputs=decrypt_outputs)
    except ValueError as exc:
        return False, str(exc)
    if compare_ops != expected.compare_ops:
        return False, "compare_ops_mismatch"
    if select_ops != expected.select_ops:
        return False, "select_ops_mismatch"
    if add_ops != expected.add_ops:
        return False, "add_ops_mismatch"
    if sort_layers != expected.sort_layers:
        return False, "sort_layers_mismatch"
    if estimated_hcu != expected.estimated_hcu:
        return False, "estimated_hcu_mismatch"
    if estimated_depth_hcu != expected.estimated_depth_hcu:
        return False, "estimated_depth_mismatch"
    if estimated_hcu > ZAMA_DEVNET_HCU_TX_CAP:
        return False, "hcu_cap_exceeded"
    if estimated_depth_hcu > ZAMA_DEVNET_HCU_DEPTH_CAP:
        return False, "depth_cap_exceeded"

    result = body.get("public_result")
    if not isinstance(result, dict):
        return False, "bad_public_result"
    units_for_sale = _receipt_int(result.get("units_for_sale"))
    clearing_price = _receipt_int(result.get("clearing_price"))
    total_filled = _receipt_int(result.get("total_filled"))
    fill_count = _receipt_int(result.get("fill_count"))
    if units_for_sale is None or clearing_price is None or total_filled is None or fill_count is None:
        return False, "bad_public_result_numeric"
    if units_for_sale <= 0 or units_for_sale > MAX_ALPHA_UNITS:
        return False, "units_for_sale_out_of_range"
    if clearing_price < 0 or clearing_price > MAX_PRICE:
        return False, "clearing_price_out_of_range"
    if total_filled < 0 or total_filled > units_for_sale:
        return False, "total_filled_out_of_range"
    if fill_count < 0 or fill_count > bid_count:
        return False, "fill_count_out_of_range"
    fills = result.get("fills")
    if not isinstance(fills, list):
        return False, "bad_fills"
    if len(fills) != fill_count:
        return False, "fill_count_mismatch"
    if decrypt_outputs != (len(fills) + 2):
        return False, "decrypt_output_mismatch"
    filled_sum = 0
    seen_fill_keys: set[tuple[str, str]] = set()
    cipher_keys = {(str(b.bidder_id), str(b.commitment)) for b in cipher_bids}
    for fill in fills:
        if not isinstance(fill, dict):
            return False, "bad_fill"
        bidder_id = fill.get("bidder_id")
        commitment = fill.get("commitment")
        if not isinstance(bidder_id, str) or not bidder_id:
            return False, "bad_fill_bidder_id"
        if not isinstance(commitment, str) or not commitment:
            return False, "bad_fill_commitment"
        key = (bidder_id, commitment)
        if key in seen_fill_keys:
            return False, "duplicate_fill_key"
        if key not in cipher_keys:
            return False, "fill_without_cipher_bid"
        seen_fill_keys.add(key)
        filled_quantity = _receipt_int(fill.get("filled_quantity"))
        paid_price = _receipt_int(fill.get("paid_price"))
        if filled_quantity is None or paid_price is None:
            return False, "bad_fill_numeric"
        if filled_quantity <= 0 or filled_quantity > MAX_ALPHA_UNITS:
            return False, "filled_quantity_out_of_range"
        if paid_price != clearing_price:
            return False, "paid_price_mismatch"
        filled_sum += filled_quantity
    if filled_sum != total_filled:
        return False, "filled_sum_mismatch"

    if trusted_plain_bids is None:
        return False, "unauthenticated_public_result"
    try:
        plain_bids = tuple(trusted_plain_bids)
    except TypeError:
        return False, "bad_trusted_plain_bids"
    if len(plain_bids) != len(cipher_bids):
        return False, "trusted_plain_bid_count_mismatch"
    plain_keys = {(str(b.bidder_id), str(b.commitment)) for b in plain_bids}
    if plain_keys != cipher_keys:
        return False, "trusted_plain_surface_mismatch"
    try:
        for bid in plain_bids:
            if not isinstance(bid.quantity, int) or isinstance(bid.quantity, bool) or bid.quantity <= 0 or bid.quantity > MAX_ALPHA_UNITS:
                return False, "trusted_plain_quantity_out_of_range"
            if not isinstance(bid.limit_price, int) or isinstance(bid.limit_price, bool) or bid.limit_price <= 0 or bid.limit_price > MAX_PRICE:
                return False, "trusted_plain_price_out_of_range"
        expected_settlement = settle_uniform_price_sealed_bids(units_for_sale=units_for_sale, bids=plain_bids)
    except (AttributeError, TypeError, ValueError, OverflowError):
        return False, "bad_trusted_plain_bids"
    expected_public_result = _settlement_to_public_result(
        settlement=expected_settlement,
        units_for_sale=units_for_sale,
    )
    if expected_public_result != result:
        return False, "public_result_mismatch"
    return True, "ok"
