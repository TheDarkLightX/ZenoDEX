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


# ---------------------------------------------------------------------------
# verify_fhe_sealed_bid_alpha_plan: fail-closed verification of a confidential
# sealed-bid alpha plan.
#
# The verifier is an ORDERED short-circuiting sequence of labeled check groups.
# Each group is split by TRUST DOMAIN so the privacy/replay/arithmetic claims
# stay crisp:
#
#   host       - claims the (untrusted) host/relay asserts about the plan
#                envelope, scheme, oracle/fallback policy, and the approved key.
#   committee  - the FHE decryption-committee surface (cipher-bid handles) and
#                the trusted-plaintext replay that re-derives the public result.
#   math       - deterministic integer relations: the HCU budget estimate and
#                the public-result conservation / fill accounting.
#
# Precedence is part of the contract; the order of these groups and the order
# of checks WITHIN each group reproduces the original verifier exactly. Parsed
# values are threaded through a frozen ``_VerifyCtx`` so each field is parsed
# once and reused downstream (cipher surface, bid_count, decrypt_outputs, the
# numeric public-result fields, and the raw ``result`` dict).
# ---------------------------------------------------------------------------

# Trust-domain label for each ordered check group, keyed by the group's check
# function name. Crisp claim boundaries:
#   host       - claims the untrusted host/relay asserts (envelope, replay hash,
#                scheme/policy/key approval).
#   committee  - the FHE decryption-committee surface (cipher-bid handles) and
#                the trusted-plaintext replay re-derivation.
#   math       - deterministic integer relations (HCU budget + public-result
#                conservation / fill accounting).
# This mapping is load-bearing: ``verify_fhe_sealed_bid_alpha_plan`` executes the
# groups in exactly this declared order, and ``check_group_trust_domain`` exposes
# the label for a given group.
_CHECK_GROUP_TRUST_DOMAIN: Dict[str, str] = {
    "_check_envelope": "host",
    "_check_replay_hash": "host",
    "_check_host_config": "host",
    "_check_cipher_surface": "committee",
    "_check_budget_arithmetic": "math",
    "_check_public_result_header": "math",
    "_check_fills_accounting": "math",
    "_check_trusted_replay": "committee",
}

# Valid trust domains for any check group result.
TRUST_DOMAINS: Tuple[str, ...] = ("host", "committee", "math")

_OK: Tuple[bool, str] = (True, "ok")


def check_group_trust_domain(group_name: str) -> str:
    """Return the trust domain ('host' | 'committee' | 'math') for a check group.

    The argument is the check function's name (e.g. ``"_check_replay_hash"``).
    Raises ``KeyError`` for an unknown group so callers fail closed rather than
    silently mislabel a claim.
    """
    return _CHECK_GROUP_TRUST_DOMAIN[group_name]


# Ordered list of (check-group function name, trust domain) pairs, in the exact
# precedence the verifier evaluates them. Single source of truth for the
# decomposition + its trust labels.
VERIFY_CHECK_GROUPS: Tuple[Tuple[str, str], ...] = tuple(
    (name, _CHECK_GROUP_TRUST_DOMAIN[name])
    for name in (
        "_check_envelope",
        "_check_replay_hash",
        "_check_host_config",
        "_check_cipher_surface",
        "_check_budget_arithmetic",
        "_check_public_result_header",
        "_check_fills_accounting",
        "_check_trusted_replay",
    )
)


@dataclass(frozen=True)
class _PublicResultHeader:
    """Parsed scalar public-result fields handed from the header check to the ctx."""

    result: Dict[str, Any]
    units_for_sale: int
    clearing_price: int
    total_filled: int
    fill_count: int


@dataclass(frozen=True)
class _VerifyCtx:
    """Values parsed once by earlier groups and consumed by later groups."""

    body: Dict[str, Any]
    cipher_bids: Tuple[FHECipherBid, ...]
    cipher_keys: frozenset[tuple[str, str]]
    bid_count: int
    decrypt_outputs: int
    result: Dict[str, Any]
    units_for_sale: int
    clearing_price: int
    total_filled: int
    fill_count: int


def _check_envelope(receipt: Dict[str, Any]) -> Tuple[bool, str, Dict[str, Any] | None]:
    """host: receipt structure + schema (schema is checked BEFORE the hash gate)."""
    if not isinstance(receipt, dict):
        return False, "bad_receipt_type", None
    body = receipt.get("body")
    if not isinstance(body, dict):
        return False, "missing_body", None
    if body.get("schema") != "zenodex/fhe_sealed_bid_alpha_plan/v1":
        return False, "bad_schema", None
    return True, "ok", body


def _check_replay_hash(receipt: Dict[str, Any], body: Dict[str, Any]) -> Tuple[bool, str]:
    """host: replay/integrity guard — the receipt hash must bind this body."""
    want_hash = receipt.get("receipt_hash")
    if not isinstance(want_hash, str) or not want_hash:
        return False, "missing_receipt_hash"
    if fhe_sealed_bid_alpha_receipt_hash(body) != want_hash:
        return False, "hash_mismatch"
    return _OK


def _check_host_config(body: Dict[str, Any], approved_key_ids: Iterable[str]) -> Tuple[bool, str]:
    """host: scheme / oracle / fallback / verification mode / auction id / key approval."""
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
    return _OK


def _check_cipher_surface(
    body: Dict[str, Any],
) -> Tuple[bool, str, Tuple[FHECipherBid, ...] | None]:
    """committee: the encrypted-bid handle surface (structure + bounded count)."""
    cipher_bids_raw = body.get("cipher_bids")
    if not isinstance(cipher_bids_raw, list):
        return False, "bad_cipher_bids", None
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
    except Exception as exc:
        return False, str(exc), None
    if len(cipher_bids) == 0 or len(cipher_bids) > MAX_ALPHA_BIDS:
        return False, "cipher_bid_count_out_of_range", None
    return True, "ok", cipher_bids


def _check_budget_arithmetic(
    body: Dict[str, Any], cipher_bids: Tuple[FHECipherBid, ...]
) -> Tuple[bool, str, tuple[int, int] | None]:
    """math: the deterministic HCU budget estimate and its caps.

    Returns ``(ok, error, (bid_count, decrypt_outputs))`` so the later groups can
    reuse the parsed budget figures without re-parsing.
    """
    budget = body.get("budget")
    if not isinstance(budget, dict):
        return False, "bad_budget", None
    try:
        bid_count = int(budget.get("bid_count"))
        decrypt_outputs = int(budget.get("decrypt_outputs"))
        compare_ops = int(budget.get("compare_ops"))
        select_ops = int(budget.get("select_ops"))
        add_ops = int(budget.get("add_ops"))
        sort_layers = int(budget.get("sort_layers"))
        estimated_hcu = int(budget.get("estimated_hcu"))
        estimated_depth_hcu = int(budget.get("estimated_depth_hcu"))
    except Exception:
        return False, "bad_budget_numeric", None

    if bid_count != len(cipher_bids):
        return False, "budget_bid_count_mismatch", None
    try:
        expected = estimate_fhe_uniform_price_ops(bid_count=bid_count, decrypt_outputs=decrypt_outputs)
    except Exception as exc:
        return False, str(exc), None
    if compare_ops != expected.compare_ops:
        return False, "compare_ops_mismatch", None
    if select_ops != expected.select_ops:
        return False, "select_ops_mismatch", None
    if add_ops != expected.add_ops:
        return False, "add_ops_mismatch", None
    if sort_layers != expected.sort_layers:
        return False, "sort_layers_mismatch", None
    if estimated_hcu != expected.estimated_hcu:
        return False, "estimated_hcu_mismatch", None
    if estimated_depth_hcu != expected.estimated_depth_hcu:
        return False, "estimated_depth_mismatch", None
    if estimated_hcu > ZAMA_DEVNET_HCU_TX_CAP:
        return False, "hcu_cap_exceeded", None
    if estimated_depth_hcu > ZAMA_DEVNET_HCU_DEPTH_CAP:
        return False, "depth_cap_exceeded", None
    return True, "ok", (bid_count, decrypt_outputs)


def _check_public_result_header(
    body: Dict[str, Any], bid_count: int
) -> Tuple[bool, str, _PublicResultHeader | None]:
    """math: the scalar public-result fields (ranges only; fills checked next)."""
    result = body.get("public_result")
    if not isinstance(result, dict):
        return False, "bad_public_result", None
    try:
        units_for_sale = int(result.get("units_for_sale"))
        clearing_price = int(result.get("clearing_price"))
        total_filled = int(result.get("total_filled"))
        fill_count = int(result.get("fill_count"))
    except Exception:
        return False, "bad_public_result_numeric", None
    if units_for_sale <= 0 or units_for_sale > MAX_ALPHA_UNITS:
        return False, "units_for_sale_out_of_range", None
    if clearing_price < 0 or clearing_price > MAX_PRICE:
        return False, "clearing_price_out_of_range", None
    if total_filled < 0 or total_filled > units_for_sale:
        return False, "total_filled_out_of_range", None
    if fill_count < 0 or fill_count > bid_count:
        return False, "fill_count_out_of_range", None
    return (
        True,
        "ok",
        _PublicResultHeader(
            result=result,
            units_for_sale=units_for_sale,
            clearing_price=clearing_price,
            total_filled=total_filled,
            fill_count=fill_count,
        ),
    )


def _check_fills_accounting(ctx: _VerifyCtx, decrypt_outputs: int) -> Tuple[bool, str]:
    """math: per-fill validation + conservation.

    The within-loop precedence (duplicate_fill_key -> fill_without_cipher_bid ->
    bad_fill_numeric -> filled_quantity range -> paid_price_mismatch), the
    short-circuit on the first bad fill, and the running ``filled_sum`` are
    preserved exactly from the original verifier.
    """
    result = ctx.result
    fills = result.get("fills")
    if not isinstance(fills, list):
        return False, "bad_fills"
    if len(fills) != ctx.fill_count:
        return False, "fill_count_mismatch"
    if decrypt_outputs != (len(fills) + 2):
        return False, "decrypt_output_mismatch"
    filled_sum = 0
    seen_fill_keys: set[tuple[str, str]] = set()
    cipher_keys = ctx.cipher_keys
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
        try:
            filled_quantity = int(fill.get("filled_quantity"))
            paid_price = int(fill.get("paid_price"))
        except Exception:
            return False, "bad_fill_numeric"
        if filled_quantity <= 0 or filled_quantity > MAX_ALPHA_UNITS:
            return False, "filled_quantity_out_of_range"
        if paid_price != ctx.clearing_price:
            return False, "paid_price_mismatch"
        filled_sum += filled_quantity
    if filled_sum != ctx.total_filled:
        return False, "filled_sum_mismatch"
    return _OK


def _check_trusted_replay(
    ctx: _VerifyCtx, trusted_plain_bids: Iterable[RevealedSealedBid] | None
) -> Tuple[bool, str]:
    """committee: authenticate the public result by trusted-plaintext re-derivation.

    NOTE (trust label, not a defect): correctness of ``public_result`` rests on
    the trusted plaintext bids. The verifier surface-matches by
    (bidder_id, commitment) and re-derives the settlement, but does NOT check the
    commitment actually commits to those quantity/price values. That is the
    ``trusted_plaintext_replay_v1`` posture: the committee/host supplying the
    plaintext is trusted for this lane.
    """
    if trusted_plain_bids is None:
        return False, "unauthenticated_public_result"
    try:
        plain_bids = tuple(trusted_plain_bids)
    except Exception:
        return False, "bad_trusted_plain_bids"
    if len(plain_bids) != len(ctx.cipher_bids):
        return False, "trusted_plain_bid_count_mismatch"
    plain_keys = {(str(b.bidder_id), str(b.commitment)) for b in plain_bids}
    if plain_keys != set(ctx.cipher_keys):
        return False, "trusted_plain_surface_mismatch"
    try:
        for bid in plain_bids:
            if not isinstance(bid.quantity, int) or isinstance(bid.quantity, bool) or bid.quantity <= 0 or bid.quantity > MAX_ALPHA_UNITS:
                return False, "trusted_plain_quantity_out_of_range"
            if not isinstance(bid.limit_price, int) or isinstance(bid.limit_price, bool) or bid.limit_price <= 0 or bid.limit_price > MAX_PRICE:
                return False, "trusted_plain_price_out_of_range"
        expected_settlement = settle_uniform_price_sealed_bids(units_for_sale=ctx.units_for_sale, bids=plain_bids)
    except Exception:
        return False, "bad_trusted_plain_bids"
    expected_public_result = _settlement_to_public_result(
        settlement=expected_settlement,
        units_for_sale=ctx.units_for_sale,
    )
    if expected_public_result != ctx.result:
        return False, "public_result_mismatch"
    return _OK


def verify_fhe_sealed_bid_alpha_plan(
    receipt: Dict[str, Any],
    *,
    approved_key_ids: Iterable[str],
    trusted_plain_bids: Iterable[RevealedSealedBid] | None = None,
) -> Tuple[bool, str]:
    # host: envelope (structure + schema, pre-hash).
    ok, error, body = _check_envelope(receipt)
    if not ok or body is None:
        return False, error

    # host: replay/integrity guard (binds body to receipt hash).
    ok, error = _check_replay_hash(receipt, body)
    if not ok:
        return False, error

    # host: scheme / policy / key approval.
    ok, error = _check_host_config(body, approved_key_ids)
    if not ok:
        return False, error

    # committee: encrypted-bid handle surface.
    ok, error, cipher_bids = _check_cipher_surface(body)
    if not ok or cipher_bids is None:
        return False, error

    # math: HCU budget estimate + caps.
    ok, error, budget_figures = _check_budget_arithmetic(body, cipher_bids)
    if not ok or budget_figures is None:
        return False, error
    bid_count, decrypt_outputs = budget_figures

    # math: scalar public-result fields.
    ok, error, header = _check_public_result_header(body, bid_count)
    if not ok or header is None:
        return False, error

    ctx = _VerifyCtx(
        body=body,
        cipher_bids=cipher_bids,
        cipher_keys=frozenset((str(b.bidder_id), str(b.commitment)) for b in cipher_bids),
        bid_count=bid_count,
        decrypt_outputs=decrypt_outputs,
        result=header.result,
        units_for_sale=header.units_for_sale,
        clearing_price=header.clearing_price,
        total_filled=header.total_filled,
        fill_count=header.fill_count,
    )

    # math: per-fill validation + conservation.
    ok, error = _check_fills_accounting(ctx, decrypt_outputs)
    if not ok:
        return False, error

    # committee: trusted-plaintext replay authentication of the public result.
    return _check_trusted_replay(ctx, trusted_plain_bids)
