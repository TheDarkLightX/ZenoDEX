"""Route quote receipt construction and hash primitives."""

from __future__ import annotations

import hashlib
from typing import Any, Dict, Tuple

from ..core.frontier_signature_root import (
    FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1,
    FrontierSignatureCertificatesRootBinding,
    normalize_frontier_signature_binding,
)
from ..core.quote_receipt_gates import _require_receipt_int
from ..core.quote_receipt_limits import (
    ROUTE_QUOTE_RECEIPT_MAX_HOPS_PER_LEG,
    ROUTE_QUOTE_RECEIPT_MAX_LEGS,
    ROUTE_QUOTE_RECEIPT_MAX_POOLS,
)
from ..core.routing import RouteHop, RouteLeg, RouteQuote
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.pools import PoolState

_U32_MAX = (1 << 32) - 1
_U64_MAX = (1 << 64) - 1
_U128_MAX = (1 << 128) - 1
_RISC0_ROUTE_BINDING_DOMAIN_V1 = b"zenodex.risc0.route_quote_receipt_binding.v1:"
_RISC0_ROUTE_BINDING_DOMAIN_V2 = b"zenodex.risc0.route_quote_receipt_binding.v2:"


def _require_builder_receipt_int(name: str, value: Any, *, positive: bool = False) -> int:
    parsed = _require_receipt_int(value)
    if parsed is None:
        raise TypeError(f"{name} must be an int")
    if positive and parsed <= 0:
        raise ValueError(f"{name} must be positive")
    return int(parsed)


def _require_uint(name: str, value: Any, *, max_value: int) -> int:
    parsed = _require_receipt_int(value)
    if parsed is None:
        raise TypeError(f"{name} must be an int")
    if parsed < 0 or parsed > max_value:
        raise ValueError(f"{name} must be in [0, {max_value}]")
    return int(parsed)


def _require_u32(name: str, value: Any) -> int:
    return _require_uint(name, value, max_value=_U32_MAX)


def _require_u64(name: str, value: Any) -> int:
    return _require_uint(name, value, max_value=_U64_MAX)


def _require_u128(name: str, value: Any) -> int:
    return _require_uint(name, value, max_value=_U128_MAX)


def _risc0_write_str(parts: list[bytes], value: str) -> None:
    if not isinstance(value, str):
        raise TypeError("risc0 route binding string fields must be str")
    data = value.encode("utf-8")
    parts.append(len(data).to_bytes(4, "big"))
    parts.append(data)


def _risc0_write_opt_str(parts: list[bytes], value: str | None) -> None:
    if value is None:
        parts.append(b"\x00")
        return
    parts.append(b"\x01")
    _risc0_write_str(parts, value)


def _risc0_write_u32(parts: list[bytes], value: int) -> None:
    parts.append(_require_u32("risc0 u32", value).to_bytes(4, "big"))


def _risc0_write_u64(parts: list[bytes], value: int) -> None:
    parts.append(_require_u64("risc0 u64", value).to_bytes(8, "big"))


def _risc0_write_u128(parts: list[bytes], value: int) -> None:
    parts.append(_require_u128("risc0 u128", value).to_bytes(16, "big"))


def _risc0_write_32_byte_hex(parts: list[bytes], value: str, *, name: str) -> None:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    text = value[2:] if value.startswith("0x") else value
    if len(text) != 64:
        raise ValueError(f"{name} must be 32-byte hex")
    parts.append(bytes.fromhex(text))


def _resolve_frontier_signature_binding(
    frontier_signature_binding: FrontierSignatureCertificatesRootBinding | None,
) -> tuple[int, str]:
    if frontier_signature_binding is None:
        return 0, FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1
    if not isinstance(frontier_signature_binding, FrontierSignatureCertificatesRootBinding):
        raise TypeError("frontier_signature_binding must be FrontierSignatureCertificatesRootBinding")
    return frontier_signature_binding.certificate_count, frontier_signature_binding.certificates_root


def _frontier_signature_binding_from_body(
    body: Dict[str, Any],
) -> FrontierSignatureCertificatesRootBinding | None:
    body_has_count = "shared_pool_frontier_signature_certificate_count" in body
    body_has_root = "shared_pool_frontier_signature_certificates_root" in body
    if not body_has_count and not body_has_root:
        return None
    count, root = normalize_frontier_signature_binding(
        count=body.get("shared_pool_frontier_signature_certificate_count"),
        root=body.get("shared_pool_frontier_signature_certificates_root"),
        count_name="shared_pool_frontier_signature_certificate_count",
        root_name="shared_pool_frontier_signature_certificates_root",
    )
    return FrontierSignatureCertificatesRootBinding(
        certificate_count=count,
        certificates_root=root,
    )


def _normalize_risc0_route_kind(kind: str) -> str:
    normalized = str(kind).strip().upper()
    if normalized in {"EXACT_IN", "ROUTE_EXACT_IN"}:
        return "ROUTE_EXACT_IN"
    if normalized in {"EXACT_OUT", "ROUTE_EXACT_OUT"}:
        return "ROUTE_EXACT_OUT"
    raise ValueError("kind must be exact_in, exact_out, ROUTE_EXACT_IN, or ROUTE_EXACT_OUT")


def _pool_status_value(pool: PoolState) -> str:
    status = pool.status
    value = getattr(status, "value", status)
    if not isinstance(value, str) or not value:
        raise ValueError("pool.status must have a non-empty string value")
    return value


def _risc0_write_pool_snapshot(parts: list[bytes], pool: PoolState) -> None:
    _risc0_write_str(parts, pool.pool_id)
    _risc0_write_str(parts, pool.asset0)
    _risc0_write_str(parts, pool.asset1)
    _risc0_write_u128(parts, _require_u128("pool.reserve0", pool.reserve0))
    _risc0_write_u128(parts, _require_u128("pool.reserve1", pool.reserve1))
    _risc0_write_u32(parts, _require_u32("pool.fee_bps", pool.fee_bps))
    _risc0_write_u128(parts, _require_u128("pool.lp_supply", pool.lp_supply))
    _risc0_write_str(parts, _pool_status_value(pool))
    _risc0_write_u64(parts, _require_u64("pool.created_at", pool.created_at))


def _default_risc0_route_totals(
    *,
    normalized_kind: str,
    quote: RouteQuote,
    total_amount_in: int | None,
    total_min_amount_out: int | None,
    total_amount_out: int | None,
    total_max_amount_in: int | None,
) -> tuple[int, int, int, int]:
    quote_amount_in = _require_u128("quote.amount_in", quote.amount_in)
    quote_amount_out = _require_u128("quote.amount_out", quote.amount_out)
    if normalized_kind == "ROUTE_EXACT_IN":
        return (
            quote_amount_in if total_amount_in is None else _require_u128("total_amount_in", total_amount_in),
            quote_amount_out if total_min_amount_out is None else _require_u128("total_min_amount_out", total_min_amount_out),
            0 if total_amount_out is None else _require_u128("total_amount_out", total_amount_out),
            0 if total_max_amount_in is None else _require_u128("total_max_amount_in", total_max_amount_in),
        )
    return (
        0 if total_amount_in is None else _require_u128("total_amount_in", total_amount_in),
        0 if total_min_amount_out is None else _require_u128("total_min_amount_out", total_min_amount_out),
        quote_amount_out if total_amount_out is None else _require_u128("total_amount_out", total_amount_out),
        quote_amount_in if total_max_amount_in is None else _require_u128("total_max_amount_in", total_max_amount_in),
    )


def make_risc0_route_quote_receipt_binding_hash(
    *,
    kind: str,
    quote: RouteQuote,
    pools_by_id: Dict[str, PoolState],
    total_amount_in: int | None = None,
    total_min_amount_out: int | None = None,
    total_amount_out: int | None = None,
    total_max_amount_in: int | None = None,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: str | None = None,
    leg_indices: tuple[int, ...] | None = None,
    frontier_signature_binding: FrontierSignatureCertificatesRootBinding | None = None,
) -> str:
    """
    Emit the exact binary route binding hash consumed by the Rust RISC0 kernel.

    This hash is distinct from the canonical JSON quote receipt hash. It binds
    route totals, protocol-fee context, leg coverage, and live pool snapshots.
    """
    normalized_kind = _normalize_risc0_route_kind(kind)
    if not quote.legs:
        raise ValueError("quote legs must be non-empty")
    expected_leg_indices = tuple(range(len(quote.legs)))
    if leg_indices is None:
        leg_indices = expected_leg_indices
    if tuple(leg_indices) != expected_leg_indices:
        raise ValueError("leg_indices must cover the full receipt")

    (
        resolved_total_amount_in,
        resolved_total_min_amount_out,
        resolved_total_amount_out,
        resolved_total_max_amount_in,
    ) = _default_risc0_route_totals(
        normalized_kind=normalized_kind,
        quote=quote,
        total_amount_in=total_amount_in,
        total_min_amount_out=total_min_amount_out,
        total_amount_out=total_amount_out,
        total_max_amount_in=total_max_amount_in,
    )
    fee_share = _require_u32("protocol_fee_share_bps", protocol_fee_share_bps)
    if fee_share > 10_000:
        raise ValueError("protocol_fee_share_bps must be in [0, 10000]")
    if protocol_fee_recipient_pubkey is not None and not isinstance(protocol_fee_recipient_pubkey, str):
        raise TypeError("protocol_fee_recipient_pubkey must be a string or None")
    if fee_share > 0 and not (protocol_fee_recipient_pubkey or "").strip():
        raise ValueError("protocol_fee_recipient_pubkey is required when protocol_fee_share_bps > 0")
    frontier_count, frontier_root = _resolve_frontier_signature_binding(frontier_signature_binding)
    uses_frontier_v2 = (
        frontier_count != 0
        or frontier_root != FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1
    )

    parts: list[bytes] = [
        _RISC0_ROUTE_BINDING_DOMAIN_V2 if uses_frontier_v2 else _RISC0_ROUTE_BINDING_DOMAIN_V1
    ]
    _risc0_write_str(parts, normalized_kind)
    _risc0_write_str(parts, quote.asset_in)
    _risc0_write_str(parts, quote.asset_out)
    _risc0_write_u128(parts, resolved_total_amount_in)
    _risc0_write_u128(parts, resolved_total_min_amount_out)
    _risc0_write_u128(parts, resolved_total_amount_out)
    _risc0_write_u128(parts, resolved_total_max_amount_in)
    _risc0_write_u32(parts, fee_share)
    _risc0_write_opt_str(parts, protocol_fee_recipient_pubkey)
    if uses_frontier_v2:
        _risc0_write_u32(parts, frontier_count)
        _risc0_write_32_byte_hex(parts, frontier_root, name="frontier_signature_certificates_root")
    _risc0_write_u32(parts, len(leg_indices))
    for index in leg_indices:
        _risc0_write_u32(parts, index)
    _risc0_write_u32(parts, len(quote.legs))
    for leg in quote.legs:
        if len(leg.hops) != 1:
            raise ValueError("RISC0 route proof v1 supports one hop per leg")
        _risc0_write_u32(parts, 1)
        hop = leg.hops[0]
        pool = pools_by_id.get(hop.pool_id)
        if pool is None:
            raise ValueError(f"missing pool for hop.pool_id={hop.pool_id!r}")
        _risc0_write_pool_snapshot(parts, pool)
    return "0x" + hashlib.sha256(b"".join(parts)).hexdigest()


def _route_quote_from_receipt_body(body: Dict[str, Any]) -> RouteQuote:
    if not isinstance(body, dict):
        raise TypeError("receipt body must be a dict")
    legs_raw = body.get("legs")
    if not isinstance(legs_raw, list) or not legs_raw:
        raise ValueError("receipt body legs must be a non-empty list")
    legs: list[RouteLeg] = []
    for leg_raw in legs_raw:
        if not isinstance(leg_raw, dict):
            raise ValueError("receipt leg must be an object")
        hops_raw = leg_raw.get("hops")
        if not isinstance(hops_raw, list) or not hops_raw:
            raise ValueError("receipt leg hops must be a non-empty list")
        hops: list[RouteHop] = []
        for hop_raw in hops_raw:
            if not isinstance(hop_raw, dict):
                raise ValueError("receipt hop must be an object")
            hops.append(
                RouteHop(
                    pool_id=str(hop_raw.get("pool_id", "")),
                    asset_in=str(hop_raw.get("asset_in", "")),
                    asset_out=str(hop_raw.get("asset_out", "")),
                    amount_in=_require_u128("hop.amount_in", hop_raw.get("amount_in")),
                    amount_out=_require_u128("hop.amount_out", hop_raw.get("amount_out")),
                )
            )
        legs.append(
            RouteLeg(
                hops=tuple(hops),
                amount_in=_require_u128("leg.amount_in", leg_raw.get("amount_in")),
                amount_out=_require_u128("leg.amount_out", leg_raw.get("amount_out")),
            )
        )
    return RouteQuote(
        asset_in=str(body.get("asset_in", "")),
        asset_out=str(body.get("asset_out", "")),
        amount_in=_require_u128("quote.amount_in", body.get("amount_in")),
        amount_out=_require_u128("quote.amount_out", body.get("amount_out")),
        legs=tuple(legs),
    )


def make_risc0_route_quote_receipt_binding_hash_from_body(
    *,
    kind: str,
    receipt_body: Dict[str, Any],
    pools_by_id: Dict[str, PoolState],
    total_amount_in: int | None = None,
    total_min_amount_out: int | None = None,
    total_amount_out: int | None = None,
    total_max_amount_in: int | None = None,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: str | None = None,
    leg_indices: tuple[int, ...] | None = None,
    frontier_signature_binding: FrontierSignatureCertificatesRootBinding | None = None,
) -> str:
    quote = _route_quote_from_receipt_body(receipt_body)
    if frontier_signature_binding is None:
        frontier_signature_binding = _frontier_signature_binding_from_body(receipt_body)
    return make_risc0_route_quote_receipt_binding_hash(
        kind=kind,
        quote=quote,
        pools_by_id=pools_by_id,
        total_amount_in=total_amount_in,
        total_min_amount_out=total_min_amount_out,
        total_amount_out=total_amount_out,
        total_max_amount_in=total_max_amount_in,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        leg_indices=leg_indices,
        frontier_signature_binding=frontier_signature_binding,
    )


def pool_state_fingerprint(pool: PoolState) -> str:
    """
    Deterministic pool fingerprint for receipts.

    Note: includes reserves so the receipt is only valid for a specific snapshot.
    """
    obj = {
        "pool_id": pool.pool_id,
        "asset0": pool.asset0,
        "asset1": pool.asset1,
        "reserve0": _require_builder_receipt_int("pool.reserve0", pool.reserve0),
        "reserve1": _require_builder_receipt_int("pool.reserve1", pool.reserve1),
        "fee_bps": _require_builder_receipt_int("pool.fee_bps", pool.fee_bps),
        "curve_tag": str(pool.curve_tag),
        "curve_params": str(pool.curve_params),
        "lp_supply": _require_builder_receipt_int("pool.lp_supply", pool.lp_supply),
        "status": str(pool.status.value),
        "created_at": _require_builder_receipt_int("pool.created_at", pool.created_at),
    }
    return sha256_hex(domain_sep_bytes("zenodex.pool_state/v1") + canonical_json_bytes(obj))


def receipt_hash(receipt_body: Dict[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes("zenodex.route_quote_receipt/v1") + canonical_json_bytes(receipt_body))


def _normalize_route_quote_receipt_kind(kind: str) -> str:
    normalized = str(kind).strip().lower()
    if normalized not in {"exact_in", "exact_out"}:
        raise ValueError("kind must be 'exact_in' or 'exact_out'")
    return normalized


def _normalize_route_quote_epoch(quote_epoch: int | None) -> int | None:
    if quote_epoch is None:
        return None
    normalized = _require_receipt_int(quote_epoch)
    if normalized is None or normalized < 0:
        raise ValueError("quote_epoch must be a non-negative int")
    return int(normalized)


def _route_quote_receipt_hop_payload(
    *,
    hop: Any,
    pools_by_id: Dict[str, PoolState],
    pool_fps: Dict[str, str],
) -> Dict[str, Any]:
    pool = pools_by_id.get(hop.pool_id)
    if pool is None:
        raise ValueError(f"missing pool for hop.pool_id={hop.pool_id!r}")
    if hop.pool_id not in pool_fps:
        pool_fps[hop.pool_id] = pool_state_fingerprint(pool)
    return {
        "pool_id": hop.pool_id,
        "asset_in": hop.asset_in,
        "asset_out": hop.asset_out,
        "amount_in": _require_builder_receipt_int("hop.amount_in", hop.amount_in, positive=True),
        "amount_out": _require_builder_receipt_int("hop.amount_out", hop.amount_out, positive=True),
    }


def _route_quote_receipt_legs_and_pool_fingerprints(
    *,
    quote: RouteQuote,
    pools_by_id: Dict[str, PoolState],
) -> Tuple[list[Dict[str, Any]], Dict[str, str]]:
    if not quote.legs or len(quote.legs) > ROUTE_QUOTE_RECEIPT_MAX_LEGS:
        raise ValueError(f"quote legs must be in [1, {ROUTE_QUOTE_RECEIPT_MAX_LEGS}]")
    legs: list[Dict[str, Any]] = []
    pool_fps: Dict[str, str] = {}
    for leg in quote.legs:
        if not leg.hops or len(leg.hops) > ROUTE_QUOTE_RECEIPT_MAX_HOPS_PER_LEG:
            raise ValueError(f"quote leg hops must be in [1, {ROUTE_QUOTE_RECEIPT_MAX_HOPS_PER_LEG}]")
        hops = [
            _route_quote_receipt_hop_payload(
                hop=hop,
                pools_by_id=pools_by_id,
                pool_fps=pool_fps,
            )
            for hop in leg.hops
        ]
        legs.append(
            {
                "amount_in": _require_builder_receipt_int("leg.amount_in", leg.amount_in, positive=True),
                "amount_out": _require_builder_receipt_int("leg.amount_out", leg.amount_out, positive=True),
                "hops": hops,
            }
        )
        if len(pool_fps) > ROUTE_QUOTE_RECEIPT_MAX_POOLS:
            raise ValueError(f"quote pools exceeds maximum {ROUTE_QUOTE_RECEIPT_MAX_POOLS}")
    return legs, pool_fps


def _attach_exact_in_canonical_route_certificate(
    *,
    body: Dict[str, Any],
    quote: RouteQuote,
    pools_by_id: Dict[str, PoolState],
) -> None:
    # Optional canonical-winner attachment: include it when the provided quote is
    # the actual canonical winner under the current router surface.
    from ..integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
        build_exact_in_route_canonical_certificate_for_pools,
    )

    certificate = build_exact_in_route_canonical_certificate_for_pools(
        pools_by_id=pools_by_id,
        asset_in=quote.asset_in,
        asset_out=quote.asset_out,
        amount_in=_require_builder_receipt_int("quote.amount_in", quote.amount_in, positive=True),
    )
    if certificate is not None and certificate.winner_quote == quote:
        body["canonical_route_certificate"] = certificate.to_dict()


def make_route_quote_receipt(
    *,
    kind: str,
    quote: RouteQuote,
    pools_by_id: Dict[str, PoolState],
    quote_epoch: int | None = None,
    frontier_signature_binding: FrontierSignatureCertificatesRootBinding | None = None,
) -> Dict[str, Any]:
    """
    Create a deterministic receipt for a RouteQuote.

    `kind` must be "exact_in" or "exact_out". (RouteQuote itself is type-agnostic.)
    """
    normalized_kind = _normalize_route_quote_receipt_kind(kind)
    quote_epoch = _normalize_route_quote_epoch(quote_epoch)
    legs, pool_fps = _route_quote_receipt_legs_and_pool_fingerprints(
        quote=quote,
        pools_by_id=pools_by_id,
    )

    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": normalized_kind,
        "asset_in": quote.asset_in,
        "asset_out": quote.asset_out,
        "amount_in": _require_builder_receipt_int("quote.amount_in", quote.amount_in, positive=True),
        "amount_out": _require_builder_receipt_int("quote.amount_out", quote.amount_out, positive=True),
        "legs": legs,
        # Deterministic map of pool_id -> snapshot fingerprint.
        "pools": {pid: pool_fps[pid] for pid in sorted(pool_fps.keys())},
    }
    if quote_epoch is not None:
        body["quote_epoch"] = int(quote_epoch)
    if frontier_signature_binding is not None:
        if not isinstance(frontier_signature_binding, FrontierSignatureCertificatesRootBinding):
            raise TypeError("frontier_signature_binding must be FrontierSignatureCertificatesRootBinding")
        body["shared_pool_frontier_signature_certificate_count"] = (
            frontier_signature_binding.certificate_count
        )
        body["shared_pool_frontier_signature_certificates_root"] = (
            frontier_signature_binding.certificates_root
        )
    if normalized_kind == "exact_in":
        _attach_exact_in_canonical_route_certificate(
            body=body,
            quote=quote,
            pools_by_id=pools_by_id,
        )
    receipt = {
        "body": body,
        "receipt_hash": receipt_hash(body),
    }
    if all(len(leg.hops) == 1 for leg in quote.legs):
        receipt["risc0_route_quote_receipt_binding_hash"] = (
            make_risc0_route_quote_receipt_binding_hash(
                kind=normalized_kind,
                quote=quote,
                pools_by_id=pools_by_id,
                frontier_signature_binding=frontier_signature_binding,
            )
        )
    return receipt


def attach_frontier_signature_binding_to_route_quote_receipt(
    receipt: Dict[str, Any],
    *,
    frontier_signature_binding: FrontierSignatureCertificatesRootBinding,
    pools_by_id: Dict[str, PoolState] | None = None,
) -> Dict[str, Any]:
    if not isinstance(frontier_signature_binding, FrontierSignatureCertificatesRootBinding):
        raise TypeError("frontier_signature_binding must be FrontierSignatureCertificatesRootBinding")
    if not isinstance(receipt, dict):
        raise TypeError("receipt must be a dict")
    body = receipt.get("body")
    if not isinstance(body, dict):
        raise TypeError("receipt.body must be a dict")
    if (
        "shared_pool_frontier_signature_certificate_count" in body
        or "shared_pool_frontier_signature_certificates_root" in body
    ):
        raise ValueError("receipt already carries frontier signature binding")
    next_body = dict(body)
    next_body["shared_pool_frontier_signature_certificate_count"] = (
        frontier_signature_binding.certificate_count
    )
    next_body["shared_pool_frontier_signature_certificates_root"] = (
        frontier_signature_binding.certificates_root
    )
    next_receipt = {
        **receipt,
        "body": next_body,
        "receipt_hash": receipt_hash(next_body),
    }
    if "risc0_route_quote_receipt_binding_hash" in next_receipt:
        if pools_by_id is None:
            next_receipt.pop("risc0_route_quote_receipt_binding_hash", None)
        else:
            next_receipt["risc0_route_quote_receipt_binding_hash"] = (
                make_risc0_route_quote_receipt_binding_hash_from_body(
                    kind=str(next_body.get("kind", "")),
                    receipt_body=next_body,
                    pools_by_id=pools_by_id,
                    frontier_signature_binding=frontier_signature_binding,
                )
            )
    return next_receipt
