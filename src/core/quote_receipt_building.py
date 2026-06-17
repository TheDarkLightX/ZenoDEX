"""Route quote receipt construction and hash primitives."""

from __future__ import annotations

from typing import Any, Dict, Tuple

from ..core.quote_receipt_gates import _require_receipt_int
from ..core.routing import RouteQuote
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.pools import PoolState


def _require_builder_receipt_int(name: str, value: Any, *, positive: bool = False) -> int:
    parsed = _require_receipt_int(value)
    if parsed is None:
        raise TypeError(f"{name} must be an int")
    if positive and parsed <= 0:
        raise ValueError(f"{name} must be positive")
    return int(parsed)


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
    legs: list[Dict[str, Any]] = []
    pool_fps: Dict[str, str] = {}
    for leg in quote.legs:
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
    if normalized_kind == "exact_in":
        _attach_exact_in_canonical_route_certificate(
            body=body,
            quote=quote,
            pools_by_id=pools_by_id,
        )
    return {
        "body": body,
        "receipt_hash": receipt_hash(body),
    }
