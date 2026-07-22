"""Central quote handler for the DEX dispatch registry."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from src.integration._dex_api_helpers import parse_pools, quote_to_dict
from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register
from src.state.immutable_json import snapshot_json_mapping

BOUNDARY_DOMAIN_ERRORS: tuple[type[Exception], ...] = (ImportError, TypeError, ValueError, ArithmeticError)
"""Expected import, parse, and arithmetic failures at the quote API boundary."""


def _optional_bool(obj: Mapping[str, Any], name: str, *, default: bool) -> bool:
    value = obj.get(name, default)
    if not isinstance(value, bool):
        raise ValueError(f"{name} must be a bool")
    return value


def _optional_int(obj: Mapping[str, Any], name: str, *, default: int) -> int:
    value = obj.get(name, default)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    return value


@dataclass(frozen=True)
class _QuoteInputs:
    kind: str
    routing_mode_req: str
    asset_in: str
    asset_out: str


def _parse_quote_inputs(obj: Mapping[str, Any]) -> DexResponse | _QuoteInputs:
    kind = str(obj.get("kind", "")).strip().lower()
    if kind not in {"exact_in", "exact_out"}:
        return 400, {"ok": False, "error": "bad_kind"}

    routing_mode_req = str(obj.get("routing_mode", "exact")).strip().lower()
    if routing_mode_req not in {"exact", "fast_v1"}:
        return 400, {"ok": False, "error": "bad_routing_mode"}

    asset_in = str(obj.get("asset_in", "")).strip()
    asset_out = str(obj.get("asset_out", "")).strip()
    if not asset_in or not asset_out or asset_in == asset_out:
        return 400, {"ok": False, "error": "bad_assets"}

    return _QuoteInputs(
        kind=kind,
        routing_mode_req=routing_mode_req,
        asset_in=asset_in,
        asset_out=asset_out,
    )


def _server_fast_router(ctx: DexRequestContext) -> Any:
    from src.integration.fast_quote_router_v1 import (
        FastQuoteRouterV1,  # pylint: disable=import-outside-toplevel
    )

    router = getattr(ctx.server, "fast_quote_router_v1", None)
    if router is None:
        router = FastQuoteRouterV1(max_cache_pairs=32)
        ctx.server.fast_quote_router_v1 = router
    return router


def _quote_exact_in(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
    pools_by_id: Mapping[str, Any],
    inputs: _QuoteInputs,
) -> tuple[str, Any]:
    from src.core.routing import best_route_exact_in_2hop  # pylint: disable=import-outside-toplevel

    amount_in = _optional_int(obj, "amount_in", default=0)
    if inputs.routing_mode_req != "fast_v1":
        return "exact", best_route_exact_in_2hop(
            pools_by_id=pools_by_id,
            asset_in=inputs.asset_in,
            asset_out=inputs.asset_out,
            amount_in=amount_in,
        )

    try:
        q = _server_fast_router(ctx).quote_exact_in_2hop_fast_v1(
            pools_by_id=pools_by_id,
            asset_in=inputs.asset_in,
            asset_out=inputs.asset_out,
            amount_in=amount_in,
            topk_max=_optional_int(obj, "fast_topk_max", default=32),
        )
    except BOUNDARY_DOMAIN_ERRORS:
        q = None
    if q is not None:
        return "fast_v1", q
    return "exact", best_route_exact_in_2hop(
        pools_by_id=pools_by_id,
        asset_in=inputs.asset_in,
        asset_out=inputs.asset_out,
        amount_in=amount_in,
    )


def _quote_exact_out(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
    pools_by_id: Mapping[str, Any],
    inputs: _QuoteInputs,
) -> tuple[str, Any]:
    from src.core.routing import (
        best_route_exact_out_2hop,  # pylint: disable=import-outside-toplevel
    )

    amount_out = _optional_int(obj, "amount_out", default=0)
    apply_two_hop_gate = _optional_bool(obj, "apply_two_hop_gate", default=False)
    if inputs.routing_mode_req != "fast_v1":
        return "exact", best_route_exact_out_2hop(
            pools_by_id=pools_by_id,
            asset_in=inputs.asset_in,
            asset_out=inputs.asset_out,
            amount_out=amount_out,
            apply_two_hop_gate=apply_two_hop_gate,
        )

    try:
        q = _server_fast_router(ctx).quote_exact_out_2hop_fast_v1(
            pools_by_id=pools_by_id,
            asset_in=inputs.asset_in,
            asset_out=inputs.asset_out,
            amount_out=amount_out,
            topk_max=_optional_int(obj, "fast_topk_max", default=32),
            apply_two_hop_gate=apply_two_hop_gate,
        )
    except BOUNDARY_DOMAIN_ERRORS:
        q = None
    if q is not None:
        return "fast_v1", q
    return "exact", best_route_exact_out_2hop(
        pools_by_id=pools_by_id,
        asset_in=inputs.asset_in,
        asset_out=inputs.asset_out,
        amount_out=amount_out,
        apply_two_hop_gate=apply_two_hop_gate,
    )


def _validate_quote_epoch(obj: Mapping[str, Any]) -> DexResponse | int | None:
    quote_epoch = obj.get("quote_epoch")
    if quote_epoch is None:
        return None
    if not isinstance(quote_epoch, int) or isinstance(quote_epoch, bool) or quote_epoch < 0:
        return 400, {"ok": False, "error": "bad_quote_epoch"}
    return int(quote_epoch)


def _route_quote(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
    pools_by_id: Mapping[str, Any],
    inputs: _QuoteInputs,
) -> tuple[str, Any]:
    if inputs.kind == "exact_in":
        return _quote_exact_in(obj, ctx, pools_by_id, inputs)
    return _quote_exact_out(obj, ctx, pools_by_id, inputs)


def _quote_boundary_error(exc: Exception) -> DexResponse:
    err = "bad_pools" if "pools" in str(exc).lower() else "quote_error"
    return 400, {"ok": False, "error": err, "details": "request failed"}


def _handle_quote(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    inputs = _parse_quote_inputs(obj)
    if isinstance(inputs, tuple):
        return inputs

    try:
        pools_by_id = parse_pools(obj)
        routing_mode_used, quote = _route_quote(obj, ctx, pools_by_id, inputs)
        if quote is None:
            return 200, {"ok": False, "error": "no_route"}
        quote_epoch = _validate_quote_epoch(obj)
        if isinstance(quote_epoch, tuple):
            return quote_epoch

        from src.core.quote_receipts import (
            make_route_quote_receipt,  # pylint: disable=import-outside-toplevel
        )

        receipt = snapshot_json_mapping(
            make_route_quote_receipt(
                kind=inputs.kind,
                quote=quote,
                pools_by_id=pools_by_id,
                quote_epoch=quote_epoch,
            ),
            name="quote receipt",
        )
        return 200, {
            "ok": True,
            "kind": inputs.kind,
            "routing_mode": str(routing_mode_used),
            "quote": quote_to_dict(quote),
            "receipt": receipt,
        }
    except BOUNDARY_DOMAIN_ERRORS as exc:
        return _quote_boundary_error(exc)


_register("/api/dex/quote", _handle_quote, default_error_code="quote_error")
