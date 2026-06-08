from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable


WriteJson = Callable[[int, object], None]
ParsePools = Callable[[], dict[str, Any]]
QuoteToDict = Callable[[object], dict[str, Any]]

_QUOTE_ENDPOINT = "/api/dex/quote"


@dataclass(frozen=True)
class _QuoteRequest:
    kind: str
    routing_mode_req: str
    asset_in: str
    asset_out: str


class _BadRequest(Exception):
    def __init__(self, error: str) -> None:
        super().__init__(error)
        self.error = error


def _parse_quote_request(obj: dict[str, object]) -> _QuoteRequest:
    kind = _require_kind(obj)
    routing_mode_req = _require_routing_mode(obj)
    asset_in, asset_out = _require_assets(obj)
    return _QuoteRequest(
        kind=kind,
        routing_mode_req=routing_mode_req,
        asset_in=asset_in,
        asset_out=asset_out,
    )


def _require_kind(obj: dict[str, object]) -> str:
    kind = str(obj.get("kind", "")).strip().lower()
    if kind not in {"exact_in", "exact_out"}:
        raise _BadRequest("bad_kind")
    return kind


def _require_routing_mode(obj: dict[str, object]) -> str:
    routing_mode_req = str(obj.get("routing_mode", "exact")).strip().lower()
    if routing_mode_req not in {"exact", "fast_v1"}:
        raise _BadRequest("bad_routing_mode")
    return routing_mode_req


def _require_assets(obj: dict[str, object]) -> tuple[str, str]:
    asset_in = str(obj.get("asset_in", "")).strip()
    asset_out = str(obj.get("asset_out", "")).strip()
    if not asset_in or not asset_out or asset_in == asset_out:
        raise _BadRequest("bad_assets")
    return asset_in, asset_out


def _get_fast_router(server: object) -> object:
    from src.integration.fast_quote_router_v1 import FastQuoteRouterV1  # pylint: disable=import-outside-toplevel

    router = getattr(server, "fast_quote_router_v1", None)
    if router is None:
        router = FastQuoteRouterV1(max_cache_pairs=32)
        setattr(server, "fast_quote_router_v1", router)
    return router


def _quote_exact_in(
    *,
    obj: dict[str, object],
    req: _QuoteRequest,
    pools_by_id: dict[str, Any],
    server: object,
    best_route_exact_in_2hop: Callable[..., object | None],
) -> tuple[object | None, str]:
    amount_in = int(obj.get("amount_in", 0))
    if req.routing_mode_req != "fast_v1":
        quote = best_route_exact_in_2hop(
            pools_by_id=pools_by_id,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_in=amount_in,
        )
        return quote, "exact"
    try:
        router = _get_fast_router(server)
        quote = router.quote_exact_in_2hop_fast_v1(
            pools_by_id=pools_by_id,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_in=amount_in,
            topk_max=int(obj.get("fast_topk_max", 32)),
        )
        if quote is not None:
            return quote, "fast_v1"
    except Exception:
        pass
    quote = best_route_exact_in_2hop(
        pools_by_id=pools_by_id,
        asset_in=req.asset_in,
        asset_out=req.asset_out,
        amount_in=amount_in,
    )
    return quote, "exact"


def _quote_exact_out(
    *,
    obj: dict[str, object],
    req: _QuoteRequest,
    pools_by_id: dict[str, Any],
    server: object,
    best_route_exact_out_2hop: Callable[..., object | None],
) -> tuple[object | None, str]:
    amount_out = int(obj.get("amount_out", 0))
    apply_two_hop_gate = bool(obj.get("apply_two_hop_gate", False))
    if req.routing_mode_req != "fast_v1":
        quote = best_route_exact_out_2hop(
            pools_by_id=pools_by_id,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_out=amount_out,
            apply_two_hop_gate=apply_two_hop_gate,
        )
        return quote, "exact"
    try:
        router = _get_fast_router(server)
        quote = router.quote_exact_out_2hop_fast_v1(
            pools_by_id=pools_by_id,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_out=amount_out,
            topk_max=int(obj.get("fast_topk_max", 32)),
            apply_two_hop_gate=apply_two_hop_gate,
        )
        if quote is not None:
            return quote, "fast_v1"
    except Exception:
        pass
    quote = best_route_exact_out_2hop(
        pools_by_id=pools_by_id,
        asset_in=req.asset_in,
        asset_out=req.asset_out,
        amount_out=amount_out,
        apply_two_hop_gate=apply_two_hop_gate,
    )
    return quote, "exact"


def _quote_epoch(obj: dict[str, object]) -> int | None:
    quote_epoch = obj.get("quote_epoch")
    if quote_epoch is None:
        return None
    if not isinstance(quote_epoch, int) or isinstance(quote_epoch, bool) or quote_epoch < 0:
        raise _BadRequest("bad_quote_epoch")
    return int(quote_epoch)


def _write_quote_response(
    *,
    req: _QuoteRequest,
    routing_mode_used: str,
    quote: object,
    receipt: dict[str, object],
    quote_to_dict: QuoteToDict,
    write_json: WriteJson,
) -> None:
    write_json(
        200,
        {
            "ok": True,
            "kind": req.kind,
            "routing_mode": str(routing_mode_used),
            "quote": quote_to_dict(quote),
            "receipt": receipt,
        },
    )


def _compute_quote(
    *,
    obj: dict[str, object],
    req: _QuoteRequest,
    pools_by_id: dict[str, Any],
    server: object,
    best_route_exact_in_2hop: Callable[..., object | None],
    best_route_exact_out_2hop: Callable[..., object | None],
) -> tuple[object | None, str]:
    if req.kind == "exact_in":
        return _quote_exact_in(
            obj=obj,
            req=req,
            pools_by_id=pools_by_id,
            server=server,
            best_route_exact_in_2hop=best_route_exact_in_2hop,
        )
    return _quote_exact_out(
        obj=obj,
        req=req,
        pools_by_id=pools_by_id,
        server=server,
        best_route_exact_out_2hop=best_route_exact_out_2hop,
    )


def _handle_quote_route(
    obj: dict[str, object],
    *,
    server: object,
    parse_pools: ParsePools,
    quote_to_dict: QuoteToDict,
    write_json: WriteJson,
) -> None:
    try:
        req = _parse_quote_request(obj)
        pools_by_id = parse_pools()
        from src.core.quote_receipts import make_route_quote_receipt  # pylint: disable=import-outside-toplevel
        from src.core.routing import (  # pylint: disable=import-outside-toplevel
            best_route_exact_in_2hop,
            best_route_exact_out_2hop,
        )

        quote, routing_mode_used = _compute_quote(
            obj=obj,
            req=req,
            pools_by_id=pools_by_id,
            server=server,
            best_route_exact_in_2hop=best_route_exact_in_2hop,
            best_route_exact_out_2hop=best_route_exact_out_2hop,
        )
        if quote is None:
            write_json(200, {"ok": False, "error": "no_route"})
            return
        quote_epoch = _quote_epoch(obj)
        receipt = make_route_quote_receipt(
            kind=req.kind,
            quote=quote,
            pools_by_id=pools_by_id,
            quote_epoch=quote_epoch,
        )
        _write_quote_response(
            req=req,
            routing_mode_used=routing_mode_used,
            quote=quote,
            receipt=receipt,
            quote_to_dict=quote_to_dict,
            write_json=write_json,
        )
    except _BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
    except Exception as exc:
        err = "bad_pools" if "pools" in str(exc).lower() else "quote_error"
        write_json(400, {"ok": False, "error": err, "details": "request failed"})


def maybe_handle_quote_route(
    *,
    path: str,
    obj: dict[str, object],
    server: object,
    parse_pools: ParsePools,
    quote_to_dict: QuoteToDict,
    write_json: WriteJson,
) -> bool:
    if path != _QUOTE_ENDPOINT:
        return False
    _handle_quote_route(
        obj,
        server=server,
        parse_pools=parse_pools,
        quote_to_dict=quote_to_dict,
        write_json=write_json,
    )
    return True
