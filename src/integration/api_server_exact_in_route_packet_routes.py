from __future__ import annotations

from typing import Any, Callable, Protocol

from src.integration.api_server_exact_in_route_common import (
    BadRequest,
    parse_exact_in_route_request,
)


WriteJson = Callable[[int, object], None]
ParsePools = Callable[[], dict[str, Any]]

_BUILD_GUARDED_QUOTE_PACKET_ENDPOINT = "/api/dex/build_exact_in_route_guarded_quote_packet"
_VERIFY_GUARDED_QUOTE_PACKET_ENDPOINT = "/api/dex/verify_exact_in_route_guarded_quote_packet"
_GUARDED_QUOTE_PACKET_SCHEMA = "zenodex/exact-in-route-guarded-quote-packet/v1"


class GuardedQuotePacket(Protocol):
    guard_ok: bool
    error: object

    def to_dict(self) -> dict[str, object]:
        ...


def _write_build_packet_success(write_json: WriteJson, packet: GuardedQuotePacket) -> None:
    packet_dict = packet.to_dict()
    response = {
        "ok": True,
        "packet_schema": _GUARDED_QUOTE_PACKET_SCHEMA,
        "verify_packet_endpoint": _VERIFY_GUARDED_QUOTE_PACKET_ENDPOINT,
        "packet": packet_dict,
    }
    if not packet.guard_ok:
        response["guard_ok"] = False
        response["error"] = str(packet.error or "exact_in_runtime_not_canonical")
    write_json(200, response)


def _handle_build_guarded_quote_packet(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        pools_by_id = parse_pools()
        req = parse_exact_in_route_request(obj)
        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_guarded_quote_packet,
        )

        packet = build_exact_in_route_guarded_quote_packet(
            pools_by_id=pools_by_id,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_in=req.amount_in,
            split_search_profile=req.split_search_profile,
            enable_mixed_direct_twohop_split=req.enable_mixed_direct_twohop_split,
            binding_ok=req.binding_ok,
        )
        _write_build_packet_success(write_json, packet)
    except BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "build_exact_in_route_guarded_quote_packet_error", "details": "request failed"},
        )


def _handle_verify_guarded_quote_packet(obj: dict[str, object], write_json: WriteJson) -> None:
    packet = obj.get("packet")
    if not isinstance(packet, dict):
        write_json(400, {"ok": False, "error": "bad_packet"})
        return
    try:
        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            verify_exact_in_route_guarded_quote_packet_payload,
        )

        ok, err = verify_exact_in_route_guarded_quote_packet_payload(packet)
        write_json(200, {"ok": bool(ok), "error": err})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "verify_exact_in_route_guarded_quote_packet_error", "details": "request failed"},
        )


def maybe_handle_exact_in_route_packet_route(
    *,
    path: str,
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> bool:
    if path == _BUILD_GUARDED_QUOTE_PACKET_ENDPOINT:
        _handle_build_guarded_quote_packet(obj, parse_pools, write_json)
        return True
    if path == _VERIFY_GUARDED_QUOTE_PACKET_ENDPOINT:
        _handle_verify_guarded_quote_packet(obj, write_json)
        return True
    return False
