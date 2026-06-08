from __future__ import annotations

from typing import Any, Callable, Protocol

from src.integration.api_server_exact_in_route_common import (
    BadRequest,
    parse_exact_in_route_no_binding_request,
)


WriteJson = Callable[[int, object], None]
ParsePools = Callable[[], dict[str, Any]]

_BUILD_RANK_PROJECTION_PACKET_ENDPOINT = "/api/dex/build_exact_in_route_rank_projection_packet"
_VERIFY_RANK_PROJECTION_PACKET_ENDPOINT = "/api/dex/verify_exact_in_route_rank_projection_packet"
_RANK_PROJECTION_PACKET_SCHEMA = "zenodex/exact-in-route-rank-projection-packet/v1"


class RankProjectionPacket(Protocol):
    def to_dict(self) -> dict[str, object]:
        ...


def _write_build_packet_success(write_json: WriteJson, packet: RankProjectionPacket | None) -> None:
    if packet is None:
        write_json(200, {"ok": False, "error": "no_route_candidates"})
        return
    write_json(
        200,
        {
            "ok": True,
            "packet_schema": _RANK_PROJECTION_PACKET_SCHEMA,
            "verify_packet_endpoint": _VERIFY_RANK_PROJECTION_PACKET_ENDPOINT,
            "packet": packet.to_dict(),
        },
    )


def _handle_build_rank_projection_packet(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        pools_by_id = parse_pools()
        req = parse_exact_in_route_no_binding_request(obj)
        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_rank_projection_packet_for_pools,
        )

        packet = build_exact_in_route_rank_projection_packet_for_pools(
            pools_by_id=pools_by_id,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_in=req.amount_in,
            split_search_profile=req.split_search_profile,
            enable_mixed_direct_twohop_split=req.enable_mixed_direct_twohop_split,
        )
        _write_build_packet_success(write_json, packet)
    except BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "build_exact_in_route_rank_projection_packet_error", "details": "request failed"},
        )


def _handle_verify_rank_projection_packet(obj: dict[str, object], write_json: WriteJson) -> None:
    packet = obj.get("packet")
    if not isinstance(packet, dict):
        write_json(400, {"ok": False, "error": "bad_packet"})
        return
    try:
        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            verify_exact_in_route_rank_projection_packet_payload,
        )

        ok, err = verify_exact_in_route_rank_projection_packet_payload(packet)
        write_json(200, {"ok": bool(ok), "error": err})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "verify_exact_in_route_rank_projection_packet_error", "details": "request failed"},
        )


def maybe_handle_exact_in_route_rank_projection_route(
    *,
    path: str,
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> bool:
    if path == _BUILD_RANK_PROJECTION_PACKET_ENDPOINT:
        _handle_build_rank_projection_packet(obj, parse_pools, write_json)
        return True
    if path == _VERIFY_RANK_PROJECTION_PACKET_ENDPOINT:
        _handle_verify_rank_projection_packet(obj, write_json)
        return True
    return False
