from __future__ import annotations

from typing import Callable


WriteJson = Callable[[int, object], None]

_BUILD_FEATURE_EXTENSION_PACKET_ENDPOINT = "/api/dex/build_settlement_feature_extension_packet"
_VERIFY_FEATURE_EXTENSION_PACKET_ENDPOINT = "/api/dex/verify_settlement_feature_extension_packet"


def _handle_build_feature_extension_packet(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        from src.integration.api_server_settlement_parsers import (  # pylint: disable=import-outside-toplevel
            _parse_settlement_feature_extension_inputs_payload,
        )
        from src.integration.settlement_feature_extension_packet import (  # pylint: disable=import-outside-toplevel
            build_settlement_feature_extension_packet,
        )

        feature_extension_inputs = _parse_settlement_feature_extension_inputs_payload(
            obj.get("feature_extension_inputs")
        )
        packet = build_settlement_feature_extension_packet(feature_extension_inputs)
        write_json(200, {"ok": True, "packet": packet.to_dict()})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "build_settlement_feature_extension_packet_error", "details": "request failed"},
        )


def _handle_verify_feature_extension_packet(obj: dict[str, object], write_json: WriteJson) -> None:
    packet = obj.get("packet")
    if not isinstance(packet, dict):
        write_json(400, {"ok": False, "error": "bad_packet"})
        return

    try:
        from src.integration.settlement_feature_extension_packet import (  # pylint: disable=import-outside-toplevel
            verify_settlement_feature_extension_packet_payload,
        )

        ok, err = verify_settlement_feature_extension_packet_payload(
            inputs_payload=obj.get("feature_extension_inputs"),
            packet_payload=packet,
        )
        write_json(200, {"ok": bool(ok), "error": err})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "verify_settlement_feature_extension_packet_error", "details": "request failed"},
        )


def maybe_handle_settlement_feature_extension_route(
    *,
    path: str,
    obj: dict[str, object],
    write_json: WriteJson,
) -> bool:
    if path == _BUILD_FEATURE_EXTENSION_PACKET_ENDPOINT:
        _handle_build_feature_extension_packet(obj, write_json)
        return True
    if path == _VERIFY_FEATURE_EXTENSION_PACKET_ENDPOINT:
        _handle_verify_feature_extension_packet(obj, write_json)
        return True
    return False
