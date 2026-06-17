"""Settlement witness lifecycle handlers for the DEX dispatch registry."""

from __future__ import annotations

from typing import Any, Mapping

from src.integration._dex_api_helpers import parse_pools
from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register
from src.integration.api_server_settlement_parsers import (
    _parse_price_history_payload,
    _parse_settlement_feature_extension_inputs_payload,
    _parse_settlement_proof_flags_payload,
)
from src.integration.api_server_settlement_witness_routes import (
    maybe_handle_settlement_witness_lifecycle_route,
)


def _handle_settlement_witness_lifecycle(path: str, obj: Mapping[str, Any]) -> DexResponse:
    response: DexResponse | None = None

    def write_json(status: int, body: object) -> None:
        nonlocal response
        if not isinstance(body, Mapping):
            response = status, {"ok": False, "error": "bad_witness_lifecycle_response"}
            return
        response = status, body

    handled = maybe_handle_settlement_witness_lifecycle_route(
        path=path,
        obj=dict(obj),
        write_json=write_json,
        parse_pools=lambda: parse_pools(obj),
        parse_settlement_proof_flags_payload=_parse_settlement_proof_flags_payload,
        parse_price_history_payload=_parse_price_history_payload,
        parse_settlement_feature_extension_inputs_payload=_parse_settlement_feature_extension_inputs_payload,
    )
    if not handled or response is None:
        return 404, {"ok": False, "error": "not_found"}
    return response


def _handle_build_settlement_witness_lifecycle_packet(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    return _handle_settlement_witness_lifecycle(
        "/api/dex/build_settlement_witness_lifecycle_packet",
        obj,
    )


def _handle_verify_settlement_witness_lifecycle_packet(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    return _handle_settlement_witness_lifecycle(
        "/api/dex/verify_settlement_witness_lifecycle_packet",
        obj,
    )


_register(
    "/api/dex/build_settlement_witness_lifecycle_packet",
    _handle_build_settlement_witness_lifecycle_packet,
)
_register(
    "/api/dex/verify_settlement_witness_lifecycle_packet",
    _handle_verify_settlement_witness_lifecycle_packet,
)
