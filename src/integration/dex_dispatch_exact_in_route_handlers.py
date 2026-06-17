"""Exact-in route certificate and quote handlers for the DEX dispatch registry."""

from __future__ import annotations

from typing import Any, Mapping

from src.integration._dex_api_helpers import parse_pools
from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register

BOUNDARY_DOMAIN_ERRORS: tuple[type[Exception], ...] = (TypeError, ValueError, ArithmeticError)
"""Expected parse/domain failures at the API adapter boundary."""


def _validate_exact_in_route_inputs(
    obj: Mapping[str, Any],
    *,
    needs_binding_ok: bool,
) -> DexResponse | dict[str, Any]:
    """Return parsed kwargs on success or the legacy ``DexResponse`` failure."""
    asset_in = str(obj.get("asset_in", "")).strip()
    asset_out = str(obj.get("asset_out", "")).strip()
    amount_in = obj.get("amount_in")
    split_search_profile = str(obj.get("split_search_profile", "adaptive_v6")).strip()
    enable_mixed_direct_twohop_split = obj.get("enable_mixed_direct_twohop_split", False)
    if not asset_in or not asset_out or asset_in == asset_out:
        return 400, {"ok": False, "error": "bad_assets"}
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return 400, {"ok": False, "error": "bad_amount_in"}
    if not split_search_profile:
        return 400, {"ok": False, "error": "bad_split_search_profile"}
    if not isinstance(enable_mixed_direct_twohop_split, bool):
        return 400, {"ok": False, "error": "bad_enable_mixed_direct_twohop_split"}
    out: dict[str, Any] = {
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": int(amount_in),
        "split_search_profile": split_search_profile,
        "enable_mixed_direct_twohop_split": bool(enable_mixed_direct_twohop_split),
    }
    if needs_binding_ok:
        binding_ok = obj.get("binding_ok", 1)
        if not isinstance(binding_ok, int) or isinstance(binding_ok, bool) or binding_ok not in {0, 1}:
            return 400, {"ok": False, "error": "bad_binding_ok"}
        out["binding_ok"] = int(binding_ok)
    return out


def _handle_build_exact_in_route_oracle_contract(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=True)
        if isinstance(kwargs, tuple):
            return kwargs

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_oracle_contract,
        )

        contract = build_exact_in_route_oracle_contract(pools_by_id=pools_by_id, **kwargs)
        return 200, {
            "ok": True,
            "contract_schema": "zenodex/exact-in-route-oracle-contract/v1",
            "verify_contract_endpoint": "/api/dex/verify_exact_in_route_oracle_contract",
            "contract": contract.to_dict(),
        }
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "build_exact_in_route_oracle_contract_error", "details": "request failed"}


_register("/api/dex/build_exact_in_route_oracle_contract", _handle_build_exact_in_route_oracle_contract)


def _handle_guard_exact_in_route_canonicality(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=True)
        if isinstance(kwargs, tuple):
            return kwargs

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            guard_exact_in_route_runtime_canonicality,
        )

        ok, err_msg, contract = guard_exact_in_route_runtime_canonicality(pools_by_id=pools_by_id, **kwargs)
        return 200, {"ok": bool(ok), "contract": contract.to_dict(), "error": err_msg}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "guard_exact_in_route_canonicality_error", "details": "request failed"}


_register("/api/dex/guard_exact_in_route_canonicality", _handle_guard_exact_in_route_canonicality)


def _handle_quote_exact_in_route_guarded(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    try:
        from src.integration.api_server import (  # pylint: disable=import-outside-toplevel
            RoutingGuardedQuoteAction,
            _check_routing_oracle_adapter_bridge,
        )

        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=True)
        if isinstance(kwargs, tuple):
            return kwargs

        bridge_err = _check_routing_oracle_adapter_bridge(
            body=obj,
            action=RoutingGuardedQuoteAction(
                path="/api/dex/quote_exact_in_route_guarded",
                asset_in=kwargs["asset_in"],
                asset_out=kwargs["asset_out"],
                amount_in=kwargs["amount_in"],
                split_search_profile=kwargs["split_search_profile"],
                enable_mixed_direct_twohop_split=kwargs["enable_mixed_direct_twohop_split"],
                binding_ok=kwargs["binding_ok"],
                pools_raw=obj.get("pools"),
            ),
        )
        if bridge_err is not None:
            return 400, {"ok": False, "error": "rejected", "detail": bridge_err}

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            quote_exact_in_route_guarded,
        )

        quote, err_msg, contract = quote_exact_in_route_guarded(pools_by_id=pools_by_id, **kwargs)
        response: dict[str, Any] = {"ok": quote is not None, "contract": contract.to_dict(), "error": err_msg}
        if quote is not None:
            response["quote"] = contract.to_dict()["runtime_quote"]
        return 200, response
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "quote_exact_in_route_guarded_error", "details": "request failed"}


_register("/api/dex/quote_exact_in_route_guarded", _handle_quote_exact_in_route_guarded)


def _handle_build_exact_in_route_guarded_quote_packet(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=True)
        if isinstance(kwargs, tuple):
            return kwargs

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_guarded_quote_packet,
        )

        packet = build_exact_in_route_guarded_quote_packet(pools_by_id=pools_by_id, **kwargs)
        packet_dict = packet.to_dict()
        response: dict[str, Any] = {
            "ok": True,
            "packet_schema": "zenodex/exact-in-route-guarded-quote-packet/v1",
            "verify_packet_endpoint": "/api/dex/verify_exact_in_route_guarded_quote_packet",
            "packet": packet_dict,
        }
        if not packet.guard_ok:
            response["guard_ok"] = False
            response["error"] = str(packet.error or "exact_in_runtime_not_canonical")
        return 200, response
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "build_exact_in_route_guarded_quote_packet_error", "details": "request failed"}


_register("/api/dex/build_exact_in_route_guarded_quote_packet", _handle_build_exact_in_route_guarded_quote_packet)


def _handle_build_exact_in_route_rank_projection_packet(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=False)
        if isinstance(kwargs, tuple):
            return kwargs

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_rank_projection_packet_for_pools,
        )

        packet = build_exact_in_route_rank_projection_packet_for_pools(pools_by_id=pools_by_id, **kwargs)
        if packet is None:
            return 200, {"ok": False, "error": "no_route_candidates"}
        return 200, {
            "ok": True,
            "packet_schema": "zenodex/exact-in-route-rank-projection-packet/v1",
            "verify_packet_endpoint": "/api/dex/verify_exact_in_route_rank_projection_packet",
            "packet": packet.to_dict(),
        }
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "build_exact_in_route_rank_projection_packet_error", "details": "request failed"}


_register("/api/dex/build_exact_in_route_rank_projection_packet", _handle_build_exact_in_route_rank_projection_packet)


def _handle_build_exact_in_route_true_key_interpretation_packet(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=False)
        if isinstance(kwargs, tuple):
            return kwargs

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_true_key_interpretation_packet_for_pools,
        )

        packet = build_exact_in_route_true_key_interpretation_packet_for_pools(pools_by_id=pools_by_id, **kwargs)
        if packet is None:
            return 200, {"ok": False, "error": "no_route_candidates"}
        return 200, {
            "ok": True,
            "packet_schema": "zenodex/exact-in-route-true-key-interpretation-packet/v1",
            "verify_packet_endpoint": "/api/dex/verify_exact_in_route_true_key_interpretation_packet",
            "packet": packet.to_dict(),
        }
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "build_exact_in_route_true_key_interpretation_packet_error",
            "details": "request failed",
        }


_register(
    "/api/dex/build_exact_in_route_true_key_interpretation_packet",
    _handle_build_exact_in_route_true_key_interpretation_packet,
)
