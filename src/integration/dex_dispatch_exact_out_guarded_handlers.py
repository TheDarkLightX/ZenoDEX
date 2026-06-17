"""Exact-out guarded/custom handlers for the DEX dispatch registry."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from src.integration._dex_api_helpers import EndpointSchema, parse_pools
from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register
from src.integration.dex_dispatch_exact_out_packet_common import (
    _PACKET_BUILDER_DEFAULT_FIELDS,
    _ExactOutPacketBuilderSpec,
    _int_field_specs_from_tuples,
    _make_exact_out_many_pool_packet_builder,
)

BOUNDARY_DOMAIN_ERRORS: tuple[type[Exception], ...] = (TypeError, ValueError, ArithmeticError)
"""Expected parse/domain failures at the API adapter boundary."""


_GUARD_FAMILY_INT_FIELDS: list[tuple[str, Any, int]] = [
    ("amount_out_total", None, 1),
    ("max_legs", 3, 1),
    ("max_candidate_pools", 5, 1),
    ("max_candidates", 12, 1),
    ("max_iters", 4096, 1),
    ("window", 64, 0),
    ("brute_force_max", 512, 0),
    ("max_enumerated_candidates", 20_000, 1),
]


def _validate_guard_family_inputs(obj: Mapping[str, Any]) -> DexResponse | dict[str, Any]:
    """Return parsed kwargs dict on success or ``DexResponse`` on failure."""
    asset_in = str(obj.get("asset_in", "")).strip()
    asset_out = str(obj.get("asset_out", "")).strip()
    if not asset_in or not asset_out or asset_in == asset_out:
        return 400, {"ok": False, "error": "bad_assets"}
    int_kwargs: dict[str, int] = {}
    for name, default, minimum in _GUARD_FAMILY_INT_FIELDS:
        raw_value = obj.get(name, default)
        if not isinstance(raw_value, int) or isinstance(raw_value, bool) or raw_value < int(minimum):
            return 400, {"ok": False, "error": f"bad_{name}"}
        int_kwargs[name] = int(raw_value)
    return {"asset_in": asset_in, "asset_out": asset_out, **int_kwargs}


def _handle_guard_exact_out_many_pool_canonicality(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        inputs = _validate_guard_family_inputs(obj)
        if isinstance(inputs, tuple):
            return inputs

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
            guard_exact_out_many_pool_runtime_canonicality,
        )

        ok, err_msg, contract = guard_exact_out_many_pool_runtime_canonicality(
            list(pools_by_id.values()),
            **inputs,
        )
        contract_dict = contract.to_dict()
        audit_payload = contract_dict["audit"]
        payload = {
            "ok": bool(ok),
            "contract": contract_dict,
            "contract_ok": bool(contract_dict["contract_ok"]),
            "contract_schema": EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
            "build_contract_endpoint": "/api/dex/build_exact_out_many_pool_oracle_contract",
            "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_oracle_contract",
            "runtime_projected_path": audit_payload["runtime_projected_path"],
            "canonical_winner_projected_path": audit_payload["canonical_winner_projected_path"],
            "runtime_matches_canonical_projected_path": audit_payload["runtime_matches_canonical_projected_path"],
            "projection_cover_available": audit_payload["projection_cover_available"],
            "projection_cover_holds": audit_payload["projection_cover_holds"],
        }
        if ok:
            payload["quote"] = dict(audit_payload["runtime_quote"])
        else:
            payload["error"] = str(err_msg or "many_pool_runtime_not_canonical")
            payload["runtime_quote"] = dict(audit_payload["runtime_quote"])
            payload["canonical_winner_quote"] = dict(audit_payload["canonical_winner_quote"])
        return 200, payload
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "guard_exact_out_many_pool_canonicality_error", "details": "request failed"}


_register("/api/dex/guard_exact_out_many_pool_canonicality", _handle_guard_exact_out_many_pool_canonicality)


@dataclass(frozen=True)
class _ExactOutGuardedQuoteResponse:
    quote: Any
    err_msg: Any
    contract_dict: Mapping[str, Any]
    audit_payload: Mapping[str, Any]
    contract_schema: str
    packet_schema: str


def _exact_out_guarded_quote_response(payload: _ExactOutGuardedQuoteResponse) -> dict[str, Any]:
    common = {
        "contract": payload.contract_dict,
        "contract_ok": bool(payload.contract_dict["contract_ok"]),
        "contract_schema": payload.contract_schema,
        "packet_schema": payload.packet_schema,
        "build_contract_endpoint": "/api/dex/build_exact_out_many_pool_oracle_contract",
        "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_oracle_contract",
        "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_guarded_quote_packet",
        "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
        "runtime_projected_path": payload.audit_payload["runtime_projected_path"],
        "canonical_winner_projected_path": payload.audit_payload["canonical_winner_projected_path"],
        "runtime_matches_canonical_projected_path": payload.audit_payload["runtime_matches_canonical_projected_path"],
        "projection_cover_available": payload.audit_payload["projection_cover_available"],
        "projection_cover_holds": payload.audit_payload["projection_cover_holds"],
    }
    if payload.quote is not None:
        return {
            "ok": True,
            "quote": dict(payload.audit_payload["runtime_quote"]),
            **common,
        }
    return {
        "ok": False,
        "error": str(payload.err_msg or "many_pool_runtime_not_canonical"),
        "runtime_quote": dict(payload.audit_payload["runtime_quote"]),
        "canonical_winner_quote": dict(payload.audit_payload["canonical_winner_quote"]),
        **common,
    }


def _handle_quote_exact_out_many_pool_guarded(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    try:
        from src.integration.api_server import (  # pylint: disable=import-outside-toplevel
            RoutingGuardedExactOutQuoteAction,
            _check_routing_exact_out_oracle_adapter_bridge,
        )

        pools_by_id = parse_pools(obj)
        inputs = _validate_guard_family_inputs(obj)
        if isinstance(inputs, tuple):
            return inputs

        bridge_err = _check_routing_exact_out_oracle_adapter_bridge(
            body=obj,
            action=RoutingGuardedExactOutQuoteAction(
                path="/api/dex/quote_exact_out_many_pool_guarded",
                pools_raw=obj.get("pools"),
                **inputs,
            ),
        )
        if bridge_err is not None:
            return 400, {"ok": False, "error": "rejected", "detail": bridge_err}

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
            EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
            quote_exact_out_many_pool_guarded,
        )

        quote, err_msg, contract = quote_exact_out_many_pool_guarded(
            list(pools_by_id.values()),
            **inputs,
        )
        contract_dict = contract.to_dict()
        audit_payload = contract_dict["audit"]
        return 200, _exact_out_guarded_quote_response(
            _ExactOutGuardedQuoteResponse(
                quote=quote,
                err_msg=err_msg,
                contract_dict=contract_dict,
                audit_payload=audit_payload,
                contract_schema=EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
                packet_schema=EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
            )
        )
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "quote_exact_out_many_pool_guarded_error", "details": "request failed"}


_register("/api/dex/quote_exact_out_many_pool_guarded", _handle_quote_exact_out_many_pool_guarded)


def _handle_build_exact_out_many_pool_guarded_quote_packet(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    """Uses packet.guard_ok (not packet_ok) as the success flag; adds guard_ok=False on failure."""
    try:
        pools_by_id = parse_pools(obj)
        inputs = _validate_guard_family_inputs(obj)
        if isinstance(inputs, tuple):
            return inputs

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
            build_exact_out_many_pool_guarded_quote_packet,
        )

        packet = build_exact_out_many_pool_guarded_quote_packet(
            list(pools_by_id.values()),
            **inputs,
        )
        packet_dict = packet.to_dict()
        response: dict[str, Any] = {
            "ok": True,
            "packet": packet_dict,
            "packet_schema": EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
            "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
        }
        if not packet.guard_ok:
            response["guard_ok"] = False
            response["error"] = str(packet.error or "many_pool_runtime_not_canonical")
        return 200, response
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "build_exact_out_many_pool_guarded_quote_packet_error", "details": "request failed"}


_register("/api/dex/build_exact_out_many_pool_guarded_quote_packet", _handle_build_exact_out_many_pool_guarded_quote_packet)


_certified_winner_field_specs = _int_field_specs_from_tuples(_PACKET_BUILDER_DEFAULT_FIELDS)
_register(
    "/api/dex/build_exact_out_many_pool_certified_winner_packet",
    _make_exact_out_many_pool_packet_builder(
        _ExactOutPacketBuilderSpec(
            field_specs=_certified_winner_field_specs,
            module_function_name="build_exact_out_many_pool_certified_winner_packet",
            module_schema_name="EXACT_OUT_MANY_POOL_CERTIFIED_WINNER_PACKET_SCHEMA",
            verify_endpoint="/api/dex/verify_exact_out_many_pool_certified_winner_packet",
            error_code="build_exact_out_many_pool_certified_winner_packet_error",
            response_mode="ok_true",
        )
    ),
    default_error_code="build_exact_out_many_pool_certified_winner_packet_error",
    schema=EndpointSchema(requires_pools=True, requires_assets=True, int_fields=_certified_winner_field_specs),
)


def _handle_quote_exact_out_many_pool_repaired_full_domain_certified(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        asset_in = str(obj.get("asset_in", "")).strip()
        asset_out = str(obj.get("asset_out", "")).strip()
        if not asset_in or not asset_out or asset_in == asset_out:
            return 400, {"ok": False, "error": "bad_assets"}
        int_kwargs: dict[str, int] = {}
        for name, default, minimum in _PACKET_BUILDER_DEFAULT_FIELDS:
            raw_value = obj.get(name, default)
            if not isinstance(raw_value, int) or isinstance(raw_value, bool) or raw_value < int(minimum):
                return 400, {"ok": False, "error": f"bad_{name}"}
            int_kwargs[name] = int(raw_value)

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA,
            quote_exact_out_many_pool_repaired_full_domain_certified,
        )

        quote, err_msg, packet = quote_exact_out_many_pool_repaired_full_domain_certified(
            list(pools_by_id.values()),
            asset_in=asset_in,
            asset_out=asset_out,
            **int_kwargs,
        )
        payload = {
            "ok": bool(quote is not None),
            "packet": packet.to_dict(),
            "packet_schema": EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA,
            "quote_policy": "repaired_full_domain_certified_v1",
            "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_repaired_full_domain_certified_packet",
            "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet",
            "runtime_quote": packet.repaired_packet.to_dict()["runtime_quote"],
            "full_domain_canonical_quote": packet.to_dict()["full_domain_canonical_quote"],
            "repaired_matches_full_canonical": bool(packet.repaired_matches_full_canonical),
            "full_domain_candidate_count": int(packet.full_domain_candidate_count),
            "full_domain_feasible_pool_ids": [str(pool_id) for pool_id in packet.full_domain_feasible_pool_ids],
        }
        if quote is not None:
            payload["quote"] = packet.to_dict()["repaired_quote"]
        else:
            payload["error"] = str(err_msg or "many_pool_repaired_advisory_not_full_domain_canonical")
        return 200, payload
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "quote_exact_out_many_pool_repaired_full_domain_certified_error",
            "details": "request failed",
        }


_register(
    "/api/dex/quote_exact_out_many_pool_repaired_full_domain_certified",
    _handle_quote_exact_out_many_pool_repaired_full_domain_certified,
)
