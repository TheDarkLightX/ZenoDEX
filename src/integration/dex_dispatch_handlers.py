"""Per-endpoint handlers for the DEX dispatch registry.

Each handler is a free function ``(obj, ctx) -> (status, body)``. Handlers
are registered with ``_register`` at module import time so the
``DEX_ENDPOINT_REGISTRY`` in ``api_server_dex_dispatch.py`` is populated
before any HTTP request is served.

Behavior preservation is the only contract: each handler MUST return a
``(status, body)`` tuple that matches byte-for-byte what the legacy
``_maybe_handle_dex_api`` block at the cited line range returned. Tests in
``tests/integration/test_api_server_dex_api.py`` validate via the live
server; the dispatch seam in ``api_server.py`` is invisible to clients.

Import strategy: ``src.core.*`` and ``src.integration.*`` modules are
imported at top of file (eager). The exception is
``src.integration.api_server`` itself — that creates a cycle since
api_server imports api_server_dex_dispatch which imports this module.
Those (2) imports stay lazy inside the handler bodies that need them.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Optional, Sequence

from src.integration._dex_api_helpers import (
    EndpointSchema,
    IntFieldSpec,
    parse_int_kwargs,
    parse_pools,
)
from src.integration.api_server_dex_dispatch import (
    DexRequestContext,
    DexResponse,
    _register,
)

BOUNDARY_DOMAIN_ERRORS: tuple[type[Exception], ...] = (TypeError, ValueError, ArithmeticError)
"""Expected parse/domain failures at the API adapter boundary.

Unexpected exceptions are intentionally left for the central dispatcher, which
preserves the same client response while producing operator diagnostics.
"""


def _int_field_specs_from_tuples(
    tuples: Sequence[tuple[str, Any, int]],
) -> tuple[IntFieldSpec, ...]:
    """Convert the legacy ``(name, default, minimum)`` tuple form into
    ``IntFieldSpec`` instances for use with ``parse_int_kwargs`` and the
    OpenAPI generator. ``default=None`` means the field is required."""
    return tuple(IntFieldSpec(name=n, default=d, minimum=m) for n, d, m in tuples)


# ======================================================================
# PR2 Batch 6 — build_exact_out_many_pool_*_packet endpoints (10 of them).
# Share the same 9-int-field validation as the contract builders but each
# has slightly different response shape:
#   - "ok_true": response.ok is always True (only valid for endpoints
#     that don't surface packet_ok)
#   - "ok_packet_ok": response.ok = bool(packet.packet_ok), error on False
#   - "ok_true_unless_packet_ok": response.ok = True initially, flipped to
#     False + error appended if packet.packet_ok is False
# Some also include extra response fields (e.g. liveness_ok) and a
# quote_policy tag.
# ======================================================================
_PACKET_BUILDER_DEFAULT_FIELDS: list[tuple[str, Any, int]] = [
    ("amount_out_total", None, 1),
    ("max_legs", 3, 1),
    ("max_candidate_pools", 5, 1),
    ("max_candidates", 12, 1),
    ("max_iters", 4096, 1),
    ("window", 64, 0),
    ("brute_force_max", 512, 0),
    ("max_full_domain_pools", 8, 1),
    ("max_enumerated_candidates", 20_000, 1),
]


@dataclass(frozen=True)
class _ExactOutPacketResponseSpec:
    schema: str
    verify_endpoint: str
    quote_policy: Optional[str]
    response_mode: str
    fallback_error: Optional[str]
    extra_response_field: Optional[tuple[str, str]]


@dataclass(frozen=True)
class _ExactOutPacketBuilderSpec:
    field_specs: Sequence[IntFieldSpec]
    module_function_name: str
    module_schema_name: str
    verify_endpoint: str
    error_code: str
    quote_policy: Optional[str] = None
    response_mode: str = "ok_packet_ok"
    fallback_error: Optional[str] = None
    extra_response_field: Optional[tuple[str, str]] = None


def _exact_out_packet_response_base(
    *,
    ok: bool,
    packet: Any,
    spec: _ExactOutPacketResponseSpec,
) -> dict[str, Any]:
    response: dict[str, Any] = {
        "ok": ok,
        "packet": packet.to_dict(),
        "packet_schema": spec.schema,
        "verify_packet_endpoint": spec.verify_endpoint,
    }
    if spec.quote_policy is not None:
        response["quote_policy"] = spec.quote_policy
    return response


def _exact_out_packet_response(
    *,
    packet: Any,
    spec: _ExactOutPacketResponseSpec,
) -> dict[str, Any]:
    if spec.response_mode == "ok_true":
        response = _exact_out_packet_response_base(
            ok=True,
            packet=packet,
            spec=spec,
        )
    elif spec.response_mode == "ok_packet_ok":
        response = _exact_out_packet_response_base(
            ok=bool(packet.packet_ok),
            packet=packet,
            spec=spec,
        )
        if not packet.packet_ok and spec.fallback_error is not None:
            response["error"] = str(getattr(packet, "error", None) or spec.fallback_error)
    else:
        response = _exact_out_packet_response_base(
            ok=True,
            packet=packet,
            spec=spec,
        )
        if not packet.packet_ok:
            response["ok"] = False
            response["error"] = str(packet.error or spec.fallback_error or "packet_not_ok")

    if spec.extra_response_field is not None:
        response_key, packet_attr = spec.extra_response_field
        response[response_key] = bool(getattr(packet, packet_attr))
    return response


def _make_exact_out_many_pool_packet_builder(spec: _ExactOutPacketBuilderSpec) -> Any:
    """Factory for build_exact_out_many_pool_*_packet endpoints."""
    if spec.response_mode not in {"ok_true", "ok_packet_ok", "ok_true_unless_packet_ok"}:
        raise ValueError(f"unknown response_mode: {spec.response_mode}")

    def _handler(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
        pools_by_id = parse_pools(obj)
        asset_in = str(obj.get("asset_in", "")).strip()
        asset_out = str(obj.get("asset_out", "")).strip()
        if not asset_in or not asset_out or asset_in == asset_out:
            return 400, {"ok": False, "error": "bad_assets"}

        int_kwargs = parse_int_kwargs(obj, spec.field_specs)

        import importlib  # pylint: disable=import-outside-toplevel
        module = importlib.import_module("src.integration.exact_out_route_certificate")
        builder = getattr(module, spec.module_function_name)
        schema = getattr(module, spec.module_schema_name)

        packet = builder(
            list(pools_by_id.values()),
            asset_in=asset_in,
            asset_out=asset_out,
            **int_kwargs,
        )
        return 200, _exact_out_packet_response(
            packet=packet,
            spec=_ExactOutPacketResponseSpec(
                schema=schema,
                verify_endpoint=spec.verify_endpoint,
                quote_policy=spec.quote_policy,
                response_mode=spec.response_mode,
                fallback_error=spec.fallback_error,
                extra_response_field=spec.extra_response_field,
            ),
        )

    return _handler


_BUILD_EXACT_OUT_PACKET_SPECS: tuple[tuple[str, dict[str, Any]], ...] = (
    (
        "/api/dex/build_exact_out_many_pool_repaired_advisory_quote_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_repaired_advisory_quote_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet",
            "error_code": "build_exact_out_many_pool_repaired_advisory_quote_packet_error",
            "response_mode": "ok_true_unless_packet_ok",
            "fallback_error": "many_pool_repaired_prefilter_contract_not_ok",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_full_domain_certified_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_repaired_full_domain_certified_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet",
            "error_code": "build_exact_out_many_pool_repaired_full_domain_certified_packet_error",
            "response_mode": "ok_packet_ok",
            "fallback_error": "many_pool_repaired_advisory_not_full_domain_canonical",
            "quote_policy": "repaired_full_domain_certified_v1",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_key_cover_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_repaired_key_cover_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_key_cover_packet",
            "error_code": "build_exact_out_many_pool_repaired_key_cover_packet_error",
            "response_mode": "ok_packet_ok",
            "fallback_error": "many_pool_repaired_selected_domain_not_key_cover_complete",
            "quote_policy": "repaired_key_cover_v1",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_key_cover_interpretation_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_repaired_key_cover_interpretation_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_INTERPRETATION_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_key_cover_interpretation_packet",
            "error_code": "build_exact_out_many_pool_repaired_key_cover_interpretation_packet_error",
            "response_mode": "ok_packet_ok",
            "fallback_error": "many_pool_repaired_key_cover_witness_interpretation_inconsistent",
            "quote_policy": "repaired_key_cover_interpretation_v1",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_bounded_advisory_quote_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_bounded_advisory_quote_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet",
            "error_code": "build_exact_out_many_pool_bounded_advisory_quote_packet_error",
            "response_mode": "ok_packet_ok",
            "fallback_error": "many_pool_bounded_advisory_unavailable",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_certified_advisory_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_certified_advisory_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_certified_advisory_packet",
            "error_code": "build_exact_out_many_pool_certified_advisory_packet_error",
            "response_mode": "ok_packet_ok",
            "fallback_error": "many_pool_certified_advisory_packet_not_ok",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_replacement_shadow_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_repaired_replacement_shadow_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_REPLACEMENT_SHADOW_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_replacement_shadow_packet",
            "error_code": "build_exact_out_many_pool_repaired_replacement_shadow_packet_error",
            "response_mode": "ok_packet_ok",
            # No fallback_error: legacy never sets an error key on packet_ok=False here.
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_default_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_default_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_default_packet",
            "error_code": "build_exact_out_many_pool_default_packet_error",
            "response_mode": "ok_packet_ok",
            "fallback_error": "many_pool_default_packet_not_ok",
            "quote_policy": "certified_advisory_v1",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_bounded_workaround_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_bounded_workaround_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_BOUNDED_WORKAROUND_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_bounded_workaround_packet",
            "error_code": "build_exact_out_many_pool_bounded_workaround_packet_error",
            "response_mode": "ok_true",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_adaptive_liveness_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_adaptive_liveness_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_ADAPTIVE_LIVENESS_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_adaptive_liveness_packet",
            "error_code": "build_exact_out_many_pool_adaptive_liveness_packet_error",
            "response_mode": "ok_packet_ok",
            "quote_policy": "adaptive_liveness_v1",
            "extra_response_field": ("liveness_ok", "liveness_ok"),
        },
    ),
)

for _path, _spec in _BUILD_EXACT_OUT_PACKET_SPECS:
    _field_specs = _int_field_specs_from_tuples(_spec["field_defaults"])
    _packet_builder_spec = _ExactOutPacketBuilderSpec(
        field_specs=_field_specs,
        module_function_name=_spec["module_function_name"],
        module_schema_name=_spec["module_schema_name"],
        verify_endpoint=_spec["verify_endpoint"],
        error_code=_spec["error_code"],
        quote_policy=_spec.get("quote_policy"),
        response_mode=_spec.get("response_mode", "ok_packet_ok"),
        fallback_error=_spec.get("fallback_error"),
        extra_response_field=_spec.get("extra_response_field"),
    )
    _handler_fn = _make_exact_out_many_pool_packet_builder(_packet_builder_spec)
    _register(
        _path,
        _handler_fn,
        default_error_code=_packet_builder_spec.error_code,
        schema=EndpointSchema(requires_pools=True, requires_assets=True, int_fields=_field_specs),
    )


# ======================================================================
# PR2 Batch 7 — guarded family (guard/quote/build) + certified_winner_packet.
# These have heavier custom response shapes that extract specific fields
# from the contract.audit payload, so per-endpoint handlers preserve
# byte-identical behavior.
# ======================================================================
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


def _handle_guard_exact_out_many_pool_canonicality(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
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


def _handle_quote_exact_out_many_pool_guarded(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        from src.integration._dex_api_helpers import (
            parse_pools,  # pylint: disable=import-outside-toplevel
        )
        from src.integration.api_server import (
            _check_routing_exact_out_oracle_adapter_bridge,  # pylint: disable=import-outside-toplevel
        )

        pools_by_id = parse_pools(obj)
        inputs = _validate_guard_family_inputs(obj)
        if isinstance(inputs, tuple):
            return inputs

        bridge_err = _check_routing_exact_out_oracle_adapter_bridge(
            body=obj,
            path="/api/dex/quote_exact_out_many_pool_guarded",
            **inputs,
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


def _handle_build_exact_out_many_pool_guarded_quote_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
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


# build_exact_out_many_pool_certified_winner_packet uses the standard 9-field
# packet builder shape with response_mode="ok_true". Fits the existing factory.
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


def _handle_quote_exact_out_many_pool_repaired_full_domain_certified(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
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
        return 400, {"ok": False, "error": "quote_exact_out_many_pool_repaired_full_domain_certified_error", "details": "request failed"}


_register("/api/dex/quote_exact_out_many_pool_repaired_full_domain_certified", _handle_quote_exact_out_many_pool_repaired_full_domain_certified)
