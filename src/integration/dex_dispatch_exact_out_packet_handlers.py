"""Exact-out many-pool packet-builder handlers for the DEX dispatch registry."""

from __future__ import annotations

from typing import Any

from src.integration._dex_api_helpers import EndpointSchema
from src.integration.api_server_dex_dispatch import _register
from src.integration.dex_dispatch_exact_out_packet_common import (
    _PACKET_BUILDER_DEFAULT_FIELDS,
    _ExactOutPacketBuilderSpec,
    _int_field_specs_from_tuples,
    _make_exact_out_many_pool_packet_builder,
)

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
