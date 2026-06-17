"""Default/adaptive exact-out quote handlers for the DEX dispatch registry."""

from __future__ import annotations

import importlib
from dataclasses import dataclass
from typing import Any, Mapping

from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register
from src.integration.dex_dispatch_exact_out_advisory_quote_handlers import (
    BOUNDARY_DOMAIN_ERRORS,
    _parse_quote_inputs,
)


@dataclass(frozen=True)
class _QuoteResult:
    quote: Any
    err: Any
    packet: Any


def _call_quote_function(obj: Mapping[str, Any], function_name: str) -> DexResponse | _QuoteResult:
    inputs = _parse_quote_inputs(obj)
    if isinstance(inputs, tuple):
        return inputs

    module = importlib.import_module("src.integration.exact_out_route_certificate")
    quote_fn = getattr(module, function_name)
    quote, err, packet = quote_fn(
        inputs.pools,
        asset_in=inputs.asset_in,
        asset_out=inputs.asset_out,
        **inputs.int_kwargs,
    )
    return _QuoteResult(quote=quote, err=err, packet=packet)


def _certified_policy_payload(
    *,
    result: _QuoteResult,
    build_packet_endpoint: str,
    verify_packet_endpoint: str,
    include_runtime_quote: bool,
) -> dict[str, Any]:
    packet_payload = result.packet.to_dict()
    payload = {
        "ok": bool(result.quote is not None),
        "quote_policy": "certified_advisory_v1",
        "packet": packet_payload,
        "packet_schema": packet_payload["schema"],
        "build_packet_endpoint": build_packet_endpoint,
        "verify_packet_endpoint": verify_packet_endpoint,
        "effective_quote": packet_payload["effective_quote"],
        **_certified_repair_fields(result=result, packet_payload=packet_payload),
        **_certified_projection_fields(packet_payload),
    }
    if include_runtime_quote:
        payload["runtime_quote"] = packet_payload["selected_domain_runtime_quote"]
    if result.quote is not None:
        payload["quote"] = packet_payload["effective_quote"]
    else:
        payload["error"] = str(result.err or "many_pool_certified_advisory_unavailable")
    return payload


def _certified_repair_fields(*, result: _QuoteResult, packet_payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "quote_source": packet_payload["effective_quote_source"],
        "repaired_advisory_available": bool(result.packet.advisory_packet.repaired_advisory_available),
        "quote_matches_runtime": bool(packet_payload["effective_quote_matches_selected_runtime_quote"]),
        "quote_matches_repaired_advisory": bool(packet_payload["effective_quote_matches_repaired_advisory_quote"]),
        "repaired_full_domain_packet_ok": bool(packet_payload["repaired_full_domain_packet_ok"]),
        "repaired_quote_matches_full_domain_canonical": bool(
            packet_payload["repaired_quote_matches_full_domain_canonical"]
        ),
        "repaired_full_domain_feasible_pool_ids": packet_payload["repaired_full_domain_feasible_pool_ids"],
        "repaired_full_domain_candidate_count": packet_payload["repaired_full_domain_candidate_count"],
        "repaired_full_domain_canonical_quote": packet_payload["repaired_full_domain_canonical_quote"],
        "effective_quote_matches_full_domain_canonical": packet_payload["effective_quote_matches_full_domain_canonical"],
        "repaired_key_cover_packet_ok": bool(packet_payload["repaired_key_cover_packet_ok"]),
        "repaired_selected_keys_subset_full_keys": bool(packet_payload["repaired_selected_keys_subset_full_keys"]),
        "repaired_key_cover_holds": bool(packet_payload["repaired_key_cover_holds"]),
        "repaired_selected_domain_canonical_matches_full_domain_canonical": bool(
            packet_payload["repaired_selected_domain_canonical_matches_full_domain_canonical"]
        ),
        "repaired_key_cover_witness_count": int(packet_payload["repaired_key_cover_witness_count"]),
        "repaired_key_cover_interpretation_packet_ok": bool(packet_payload["repaired_key_cover_interpretation_packet_ok"]),
        "repaired_key_cover_selected_winner_index_in_range": bool(
            packet_payload["repaired_key_cover_selected_winner_index_in_range"]
        ),
        "repaired_key_cover_selected_winner_matches_certificate": bool(
            packet_payload["repaired_key_cover_selected_winner_matches_certificate"]
        ),
        "repaired_key_cover_selected_winner_key_minimal": bool(
            packet_payload["repaired_key_cover_selected_winner_key_minimal"]
        ),
        "repaired_key_cover_witness_indices_in_range": bool(packet_payload["repaired_key_cover_witness_indices_in_range"]),
        "repaired_key_cover_witness_coverage_complete": bool(
            packet_payload["repaired_key_cover_witness_coverage_complete"]
        ),
        "repaired_key_cover_witness_keys_match_candidates": bool(
            packet_payload["repaired_key_cover_witness_keys_match_candidates"]
        ),
        "repaired_key_cover_witness_domination_holds": bool(packet_payload["repaired_key_cover_witness_domination_holds"]),
        "selected_runtime_quotes_agree": bool(result.packet.selected_runtime_quotes_agree),
    }


def _certified_projection_fields(packet_payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "selected_domain_runtime_projected_path": packet_payload["selected_domain_runtime_projected_path"],
        "advisory_projected_path": packet_payload["advisory_projected_path"],
        "selected_domain_projection_cover_available": packet_payload["selected_domain_projection_cover_available"],
        "selected_domain_projection_cover_holds": packet_payload["selected_domain_projection_cover_holds"],
        "selected_domain_canonical_projected_path": packet_payload["selected_domain_canonical_projected_path"],
        "selected_runtime_matches_selected_canonical_projected_path": packet_payload[
            "selected_runtime_matches_selected_canonical_projected_path"
        ],
        "repaired_projection_cover_available": packet_payload["repaired_projection_cover_available"],
        "repaired_projection_cover_holds": packet_payload["repaired_projection_cover_holds"],
        "repaired_canonical_projected_path": packet_payload["repaired_canonical_projected_path"],
        "advisory_matches_repaired_canonical_projected_path": packet_payload[
            "advisory_matches_repaired_canonical_projected_path"
        ],
        "effective_projection_cover_side": packet_payload["effective_projection_cover_side"],
        "effective_projection_cover_holds": packet_payload["effective_projection_cover_holds"],
        "effective_canonical_projected_path": packet_payload["effective_canonical_projected_path"],
        "effective_quote_projected_path": packet_payload["effective_quote_projected_path"],
        "effective_quote_matches_canonical_projected_path": packet_payload[
            "effective_quote_matches_canonical_projected_path"
        ],
    }


def _adaptive_payload(result: _QuoteResult) -> dict[str, Any]:
    packet_payload = result.packet.to_dict()
    payload = {
        "ok": bool(result.quote is not None),
        "quote_policy": "adaptive_liveness_v1",
        "packet": packet_payload,
        "packet_schema": packet_payload["schema"],
        "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_adaptive_liveness_packet",
        "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_adaptive_liveness_packet",
        "audited_bounds_contract_ok": bool(packet_payload["audited_bounds_contract_ok"]),
        "default_packet_ok": bool(packet_payload["default_packet_ok"]),
        "default_effective_quote_source": packet_payload["default_effective_quote_source"],
        "repaired_full_domain_packet_ok": bool(packet_payload["repaired_full_domain_packet_ok"]),
        "repaired_quote_matches_full_domain_canonical": bool(
            packet_payload["repaired_quote_matches_full_domain_canonical"]
        ),
        "cheap_path_attempted": bool(packet_payload["cheap_path_attempted"]),
        "cheap_path_success": bool(packet_payload["cheap_path_success"]),
        "fallback_required": bool(packet_payload["fallback_required"]),
        "fallback_attempted": bool(packet_payload["fallback_attempted"]),
        "fallback_available": bool(packet_payload["fallback_available"]),
        "fallback_success": bool(packet_payload["fallback_success"]),
        "returned_success": bool(packet_payload["returned_success"]),
        "explicit_failure": bool(packet_payload["explicit_failure"]),
        "no_spurious_failure": bool(packet_payload["no_spurious_failure"]),
        "packet_ok": bool(packet_payload["packet_ok"]),
        "liveness_ok": bool(packet_payload["liveness_ok"]),
        "quote_source": packet_payload["effective_quote_source"],
        "effective_quote": packet_payload["effective_quote"],
        "failure_reason": packet_payload["failure_reason"],
        "nested_error": packet_payload["nested_error"],
    }
    if result.quote is not None:
        payload["quote"] = packet_payload["effective_quote"]
    else:
        payload["error"] = str(result.err or packet_payload["failure_reason"] or "many_pool_adaptive_unavailable")
    return payload


def _handle_quote_exact_out_many_pool(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    try:
        result = _call_quote_function(obj, "quote_exact_out_many_pool_default")
        if isinstance(result, tuple):
            return result
        return 200, _certified_policy_payload(
            result=result,
            build_packet_endpoint="/api/dex/build_exact_out_many_pool_default_packet",
            verify_packet_endpoint="/api/dex/verify_exact_out_many_pool_default_packet",
            include_runtime_quote=True,
        )
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "quote_exact_out_many_pool_error", "details": "request failed"}


def _handle_quote_exact_out_many_pool_adaptive(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    try:
        result = _call_quote_function(obj, "quote_exact_out_many_pool_adaptive")
        if isinstance(result, tuple):
            return result
        return 200, _adaptive_payload(result)
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "quote_exact_out_many_pool_adaptive_error", "details": "request failed"}


def _handle_quote_exact_out_many_pool_certified_advisory(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    try:
        result = _call_quote_function(obj, "quote_exact_out_many_pool_certified_advisory")
        if isinstance(result, tuple):
            return result
        return 200, _certified_policy_payload(
            result=result,
            build_packet_endpoint="/api/dex/build_exact_out_many_pool_certified_advisory_packet",
            verify_packet_endpoint="/api/dex/verify_exact_out_many_pool_certified_advisory_packet",
            include_runtime_quote=False,
        )
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "quote_exact_out_many_pool_certified_advisory_error",
            "details": "request failed",
        }


_register("/api/dex/quote_exact_out_many_pool", _handle_quote_exact_out_many_pool)
_register("/api/dex/quote_exact_out_many_pool_adaptive", _handle_quote_exact_out_many_pool_adaptive)
_register(
    "/api/dex/quote_exact_out_many_pool_certified_advisory",
    _handle_quote_exact_out_many_pool_certified_advisory,
)
