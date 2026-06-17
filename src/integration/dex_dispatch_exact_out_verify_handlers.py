"""Exact-out verifier handlers for the DEX dispatch registry."""

from __future__ import annotations

import importlib
from dataclasses import dataclass
from typing import Any, Mapping, Optional

from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register

BOUNDARY_DOMAIN_ERRORS: tuple[type[Exception], ...] = (TypeError, ValueError, ArithmeticError)


@dataclass(frozen=True)
class _PolicyVerifierSpec:
    payload_key: str
    importer: Any
    error_code: str
    default_error: str
    quote_policy: Optional[str] = None


def _make_policy_verifier(spec: _PolicyVerifierSpec) -> Any:
    """Build a handler for policy-aware verify endpoints."""

    def _handler(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
        payload = obj.get(spec.payload_key)
        if not isinstance(payload, dict):
            return 400, {"ok": False, "error": f"bad_{spec.payload_key}"}
        try:
            verifier = spec.importer()
            ok, err = verifier(payload)
            if ok:
                body: dict[str, Any] = {"ok": True}
                if spec.quote_policy is not None:
                    body["quote_policy"] = spec.quote_policy
                return 200, body
            fail_body: dict[str, Any] = {"ok": False, "error": err or spec.default_error}
            if spec.quote_policy is not None:
                fail_body["quote_policy"] = spec.quote_policy
            return 200, fail_body
        except BOUNDARY_DOMAIN_ERRORS:
            return 400, {"ok": False, "error": spec.error_code, "details": "request failed"}

    return _handler


def _import_exact_out_route_certificate(name: str) -> Any:
    """Lazy import of any verifier from ``src.integration.exact_out_route_certificate``."""

    def _importer() -> Any:
        module = importlib.import_module("src.integration.exact_out_route_certificate")
        return getattr(module, name)

    return _importer


_EXACT_OUT_POLICY_VERIFIERS: tuple[tuple[str, str, str, str, str, Optional[str]], ...] = (
    (
        "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
        "packet",
        "verify_exact_out_many_pool_guarded_quote_packet_payload",
        "verify_exact_out_many_pool_guarded_quote_packet_error",
        "guarded quote packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_certified_winner_packet",
        "packet",
        "verify_exact_out_many_pool_certified_winner_packet_payload",
        "verify_exact_out_many_pool_certified_winner_packet_error",
        "certified winner packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet",
        "packet",
        "verify_exact_out_many_pool_repaired_advisory_quote_packet_payload",
        "verify_exact_out_many_pool_repaired_advisory_quote_packet_error",
        "repaired advisory quote packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet",
        "packet",
        "verify_exact_out_many_pool_repaired_full_domain_certified_packet_payload",
        "verify_exact_out_many_pool_repaired_full_domain_certified_packet_error",
        "repaired full-domain certified packet verification failed",
        "repaired_full_domain_certified_v1",
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_key_cover_packet",
        "packet",
        "verify_exact_out_many_pool_repaired_key_cover_packet_payload",
        "verify_exact_out_many_pool_repaired_key_cover_packet_error",
        "repaired key-cover packet verification failed",
        "repaired_key_cover_v1",
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_key_cover_interpretation_packet",
        "packet",
        "verify_exact_out_many_pool_repaired_key_cover_interpretation_packet_payload",
        "verify_exact_out_many_pool_repaired_key_cover_interpretation_packet_error",
        "repaired key-cover interpretation packet verification failed",
        "repaired_key_cover_interpretation_v1",
    ),
    (
        "/api/dex/verify_exact_out_many_pool_certified_advisory_packet",
        "packet",
        "verify_exact_out_many_pool_certified_advisory_packet_payload",
        "verify_exact_out_many_pool_certified_advisory_packet_error",
        "certified advisory packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_replacement_shadow_packet",
        "packet",
        "verify_exact_out_many_pool_repaired_replacement_shadow_packet_payload",
        "verify_exact_out_many_pool_repaired_replacement_shadow_packet_error",
        "repaired replacement shadow packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_default_packet",
        "packet",
        "verify_exact_out_many_pool_default_packet_payload",
        "verify_exact_out_many_pool_default_packet_error",
        "default packet verification failed",
        "certified_advisory_v1",
    ),
    (
        "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet",
        "packet",
        "verify_exact_out_many_pool_bounded_advisory_quote_packet_payload",
        "verify_exact_out_many_pool_bounded_advisory_quote_packet_error",
        "bounded advisory quote packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_bounded_workaround_packet",
        "packet",
        "verify_exact_out_many_pool_bounded_workaround_packet_payload",
        "verify_exact_out_many_pool_bounded_workaround_packet_error",
        "bounded workaround packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_selected_domain_oracle_contract",
        "contract",
        "verify_exact_out_many_pool_repaired_selected_domain_oracle_contract_payload",
        "verify_exact_out_many_pool_repaired_selected_domain_oracle_contract_error",
        "repaired selected-domain oracle contract verification failed",
        "repaired_selected_domain_v1",
    ),
    (
        "/api/dex/verify_exact_out_many_pool_candidate_domain_contract",
        "contract",
        "verify_exact_out_many_pool_candidate_domain_contract_payload",
        "verify_exact_out_many_pool_candidate_domain_contract_error",
        "candidate domain contract verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_prefilter_contract",
        "contract",
        "verify_exact_out_many_pool_prefilter_contract_payload",
        "verify_exact_out_many_pool_prefilter_contract_error",
        "prefilter contract verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_prefilter_contract",
        "contract",
        "verify_exact_out_many_pool_repaired_prefilter_contract_payload",
        "verify_exact_out_many_pool_repaired_prefilter_contract_error",
        "repaired prefilter contract verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_oracle_contract",
        "contract",
        "verify_exact_out_many_pool_oracle_contract_payload",
        "verify_exact_out_many_pool_oracle_contract_error",
        "oracle contract verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_audited_bounds_contract",
        "contract",
        "verify_exact_out_many_pool_audited_bounds_contract_payload",
        "verify_exact_out_many_pool_audited_bounds_contract_error",
        "audited bounds contract verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_adaptive_liveness_packet",
        "packet",
        "verify_exact_out_many_pool_adaptive_liveness_packet_payload",
        "verify_exact_out_many_pool_adaptive_liveness_packet_error",
        "adaptive liveness packet verification failed",
        "adaptive_liveness_v1",
    ),
)


def _handle_verify_exact_out_route_certificate(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    certificate = obj.get("certificate")
    if not isinstance(certificate, dict):
        return 400, {"ok": False, "error": "bad_certificate"}
    try:
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            verify_exact_out_route_canonical_certificate_payload,
        )

        ok, err = verify_exact_out_route_canonical_certificate_payload(certificate)
        return 200, {"ok": bool(ok), "error": ("ok" if ok else str(err))}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "verify_exact_out_certificate_error", "details": "request failed"}


def register_exact_out_verify_handlers() -> None:
    for path, payload_key, fn_name, error_code, default_error, quote_policy in _EXACT_OUT_POLICY_VERIFIERS:
        _register(
            path,
            _make_policy_verifier(
                _PolicyVerifierSpec(
                    payload_key=payload_key,
                    importer=_import_exact_out_route_certificate(fn_name),
                    error_code=error_code,
                    default_error=default_error,
                    quote_policy=quote_policy,
                )
            ),
        )
    _register("/api/dex/verify_exact_out_route_certificate", _handle_verify_exact_out_route_certificate)


register_exact_out_verify_handlers()
