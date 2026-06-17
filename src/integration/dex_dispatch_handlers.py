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

from src.core.price_impact_preview import price_impact_preview
from src.core.quote_receipts import verify_route_quote_receipt
from src.integration._dex_api_helpers import (
    EndpointSchema,
    IntFieldSpec,
    exact_out_split_quote_from_dict,
    parse_int_kwargs,
    parse_pools,
)
from src.integration.api_server_dex_dispatch import (
    DexRequestContext,
    DexResponse,
    _register,
)
from src.integration.api_server_settlement_parsers import (
    _parse_settlement_feature_extension_inputs_payload,
)
from src.integration.exact_in_route_certificate import (
    verify_exact_in_route_guarded_quote_packet_payload,
    verify_exact_in_route_oracle_contract_payload,
    verify_exact_in_route_rank_projection_packet_payload,
    verify_exact_in_route_true_key_interpretation_packet_payload,
)
from src.integration.settlement_feature_extension_packet import (
    build_settlement_feature_extension_packet,
    verify_settlement_feature_extension_packet_payload,
)
from src.integration.settlement_price_attestation import (
    build_settlement_spot_price_attestation,
    verify_settlement_spot_price_attestation_payload,
)
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    SettlementSpotPricePacket,
    build_settlement_spot_price_packet,
    verify_settlement_spot_price_packet_payload,
)

BOUNDARY_DOMAIN_ERRORS: tuple[type[Exception], ...] = (TypeError, ValueError, ArithmeticError)
"""Expected parse/domain failures at the API adapter boundary.

Unexpected exceptions are intentionally left for the central dispatcher, which
preserves the same client response while producing operator diagnostics.
"""


# ----------------------------------------------------------------------
# /api/dex/impact_preview
# Legacy: src/integration/api_server.py:1443-1490
# ----------------------------------------------------------------------
def _handle_impact_preview(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """No try/except: the dispatcher's catch-all converts any raised
    exception to ``(400, {"ok": False, "error": "impact_preview_error",
    "details": "request failed"})`` via the registered default_error_code.
    """
    reserve_in = int(obj.get("reserve_in", 0))
    reserve_out = int(obj.get("reserve_out", 0))
    amount_in = int(obj.get("amount_in", 0))
    fee_bps = int(obj.get("fee_bps", 0))
    pending_same_dir = int(obj.get("pending_volume_same_direction", 0))
    confidence_bps = int(obj.get("confidence_bps", 9500))

    preview = price_impact_preview(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        pending_volume_same_direction=pending_same_dir,
        confidence_bps=confidence_bps,
    )
    return 200, {
        "ok": True,
        "preview": {
            "amount_out_isolated": int(preview.amount_out_isolated),
            "fee_amount": int(preview.fee_amount),
            "price_impact_bps": int(preview.price_impact_bps),
            "effective_price_e8": int(preview.effective_price_e8),
            "spot_price_e8": int(preview.spot_price_e8),
            "amount_out_best_case": int(preview.amount_out_best_case),
            "amount_out_worst_case": int(preview.amount_out_worst_case),
            "recommended_min_out": int(preview.recommended_min_out),
            "pending_volume_same_direction": int(preview.pending_volume_same_direction),
            "confidence_bps": int(preview.confidence_bps),
            "pending_volume_at_confidence": int(preview.pending_volume_at_confidence),
            "amount_out_at_confidence": int(preview.amount_out_at_confidence),
        },
    }


_register("/api/dex/impact_preview", _handle_impact_preview, default_error_code="impact_preview_error")


# ======================================================================
# PR2 Batch 1 — verify_exact_in_route_* and verify_quote_receipt.
# These are all variations on "parse a dict-shaped payload, call a
# verifier, return {ok, error}". A factory pattern replaces the
# copy-paste.
# ======================================================================
def _make_simple_verifier(
    *,
    payload_key: str,
    importer: Any,
    error_code: str,
) -> Any:
    """Build a handler for the (payload_key -> importer() -> ok/err) shape.

    ``importer`` is a zero-arg callable that returns the verifier
    function from a lazy import. This preserves the legacy import-cycle
    guard (imports happen only when the endpoint is invoked).
    """

    def _handler(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
        payload = obj.get(payload_key)
        if not isinstance(payload, dict):
            return 400, {"ok": False, "error": f"bad_{payload_key}"}
        try:
            verifier = importer()
            ok, err = verifier(payload)
            return 200, {"ok": bool(ok), "error": err}
        except BOUNDARY_DOMAIN_ERRORS:
            return 400, {"ok": False, "error": error_code, "details": "request failed"}

    return _handler


def _import_verify_exact_in_route_oracle_contract_payload() -> Any:

    return verify_exact_in_route_oracle_contract_payload


def _import_verify_exact_in_route_guarded_quote_packet_payload() -> Any:

    return verify_exact_in_route_guarded_quote_packet_payload


def _import_verify_exact_in_route_rank_projection_packet_payload() -> Any:

    return verify_exact_in_route_rank_projection_packet_payload


def _import_verify_exact_in_route_true_key_interpretation_packet_payload() -> Any:

    return verify_exact_in_route_true_key_interpretation_packet_payload


_register(
    "/api/dex/verify_exact_in_route_oracle_contract",
    _make_simple_verifier(
        payload_key="contract",
        importer=_import_verify_exact_in_route_oracle_contract_payload,
        error_code="verify_exact_in_route_oracle_contract_error",
    ),
)
_register(
    "/api/dex/verify_exact_in_route_guarded_quote_packet",
    _make_simple_verifier(
        payload_key="packet",
        importer=_import_verify_exact_in_route_guarded_quote_packet_payload,
        error_code="verify_exact_in_route_guarded_quote_packet_error",
    ),
)
_register(
    "/api/dex/verify_exact_in_route_rank_projection_packet",
    _make_simple_verifier(
        payload_key="packet",
        importer=_import_verify_exact_in_route_rank_projection_packet_payload,
        error_code="verify_exact_in_route_rank_projection_packet_error",
    ),
)
_register(
    "/api/dex/verify_exact_in_route_true_key_interpretation_packet",
    _make_simple_verifier(
        payload_key="packet",
        importer=_import_verify_exact_in_route_true_key_interpretation_packet_payload,
        error_code="verify_exact_in_route_true_key_interpretation_packet_error",
    ),
)


# /api/dex/verify_quote_receipt — same shape but takes `expected_quote_epoch`
# and pools as extra inputs, so it can't use the simple factory.
def _handle_verify_quote_receipt(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    rec = obj.get("receipt")
    if not isinstance(rec, dict):
        return 400, {"ok": False, "error": "bad_receipt"}
    expected_quote_epoch = obj.get("expected_quote_epoch")
    if expected_quote_epoch is not None:
        if (
            not isinstance(expected_quote_epoch, int)
            or isinstance(expected_quote_epoch, bool)
            or expected_quote_epoch < 0
        ):
            return 400, {"ok": False, "error": "bad_expected_quote_epoch"}
    try:
        pools_by_id = parse_pools(obj)
        ok, err = verify_route_quote_receipt(
            rec,
            pools_by_id=pools_by_id,
            expected_quote_epoch=(None if expected_quote_epoch is None else int(expected_quote_epoch)),
        )
        return 200, {"ok": bool(ok), "error": str(err)}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "verify_error", "details": "request failed"}


_register("/api/dex/verify_quote_receipt", _handle_verify_quote_receipt)


# ======================================================================
# PR2 Batch 2 — verify_exact_out_many_pool_* and verify_exact_out_route_*.
# Policy-aware verifier shape: returns {"ok": True} or {"ok": True,
# "quote_policy": "..."} on success; on failure, includes the default
# error text and optionally the quote_policy.
# ======================================================================
@dataclass(frozen=True)
class _PolicyVerifierSpec:
    payload_key: str
    importer: Any
    error_code: str
    default_error: str
    quote_policy: Optional[str] = None


def _make_policy_verifier(spec: _PolicyVerifierSpec) -> Any:
    """Build a handler for policy-aware verify endpoints.

    Matches the legacy shape exactly:
      success: {"ok": True} + optional {"quote_policy": policy}
      failure: {"ok": False, "error": err or default_error} + optional {"quote_policy"}
      exception: 400, {"ok": False, "error": error_code, "details": "request failed"}
    """

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
            else:
                fail_body: dict[str, Any] = {"ok": False, "error": err or spec.default_error}
                if spec.quote_policy is not None:
                    fail_body["quote_policy"] = spec.quote_policy
                return 200, fail_body
        except BOUNDARY_DOMAIN_ERRORS:
            return 400, {"ok": False, "error": spec.error_code, "details": "request failed"}

    return _handler


def _import_exact_out_route_certificate(name: str) -> Any:
    """Lazy import of any verifier from src.integration.exact_out_route_certificate."""

    def _importer() -> Any:
        import importlib  # pylint: disable=import-outside-toplevel

        module = importlib.import_module("src.integration.exact_out_route_certificate")
        return getattr(module, name)

    return _importer


# (endpoint_path, payload_key, verifier_fn_name, error_code, default_error, quote_policy)
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

for _path, _key, _fn_name, _err_code, _default_err, _policy in _EXACT_OUT_POLICY_VERIFIERS:
    _register(
        _path,
        _make_policy_verifier(
            _PolicyVerifierSpec(
                payload_key=_key,
                importer=_import_exact_out_route_certificate(_fn_name),
                error_code=_err_code,
                default_error=_default_err,
                quote_policy=_policy,
            )
        ),
    )


# verify_exact_out_route_certificate uses a different response shape:
# returns {"ok": bool, "error": "ok"|err} (always populates "error" with
# string "ok" on success). Custom handler.
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


_register("/api/dex/verify_exact_out_route_certificate", _handle_verify_exact_out_route_certificate)


# ======================================================================
# PR2 Batch 3 — verify_settlement_spot_price_packet,
# verify_settlement_feature_extension_packet,
# verify_settlement_spot_price_attestation,
# build_settlement_spot_price_attestation,
# build_exact_out_route_certificate,
# audit_exact_out_two_pool_canonicality,
# audit_exact_out_many_pool_canonicality
# ======================================================================
def _import_verify_settlement_spot_price_packet_payload() -> Any:

    return verify_settlement_spot_price_packet_payload


_register(
    "/api/dex/verify_settlement_spot_price_packet",
    _make_simple_verifier(
        payload_key="packet",
        importer=_import_verify_settlement_spot_price_packet_payload,
        error_code="verify_settlement_spot_price_packet_error",
    ),
)


def _handle_verify_settlement_feature_extension_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """2-input verify: takes both feature_extension_inputs and packet."""
    feature_extension_inputs_obj = obj.get("feature_extension_inputs")
    packet_obj = obj.get("packet")
    if not isinstance(packet_obj, dict):
        return 400, {"ok": False, "error": "bad_packet"}
    try:
        ok, err = verify_settlement_feature_extension_packet_payload(
            inputs_payload=feature_extension_inputs_obj,
            packet_payload=packet_obj,
        )
        return 200, {"ok": bool(ok), "error": err}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "verify_settlement_feature_extension_packet_error", "details": "request failed"}


_register("/api/dex/verify_settlement_feature_extension_packet", _handle_verify_settlement_feature_extension_packet)


def _handle_verify_settlement_spot_price_attestation(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """Verify a spot-price attestation against a freshness window + signer allowlist."""
    attestation_obj = obj.get("attestation")
    consumer_now_epoch = obj.get("consumer_now_epoch")
    max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
    allowed_signers_obj = obj.get("allowed_signers")
    if not isinstance(attestation_obj, dict):
        return 400, {"ok": False, "error": "bad_attestation"}
    if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
        return 400, {"ok": False, "error": "bad_consumer_now_epoch"}
    if (
        not isinstance(max_attestation_age_epochs, int)
        or isinstance(max_attestation_age_epochs, bool)
        or max_attestation_age_epochs < 0
    ):
        return 400, {"ok": False, "error": "bad_max_attestation_age_epochs"}
    if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
        return 400, {"ok": False, "error": "bad_allowed_signers"}
    try:
        ok, err = verify_settlement_spot_price_attestation_payload(
            payload=attestation_obj,
            consumer_now_epoch=int(consumer_now_epoch),
            max_attestation_age_epochs=int(max_attestation_age_epochs),
            allowed_signers=allowed_signers_obj,
        )
        return 200, {"ok": bool(ok), "error": err}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "verify_settlement_spot_price_attestation_error", "details": "request failed"}


_register("/api/dex/verify_settlement_spot_price_attestation", _handle_verify_settlement_spot_price_attestation)


def _handle_build_settlement_spot_price_attestation(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """Sign a settlement spot-price packet into an attestation."""
    packet_obj = obj.get("packet")
    signer_privkey = obj.get("signer_privkey")
    if not isinstance(packet_obj, dict):
        return 400, {"ok": False, "error": "bad_packet"}
    if isinstance(signer_privkey, bool) or not isinstance(signer_privkey, (str, int)):
        return 400, {"ok": False, "error": "bad_signer_privkey"}
    try:
        packet = SettlementSpotPricePacket.from_dict(packet_obj)
        attestation = build_settlement_spot_price_attestation(
            packet=packet,
            signer_privkey=signer_privkey,
        )
        return 200, {"ok": True, "attestation": attestation.to_dict()}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "build_settlement_spot_price_attestation_error", "details": "request failed"}


_register("/api/dex/build_settlement_spot_price_attestation", _handle_build_settlement_spot_price_attestation)


def _handle_build_exact_out_route_certificate(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """Combine exact-out quote payloads into a canonical certificate."""
    quotes_obj = obj.get("quotes")
    if not isinstance(quotes_obj, list) or not quotes_obj:
        return 400, {"ok": False, "error": "bad_quotes"}
    try:
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_out_route_canonical_certificate,
        )

        quotes = tuple(exact_out_split_quote_from_dict(quote_obj) for quote_obj in quotes_obj)
        certificate = build_exact_out_route_canonical_certificate(quotes)
        return 200, {"ok": True, "certificate": certificate.to_dict()}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "bad_exact_out_certificate_request", "details": "request failed"}


_register("/api/dex/build_exact_out_route_certificate", _handle_build_exact_out_route_certificate)


def _handle_audit_exact_out_two_pool_canonicality(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        if len(pools_by_id) != 2:
            return 400, {"ok": False, "error": "expected_exactly_two_pools"}
        asset_in = str(obj.get("asset_in", "")).strip()
        asset_out = str(obj.get("asset_out", "")).strip()
        amount_out_total = obj.get("amount_out_total")
        brute_force_max = obj.get("brute_force_max")
        if not asset_in or not asset_out or asset_in == asset_out:
            return 400, {"ok": False, "error": "bad_assets"}
        if not isinstance(amount_out_total, int) or isinstance(amount_out_total, bool) or amount_out_total <= 0:
            return 400, {"ok": False, "error": "bad_amount_out_total"}
        if brute_force_max is not None and (
            not isinstance(brute_force_max, int) or isinstance(brute_force_max, bool) or brute_force_max < 0
        ):
            return 400, {"ok": False, "error": "bad_brute_force_max"}

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            audit_exact_out_two_pool_runtime_canonicality,
        )

        pools = list(pools_by_id.values())
        audit = audit_exact_out_two_pool_runtime_canonicality(
            pools[0],
            pools[1],
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=int(amount_out_total),
            brute_force_max=(None if brute_force_max is None else int(brute_force_max)),
        )
        return 200, {"ok": True, "audit": audit.to_dict()}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "audit_exact_out_two_pool_canonicality_error", "details": "request failed"}


_register("/api/dex/audit_exact_out_two_pool_canonicality", _handle_audit_exact_out_two_pool_canonicality)


# Step 6 declarative schema. Replaces the inline int_fields tuple loop.
# Use this as a template for migrating other handlers and as the single
# source of truth for OpenAPI / JSON-Schema generation.
_AUDIT_MANY_POOL_SCHEMA = EndpointSchema(
    summary="Audit canonicality of many-pool exact-out runtime quote against the canonical winner.",
    requires_pools=True,
    requires_assets=True,
    int_fields=(
        IntFieldSpec(name="amount_out_total", minimum=1, description="Target output amount."),
        IntFieldSpec(name="max_legs", default=3, minimum=1),
        IntFieldSpec(name="max_candidate_pools", default=5, minimum=1),
        IntFieldSpec(name="max_candidates", default=12, minimum=1),
        IntFieldSpec(name="max_iters", default=4096, minimum=1),
        IntFieldSpec(name="window", default=64, minimum=0),
        IntFieldSpec(name="brute_force_max", default=512, minimum=0),
        IntFieldSpec(name="max_full_domain_pools", default=8, minimum=1),
        IntFieldSpec(name="max_enumerated_candidates", default=20_000, minimum=1),
    ),
)


def _handle_audit_exact_out_many_pool_canonicality(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """Demonstrates the Step 6 declarative-schema pattern.

    No try/except: the dispatcher catches ``BadFieldError`` (raised by
    ``parse_int_kwargs`` on validation failure) and converts to
    ``(400, {"ok": False, "error": f"bad_{field}"})``. Any other
    ``Exception`` becomes ``(400, default_error_code, details="request
    failed")`` via the registered ``default_error_code``.
    """
    pools_by_id = parse_pools(obj)
    asset_in = str(obj.get("asset_in", "")).strip()
    asset_out = str(obj.get("asset_out", "")).strip()
    if not asset_in or not asset_out or asset_in == asset_out:
        return 400, {"ok": False, "error": "bad_assets"}
    validated = parse_int_kwargs(obj, _AUDIT_MANY_POOL_SCHEMA.int_fields)

    from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
        audit_exact_out_many_pool_runtime_canonicality,
    )

    audit = audit_exact_out_many_pool_runtime_canonicality(
        list(pools_by_id.values()),
        asset_in=asset_in,
        asset_out=asset_out,
        **validated,
    )
    return 200, {"ok": True, "audit": audit.to_dict()}


_register(
    "/api/dex/audit_exact_out_many_pool_canonicality",
    _handle_audit_exact_out_many_pool_canonicality,
    default_error_code="audit_exact_out_many_pool_canonicality_error",
    schema=_AUDIT_MANY_POOL_SCHEMA,
)


# ======================================================================
# PR2 Batch 4 — build/guard/quote_exact_in_route_* endpoints.
# All 6 share an identical input-validation block (asset_in, asset_out,
# amount_in, split_search_profile, enable_mixed_direct_twohop_split,
# optional binding_ok). Extract that block, then per-endpoint dispatch
# differs only in (importer, response_builder, has_binding_ok, has_bridge).
# ======================================================================
def _validate_exact_in_route_inputs(
    obj: Mapping[str, Any],
    *,
    needs_binding_ok: bool,
) -> DexResponse | dict[str, Any]:
    """Return a parsed kwargs dict on success or a ``DexResponse`` on failure.

    The two return shapes are distinguishable by ``isinstance(result, tuple)``
    (DexResponse is ``Tuple[int, Mapping[str, Any]]``). This gives mypy a
    narrowable union without a sentinel ``None`` second element.
    """
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


def _handle_build_exact_in_route_oracle_contract(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
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


def _handle_guard_exact_in_route_canonicality(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
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


def _handle_quote_exact_in_route_guarded(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        from src.integration._dex_api_helpers import (
            parse_pools,  # pylint: disable=import-outside-toplevel
        )
        from src.integration.api_server import (
            _check_routing_oracle_adapter_bridge,  # pylint: disable=import-outside-toplevel
        )

        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=True)
        if isinstance(kwargs, tuple):
            return kwargs

        bridge_err = _check_routing_oracle_adapter_bridge(
            body=obj,
            path="/api/dex/quote_exact_in_route_guarded",
            asset_in=kwargs["asset_in"],
            asset_out=kwargs["asset_out"],
            amount_in=kwargs["amount_in"],
            split_search_profile=kwargs["split_search_profile"],
            enable_mixed_direct_twohop_split=kwargs["enable_mixed_direct_twohop_split"],
            binding_ok=kwargs["binding_ok"],
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


def _handle_build_exact_in_route_guarded_quote_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
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


def _handle_build_exact_in_route_rank_projection_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
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


def _handle_build_exact_in_route_true_key_interpretation_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
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
        return 400, {"ok": False, "error": "build_exact_in_route_true_key_interpretation_packet_error", "details": "request failed"}


_register("/api/dex/build_exact_in_route_true_key_interpretation_packet", _handle_build_exact_in_route_true_key_interpretation_packet)


# ======================================================================
# PR2 Batch 5 — build_exact_out_many_pool_*_contract endpoints.
# Six contract-builder endpoints share an identical skeleton:
#   parse_pools → assets → int_fields → call → respond.
# Variance: int_field set, module function/schema names, response extras
# (contract_ok flag, quote_endpoint).
# ======================================================================
def _int_field_specs_from_tuples(
    tuples: Sequence[tuple[str, Any, int]],
) -> tuple[IntFieldSpec, ...]:
    """Convert the legacy ``(name, default, minimum)`` tuple form into
    ``IntFieldSpec`` instances for use with ``parse_int_kwargs`` and the
    OpenAPI generator. ``default=None`` means the field is required."""
    return tuple(IntFieldSpec(name=n, default=d, minimum=m) for n, d, m in tuples)


@dataclass(frozen=True)
class _ExactOutContractResponseSpec:
    schema: str
    verify_endpoint: str
    include_contract_ok: bool
    quote_endpoint: Optional[str]


@dataclass(frozen=True)
class _ExactOutContractBuilderSpec:
    field_specs: Sequence[IntFieldSpec]
    module_function_name: str
    module_schema_name: str
    verify_endpoint: str
    error_code: str
    include_contract_ok: bool = False
    quote_endpoint: Optional[str] = None


def _exact_out_contract_response(
    *,
    contract_dict: Mapping[str, Any],
    spec: _ExactOutContractResponseSpec,
) -> dict[str, Any]:
    if spec.quote_endpoint is not None:
        return {
            "ok": True,
            "contract": contract_dict,
            "contract_schema": spec.schema,
            "quote_endpoint": spec.quote_endpoint,
            "verify_contract_endpoint": spec.verify_endpoint,
        }
    if spec.include_contract_ok:
        return {
            "ok": True,
            "contract": contract_dict,
            "contract_ok": bool(contract_dict["contract_ok"]),
            "contract_schema": spec.schema,
            "verify_contract_endpoint": spec.verify_endpoint,
        }
    return {
        "ok": True,
        "contract": contract_dict,
        "contract_schema": spec.schema,
        "verify_contract_endpoint": spec.verify_endpoint,
    }


def _make_exact_out_many_pool_contract_builder(spec: _ExactOutContractBuilderSpec) -> Any:
    """Factory for the build_exact_out_many_pool_*_contract endpoints."""
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

        contract = builder(
            list(pools_by_id.values()),
            asset_in=asset_in,
            asset_out=asset_out,
            **int_kwargs,
        )
        return 200, _exact_out_contract_response(
            contract_dict=contract.to_dict(),
            spec=_ExactOutContractResponseSpec(
                schema=schema,
                verify_endpoint=spec.verify_endpoint,
                include_contract_ok=spec.include_contract_ok,
                quote_endpoint=spec.quote_endpoint,
            ),
        )

    return _handler


_BUILD_EXACT_OUT_CONTRACT_SPECS: tuple[tuple[str, dict[str, Any]], ...] = (
    (
        "/api/dex/build_exact_out_many_pool_candidate_domain_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_candidate_domain_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_candidate_domain_contract",
            "error_code": "build_exact_out_many_pool_candidate_domain_contract_error",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_prefilter_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_prefilter_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_prefilter_contract",
            "error_code": "build_exact_out_many_pool_prefilter_contract_error",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_prefilter_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_full_domain_pools", 8, 1),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_repaired_prefilter_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_prefilter_contract",
            "error_code": "build_exact_out_many_pool_repaired_prefilter_contract_error",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_selected_domain_oracle_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_candidates", 12, 1),
                ("max_iters", 4096, 1),
                ("window", 64, 0),
                ("brute_force_max", 512, 0),
                ("max_full_domain_pools", 8, 1),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_repaired_selected_domain_oracle_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_selected_domain_oracle_contract",
            "error_code": "build_exact_out_many_pool_repaired_selected_domain_oracle_contract_error",
            "quote_endpoint": "/api/dex/quote_exact_out_many_pool_repaired_selected_domain",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_oracle_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_candidates", 12, 1),
                ("max_iters", 4096, 1),
                ("window", 64, 0),
                ("brute_force_max", 512, 0),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_oracle_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_oracle_contract",
            "error_code": "build_exact_out_many_pool_oracle_contract_error",
            "include_contract_ok": True,
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_audited_bounds_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_candidates", 12, 1),
                ("max_iters", 4096, 1),
                ("window", 64, 0),
                ("brute_force_max", 512, 0),
                ("max_full_domain_pools", 8, 1),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_audited_bounds_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_AUDITED_BOUNDS_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_audited_bounds_contract",
            "error_code": "build_exact_out_many_pool_audited_bounds_contract_error",
        },
    ),
)

for _path, _spec in _BUILD_EXACT_OUT_CONTRACT_SPECS:
    # Convert the legacy tuple form to IntFieldSpec for the factory + the
    # registered EndpointSchema. The schema gives us OpenAPI for every
    # contract builder for free.
    _field_specs = _int_field_specs_from_tuples(_spec["field_defaults"])
    _contract_builder_spec = _ExactOutContractBuilderSpec(
        field_specs=_field_specs,
        module_function_name=_spec["module_function_name"],
        module_schema_name=_spec["module_schema_name"],
        verify_endpoint=_spec["verify_endpoint"],
        error_code=_spec["error_code"],
        include_contract_ok=_spec.get("include_contract_ok", False),
        quote_endpoint=_spec.get("quote_endpoint"),
    )
    _handler_fn = _make_exact_out_many_pool_contract_builder(_contract_builder_spec)
    _register(
        _path,
        _handler_fn,
        default_error_code=_contract_builder_spec.error_code,
        schema=EndpointSchema(requires_pools=True, requires_assets=True, int_fields=_field_specs),
    )


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


# ======================================================================
# PR2 Batch 8 — small settlement builders + repaired_full_domain_certified
# quote endpoint.
# ======================================================================
def _handle_build_settlement_feature_extension_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    feature_extension_inputs_obj = obj.get("feature_extension_inputs")
    try:

        feature_extension_inputs = _parse_settlement_feature_extension_inputs_payload(feature_extension_inputs_obj)
        packet = build_settlement_feature_extension_packet(feature_extension_inputs)
        return 200, {"ok": True, "packet": packet.to_dict()}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "build_settlement_feature_extension_packet_error", "details": "request failed"}


_register("/api/dex/build_settlement_feature_extension_packet", _handle_build_settlement_feature_extension_packet)


def _handle_build_settlement_spot_price_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    entries_obj = obj.get("entries")
    now_epoch = obj.get("now_epoch")
    max_staleness_epochs = obj.get("max_staleness_epochs")
    cross_module_sync_required = obj.get("cross_module_sync_required", False)
    cross_module_sync_contract = obj.get("cross_module_sync_contract")
    if not isinstance(entries_obj, list) or not entries_obj:
        return 400, {"ok": False, "error": "bad_entries"}
    if not isinstance(now_epoch, int) or isinstance(now_epoch, bool) or now_epoch < 0:
        return 400, {"ok": False, "error": "bad_now_epoch"}
    if not isinstance(max_staleness_epochs, int) or isinstance(max_staleness_epochs, bool) or max_staleness_epochs < 0:
        return 400, {"ok": False, "error": "bad_max_staleness_epochs"}
    if not isinstance(cross_module_sync_required, bool):
        return 400, {"ok": False, "error": "bad_cross_module_sync_required"}
    if cross_module_sync_contract is not None and not isinstance(cross_module_sync_contract, dict):
        return 400, {"ok": False, "error": "bad_cross_module_sync_contract"}
    try:
        entries = tuple(SettlementSpotPriceEntry.from_dict(entry) for entry in entries_obj)
        packet = build_settlement_spot_price_packet(
            entries=entries,
            now_epoch=int(now_epoch),
            max_staleness_epochs=int(max_staleness_epochs),
            cross_module_sync_required=bool(cross_module_sync_required),
            cross_module_sync_contract=cross_module_sync_contract,
        )
        return 200, {"ok": True, "packet": packet.to_dict()}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "build_settlement_spot_price_packet_error", "details": "request failed"}


_register("/api/dex/build_settlement_spot_price_packet", _handle_build_settlement_spot_price_packet)


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
