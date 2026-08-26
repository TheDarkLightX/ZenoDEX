"""Settlement price, feature-extension, and exact-out audit dispatch handlers."""

from __future__ import annotations

from typing import Any, Mapping

from src.integration._dex_api_helpers import (
    EndpointSchema,
    IntFieldSpec,
    exact_out_split_quote_from_dict,
    parse_int_kwargs,
    parse_pools,
)
from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register
from src.integration.api_server_settlement_parsers import (
    _parse_settlement_feature_extension_inputs_payload,
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


def _make_simple_verifier(
    *,
    payload_key: str,
    importer: Any,
    error_code: str,
) -> Any:
    """Build a handler for the ``payload_key -> verifier -> ok/err`` shape."""

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


def _import_verify_settlement_spot_price_packet_payload() -> Any:
    return verify_settlement_spot_price_packet_payload


def _handle_verify_settlement_feature_extension_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
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


def _handle_verify_settlement_spot_price_attestation(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
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


def _handle_build_settlement_spot_price_attestation(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
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


def _handle_build_exact_out_route_certificate(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
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


def _handle_build_settlement_feature_extension_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    feature_extension_inputs_obj = obj.get("feature_extension_inputs")
    try:
        feature_extension_inputs = _parse_settlement_feature_extension_inputs_payload(feature_extension_inputs_obj)
        packet = build_settlement_feature_extension_packet(feature_extension_inputs)
        return 200, {"ok": True, "packet": packet.to_dict()}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "build_settlement_feature_extension_packet_error", "details": "request failed"}


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


def register_settlement_audit_handlers() -> None:
    _register(
        "/api/dex/verify_settlement_spot_price_packet",
        _make_simple_verifier(
            payload_key="packet",
            importer=_import_verify_settlement_spot_price_packet_payload,
            error_code="verify_settlement_spot_price_packet_error",
        ),
    )
    _register("/api/dex/verify_settlement_feature_extension_packet", _handle_verify_settlement_feature_extension_packet)
    _register("/api/dex/verify_settlement_spot_price_attestation", _handle_verify_settlement_spot_price_attestation)
    _register("/api/dex/build_exact_out_route_certificate", _handle_build_exact_out_route_certificate)
    _register("/api/dex/audit_exact_out_two_pool_canonicality", _handle_audit_exact_out_two_pool_canonicality)
    _register(
        "/api/dex/audit_exact_out_many_pool_canonicality",
        _handle_audit_exact_out_many_pool_canonicality,
        default_error_code="audit_exact_out_many_pool_canonicality_error",
        schema=_AUDIT_MANY_POOL_SCHEMA,
    )
    _register("/api/dex/build_settlement_feature_extension_packet", _handle_build_settlement_feature_extension_packet)
    _register("/api/dex/build_settlement_spot_price_packet", _handle_build_settlement_spot_price_packet)


register_settlement_audit_handlers()
