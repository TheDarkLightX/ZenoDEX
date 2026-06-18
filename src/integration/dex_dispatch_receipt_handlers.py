"""Impact-preview and receipt-verifier handlers for the DEX dispatch registry."""

from __future__ import annotations

from typing import Any, Mapping

from src.core.price_impact_preview import price_impact_preview
from src.core.quote_receipts import verify_route_quote_receipt
from src.integration._dex_api_helpers import parse_pools
from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register
from src.integration.exact_in_route_certificate import (
    verify_exact_in_route_guarded_quote_packet_payload,
    verify_exact_in_route_oracle_contract_payload,
    verify_exact_in_route_rank_projection_packet_payload,
    verify_exact_in_route_true_key_interpretation_packet_payload,
)

BOUNDARY_DOMAIN_ERRORS: tuple[type[Exception], ...] = (TypeError, ValueError, ArithmeticError)


def _coerce_int(value: Any, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{field} must be an int")
    return int(value)


def _handle_impact_preview(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """Return the legacy price-impact response shape for ``/api/dex/impact_preview``."""
    reserve_in = _coerce_int(obj.get("reserve_in", 0), "reserve_in")
    reserve_out = _coerce_int(obj.get("reserve_out", 0), "reserve_out")
    amount_in = _coerce_int(obj.get("amount_in", 0), "amount_in")
    fee_bps = _coerce_int(obj.get("fee_bps", 0), "fee_bps")
    pending_same_dir = _coerce_int(obj.get("pending_volume_same_direction", 0), "pending_volume_same_direction")
    confidence_bps = _coerce_int(obj.get("confidence_bps", 9500), "confidence_bps")

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


def _import_verify_exact_in_route_oracle_contract_payload() -> Any:
    return verify_exact_in_route_oracle_contract_payload


def _import_verify_exact_in_route_guarded_quote_packet_payload() -> Any:
    return verify_exact_in_route_guarded_quote_packet_payload


def _import_verify_exact_in_route_rank_projection_packet_payload() -> Any:
    return verify_exact_in_route_rank_projection_packet_payload


def _import_verify_exact_in_route_true_key_interpretation_packet_payload() -> Any:
    return verify_exact_in_route_true_key_interpretation_packet_payload


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


def register_receipt_handlers() -> None:
    _register("/api/dex/impact_preview", _handle_impact_preview, default_error_code="impact_preview_error")
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
    _register("/api/dex/verify_quote_receipt", _handle_verify_quote_receipt)


register_receipt_handlers()
