"""Settlement value-packet handlers for the DEX dispatch registry."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register
from src.integration.dex_dispatch_settlement_value_handlers import (
    BOUNDARY_DOMAIN_ERRORS,
    _bad_request,
    _parse_lp_unit_values,
    _parse_nonnegative_int,
    _parse_settlement,
)


@dataclass(frozen=True)
class _ValuePacketInputs:
    settlement_obj: dict[str, Any]
    price_packet_obj: dict[str, Any] | None
    price_attestation_obj: dict[str, Any] | None
    consumer_now_epoch: int | None
    max_attestation_age_epochs: int | None
    allowed_signers_obj: dict[str, Any] | None
    lp_unit_values_obj: dict[str, Any] | None
    packet_obj: dict[str, Any] | None = None


def _parse_value_packet_inputs(
    obj: Mapping[str, Any],
    *,
    require_packet: bool,
) -> DexResponse | _ValuePacketInputs:
    settlement_obj = obj.get("settlement")
    price_packet_obj = obj.get("price_packet")
    price_attestation_obj = obj.get("price_attestation")
    consumer_now_epoch = obj.get("consumer_now_epoch")
    max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
    allowed_signers_obj = obj.get("allowed_signers")
    lp_unit_values_obj = obj.get("lp_unit_values")
    packet_obj = obj.get("packet")

    if not isinstance(settlement_obj, dict):
        return _bad_request("bad_settlement")
    if price_packet_obj is None and price_attestation_obj is None:
        return _bad_request("missing_price_input")
    if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
        return _bad_request("bad_price_packet")
    if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
        return _bad_request("bad_price_attestation")
    if lp_unit_values_obj is not None and (not isinstance(lp_unit_values_obj, dict) or not lp_unit_values_obj):
        return _bad_request("bad_lp_unit_values")
    if require_packet and not isinstance(packet_obj, dict):
        return _bad_request("bad_packet")

    parsed_consumer_now_epoch: int | None = None
    parsed_max_attestation_age_epochs: int | None = None
    if price_attestation_obj is not None:
        parsed_consumer_now_epoch = _parse_nonnegative_int(
            consumer_now_epoch,
            error="bad_consumer_now_epoch",
        )
        if isinstance(parsed_consumer_now_epoch, tuple):
            return parsed_consumer_now_epoch

        parsed_max_attestation_age_epochs = _parse_nonnegative_int(
            max_attestation_age_epochs,
            error="bad_max_attestation_age_epochs",
        )
        if isinstance(parsed_max_attestation_age_epochs, tuple):
            return parsed_max_attestation_age_epochs

        if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
            return _bad_request("bad_allowed_signers")

    return _ValuePacketInputs(
        settlement_obj=settlement_obj,
        price_packet_obj=price_packet_obj if isinstance(price_packet_obj, dict) else None,
        price_attestation_obj=price_attestation_obj if isinstance(price_attestation_obj, dict) else None,
        consumer_now_epoch=parsed_consumer_now_epoch,
        max_attestation_age_epochs=parsed_max_attestation_age_epochs,
        allowed_signers_obj=allowed_signers_obj if isinstance(allowed_signers_obj, dict) else None,
        lp_unit_values_obj=lp_unit_values_obj if isinstance(lp_unit_values_obj, dict) else None,
        packet_obj=packet_obj if isinstance(packet_obj, dict) else None,
    )


def _optional_lp_unit_values(lp_unit_values_obj: Mapping[str, Any] | None) -> dict[str, int] | None:
    if lp_unit_values_obj is None:
        return None
    return _parse_lp_unit_values(lp_unit_values_obj)


def _build_value_packet(inputs: _ValuePacketInputs) -> Any:
    settlement = _parse_settlement(inputs.settlement_obj)
    lp_unit_values = _optional_lp_unit_values(inputs.lp_unit_values_obj)

    if inputs.price_attestation_obj is not None:
        from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
            SettlementSpotPriceAttestation,
        )
        from src.integration.settlement_value_packet import (  # pylint: disable=import-outside-toplevel
            build_settlement_value_packet_from_price_attestation,
        )

        return build_settlement_value_packet_from_price_attestation(
            settlement=settlement,
            price_attestation=SettlementSpotPriceAttestation.from_dict(inputs.price_attestation_obj),
            consumer_now_epoch=int(inputs.consumer_now_epoch),
            max_attestation_age_epochs=int(inputs.max_attestation_age_epochs),
            lp_unit_values=lp_unit_values,
            allowed_signers=inputs.allowed_signers_obj,
        )

    from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
        SettlementSpotPricePacket,
    )
    from src.integration.settlement_value_packet import (  # pylint: disable=import-outside-toplevel
        build_settlement_value_packet_from_price_packet,
    )

    return build_settlement_value_packet_from_price_packet(
        settlement=settlement,
        price_packet=SettlementSpotPricePacket.from_dict(inputs.price_packet_obj),
        lp_unit_values=lp_unit_values,
    )


def _verify_value_packet(inputs: _ValuePacketInputs) -> tuple[bool, str | None]:
    settlement = _parse_settlement(inputs.settlement_obj)
    if inputs.packet_obj is None:
        raise ValueError("missing packet")
    lp_unit_values = _optional_lp_unit_values(inputs.lp_unit_values_obj)

    if inputs.price_attestation_obj is not None:
        from src.integration.settlement_value_packet import (  # pylint: disable=import-outside-toplevel
            verify_settlement_value_packet_payload_from_price_attestation,
        )

        return verify_settlement_value_packet_payload_from_price_attestation(
            settlement=settlement,
            price_attestation_payload=inputs.price_attestation_obj,
            consumer_now_epoch=int(inputs.consumer_now_epoch),
            max_attestation_age_epochs=int(inputs.max_attestation_age_epochs),
            packet_payload=inputs.packet_obj,
            lp_unit_values=lp_unit_values,
            allowed_signers=inputs.allowed_signers_obj,
        )

    from src.integration.settlement_value_packet import (  # pylint: disable=import-outside-toplevel
        verify_settlement_value_packet_payload_from_price_packet,
    )

    return verify_settlement_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=inputs.price_packet_obj,
        packet_payload=inputs.packet_obj,
        lp_unit_values=lp_unit_values,
    )


def _handle_build_settlement_value_packet(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    inputs = _parse_value_packet_inputs(obj, require_packet=False)
    if isinstance(inputs, tuple):
        return inputs
    try:
        packet = _build_value_packet(inputs)
        return 200, {"ok": True, "packet": packet.to_dict()}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "build_settlement_value_packet_error",
            "details": "request failed",
        }


def _handle_verify_settlement_value_packet(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    inputs = _parse_value_packet_inputs(obj, require_packet=True)
    if isinstance(inputs, tuple):
        return inputs
    try:
        ok, err = _verify_value_packet(inputs)
        return 200, {"ok": bool(ok), "error": err}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "verify_settlement_value_packet_error",
            "details": "request failed",
        }


_register("/api/dex/build_settlement_value_packet", _handle_build_settlement_value_packet)
_register("/api/dex/verify_settlement_value_packet", _handle_verify_settlement_value_packet)
