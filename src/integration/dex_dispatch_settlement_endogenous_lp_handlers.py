"""Endogenous LP value-packet handlers for the DEX dispatch registry."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register
from src.integration.dex_dispatch_settlement_value_handlers import (
    BOUNDARY_DOMAIN_ERRORS,
    _bad_request,
    _parse_nonnegative_int,
    _parse_settlement,
)


@dataclass(frozen=True)
class _EndogenousLPInputs:
    settlement_obj: dict[str, Any]
    price_packet_obj: dict[str, Any] | None
    price_attestation_obj: dict[str, Any] | None
    pool_snapshots_obj: list[Any]
    consumer_now_epoch: int | None
    max_attestation_age_epochs: int | None
    allowed_signers_obj: dict[str, Any] | None
    packet_obj: dict[str, Any] | None = None


def _parse_endogenous_lp_inputs(
    obj: Mapping[str, Any],
    *,
    require_packet: bool,
) -> DexResponse | _EndogenousLPInputs:
    settlement_obj = obj.get("settlement")
    price_packet_obj = obj.get("price_packet")
    price_attestation_obj = obj.get("price_attestation")
    pool_snapshots_obj = obj.get("pool_snapshots")
    consumer_now_epoch = obj.get("consumer_now_epoch")
    max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
    allowed_signers_obj = obj.get("allowed_signers")
    packet_obj = obj.get("packet")

    if not isinstance(settlement_obj, dict):
        return _bad_request("bad_settlement")
    if price_packet_obj is None and price_attestation_obj is None:
        return _bad_request("missing_price_input")
    if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
        return _bad_request("bad_price_packet")
    if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
        return _bad_request("bad_price_attestation")
    if not isinstance(pool_snapshots_obj, list) or not pool_snapshots_obj:
        return _bad_request("bad_pool_snapshots")
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

    return _EndogenousLPInputs(
        settlement_obj=settlement_obj,
        price_packet_obj=price_packet_obj if isinstance(price_packet_obj, dict) else None,
        price_attestation_obj=price_attestation_obj if isinstance(price_attestation_obj, dict) else None,
        pool_snapshots_obj=pool_snapshots_obj,
        consumer_now_epoch=parsed_consumer_now_epoch,
        max_attestation_age_epochs=parsed_max_attestation_age_epochs,
        allowed_signers_obj=allowed_signers_obj if isinstance(allowed_signers_obj, dict) else None,
        packet_obj=packet_obj if isinstance(packet_obj, dict) else None,
    )


def _parse_pool_snapshots(pool_snapshots_obj: Sequence[Any]) -> tuple[Any, ...]:
    from src.integration.settlement_endogenous_lp_value_packet import (  # pylint: disable=import-outside-toplevel
        _pool_from_dict,
    )

    return tuple(_pool_from_dict(snapshot) for snapshot in pool_snapshots_obj)


def _build_endogenous_lp_packet(inputs: _EndogenousLPInputs) -> Any:
    settlement = _parse_settlement(inputs.settlement_obj)
    pool_snapshots = _parse_pool_snapshots(inputs.pool_snapshots_obj)

    if inputs.price_attestation_obj is not None:
        from src.integration.settlement_endogenous_lp_value_packet import (  # pylint: disable=import-outside-toplevel
            build_settlement_endogenous_lp_value_packet_from_price_attestation,
        )
        from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
            SettlementSpotPriceAttestation,
        )

        return build_settlement_endogenous_lp_value_packet_from_price_attestation(
            settlement=settlement,
            price_attestation=SettlementSpotPriceAttestation.from_dict(inputs.price_attestation_obj),
            consumer_now_epoch=int(inputs.consumer_now_epoch),
            max_attestation_age_epochs=int(inputs.max_attestation_age_epochs),
            pool_snapshots=pool_snapshots,
            allowed_signers=inputs.allowed_signers_obj,
        )

    from src.integration.settlement_endogenous_lp_value_packet import (  # pylint: disable=import-outside-toplevel
        build_settlement_endogenous_lp_value_packet_from_price_packet,
    )
    from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
        SettlementSpotPricePacket,
    )

    return build_settlement_endogenous_lp_value_packet_from_price_packet(
        settlement=settlement,
        price_packet=SettlementSpotPricePacket.from_dict(inputs.price_packet_obj),
        pool_snapshots=pool_snapshots,
    )


def _verify_endogenous_lp_packet(inputs: _EndogenousLPInputs) -> tuple[bool, str | None]:
    settlement = _parse_settlement(inputs.settlement_obj)
    if inputs.packet_obj is None:
        raise ValueError("missing packet")

    if inputs.price_attestation_obj is not None:
        from src.integration.settlement_endogenous_lp_value_packet import (  # pylint: disable=import-outside-toplevel
            verify_settlement_endogenous_lp_value_packet_payload_from_price_attestation,
        )

        return verify_settlement_endogenous_lp_value_packet_payload_from_price_attestation(
            settlement=settlement,
            price_attestation_payload=inputs.price_attestation_obj,
            consumer_now_epoch=int(inputs.consumer_now_epoch),
            max_attestation_age_epochs=int(inputs.max_attestation_age_epochs),
            pool_snapshots_payload=inputs.pool_snapshots_obj,
            packet_payload=inputs.packet_obj,
            allowed_signers=inputs.allowed_signers_obj,
        )

    from src.integration.settlement_endogenous_lp_value_packet import (  # pylint: disable=import-outside-toplevel
        verify_settlement_endogenous_lp_value_packet_payload_from_price_packet,
    )

    return verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=inputs.price_packet_obj,
        pool_snapshots_payload=inputs.pool_snapshots_obj,
        packet_payload=inputs.packet_obj,
    )


def _handle_build_settlement_endogenous_lp_value_packet(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    inputs = _parse_endogenous_lp_inputs(obj, require_packet=False)
    if isinstance(inputs, tuple):
        return inputs
    try:
        packet = _build_endogenous_lp_packet(inputs)
        return 200, {"ok": True, "packet": packet.to_dict()}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "build_settlement_endogenous_lp_value_packet_error",
            "details": "request failed",
        }


def _handle_verify_settlement_endogenous_lp_value_packet(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    inputs = _parse_endogenous_lp_inputs(obj, require_packet=True)
    if isinstance(inputs, tuple):
        return inputs
    try:
        ok, err = _verify_endogenous_lp_packet(inputs)
        return 200, {"ok": bool(ok), "error": err}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "verify_settlement_endogenous_lp_value_packet_error",
            "details": "request failed",
        }


_register(
    "/api/dex/build_settlement_endogenous_lp_value_packet",
    _handle_build_settlement_endogenous_lp_value_packet,
)
_register(
    "/api/dex/verify_settlement_endogenous_lp_value_packet",
    _handle_verify_settlement_endogenous_lp_value_packet,
)
