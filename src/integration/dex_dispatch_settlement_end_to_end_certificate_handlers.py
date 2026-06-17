"""End-to-end settlement certificate-packet handlers for DEX dispatch."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register
from src.integration.api_server_settlement_parsers import (
    _parse_price_history_payload,
    _parse_settlement_feature_extension_inputs_payload,
    _parse_settlement_proof_flags_payload,
)
from src.integration.dex_dispatch_settlement_endogenous_lp_handlers import _parse_pool_snapshots
from src.integration.dex_dispatch_settlement_value_handlers import (
    BOUNDARY_DOMAIN_ERRORS,
    _bad_request,
    _parse_lp_unit_values,
    _parse_nonnegative_int,
    _parse_settlement,
)


@dataclass(frozen=True)
class _EndToEndCertificateInputs:
    settlement_obj: dict[str, Any]
    proof_flags_obj: object
    price_history_obj: object
    feature_extension_inputs_obj: object
    price_packet_obj: dict[str, Any] | None
    price_attestation_obj: dict[str, Any] | None
    pool_snapshots_obj: list[Any] | None
    lp_unit_values_obj: dict[str, Any] | None
    consumer_now_epoch: int | None
    max_attestation_age_epochs: int | None
    allowed_signers_obj: dict[str, Any] | None
    packet_obj: dict[str, Any] | None = None


@dataclass(frozen=True)
class _AttestationControls:
    consumer_now_epoch: int | None
    max_attestation_age_epochs: int | None
    allowed_signers_obj: dict[str, Any] | None


def _parse_attestation_controls(
    *,
    price_attestation_obj: object,
    consumer_now_epoch: object,
    max_attestation_age_epochs: object,
    allowed_signers_obj: object,
) -> DexResponse | _AttestationControls:
    if price_attestation_obj is None:
        return _AttestationControls(None, None, None)

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

    return _AttestationControls(
        parsed_consumer_now_epoch,
        parsed_max_attestation_age_epochs,
        allowed_signers_obj if isinstance(allowed_signers_obj, dict) else None,
    )


def _parse_end_to_end_inputs(
    obj: Mapping[str, Any],
    *,
    require_packet: bool,
) -> DexResponse | _EndToEndCertificateInputs:
    settlement_obj = obj.get("settlement")
    proof_flags_obj = obj.get("proof_flags")
    price_history_obj = obj.get("price_history")
    feature_extension_inputs_obj = obj.get("feature_extension_inputs")
    price_packet_obj = obj.get("price_packet")
    price_attestation_obj = obj.get("price_attestation")
    pool_snapshots_obj = obj.get("pool_snapshots")
    lp_unit_values_obj = obj.get("lp_unit_values")
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
    if pool_snapshots_obj is not None and (not isinstance(pool_snapshots_obj, list) or not pool_snapshots_obj):
        return _bad_request("bad_pool_snapshots")
    if lp_unit_values_obj is not None and (not isinstance(lp_unit_values_obj, dict) or not lp_unit_values_obj):
        return _bad_request("bad_lp_unit_values")
    if pool_snapshots_obj is not None and lp_unit_values_obj is not None:
        return _bad_request("conflicting_value_mode_inputs")
    if require_packet and not isinstance(packet_obj, dict):
        return _bad_request("bad_packet")

    attestation_controls = _parse_attestation_controls(
        price_attestation_obj=price_attestation_obj,
        consumer_now_epoch=consumer_now_epoch,
        max_attestation_age_epochs=max_attestation_age_epochs,
        allowed_signers_obj=allowed_signers_obj,
    )
    if isinstance(attestation_controls, tuple):
        return attestation_controls

    return _EndToEndCertificateInputs(
        settlement_obj=settlement_obj,
        proof_flags_obj=proof_flags_obj,
        price_history_obj=price_history_obj,
        feature_extension_inputs_obj=feature_extension_inputs_obj,
        price_packet_obj=price_packet_obj if isinstance(price_packet_obj, dict) else None,
        price_attestation_obj=price_attestation_obj if isinstance(price_attestation_obj, dict) else None,
        pool_snapshots_obj=pool_snapshots_obj if isinstance(pool_snapshots_obj, list) else None,
        lp_unit_values_obj=lp_unit_values_obj if isinstance(lp_unit_values_obj, dict) else None,
        consumer_now_epoch=attestation_controls.consumer_now_epoch,
        max_attestation_age_epochs=attestation_controls.max_attestation_age_epochs,
        allowed_signers_obj=attestation_controls.allowed_signers_obj,
        packet_obj=packet_obj if isinstance(packet_obj, dict) else None,
    )


def _optional_lp_unit_values(lp_unit_values_obj: Mapping[str, Any] | None) -> dict[str, int] | None:
    if lp_unit_values_obj is None:
        return None
    return _parse_lp_unit_values(lp_unit_values_obj)


def _optional_pool_snapshots(pool_snapshots_obj: list[Any] | None) -> tuple[Any, ...] | None:
    if pool_snapshots_obj is None:
        return None
    return _parse_pool_snapshots(pool_snapshots_obj)


def _build_end_to_end_packet(inputs: _EndToEndCertificateInputs) -> Any:
    settlement = _parse_settlement(inputs.settlement_obj)
    proof_flags = _parse_settlement_proof_flags_payload(inputs.proof_flags_obj)
    price_history = _parse_price_history_payload(inputs.price_history_obj)
    feature_extension_inputs = _parse_settlement_feature_extension_inputs_payload(
        inputs.feature_extension_inputs_obj,
    )
    lp_unit_values = _optional_lp_unit_values(inputs.lp_unit_values_obj)
    pool_snapshots = _optional_pool_snapshots(inputs.pool_snapshots_obj)

    if inputs.price_attestation_obj is not None:
        from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
            build_settlement_end_to_end_certificate_packet_from_price_attestation,
        )
        from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
            SettlementSpotPriceAttestation,
        )

        return build_settlement_end_to_end_certificate_packet_from_price_attestation(
            settlement=settlement,
            proof_flags=proof_flags,
            price_history=price_history,
            feature_extension_inputs=feature_extension_inputs,
            price_attestation=SettlementSpotPriceAttestation.from_dict(inputs.price_attestation_obj),
            consumer_now_epoch=int(inputs.consumer_now_epoch),
            max_attestation_age_epochs=int(inputs.max_attestation_age_epochs),
            lp_unit_values=lp_unit_values,
            pool_snapshots=pool_snapshots,
            allowed_signers=inputs.allowed_signers_obj,
        )

    from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
        build_settlement_end_to_end_certificate_packet_from_price_packet,
    )
    from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
        SettlementSpotPricePacket,
    )

    return build_settlement_end_to_end_certificate_packet_from_price_packet(
        settlement=settlement,
        proof_flags=proof_flags,
        price_history=price_history,
        feature_extension_inputs=feature_extension_inputs,
        price_packet=SettlementSpotPricePacket.from_dict(inputs.price_packet_obj),
        lp_unit_values=lp_unit_values,
        pool_snapshots=pool_snapshots,
    )


def _verify_end_to_end_packet(inputs: _EndToEndCertificateInputs) -> tuple[bool, str | None]:
    settlement = _parse_settlement(inputs.settlement_obj)
    proof_flags = _parse_settlement_proof_flags_payload(inputs.proof_flags_obj)
    price_history = _parse_price_history_payload(inputs.price_history_obj)
    lp_unit_values = _optional_lp_unit_values(inputs.lp_unit_values_obj)
    if inputs.packet_obj is None:
        raise ValueError("missing packet")

    if inputs.price_attestation_obj is not None:
        from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
            verify_settlement_end_to_end_certificate_packet_payload_from_price_attestation,
        )

        return verify_settlement_end_to_end_certificate_packet_payload_from_price_attestation(
            settlement=settlement,
            proof_flags=proof_flags,
            price_history=price_history,
            feature_extension_inputs_payload=inputs.feature_extension_inputs_obj,
            price_attestation_payload=inputs.price_attestation_obj,
            consumer_now_epoch=int(inputs.consumer_now_epoch),
            max_attestation_age_epochs=int(inputs.max_attestation_age_epochs),
            packet_payload=inputs.packet_obj,
            lp_unit_values=lp_unit_values,
            pool_snapshots_payload=inputs.pool_snapshots_obj,
            allowed_signers=inputs.allowed_signers_obj,
        )

    from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
        verify_settlement_end_to_end_certificate_packet_payload_from_price_packet,
    )

    return verify_settlement_end_to_end_certificate_packet_payload_from_price_packet(
        settlement=settlement,
        proof_flags=proof_flags,
        price_history=price_history,
        feature_extension_inputs_payload=inputs.feature_extension_inputs_obj,
        price_packet_payload=inputs.price_packet_obj,
        packet_payload=inputs.packet_obj,
        lp_unit_values=lp_unit_values,
        pool_snapshots_payload=inputs.pool_snapshots_obj,
    )


def _handle_build_settlement_end_to_end_certificate_packet(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    inputs = _parse_end_to_end_inputs(obj, require_packet=False)
    if isinstance(inputs, tuple):
        return inputs
    try:
        packet = _build_end_to_end_packet(inputs)
        return 200, {"ok": True, "packet": packet.to_dict()}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "build_settlement_end_to_end_certificate_packet_error",
            "details": "request failed",
        }


def _handle_verify_settlement_end_to_end_certificate_packet(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    inputs = _parse_end_to_end_inputs(obj, require_packet=True)
    if isinstance(inputs, tuple):
        return inputs
    try:
        ok, err = _verify_end_to_end_packet(inputs)
        return 200, {"ok": bool(ok), "error": err}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "verify_settlement_end_to_end_certificate_packet_error",
            "details": "request failed",
        }


_register(
    "/api/dex/build_settlement_end_to_end_certificate_packet",
    _handle_build_settlement_end_to_end_certificate_packet,
)
_register(
    "/api/dex/verify_settlement_end_to_end_certificate_packet",
    _handle_verify_settlement_end_to_end_certificate_packet,
)
