from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


WriteJson = Callable[[int, object], None]

_BUILD_END_TO_END_CERTIFICATE_PACKET_ENDPOINT = "/api/dex/build_settlement_end_to_end_certificate_packet"
_VERIFY_END_TO_END_CERTIFICATE_PACKET_ENDPOINT = "/api/dex/verify_settlement_end_to_end_certificate_packet"


@dataclass(frozen=True)
class EndToEndCertificateRequest:
    settlement: dict[str, object]
    proof_flags: object
    price_history: object
    feature_extension_inputs: object
    price_packet: dict[str, object] | None
    price_attestation: dict[str, object] | None
    pool_snapshots: list[object] | None
    lp_unit_values: dict[str, object] | None
    consumer_now_epoch: int | None
    max_attestation_age_epochs: int | None
    allowed_signers: dict[str, object] | None


class BadRequest(Exception):
    def __init__(self, error: str) -> None:
        super().__init__(error)
        self.error = error


def _parse_request(obj: dict[str, object], *, validate_attestation: bool) -> EndToEndCertificateRequest:
    settlement = _required_dict(obj.get("settlement"), "bad_settlement")
    price_packet = _optional_dict(obj.get("price_packet"), "bad_price_packet")
    price_attestation = _optional_dict(obj.get("price_attestation"), "bad_price_attestation")
    _require_price_input(price_packet, price_attestation)
    pool_snapshots = _optional_list(obj.get("pool_snapshots"), "bad_pool_snapshots", non_empty=True)
    lp_unit_values = _optional_dict(obj.get("lp_unit_values"), "bad_lp_unit_values", non_empty=True)
    _reject_conflicting_value_mode_inputs(pool_snapshots, lp_unit_values)
    parsed_consumer_epoch, parsed_max_age, parsed_allowed_signers = _parse_attestation_options(
        obj=obj,
        has_price_attestation=price_attestation is not None,
        validate_attestation=validate_attestation,
    )

    return EndToEndCertificateRequest(
        settlement=settlement,
        proof_flags=obj.get("proof_flags"),
        price_history=obj.get("price_history"),
        feature_extension_inputs=obj.get("feature_extension_inputs"),
        price_packet=price_packet,
        price_attestation=price_attestation,
        pool_snapshots=pool_snapshots,
        lp_unit_values=lp_unit_values,
        consumer_now_epoch=parsed_consumer_epoch,
        max_attestation_age_epochs=parsed_max_age,
        allowed_signers=parsed_allowed_signers,
    )


def _required_dict(value: object, error: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise BadRequest(error)
    return value


def _optional_dict(value: object, error: str, *, non_empty: bool = False) -> dict[str, object] | None:
    if value is None:
        return None
    if not isinstance(value, dict):
        raise BadRequest(error)
    if non_empty and not value:
        raise BadRequest(error)
    return value


def _optional_list(value: object, error: str, *, non_empty: bool = False) -> list[object] | None:
    if value is None:
        return None
    if not isinstance(value, list):
        raise BadRequest(error)
    if non_empty and not value:
        raise BadRequest(error)
    return value


def _require_price_input(
    price_packet: dict[str, object] | None,
    price_attestation: dict[str, object] | None,
) -> None:
    if price_packet is None and price_attestation is None:
        raise BadRequest("missing_price_input")


def _reject_conflicting_value_mode_inputs(
    pool_snapshots: list[object] | None,
    lp_unit_values: dict[str, object] | None,
) -> None:
    if pool_snapshots is not None and lp_unit_values is not None:
        raise BadRequest("conflicting_value_mode_inputs")


def _parse_attestation_options(
    *,
    obj: dict[str, object],
    has_price_attestation: bool,
    validate_attestation: bool,
) -> tuple[int | None, int | None, dict[str, object] | None]:
    if not has_price_attestation or not validate_attestation:
        return None, None, None
    allowed_signers = obj.get("allowed_signers")
    return (
        _non_negative_int(obj.get("consumer_now_epoch"), "bad_consumer_now_epoch"),
        _non_negative_int(obj.get("max_attestation_age_epochs"), "bad_max_attestation_age_epochs"),
        _allowed_signers(allowed_signers),
    )


def _non_negative_int(value: object, error: str) -> int:
    if isinstance(value, bool):
        raise BadRequest(error)
    if not isinstance(value, int):
        raise BadRequest(error)
    if value < 0:
        raise BadRequest(error)
    return int(value)


def _allowed_signers(value: object) -> dict[str, object] | None:
    if value is None:
        return None
    if not isinstance(value, dict):
        raise BadRequest("bad_allowed_signers")
    return value


def _parse_lp_unit_values(lp_unit_values_obj: dict[str, object] | None) -> dict[str, int] | None:
    if lp_unit_values_obj is None:
        return None
    lp_unit_values: dict[str, int] = {}
    for raw_pool_id, raw_unit_value in lp_unit_values_obj.items():
        pool_id = _pool_id(raw_pool_id)
        lp_unit_values[pool_id] = _lp_unit_value(pool_id, raw_unit_value)
    return lp_unit_values


def _pool_id(raw_pool_id: object) -> str:
    pool_id = str(raw_pool_id).strip()
    if not pool_id:
        raise ValueError("lp_unit_values keys must be non-empty strings")
    return pool_id


def _lp_unit_value(pool_id: str, raw_unit_value: object) -> int:
    if isinstance(raw_unit_value, bool):
        raise ValueError(f"lp unit value must be a non-negative int for {pool_id}")
    if not isinstance(raw_unit_value, int):
        raise ValueError(f"lp unit value must be a non-negative int for {pool_id}")
    if raw_unit_value < 0:
        raise ValueError(f"lp unit value must be a non-negative int for {pool_id}")
    return int(raw_unit_value)


def _handle_build_end_to_end_certificate_packet(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        req = _parse_request(obj, validate_attestation=True)
    except BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
        return

    try:
        from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel

        settlement = _parse_settlement(req.settlement)
        proof_flags, price_history, feature_inputs = _parse_common_inputs(req)
        pool_snapshots = _parse_pool_snapshots(req.pool_snapshots)
        lp_unit_values = _parse_lp_unit_values(req.lp_unit_values)
        packet = _build_packet(req, settlement, proof_flags, price_history, feature_inputs, lp_unit_values, pool_snapshots)
        write_json(200, {"ok": True, "packet": packet.to_dict()})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "build_settlement_end_to_end_certificate_packet_error", "details": "request failed"},
        )


def _parse_common_inputs(req: EndToEndCertificateRequest) -> tuple[object, object, object]:
    from src.integration.api_server_settlement_parsers import (  # pylint: disable=import-outside-toplevel
        _parse_price_history_payload,
        _parse_settlement_feature_extension_inputs_payload,
        _parse_settlement_proof_flags_payload,
    )

    return (
        _parse_settlement_proof_flags_payload(req.proof_flags),
        _parse_price_history_payload(req.price_history),
        _parse_settlement_feature_extension_inputs_payload(req.feature_extension_inputs),
    )


def _parse_pool_snapshots(pool_snapshots_obj: list[object] | None) -> tuple[object, ...] | None:
    if pool_snapshots_obj is None:
        return None
    from src.integration.settlement_endogenous_lp_value_packet import (  # pylint: disable=import-outside-toplevel
        _pool_from_dict,
    )

    return tuple(_pool_from_dict(snapshot) for snapshot in pool_snapshots_obj)


def _build_packet(
    req: EndToEndCertificateRequest,
    settlement: object,
    proof_flags: object,
    price_history: object,
    feature_inputs: object,
    lp_unit_values: dict[str, int] | None,
    pool_snapshots: tuple[object, ...] | None,
) -> object:
    if req.price_attestation is not None:
        return _build_packet_from_attestation(
            req, settlement, proof_flags, price_history, feature_inputs, lp_unit_values, pool_snapshots
        )
    return _build_packet_from_price_packet(
        req, settlement, proof_flags, price_history, feature_inputs, lp_unit_values, pool_snapshots
    )


def _build_packet_from_attestation(
    req: EndToEndCertificateRequest,
    settlement: object,
    proof_flags: object,
    price_history: object,
    feature_inputs: object,
    lp_unit_values: dict[str, int] | None,
    pool_snapshots: tuple[object, ...] | None,
) -> object:
    from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
        build_settlement_end_to_end_certificate_packet_from_price_attestation,
    )
    from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
        SettlementSpotPriceAttestation,
    )

    price_attestation = SettlementSpotPriceAttestation.from_dict(req.price_attestation)
    return build_settlement_end_to_end_certificate_packet_from_price_attestation(
        settlement=settlement,
        proof_flags=proof_flags,
        price_history=price_history,
        feature_extension_inputs=feature_inputs,
        price_attestation=price_attestation,
        consumer_now_epoch=int(req.consumer_now_epoch),
        max_attestation_age_epochs=int(req.max_attestation_age_epochs),
        lp_unit_values=lp_unit_values,
        pool_snapshots=pool_snapshots,
        allowed_signers=req.allowed_signers,
    )


def _build_packet_from_price_packet(
    req: EndToEndCertificateRequest,
    settlement: object,
    proof_flags: object,
    price_history: object,
    feature_inputs: object,
    lp_unit_values: dict[str, int] | None,
    pool_snapshots: tuple[object, ...] | None,
) -> object:
    from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
        build_settlement_end_to_end_certificate_packet_from_price_packet,
    )
    from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
        SettlementSpotPricePacket,
    )

    price_packet = SettlementSpotPricePacket.from_dict(req.price_packet)
    return build_settlement_end_to_end_certificate_packet_from_price_packet(
        settlement=settlement,
        proof_flags=proof_flags,
        price_history=price_history,
        feature_extension_inputs=feature_inputs,
        price_packet=price_packet,
        lp_unit_values=lp_unit_values,
        pool_snapshots=pool_snapshots,
    )


def _handle_verify_end_to_end_certificate_packet(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        req = _parse_request(obj, validate_attestation=False)
        packet = obj.get("packet")
        if not isinstance(packet, dict):
            raise BadRequest("bad_packet")
        req = _with_attestation_options(req, obj)
    except BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
        return

    try:
        from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel

        settlement = _parse_settlement(req.settlement)
        proof_flags, price_history = _parse_verify_common_inputs(req)
        lp_unit_values = _parse_lp_unit_values(req.lp_unit_values)
        ok, err = _verify_packet(req, settlement, proof_flags, price_history, lp_unit_values, packet)
        write_json(200, {"ok": bool(ok), "error": err})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "verify_settlement_end_to_end_certificate_packet_error", "details": "request failed"},
        )


def _parse_verify_common_inputs(req: EndToEndCertificateRequest) -> tuple[object, object]:
    from src.integration.api_server_settlement_parsers import (  # pylint: disable=import-outside-toplevel
        _parse_price_history_payload,
        _parse_settlement_proof_flags_payload,
    )

    return (
        _parse_settlement_proof_flags_payload(req.proof_flags),
        _parse_price_history_payload(req.price_history),
    )


def _with_attestation_options(
    req: EndToEndCertificateRequest,
    obj: dict[str, object],
) -> EndToEndCertificateRequest:
    if req.price_attestation is None:
        return req
    consumer_epoch, max_age, allowed_signers = _parse_attestation_options(
        obj=obj,
        has_price_attestation=True,
        validate_attestation=True,
    )
    return EndToEndCertificateRequest(
        settlement=req.settlement,
        proof_flags=req.proof_flags,
        price_history=req.price_history,
        feature_extension_inputs=req.feature_extension_inputs,
        price_packet=req.price_packet,
        price_attestation=req.price_attestation,
        pool_snapshots=req.pool_snapshots,
        lp_unit_values=req.lp_unit_values,
        consumer_now_epoch=consumer_epoch,
        max_attestation_age_epochs=max_age,
        allowed_signers=allowed_signers,
    )


def _verify_packet(
    req: EndToEndCertificateRequest,
    settlement: object,
    proof_flags: object,
    price_history: object,
    lp_unit_values: dict[str, int] | None,
    packet: dict[str, object],
) -> tuple[bool, str | None]:
    if req.price_attestation is not None:
        return _verify_packet_from_attestation(req, settlement, proof_flags, price_history, lp_unit_values, packet)
    return _verify_packet_from_price_packet(req, settlement, proof_flags, price_history, lp_unit_values, packet)


def _verify_packet_from_attestation(
    req: EndToEndCertificateRequest,
    settlement: object,
    proof_flags: object,
    price_history: object,
    lp_unit_values: dict[str, int] | None,
    packet: dict[str, object],
) -> tuple[bool, str | None]:
    from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
        verify_settlement_end_to_end_certificate_packet_payload_from_price_attestation,
    )

    return verify_settlement_end_to_end_certificate_packet_payload_from_price_attestation(
        settlement=settlement,
        proof_flags=proof_flags,
        price_history=price_history,
        feature_extension_inputs_payload=req.feature_extension_inputs,
        price_attestation_payload=req.price_attestation,
        consumer_now_epoch=int(req.consumer_now_epoch),
        max_attestation_age_epochs=int(req.max_attestation_age_epochs),
        packet_payload=packet,
        lp_unit_values=lp_unit_values,
        pool_snapshots_payload=req.pool_snapshots,
        allowed_signers=req.allowed_signers,
    )


def _verify_packet_from_price_packet(
    req: EndToEndCertificateRequest,
    settlement: object,
    proof_flags: object,
    price_history: object,
    lp_unit_values: dict[str, int] | None,
    packet: dict[str, object],
) -> tuple[bool, str | None]:
    from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
        verify_settlement_end_to_end_certificate_packet_payload_from_price_packet,
    )

    return verify_settlement_end_to_end_certificate_packet_payload_from_price_packet(
        settlement=settlement,
        proof_flags=proof_flags,
        price_history=price_history,
        feature_extension_inputs_payload=req.feature_extension_inputs,
        price_packet_payload=req.price_packet,
        packet_payload=packet,
        lp_unit_values=lp_unit_values,
        pool_snapshots_payload=req.pool_snapshots,
    )


def maybe_handle_settlement_end_to_end_certificate_route(
    *,
    path: str,
    obj: dict[str, object],
    write_json: WriteJson,
) -> bool:
    if path == _BUILD_END_TO_END_CERTIFICATE_PACKET_ENDPOINT:
        _handle_build_end_to_end_certificate_packet(obj, write_json)
        return True
    if path == _VERIFY_END_TO_END_CERTIFICATE_PACKET_ENDPOINT:
        _handle_verify_end_to_end_certificate_packet(obj, write_json)
        return True
    return False
