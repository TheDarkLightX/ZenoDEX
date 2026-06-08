from __future__ import annotations

from typing import Callable


WriteJson = Callable[[int, object], None]

_BUILD_SPOT_PRICE_PACKET_ENDPOINT = "/api/dex/build_settlement_spot_price_packet"
_VERIFY_SPOT_PRICE_PACKET_ENDPOINT = "/api/dex/verify_settlement_spot_price_packet"
_BUILD_SPOT_PRICE_ATTESTATION_ENDPOINT = "/api/dex/build_settlement_spot_price_attestation"
_VERIFY_SPOT_PRICE_ATTESTATION_ENDPOINT = "/api/dex/verify_settlement_spot_price_attestation"


class BadRequest(Exception):
    def __init__(self, error: str) -> None:
        super().__init__(error)
        self.error = error


def _required_dict(value: object, error: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise BadRequest(error)
    return value


def _optional_dict(value: object, error: str) -> dict[str, object] | None:
    if value is None:
        return None
    if not isinstance(value, dict):
        raise BadRequest(error)
    return value


def _non_empty_list(value: object, error: str) -> list[object]:
    if not isinstance(value, list) or not value:
        raise BadRequest(error)
    return value


def _non_negative_int(value: object, error: str) -> int:
    if isinstance(value, bool):
        raise BadRequest(error)
    if not isinstance(value, int):
        raise BadRequest(error)
    if value < 0:
        raise BadRequest(error)
    return int(value)


def _bool(value: object, error: str) -> bool:
    if not isinstance(value, bool):
        raise BadRequest(error)
    return bool(value)


def _bad_request(write_json: WriteJson, error: str) -> None:
    write_json(400, {"ok": False, "error": error})


def _handle_build_spot_price_packet(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        entries_obj = _non_empty_list(obj.get("entries"), "bad_entries")
        now_epoch = _non_negative_int(obj.get("now_epoch"), "bad_now_epoch")
        max_staleness_epochs = _non_negative_int(obj.get("max_staleness_epochs"), "bad_max_staleness_epochs")
        cross_module_sync_required = _bool(
            obj.get("cross_module_sync_required", False),
            "bad_cross_module_sync_required",
        )
        cross_module_sync_contract = _optional_dict(
            obj.get("cross_module_sync_contract"),
            "bad_cross_module_sync_contract",
        )
    except BadRequest as exc:
        _bad_request(write_json, exc.error)
        return

    try:
        from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
            SettlementSpotPriceEntry,
            build_settlement_spot_price_packet,
        )

        entries = tuple(SettlementSpotPriceEntry.from_dict(entry) for entry in entries_obj)
        packet = build_settlement_spot_price_packet(
            entries=entries,
            now_epoch=int(now_epoch),
            max_staleness_epochs=int(max_staleness_epochs),
            cross_module_sync_required=bool(cross_module_sync_required),
            cross_module_sync_contract=cross_module_sync_contract,
        )
        write_json(200, {"ok": True, "packet": packet.to_dict()})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "build_settlement_spot_price_packet_error", "details": "request failed"},
        )


def _handle_verify_spot_price_packet(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        packet_obj = _required_dict(obj.get("packet"), "bad_packet")
    except BadRequest as exc:
        _bad_request(write_json, exc.error)
        return

    try:
        from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
            verify_settlement_spot_price_packet_payload,
        )

        ok, err = verify_settlement_spot_price_packet_payload(packet_obj)
        write_json(200, {"ok": bool(ok), "error": err})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "verify_settlement_spot_price_packet_error", "details": "request failed"},
        )


def _handle_build_spot_price_attestation(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        packet_obj = _required_dict(obj.get("packet"), "bad_packet")
        signer_privkey = obj.get("signer_privkey")
        if not isinstance(signer_privkey, (str, int)):
            raise BadRequest("bad_signer_privkey")
    except BadRequest as exc:
        _bad_request(write_json, exc.error)
        return

    try:
        from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
            build_settlement_spot_price_attestation,
        )
        from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
            SettlementSpotPricePacket,
        )

        packet = SettlementSpotPricePacket.from_dict(packet_obj)
        attestation = build_settlement_spot_price_attestation(
            packet=packet,
            signer_privkey=signer_privkey,
        )
        write_json(200, {"ok": True, "attestation": attestation.to_dict()})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "build_settlement_spot_price_attestation_error", "details": "request failed"},
        )


def _handle_verify_spot_price_attestation(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        attestation_obj = _required_dict(obj.get("attestation"), "bad_attestation")
        consumer_now_epoch = _non_negative_int(obj.get("consumer_now_epoch"), "bad_consumer_now_epoch")
        max_age = _non_negative_int(obj.get("max_attestation_age_epochs"), "bad_max_attestation_age_epochs")
        allowed_signers = _optional_dict(obj.get("allowed_signers"), "bad_allowed_signers")
    except BadRequest as exc:
        _bad_request(write_json, exc.error)
        return

    try:
        from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
            verify_settlement_spot_price_attestation_payload,
        )

        ok, err = verify_settlement_spot_price_attestation_payload(
            payload=attestation_obj,
            consumer_now_epoch=int(consumer_now_epoch),
            max_attestation_age_epochs=int(max_age),
            allowed_signers=allowed_signers,
        )
        write_json(200, {"ok": bool(ok), "error": err})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "verify_settlement_spot_price_attestation_error", "details": "request failed"},
        )


def maybe_handle_settlement_spot_price_route(
    *,
    path: str,
    obj: dict[str, object],
    write_json: WriteJson,
) -> bool:
    if path == _BUILD_SPOT_PRICE_PACKET_ENDPOINT:
        _handle_build_spot_price_packet(obj, write_json)
        return True
    if path == _VERIFY_SPOT_PRICE_PACKET_ENDPOINT:
        _handle_verify_spot_price_packet(obj, write_json)
        return True
    if path == _BUILD_SPOT_PRICE_ATTESTATION_ENDPOINT:
        _handle_build_spot_price_attestation(obj, write_json)
        return True
    if path == _VERIFY_SPOT_PRICE_ATTESTATION_ENDPOINT:
        _handle_verify_spot_price_attestation(obj, write_json)
        return True
    return False
